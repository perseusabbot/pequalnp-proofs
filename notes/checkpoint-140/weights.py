"""Verify the nonnegative integer weight certificates against the upstream matrix."""
import argparse
from collections import Counter
import gzip
from hashlib import sha256
from functools import reduce
from operator import and_
import json
from pathlib import Path
import re

import numpy as np
from input_data import HERE, ROWS, group, require

PIN = 'd036a648649d11adbb25b8ed6d9e7ac34d1edd24e56b14e8891e6408502a093a'
FULL = (1 << 21) - 1


def positions(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


class Checker:
    def __init__(self, matrix):
        source = matrix.read_bytes()
        require(sha256(source).hexdigest() == PIN, 'The upstream matrix source differs')
        match = re.search(rb'^def incidence : List Nat := \[([0-9, ]+)\]$', source, re.M)
        require(match is not None, 'The source has no incidence matrix')
        self.rows = [FULL ^ int(x) for x in match.group(1).split(b',')]
        require(self.rows == list(ROWS), 'The symmetry generators use a different board')
        self.cells = [(p, q) for p, mask in enumerate(self.rows) for q in positions(mask)]
        self.coords = {c: i for i, c in enumerate(self.cells)}
        intersections = {FULL}
        for row in self.rows:
            intersections.update({row & b for b in intersections})
        boxes = []
        for b in intersections - {0}:
            a = sum(1 << p for p, row in enumerate(self.rows) if row & b == b)
            if a:
                require(reduce(and_, (self.rows[p] for p in positions(a))) == b, 'A rectangle fails closure')
                boxes.append((a, b))
        self.maximum = sorted((a, b) for a, b in boxes if a.bit_count() * b.bit_count() == 36)
        self.other = sorted(set(boxes) - set(self.maximum))
        require(len(self.maximum) == 168 and len(self.other) == 25067, 'Maximal rectangles differ')
        self.lookup = {a | b << 21: i for i, (a, b) in enumerate(self.other)}
        self.postings = np.full((len(self.other), 28), len(self.cells), dtype=np.int32)
        for i, box in enumerate(self.other):
            entries = self.box_cells(box)
            self.postings[i, :len(entries)] = entries
        self.group = group()
        self.first = {}
        self.stats = Counter()
        self.depths = Counter()
        self.physical = Counter()
        self.himages = {}
        self.actions = np.frombuffer(b''.join(self.group), dtype=np.uint8).reshape(-1, 42)
        self.hwords = np.array([a | b << 21 for a, b in self.maximum], dtype=np.uint64)
        self.horder = np.argsort(self.hwords)

    def box_cells(self, box):
        a, b = box
        return [self.coords[p, q] for p in positions(a) for q in positions(b)]

    def fixing(self, elements, box):
        a, b = box
        word = a | (b << 21)
        key = elements is self.group
        if key and word in self.first:
            return self.first[word]
        indices = list(positions(word))
        sub = [g for g in elements if all(word >> g[x] & 1 for x in indices)]
        if key: self.first[word] = sub
        return sub

    def himage(self, h):
        if h not in self.himages:
            word = int(self.hwords[h])
            image = np.zeros(len(self.group), dtype=np.uint64)
            for p in positions(word):
                image |= np.left_shift(np.uint64(1), self.actions[:, p].astype(np.uint64))
            ix = np.searchsorted(self.hwords[self.horder], image)
            require(np.array_equal(self.hwords[self.horder[ix]], image), 'A maximum rectangle image is missing')
            self.himages[h] = self.horder[ix].astype(np.int32)
        return self.himages[h]

    def complete_maximum_orbits(self, cases, k):
        from math import comb
        if k == 0:
            require([r['maximum'] for r in cases] == [[]], 'Missing empty family')
            return 1
        seen = np.zeros(comb(168, k), dtype=bool)
        choose = np.array([[comb(i, j) for i in range(168)] for j in range(k + 1)], dtype=np.int32)
        for case in cases:
            ids = case['maximum']
            require(len(ids) == k and ids == sorted(set(ids)) and all(0 <= h < 168 for h in ids), 'Invalid family')
            images = np.sort(np.stack([self.himage(h) for h in ids]), axis=0)
            pos = sum(choose[j + 1, images[j]] for j in range(k))
            require(not np.any(seen[pos]), 'Maximum-rectangle orbits intersect')
            seen[pos] = True
        require(np.all(seen), 'Some fixed maximum rectangles are missing')
        return len(seen)

    def orbit(self, elements, e):
        a, b = self.other[e]
        labels = list(positions(a | (b << 21)))
        return {self.lookup[sum(1 << g[i] for i in labels)] for g in elements}

    def invariant(self, elements, weights):
        if len(elements) == 1 or np.all(weights == weights[0]): return
        left = set(range(336))
        while left:
            i = min(left)
            p, q = self.cells[i]
            orbit = set()
            for g in elements:
                r, c = sorted((g[p], g[q + 21]))
                orbit.add(self.coords[r, c - 21])
            require(i in orbit and orbit <= left and all(weights[j] == weights[i] for j in orbit),
                    'Weights vary within a symmetry orbit')
            left -= orbit

    def loads(self, w):
        padded = np.append(w, np.int64(0))
        return padded[self.postings].sum(axis=1)

    def node(self, record, holes, allowed, elements, slots, depth):
        raw = record['w']
        require(len(raw) == 336 and all(type(v) is int and 0 <= v <= 1000000 for v in raw), 'Invalid integer weights')
        w = np.asarray(raw, dtype=np.int64)
        require(not np.any(w[~holes]), 'A covered cell carries weight')
        total = int(w.sum())
        require(total > 0 and slots > 0, 'Invalid residual budget or weight')
        load = self.loads(w)
        candidates = set(map(int, np.flatnonzero(allowed & (slots * load >= total))))
        children = record.get('children', [])
        self.stats['nodes'] += 1
        self.depths[depth] += 1
        if not candidates:
            require(not children, 'A terminal certificate has extra branches')
            self.stats['leaves'] += 1
            return
        self.invariant(elements, w)
        self.stats['splits'] += 1
        self.physical[depth] += len(candidates)
        for e, child in children:
            require(type(e) is int and e in candidates, 'A marked rectangle is repeated or ineligible')
            orbit = self.orbit(elements, e)
            require(e in orbit and orbit <= candidates, 'The marked orbit leaves the eligible set')
            candidates -= orbit
            box = self.other[e]
            next_holes = holes.copy()
            next_holes[self.box_cells(box)] = False
            fresh = w * next_holes
            cap = int(load[e])
            floor = int(fresh.sum()) - (slots - 2) * cap
            next_allowed = allowed & (load <= cap)
            if floor > 0:
                next_allowed &= self.loads(fresh) >= floor
            next_allowed[e] = False
            self.node(child, next_holes, next_allowed, self.fixing(elements, box), slots - 1, depth + 1)
        require(not candidates, 'A possible heaviest rectangle was omitted')

    def stratum(self, name):
        packet = gzip.decompress((HERE / 'certificates' / (name + '.json.gz')).read_bytes())
        proof = json.loads(packet)
        k, cases = proof['fixed_maximum_count'], proof['cases']
        area_cap = proof.get('exceptional_area_cap', 28)
        require(area_cap in (27,28) and 0 <= k <= 3, 'Unsupported initial stratum')
        mass = self.complete_maximum_orbits(cases, k)
        allowed = np.array([a.bit_count() * b.bit_count() <= area_cap for a, b in self.other])
        self.stats.clear(); self.depths.clear(); self.physical.clear()
        for case in cases:
            holes = np.ones(336, dtype=bool)
            elements = self.group
            for j in case['maximum']:
                box = self.maximum[j]; holes[self.box_cells(box)] = False
                elements = self.fixing(elements, box)
            self.node(case['proof'], holes, allowed, elements, 13-k, 0)
        return dict(fixed_maximum_count=k, exceptional_area_cap=area_cap, physical_maximum_families=mass,
                    maximum_representatives=len(cases), **self.stats, nodes_by_depth=dict(sorted(self.depths.items())),
                    eligible_marks_by_depth=dict(sorted(self.physical.items())), certificate_sha256=sha256(packet).hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('matrix', type=Path)
    parser.add_argument('strata', nargs='+')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    checker = Checker(args.matrix)
    result = {n: checker.stratum(n) for n in args.strata}
    if args.output: args.output.write_text(json.dumps(result, indent=2) + '\n')
    else:
        expected = json.loads((HERE/'weights.json').read_bytes())
        require(json.loads(json.dumps(result)) == {n: expected[n] for n in args.strata}, 'Published weight receipt differs')
    for k, r in result.items(): print(k, r['nodes'], 'exact integer certificates verified')
