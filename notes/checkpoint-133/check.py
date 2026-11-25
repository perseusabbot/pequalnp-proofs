"""Reproduce the finite enumerations and check the constructions on every input."""
import itertools
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from plane import ALL, HERE, LINES, ROWS, check, rotates


def read(name):
    return json.loads((HERE / name).read_text())


def build(output, source):
    subprocess.run(['c++', '-std=c++20', '-O3', str(source), '-o', str(output)], check=True)


def run(binary, data=''):
    return subprocess.check_output([str(binary)], input=data, text=True)


def plane_examples():
    results = read('plane-results.json')
    examples = read('plane-examples.json')
    actual = {(i,j) for i,row in enumerate(LINES) for j in range(21) if not row >> j & 1}
    for tag, expected in [('unrestricted',334), ('two_orbits',308)]:
        record = examples[tag]
        boxes = record['rectangles']
        check(len(boxes) == len({tuple(b) for b in boxes}) == 14, 'Rectangle count')
        check(all(0 < x <= ALL for box in boxes for x in box), 'Board size')
        hit = {(i,j) for a,b in boxes for i in range(21) if a >> i & 1
               for j in range(21) if b >> j & 1}
        check(hit <= actual and len(hit) == expected == record['covered'], tag)
        check(sorted(actual-hit) == [tuple(p) for p in record['missing']], 'Missing cells')
    generated = [[rotates(a,q), rotates(b,q)] for a,b in results['example'] for q in range(7)]
    check(examples['two_orbits']['rectangles'] == generated, 'Order-seven example')
    return examples['unrestricted']['rectangles']


def reference(directory):
    executable = directory / 'reference'
    build(executable, HERE/'reference.cpp')
    header, *hist = run(executable).splitlines()
    counts = read('plane-results.json')
    check(list(map(int, header.split())) == [counts[k] for k in
          ('maximal_rectangles','rectangle_orbits','distinct_signatures','pairs')], 'Direct subset census')
    check({k:int(v) for k,v in (line.split() for line in hist)} == counts['pair_histogram'],
          'Direct subset histogram')


def repair_checks(directory, boxes):
    executable = directory / 'repair'
    build(executable, HERE/'repair.cpp')
    body = ' '.join(map(str,ROWS))+'\n'+''.join(f'{a} {b}\n' for a,b in boxes)
    for k, record in enumerate(read('repair-results.json'),1):
        actual = run(executable, f'21 14 {k}\n'+body).strip()
        check(actual == record and actual.startswith('EXCLUDED '), 'Replacement window '+str(k))
    print('Exact replacement searches:', record, flush=True)


def wheel_checks(directory):
    record = read('wheel.json')
    rim = {(i,1+i%6) for i in range(1,7)}
    edges = rim | {(0,i) for i in range(1,7)}
    truth = [any((row >> i) & (row >> j) & 1 for i,j in edges) for row in range(128)]
    for row in range(128):
        wires = [(row >> i) & 1 for i in range(7)]
        for op,a,b in record['gates']:
            check(op in ('and','or') and 0 <= a < len(wires) and 0 <= b < len(wires), 'Gate encoding')
            wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
        check(wires[-1] == truth[row], 'Wheel row '+str(row))
    check(len(record['gates']) == 13, 'Wheel size')
    lo = [x for x in range(128) if truth[x] and all(not truth[x ^ (1<<i)] for i in range(7) if x>>i&1)]
    hi = [x for x in range(128) if not truth[x] and all(truth[x ^ (1<<i)] for i in range(7) if not x>>i&1)]
    automorphisms = []
    for perm in itertools.permutations(range(7)):
        if all(sum((1<<perm[i]) for i in range(7) if x>>i&1) in lo for x in lo):
            automorphisms.append(perm)
    check((len(lo),len(hi),len(automorphisms)) == (12,6,12), 'Extremal rows or symmetry')
    columns = [sum(((x>>i)&1)<<j for j,x in enumerate(lo+hi)) for i in range(7)]
    exe = directory/'monotone'
    build(exe, HERE.parent/'heawood-132'/'symmetry_search.cpp')
    for cap in (12,13):
        params = [[cap,len(lo),len(hi),7,0], columns, [len(automorphisms)], *automorphisms]
        data = ''.join(' '.join(map(str,r))+'\n' for r in params)
        lines = run(exe,data).splitlines()
        verdict,roots,states = lines[0].split()
        want = record['cap'+str(cap)]
        check((verdict,roots,int(states)) == (want['result'],'1',want['states']), 'Wheel enumeration')
        if verdict == 'YES':
            words = columns.copy()
            for row, (op,i,j) in zip(lines[1:],record['gates'],strict=True):
                a,b,bit,z = map(int,row.split())
                check((a,b,bit)==(words[i],words[j],int(op=='or')), 'Wheel trace')
                check(z==(a|b if bit else a&b), 'Wheel wire')
                words.append(z)
            check(words[-1] == (1<<len(lo))-1, 'Wheel output')
    print('Wheel: all 128 assignments, 12-gate exhaustion and 13-gate construction reproduced.',flush=True)


def target_checks():
    t = read('desk-targets.json')
    rows = list(map(int,re.search(r'\[([0-9, ]+)\]',t['L-meta-9348']['statement']).group(1).split(',')))
    check(rows == LINES and t['L-meta-9350']['statement']=='¬ ('+t['L-meta-9348']['statement']+')','Posted board')
    p = (HERE/'src'/'PetersenCofactors.lean').read_text().split('def edge ',1)[1].split('def restore',1)[0]
    pairs = lambda s: re.findall(r'x (\d+) && x (\d+)',s)
    check(len(pairs(p)) == 15 and pairs(p) == pairs(t['L-meta-651']['statement']), 'Posted Petersen graph')
    check(t['L-meta-16082']['statement'] in (HERE/'src'/'Wheel133.lean').read_text(), 'Posted wheel target')


if __name__=='__main__':
    target_checks()
    subprocess.run([sys.executable,'-B',str(HERE/'plane.py')],check=True)
    rectangles = plane_examples()
    with tempfile.TemporaryDirectory() as td:
        directory = Path(td)
        reference(directory)
        repair_checks(directory,rectangles)
        wheel_checks(directory)
    print('Independent counts match for all 6,175,855 pairs. Explicit families cover 334 and 308 of 336.')
