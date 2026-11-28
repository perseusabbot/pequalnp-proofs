"""Restore a compact size-14 journal into a new directory for fourteen.py."""
import argparse
import gzip
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory


def decode(anchors, packed, state, signature):
    if state['status'] not in ('running', 'paused', 'complete') or signature['budget'] != 14:
        raise ValueError('Unsupported status or budget')
    if sha256(anchors).hexdigest() != signature['anchors_sha256']:
        raise ValueError('The anchor digest differs')
    seeds = [int(row.split()[-1]) for row in anchors.splitlines()]
    if len(seeds) != state['total_orbits'] or len(seeds) != 121572 or sum(seeds) != 28530983404:
        raise ValueError('Invalid six-rectangle inventory')
    limit = signature['block_size']
    rows = gzip.decompress(packed).splitlines(keepends=True)
    if limit != 64 or len(rows) != min(state['completed_blocks'] * limit, len(seeds)):
        raise ValueError('Truncated search blocks')
    if state['completed_blocks'] != (len(rows) + limit - 1) // limit:
        raise ValueError('Invalid block count')
    if state['status'] == 'complete' and len(rows) != len(seeds):
        raise ValueError('Incomplete final journal')
    states = 0
    for i, line in enumerate(rows):
        kind, idx, mass, holes, nodes = line.split()
        if (kind != b'EXCLUDED' or int(idx) != i or int(mass) != seeds[i]
                or not 120 <= int(holes) <= 336 or int(nodes) < 1 or not line.endswith(b'\n')):
            raise ValueError(f'Invalid decision at orbit {i}')
        states += int(nodes)
    if (len(rows), states, sum(seeds[:len(rows)])) != (
            state['excluded'], state['search_states'], state['physical_six_subsets_excluded']):
        raise ValueError('Receipt and totals differ')
    return [b''.join(rows[i:i + limit]) for i in range(0, len(rows), limit)]


def restore(source, destination):
    if destination.exists():
        raise FileExistsError(f'The destination already exists: {destination}')
    signature = (source / 'signature.json').read_bytes()
    anchors = (source / 'anchors.txt').read_bytes()
    state = json.loads((source / 'status.json').read_bytes())
    blocks = decode(anchors, (source / 'blocks.tsv.gz').read_bytes(), state, json.loads(signature))
    with TemporaryDirectory(dir=destination.parent) as temporary:
        prepared = Path(temporary) / 'journal'
        (prepared / 'blocks').mkdir(parents=True)
        (prepared / 'signature.json').write_bytes(signature)
        (prepared / 'anchors.txt').write_bytes(anchors)
        state.update(status='complete' if state['excluded'] == state['total_orbits'] else 'paused', pid=None)
        (prepared / 'status.json').write_text(json.dumps(state) + '\n')
        for i, block in enumerate(blocks):
            (prepared / 'blocks' / f'{i:05}.tsv').write_bytes(block)
        prepared.rename(destination)
    print(state['excluded'], 'six-rectangle orbits restored')


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path)
    ap.add_argument('destination', type=Path)
    args = ap.parse_args()
    restore(args.source, args.destination)
