"""Replay the 35 one-gate extensions on every Heawood assignment, then cut their nested AND."""
import argparse
import json
from pathlib import Path
import re
from census import read_edges, STAGES

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parents[1] / 'check122/heawood'


def insert_duplicate(original, slot):
    replaced = 28 + slot
    duplicate_wire = 35

    def remap(port):
        if port == replaced:
            return duplicate_wire
        return port + int(port >= duplicate_wire)

    result = original[:21] + [replaced + 64*replaced]
    for gate in original[21:]:
        a = remap(gate % 64)
        b = remap(gate // 64 % 64)
        result.append(a + 64*b + 4096*int(gate >= 4096))
    return result


def evaluate(gates, inputs, cut=False):
    wires = list(inputs)
    has_and = [False]*len(wires)
    nested = []
    for index, gate in enumerate(gates):
        a, b = gate % 64, gate // 64 % 64
        if max(a, b) >= len(wires):
            raise ValueError('A control reads an unavailable wire')
        inherited = has_and[a] or has_and[b]
        if gate >= 4096:
            value = wires[a] | wires[b]
        else:
            if inherited:
                nested.append(index)
            value = 0 if inherited and cut else wires[a] & wires[b]
        wires.append(value)
        has_and.append(inherited or gate < 4096)
    return wires[-1], nested


def controls(stages, source, statement):
    edges = read_edges(stages)
    prefix = json.loads(source.read_bytes())['controls']
    text = statement.read_text().split(']; have x2', 1)[0]
    compressed = [int(n) for n in re.findall(r'\((\d+) : ℕ\)', text)]
    raw = [sum(1 << x for x in range(1 << 14) if x >> i & 1) for i in range(14)]
    records = []
    for row in prefix:
        original = row['codes']
        for slot in range(7):
            center = slot+7
            gates = insert_duplicate(original, slot)
            if len(gates) != 28 or gates[:2] != original[:2]:
                raise ValueError('Length or prescribed prefix changed')
            for inputs in (compressed, raw):
                full_target = 0
                retained_target = 0
                for a,b in edges:
                    signal = inputs[a] & inputs[b]
                    full_target |= signal
                    if center not in (a,b):
                        retained_target |= signal
                for cut, target in ((False,full_target), (True,retained_target)):
                    value, nested = evaluate(gates,inputs,cut)
                    if nested != [21] or value != target:
                        raise ValueError(f'Invalid control for opening {row["index"]} and center {center}')
            lost = [i for i, edge in enumerate(edges) if center in edge]
            if len(lost) != 3:
                raise ValueError('Invalid center degree')
            records.append(dict(opening=row['index'],center=center,nested_gate=21,
                                lost_edge_indices=lost,packed_output=evaluate(gates,compressed)[0],
                                packed_after_cut=evaluate(gates,compressed,True)[0]))
    return dict(gates=28,controls=len(records),all_assignments_per_control=16384,
                compressed_assignments_per_control=58,records=records)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stages', type=Path, default=STAGES)
    parser.add_argument('--prefixes', type=Path, default=PREVIOUS/'prefixes.json')
    parser.add_argument('--statement', type=Path, default=PREVIOUS/'statement.txt')
    args = parser.parse_args()
    print(json.dumps(controls(args.stages,args.prefixes,args.statement),indent=2))
