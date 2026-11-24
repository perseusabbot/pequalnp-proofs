"""Exhaust single-gate repairs after a deletion in each compatible canonical schedule."""
import argparse
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from prefixes import HERE, STAGES, build, encode, families, read_inputs


def check(executable, columns, schedules):
    rows = [' '.join(map(str, columns))]
    for i, gates in schedules:
        rows.append(' '.join(map(str, [i, len(gates), *gates])))
    out = subprocess.run([executable], input='\n'.join(rows)+'\n', capture_output=True,
                         text=True, check=True).stdout
    fields = ('index', 'schedules', 'deletions_with_rerouting', 'replacement_tuples',
              'tuples_after_suffix_screen', 'solutions')
    return [dict(zip(fields, map(int, line.split()), strict=True)) for line in out.splitlines()]


def scan(statement, stages):
    columns, keys, edges = read_inputs(statement, stages)
    neighbors = [set() for _ in columns]
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    schedules = [(i, build(p, cs, neighbors, pairs)) for i, p, cs, pairs in families(keys, neighbors)]
    with TemporaryDirectory() as td:
        exe = Path(td)/'repairs'
        subprocess.run(['c++','-std=c++17','-O3','-Wall','-Wextra','-Werror',
                        str(HERE/'repairs.cpp'),'-o',str(exe)],check=True)
        i, gs = schedules[0]
        last = 13 + len(gs)
        control = check(exe, columns, [(i, gs+[encode(last,last,True)])])[0]
        if not control['solutions']:
            raise ValueError('Deletion search missed the padded positive control')
        result = check(exe, columns, schedules)
    totals = {field: sum(row[field] for row in result) for field in result[0] if field != 'index'}
    return dict(per_index=result, total=totals, padded_28_gate_control=control,
                row_count=58, canonical_schedule_rule='two forced ORs, missing pairs and triples in center order, products in center order, left fold of products')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--statement',type=Path,default=HERE/'statement.txt')
    parser.add_argument('--stages',type=Path,default=STAGES)
    args=parser.parse_args()
    print(json.dumps(scan(args.statement,args.stages),indent=2))
