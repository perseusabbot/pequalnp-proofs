"""Rebuild both censuses, run both exact searches and check the control circuits."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from generate_lean import generate, transport_tables, local_controls
from inheritance import cover_layers
from instances import HERE, EDGES, ENDS, census, endpoints, instance, search_line


def check(condition, message):
    if not condition:
        raise ValueError(message)


def compile_engines(directory):
    binaries = []
    for name in ('live_search','available_search'):
        binary = directory/name
        subprocess.run(['c++','-O3','-std=c++17','-Wall','-Wextra',str(HERE/(name+'.cpp')),
                        '-o',str(binary)],check=True)
        binaries.append(binary)
    return binaries


def run_both(binaries, c, cap):
    result = subprocess.check_output([binaries[0]],input=search_line(c, cap),text=True).split()
    check(len(result)==3 and result[0] in ('Y','N'), 'Incomplete last-use search')
    availability = json.loads(subprocess.check_output(
        [binaries[1],str(c['representative']),str(c['sample_vertices']),str(cap)],text=True))
    check((len(c['positive_rows']),len(c['negative_rows']))==
          (availability['positive_rows'],availability['negative_rows']), 'Independent row counts differ')
    check((result[0]=='Y')==availability['possible'], 'Independent circuit decisions differ')
    return dict(possible=availability['possible'],last_use_states=int(result[1]),
                root_supports=int(result[2]),available_states=availability['expanded_states'])


def small_oracle(c, cap):
    # Enumerate every possible next gate with all old ports available. This small
    # control oracle has no leaf bound, separation pruning or last-use hypothesis.
    data = list(map(int,search_line(c,cap).split()))
    target = (1 << data[1])-1
    states = {frozenset(data[4:])}
    for k in range(cap+1):
        if any(target in state for state in states):
            return True
        if k==cap:
            return False
        states = {state | {value} for state in states for a,b in combinations(state,2)
                  for value in (a & b,a | b) if value not in state}


def controls(binaries):
    tested = []
    for mask, caps in [(1,(0,1)),(3,(1,2)),(7,(2,3)),(9,(1,2)),(65,(2,3)),(73,(3,4))]:
        c = instance(mask,endpoints(mask))
        for cap in caps:
            answer = run_both(binaries,c,cap)['possible']
            check(answer==small_oracle(c,cap), 'Tiny oracle mismatch')
            tested.append([mask,cap,answer])
    check(any(r[2] for r in tested) and any(not r[2] for r in tested), 'Missing control outcome')
    return tested


def local_control(filename, points, expected_gates):
    c = json.loads((HERE/filename).read_text())
    mask = c['representative']
    sample = instance(mask,points)
    order = [v for v in range(14) if points >> v & 1]
    check(c['vertex_order']==order and len(order)==10, 'Incorrect vertex labels')
    def pack(m):
        return sum(1 << i for i,v in enumerate(order) if m >> v & 1)
    internal = [e for e in ENDS if e & points == e]
    check(sample['positive_rows']==internal, 'Unexpected surviving internal edge')
    check(c['signals']==[pack(m) for m in sample['signals']] and
          c['edge_words']==[pack(e) for e in internal], 'Incorrect control port table')
    adjacent = {v:{w for w in order if (1 << v) | (1 << w) in internal} for v in order}
    centers = {v for v in order if len(adjacent[v])==3}
    middles = set(order)-centers
    if filename=='k4.json':
        check(len(centers)==4 and {frozenset(adjacent[v]) for v in middles}==
              {frozenset(pair) for pair in combinations(centers,2)}, 'Not a subdivided K4')
    check(len(c['gates'])==expected_gates, 'Incorrect gate count')
    for row in range(1 << len(order)):
        wires = [bool(row & s) for s in c['signals']]
        for op,a,b in c['gates']:
            check(op in ('AND','OR') and min(a,b)>=0 and max(a,b)<len(wires), 'Invalid gate')
            wires.append(wires[a] and wires[b] if op=='AND' else wires[a] or wires[b])
        check(wires[c['output']]==any(row & e == e for e in c['edge_words']), 'Control fails')
    return dict(representative=mask,vertices=len(order),gates=len(c['gates']),assignments=1 << len(order),
                allowed_signals=len(c['signals']))


def verify(directory):
    for filename, source in [*generate(), *transport_tables(), *local_controls()]:
        check((HERE/'src'/filename).read_text()==source,'Lean table mismatch for '+filename)
    binaries = compile_engines(directory)
    small = controls(binaries)
    k4 = local_control('k4.json',endpoints(32711),15)
    five = local_control('five_stars.json',11679,16)
    screens = json.loads((HERE/'screens.json').read_text())
    records = {c['representative']:c for c in screens}
    check(len(records)==len(screens), 'Duplicate representative')
    layers = census(range(12,22))
    totals = []
    visited = set()
    for layer in layers[:2]:
        results = []
        for orbit in layer.pop('orbits'):
            m = orbit['representative']
            c = records[m]
            expected = dict(**instance(m,c['sample_vertices']),orbit_size=orbit['size'],stabilizer=orbit['stabilizer'])
            check(c==expected, 'Row table, matching or orbit mismatch for '+str(m))
            r = run_both(binaries,c,c['gate_cap'])
            check(not r['possible'], 'A projection admits a circuit: '+str(m))
            results.append(dict(representative=m,**r))
            visited.add(m)
        totals.append(dict(**layer,representatives=len(results),exhaustions=results))
        print(f"Excluded {layer['candidates']} candidates in {len(results)} symmetry classes at {layer['losses']} losses.",
              file=sys.stderr,flush=True)
    supplement = []
    for orbit in layers[2]['orbits']:
        m = orbit['representative']
        if m not in records:
            continue
        c = records[m]
        check(c==dict(**instance(m,c['sample_vertices']),orbit_size=orbit['size'],stabilizer=orbit['stabilizer']),
              'Supplementary row table mismatch')
        r = run_both(binaries,c,c['gate_cap'])
        check(not r['possible'], 'Supplementary projection admits a circuit')
        supplement.append(dict(representative=m,**r))
        visited.add(m)
    check(visited==set(records) and k4['representative'] in visited,'Missing or unreferenced case')
    higher = cover_layers(layers[2:],screens)
    transferred = [q for q in higher[0]['certificates'] if not q.get('direct')]
    check(transferred==json.loads((HERE/'transfers.json').read_text()), 'Transferred Lean tables differ')
    print(f"At fourteen losses, {higher[0]['remaining']} labelings remain after the projected tests.",
          file=sys.stderr,flush=True)
    return dict(layers=totals,additional_checks=supplement,higher_layers=higher,small_controls=small,k4_control=k4,five_star_control=five)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='write a fresh result instead of comparing the published one')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temp:
        result = verify(Path(temp))
    if args.output:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    else:
        check(result==json.loads((HERE/'results.json').read_text()), 'Published result differs')
        print('All census, search and control results reproduced.')


if __name__=='__main__':
    main()
