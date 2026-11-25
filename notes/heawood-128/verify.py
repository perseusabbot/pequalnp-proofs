"""Recompute every numerical result and compare two different exhaustive searches."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def run(*cmd):
    return subprocess.check_output(cmd,cwd=HERE)


def saved(name):
    return (HERE/name).read_bytes()


def main():
    theta = run(sys.executable,'-B','theta_check.py')
    boundary = run(sys.executable,'-B','boundary.py')
    if theta != saved('theta_search.json') or boundary != saved('boundary.json'):
        raise ValueError('Python enumeration differs from the recorded tables')
    theta,boundary=json.loads(theta),json.loads(boundary)
    cases=[(1,0),(1,1)]+[(16071,x['cap']) for x in theta['search']]
    expected={(1,0):False,(1,1):True}
    expected.update({(16071,x['cap']):x['possible'] for x in theta['search']})
    for model in boundary['orbits']:
        case=(model['representative'],model['gate_cap'])
        cases.append(case)
        expected[case]=model['search']['possible']
    with TemporaryDirectory() as tmp:
        binary=str(Path(tmp)/'availability')
        subprocess.run([os.environ.get('CXX','c++'),'-std=c++17','-O3','-Wall','-Wextra','-pedantic',
                        str(HERE/'availability.cpp'),'-o',binary],check=True)
        results=[json.loads(run(binary,str(m),str(k))) for m,k in cases]
    if results!=json.loads(saved('availability.json')):
        raise ValueError('Independent availability search differs from its record')
    for model in boundary['orbits']:
        record=next(x for x in results if x['mask']==model['representative'])
        if (record['positive_rows'],record['negative_rows'],record['input_signatures'])!=(
                len(model['positive_rows']),len(model['maximal_negative_rows']),len(model['regular_signals'])):
            raise ValueError('The independent input or row counts differ')
    if any(x['possible']!=expected[(x['mask'],x['cap'])] for x in results):
        raise ValueError('The two searches disagree')
    print(f"Exact theta minimum {theta['minimum_gates']}. All {boundary['prior_candidates']} eleven-loss masks excluded.")
    print(f"{boundary['checked_masks']} eleven-edge sets and {len(boundary['orbits'])} representatives checked.")


if __name__=='__main__':
    main()
