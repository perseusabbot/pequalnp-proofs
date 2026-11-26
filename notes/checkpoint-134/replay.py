"""Build the exact translation theorem and audit the declarations printed by its sources."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
UPSTREAM = '501dda8586110abcaebe0ea32060309d020bb2ee'
MATHLIB = 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
DECLARATIONS = {'Checkpoint134.exactMinimum', 'Checkpoint134.smallCoverTranslations',
                'Checkpoint134.stableMinimum', 'Checkpoint134.noFour',
                'Checkpoint134.noThree', 'Checkpoint134.noTwo'}


def command(args, cwd):
    return subprocess.check_output(args,cwd=cwd,text=True).strip()


def dependencies():
    roots = [HERE/'src',HERE.parent/'checkpoint-133'/'src']
    available = {p.stem:p for folder in reversed(roots) for p in folder.glob('*.lean')}
    graph = {}
    def visit(name):
        if name not in graph:
            raw = available[name].read_text()
            found = re.findall(r'^import\s+(\S+)',raw,re.MULTILINE)
            graph[name] = {n for n in found if n in available}
            for n in graph[name]:
                visit(n)
    visit('AllTranslations')
    visit('OrderFive')
    if not {p.stem for p in roots[0].glob('*.lean')} <= graph.keys():
        raise ValueError('An unreferenced Checkpoint 134 module is present')
    return graph, available


def read_audits(text, source):
    if 'sorryAx' in text or ': error' in text:
        raise ValueError('Unverified declaration in '+source.name)
    found = {name:sorted(set(a.split(', ')) if a else set())
             for name,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms",text):
        found[name]=[]
    wanted = re.findall(r'^#print axioms (\S+)',source.read_text(),re.MULTILINE)
    if len(wanted)!=len(found) or any(not any(n==w or n.endswith('.'+w) for n in found) for w in wanted):
        raise ValueError('Missing axiom audit in '+source.name)
    if any(set(a)-STANDARD for a in found.values()):
        raise ValueError('Unexpected axiom in '+source.name)
    return found


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('project',type=Path,help='Upstream Git checkout at the documented revision')
    ap.add_argument('--build',type=Path,required=True,help='Empty directory for objects, logs and receipt')
    ap.add_argument('--jobs',type=int,default=1,help='Concurrent Lean jobs')
    args=ap.parse_args()
    if args.jobs<1:
        ap.error('--jobs must be positive')
    project=args.project.resolve()
    target=args.build.resolve()
    target.mkdir(exist_ok=True,parents=True)
    if any(target.iterdir()):
        raise ValueError('Choose an empty build directory')
    if command(['git','rev-parse','HEAD'],project)!=UPSTREAM:
        raise ValueError('Expected upstream '+UPSTREAM)
    subprocess.run(['git','diff','--quiet','HEAD','--','lean'],cwd=project,check=True)
    lean_dir=project/'lean'
    manifest=json.loads((lean_dir/'lake-manifest.json').read_text())
    if next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')!=MATHLIB:
        raise ValueError('Unexpected Mathlib revision')
    with (target/'upstream.log').open('w') as log:
        subprocess.run(['lake','build','+PEqualNP.Outside.L_meta_9338','+PEqualNP.Outside.L_meta_9351'],
                       cwd=lean_dir,stdout=log,stderr=subprocess.STDOUT,check=True,
                       env=dict(os.environ,LEAN_NUM_THREADS='1'))
    lean=command(['lake','env','which','lean'],lean_dir)
    version=command([lean,'--version'],lean_dir)
    if 'version 4.36.0' not in version:
        raise ValueError('Expected Lean 4.36.0')
    paths=[(lean_dir/p).resolve() for p in command(['lake','env','printenv','LEAN_PATH'],lean_dir).split(os.pathsep)]
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[target,*paths])),LEAN_NUM_THREADS='1')
    graph, available=dependencies()
    def check(name):
        file=available[name]
        output=target/(name+'.olean')
        logfile=target/(name+'.log')
        with logfile.open('w') as log:
            subprocess.run([lean,'-j1','-M','7500','-R',str(file.parent),'-o',str(output),str(file)],cwd=lean_dir,
                           env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
        audits=read_audits(logfile.read_text(),file)
        print(name,flush=True)
        return name,dict(source_sha256=sha256(file.read_bytes()).hexdigest(),audits=audits)
    results={}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while len(results)<len(graph):
            ready=sorted(n for n,deps in graph.items() if n not in results and deps<=results.keys())
            if not ready:
                raise ValueError('Dependency cycle')
            results.update(pool.map(check,ready))
    statements={n for v in results.values() for n in v['audits']}
    if not DECLARATIONS<=statements:
        raise ValueError('Final declarations missing')
    receipt=dict(lean=version,upstream=UPSTREAM,mathlib=MATHLIB,modules=results)
    (target/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(len(results),'modules checked,',len(statements),'declarations audited')


if __name__=='__main__':
    main()
