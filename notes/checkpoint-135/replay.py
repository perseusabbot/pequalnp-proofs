"""Check the finite certificates and audit every printed Lean declaration."""
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
STANDARD = {'propext','Classical.choice','Quot.sound'}


def audit(source, log):
    if 'sorryAx' in log or ': error:' in log or re.search(r'\b(sorry|admit|native_decide)\b',source.read_text()):
        raise ValueError(f'Unverified declaration in {source.name}')
    found={n:sorted(set(a.split(', '))) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",log):
        found[n]=[]
    names=re.findall(r'^#print axioms (\S+)',source.read_text(),re.M)
    if len(names)!=len(found) or any(not any(n.endswith('.'+name) for n in found) for name in names):
        raise ValueError(f'Incomplete axiom audit in {source.name}')
    if any(set(v)-STANDARD for v in found.values()):
        raise ValueError(f'Additional axiom in {source.name}')
    return {'source_sha256':sha256(source.read_bytes()).hexdigest(),'audits':found}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('upstream',type=Path)
    ap.add_argument('--build',type=Path,required=True,help='Directory for objects, logs and the receipt')
    ap.add_argument('--jobs',type=int,default=1)
    args=ap.parse_args()
    if args.jobs<1:
        raise ValueError('At least one worker is required')
    upstream=args.upstream.resolve()
    project=upstream/'lean'
    build=args.build.resolve()
    build.mkdir(parents=True,exist_ok=True)
    def output(*args,cwd=project):
        return subprocess.check_output(list(args),cwd=cwd,text=True).strip()
    if output('git','rev-parse','HEAD',cwd=upstream)!=UPSTREAM:
        raise ValueError(f'Expected upstream revision {UPSTREAM}')
    manifest=json.loads((project/'lake-manifest.json').read_text())
    if next(x['rev'] for x in manifest['packages'] if x['name']=='mathlib')!=MATHLIB:
        raise ValueError(f'Expected mathlib revision {MATHLIB}')
    with (build/'upstream.log').open('w') as log:
        subprocess.run(['lake','build','+PEqualNP.Outside.L_meta_9338'],cwd=project,
                       stdout=log,stderr=subprocess.STDOUT,check=True)
    lean=output('lake','env','which','lean')
    version=output(lean,'--version')
    if 'version 4.36.0' not in version:
        raise ValueError('Lean toolchain differs')
    path=[build,*[(project/p).resolve() for p in output('lake','env','printenv','LEAN_PATH').split(os.pathsep)]]
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,path)),LEAN_NUM_THREADS='1')
    sources={p.stem:p for p in (HERE/'src').glob('*.lean')}
    deps={n:set(re.findall(r'^import (\S+)',p.read_text(),re.M))&sources.keys() for n,p in sources.items()}
    def check(n):
        file=sources[n]
        logfile=build/(n+'.log')
        with logfile.open('w') as log:
            subprocess.run([lean,'-j1','-M','6000','-R',str(file.parent),'-o',str(build/(n+'.olean')),str(file)],
                           cwd=project,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
        print(n,flush=True)
        return n,audit(file,logfile.read_text())
    checked={}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while len(checked)<len(sources):
            ready=sorted(n for n,d in deps.items() if n not in checked and d<=checked.keys())
            if not ready:
                raise ValueError('Proof module cycle')
            checked.update(pool.map(check,ready))
    report=dict(lean=version,upstream=UPSTREAM,mathlib=MATHLIB,modules=checked)
    (build/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(len(checked),'modules checked')

if __name__=='__main__':
    main()
