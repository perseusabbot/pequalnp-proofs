"""Rebuild Checkpoint 136 from the posted board and audit its Lean declarations."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from importlib.util import module_from_spec, spec_from_file_location
import json
import os
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
PARENT=HERE.parent/'checkpoint-135'
spec=spec_from_file_location('previous_proof_audit',PARENT/'replay.py')
prior=module_from_spec(spec)
spec.loader.exec_module(prior)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('upstream',type=Path)
    ap.add_argument('--build',type=Path,required=True)
    ap.add_argument('--jobs',type=int,default=1)
    args=ap.parse_args()
    if args.jobs<1:raise ValueError('At least one worker is required')
    upstream=args.upstream.resolve(); project=upstream/'lean'; build=args.build.resolve()
    build.mkdir(parents=True,exist_ok=True)
    def output(*cmd,cwd=project):
        return subprocess.check_output(cmd,cwd=cwd,text=True).strip()
    if output('git','rev-parse','HEAD',cwd=upstream)!=prior.UPSTREAM:
        raise ValueError('The upstream board revision differs')
    packages=json.loads((project/'lake-manifest.json').read_text())['packages']
    if next(x['rev'] for x in packages if x['name']=='mathlib')!=prior.MATHLIB:
        raise ValueError('The Mathlib revision differs')
    with (build/'upstream.log').open('w') as log:
        subprocess.run(['lake','build','+PEqualNP.Outside.L_meta_9338'],cwd=project,stdout=log,stderr=subprocess.STDOUT,check=True)
    lean=output('lake','env','which','lean')
    version=output(lean,'--version')
    if 'version 4.36.0' not in version:raise ValueError('Unexpected Lean version')
    paths=[build,*[(project/p).resolve() for p in output('lake','env','printenv','LEAN_PATH').split(os.pathsep)]]
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)),LEAN_NUM_THREADS='1')
    src=HERE/'src'
    def compile_file(p):
        log=build/(p.stem+'.log')
        with log.open('w') as sink:
            subprocess.run([lean,'-j1','-M','5500','-R',str(p.parent),'-o',str(build/(p.stem+'.olean')),str(p)],
                           cwd=project,env=env,stdout=sink,stderr=subprocess.STDOUT,check=True)
        print(p.stem,flush=True)
        return p.stem,prior.audit(p,log.read_text())
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        first=dict(pool.map(compile_file,[PARENT/'src/OrbitDivisibility.lean',src/'FrameCore.lean']))
        checked=dict(pool.map(compile_file,[src/'Frames.lean',src/'RectangleOrbits.lean',src/'OrbitBounds.lean']))
    previous=first.pop('OrbitDivisibility')
    checked.update(first)
    report=dict(lean=version,upstream=prior.UPSTREAM,mathlib=prior.MATHLIB,modules=checked,reused={'OrbitDivisibility':previous},
                audited_declarations=sum(len(x['audits']) for x in checked.values()))
    (build/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['audited_declarations'],'new declarations audited')


if __name__=='__main__':
    main()
