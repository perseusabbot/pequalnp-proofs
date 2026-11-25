"""Rebuild all checkpoint proofs with the upstream project and audit their axioms."""
import argparse
import hashlib
import json
import os
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
UPSTREAM = '2a775730536a0e98b3f16d2736228dda5e0c06e4'
MATHLIB = 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def output(args, cwd):
    return subprocess.check_output(args,cwd=cwd,text=True).strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('project',type=Path,help='Upstream Git checkout containing the lean directory')
    ap.add_argument('--build',type=Path,required=True,help='Empty directory for rebuilt objects and logs')
    ap.add_argument('--jobs',type=int,default=1,choices=(1,2),help='Parallelism for small independent modules')
    args = ap.parse_args()
    project = args.project.resolve()
    lean_dir = project/'lean'
    objects = args.build.resolve()
    objects.mkdir(exist_ok=True,parents=True)
    if any(objects.iterdir()):
        raise ValueError('Choose an empty build directory')
    if output(['git','rev-parse','HEAD'],project) != UPSTREAM:
        raise ValueError('Use upstream commit '+UPSTREAM)
    subprocess.run(['git','diff','--quiet','HEAD','--','lean'],cwd=project,check=True)
    manifest = json.loads((lean_dir/'lake-manifest.json').read_text())
    if next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib') != MATHLIB:
        raise ValueError('Unexpected Mathlib version')
    lake = lambda *args: output(['lake','env',*args],lean_dir)
    lean = lake('which','lean')
    version = output([lean,'--version'],lean_dir)
    if 'version 4.36.0' not in version:
        raise ValueError('Expected Lean 4.36.0')
    paths = [(lean_dir/p).resolve() for p in lake('printenv','LEAN_PATH').split(os.pathsep)]
    env = dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[objects,*paths])),LEAN_NUM_THREADS='1')
    src = HERE/'src'

    def build(name):
        file = src/(name+'.lean')
        log = objects/(name+'.log')
        target = objects/(name+'.olean')
        with log.open('w') as handle:
            subprocess.run([lean,'-j1','-M','8500','-R',str(src),'-o',str(target),str(file)],
                           env=env,cwd=lean_dir,stdout=handle,stderr=subprocess.STDOUT,check=True)
        audits = {}
        logs = log.read_text()
        for decl, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",logs):
            found = set(axioms.split(', ')) if axioms else set()
            if found - STANDARD: raise ValueError('Unexpected axiom for '+decl+': '+axioms)
            audits[decl] = sorted(found)
        for decl in re.findall(r"'([^']+)' does not depend on any axioms",logs): audits[decl]=[]
        wanted = re.findall(r'^#print axioms (\S+)$',file.read_text(),re.MULTILINE)
        if len(wanted)!=len(audits) or any(not any(d==n or d.endswith('.'+n) for d in audits) for n in wanted):
            raise ValueError('Missing declaration audit in '+name)
        if 'sorryAx' in logs: raise ValueError('Unexpected placeholder in '+name)
        print(name,'checked',flush=True)
        return name,dict(source=digest(file),object=digest(target),audited=audits)

    groups = [['PlaneOrbit'],['PlaneCertificate'],[f'PlaneData{i}' for i in range(7)],['PlaneLookup'],
              [f'PlaneChecks{i}' for i in range(13)],['PlaneTwo'],['PlaneMinimum'],['PlaneExamples']]
    modules={}
    for group in groups:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool: modules.update(pool.map(build,group))
    with (objects/'upstream-build.log').open('w') as handle:
        subprocess.run(['lake','build','+PEqualNP.Outside.L_meta_927','+PEqualNP.Outside.L_meta_8443',
                        '+PEqualNP.MetaComplexity.Helpers.PadOr'],cwd=lean_dir,
                       env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=handle,stderr=subprocess.STDOUT,check=True)
    for name in ('Wheel133','PetersenCofactors','PetersenLower'):
        modules.update([build(name)])
    if set(modules)!={p.stem for p in src.glob('*.lean')}: raise ValueError('Module inventory differs')
    count=sum(len(v['audited']) for v in modules.values())
    receipt=dict(lean=version,upstream=UPSTREAM,mathlib=MATHLIB,modules=modules,audited=count)
    (objects/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(f'{len(modules)} rebuilt modules, {count} audited declarations, standard axioms only.',flush=True)


if __name__=='__main__':
    main()
