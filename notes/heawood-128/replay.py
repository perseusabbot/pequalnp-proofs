"""Replay the Checkpoint 127 base and the kernel proofs added in Checkpoint 128."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / 'heawood-127'
UPSTREAM = '048b39bb2c5b2c21da06d44218d16366086a68d9'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def extension(project, build, jobs, resume, targets=None):
    project = project.resolve()
    library = project / 'lean'
    base = build / 'base'
    dest = build / 'extension'
    src,obj,logs = (dest/p for p in ('src','objects','logs'))
    for p in (src,obj,logs):
        p.mkdir(parents=True,exist_ok=True)
    if subprocess.check_output(['git','-C',str(project),'rev-parse','HEAD'],text=True).strip()!=UPSTREAM:
        raise ValueError('The upstream project revision differs from the pinned revision')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=library,text=True).strip()
    lean=lake('which','lean')
    version=subprocess.check_output([lean,'--version'],text=True).strip()
    if 'version 4.36.0' not in version:
        raise ValueError(version)
    extra=[(library/p).resolve() for p in lake('printenv','LEAN_PATH').split(os.pathsep)]
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[obj,base/'objects',*extra])))
    modules=json.loads((HERE/'sources.json').read_text())
    previous=json.loads((PRIOR/'modules.json').read_text())
    required=set()
    def add(name):
        if name in required:
            return
        required.add(name)
        for dep in modules[name]['imports']:
            if dep in modules:
                add(dep)
    for name in (targets or modules):
        add(name)
    for name in required:
        original=HERE/'src'/(name+'.lean')
        if digest(original)!=modules[name]['source_sha256']:
            raise ValueError('Source checksum mismatch for '+name)
        (src/original.name).write_bytes(original.read_bytes())

    def compile_one(name):
        dep_hash={}
        for dep in modules[name]['imports']:
            if dep in modules:
                dep_hash[dep]=digest(obj/(dep+'.olean'))
            elif dep in previous:
                path=(base/'objects'/dep.replace('.','/')).with_suffix('.olean')
                stamp=json.loads((base/'logs'/(dep+'.json')).read_text())
                dep_hash[dep]=digest(path)
                if stamp['object']!=dep_hash[dep] or stamp['build']['graph']!=digest(PRIOR/'modules.json'):
                    raise ValueError('Prior module authentication failed for '+dep)
        source=src/(name+'.lean')
        output=obj/(name+'.olean')
        stamp=logs/(name+'.json')
        log=logs/(name+'.log')
        inputs=dict(source=digest(source),imports=dep_hash,upstream=UPSTREAM,lean=version,
                    lake_manifest=digest(library/'lake-manifest.json'))
        if resume and stamp.is_file() and output.is_file() and log.is_file():
            saved=json.loads(stamp.read_text())
            if saved==dict(inputs=inputs,object=digest(output),log=digest(log)):
                return 'verified'
        with tempfile.TemporaryDirectory(dir=obj) as tmp:
            new=Path(tmp)/(name+'.olean')
            with log.open('w') as stream:
                result=subprocess.run([lean,'-j1','-R',str(src),'-o',str(new),str(source)],
                                      cwd=library,env=env,stdout=stream,stderr=subprocess.STDOUT)
            if result.returncode:
                raise RuntimeError(f'Lean failed on {name}. See {log}')
            new.replace(output)
        if 'sorryAx' in log.read_text():
            raise ValueError('Unexpected axiom in '+name)
        stamp.write_text(json.dumps(dict(inputs=inputs,object=digest(output),log=digest(log)),indent=2)+'\n')
        return 'built'

    todo=set(required);done=set();running={}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while todo or running:
            ready=sorted(n for n in todo if (set(modules[n]['imports']) & required)<=done)
            for name in ready[:jobs-len(running)]:
                todo.remove(name)
                running[pool.submit(compile_one,name)]=name
            if not running:
                raise ValueError('No eligible proof module')
            finished,_=wait(running,return_when=FIRST_COMPLETED)
            for f in finished:
                name=running.pop(f)
                status=f.result()
                done.add(name)
                print(f'{len(done)}/{len(required)} {name} {status}',flush=True)
    audited={}
    for name in sorted(required):
        output=(logs/(name+'.log')).read_text()
        for declaration,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output):
            axioms=raw.split(', ') if raw else []
            if set(axioms)-{'propext','Classical.choice','Quot.sound'}:
                raise ValueError('Unexpected axiom in '+declaration)
            audited[declaration]=axioms
    if targets is None:
        for name in ('Theta.searchNecessary','Theta.rootNecessary','Theta.controlWorks','Theta.localLower',
                     'Heawood.labelWord','Heawood.transfer','Heawood.thetaBudget','Heawood.elevenLost',
                     'Heawood.postedElevenLost','Heawood.boundaryDomain','Heawood.boundaryCircuit',
                     'Heawood.screenNecessary'):
            if 'Checkpoint128.'+name not in audited:
                raise ValueError('Missing theorem audit for '+name)
    return audited


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('project',type=Path)
    ap.add_argument('--build',required=True,type=Path)
    ap.add_argument('--jobs',default=2,type=int)
    ap.add_argument('--resume',action='store_true')
    args=ap.parse_args()
    if args.jobs<1:
        ap.error('Use at least one worker')
    root=args.build.resolve()
    cmd=['python3','-B',str(PRIOR/'replay.py'),str(args.project.resolve()),'--build',str(root/'base'),'--jobs',str(args.jobs)]
    if args.resume:
        cmd.append('--resume')
    subprocess.run(cmd,check=True)
    audits=extension(args.project,root,args.jobs,args.resume)
    print(json.dumps(audits,indent=2))


if __name__=='__main__':
    main()
