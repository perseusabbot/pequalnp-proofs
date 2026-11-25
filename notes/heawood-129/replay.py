"""Verify the previous proof packet and build the projected-boundary extension."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent/'heawood-128'
UPSTREAM = '048b39bb2c5b2c21da06d44218d16366086a68d9'
AUDIT = {'Checkpoint129.Heawood.'+name for name in ('projectedBoundaryCircuit','projectedScreenNecessary',
         'allScreensValid','allTransferredValid','representativeNecessary','postedRepresentativeNecessary')} | {'Checkpoint129.FourStar.controlWorks','Checkpoint129.FiveStar.controlWorks'}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def tree(build, module):
    return (build/'objects'/module.replace('.','/')).with_suffix('.olean')


def build_new(project, build, jobs, resume):
    library = project.resolve()/'lean'
    if subprocess.check_output(['git','-C',str(project),'rev-parse','HEAD'],text=True).strip()!=UPSTREAM:
        raise ValueError('Incorrect upstream commit')
    def lake(*args):
        return subprocess.check_output(['lake','env',*args],cwd=library,text=True).strip()
    lean = lake('which','lean')
    version = subprocess.check_output([lean,'--version'],text=True).strip()
    if 'version 4.36.0' not in version:
        raise ValueError(version)
    old_base = build/'prior/base'
    old_extra = build/'prior/extension'
    new = build/'extension'
    src, obj, logs = (new/key for key in ('src','objects','logs'))
    for directory in (src,obj,logs):
        directory.mkdir(parents=True,exist_ok=True)
    extra = [(library/p).resolve() for p in lake('printenv','LEAN_PATH').split(os.pathsep)]
    env = dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[obj,old_extra/'objects',old_base/'objects',*extra])))
    base_modules = read(PREVIOUS.parent/'heawood-127/modules.json')
    previous = read(PREVIOUS/'sources.json')
    modules = read(HERE/'sources.json')
    if set(modules)!={p.stem for p in (HERE/'src').glob('*.lean')}:
        raise ValueError('Source inventory mismatch')
    for name,entry in modules.items():
        path = HERE/'src'/(name+'.lean')
        actual = re.findall(r'^import ([\w.]+)$',path.read_text(),re.MULTILINE)
        if digest(path)!=entry['sha256'] or actual!=entry['imports']:
            raise ValueError('Source manifest differs for '+name)
        code = re.sub(r'(?s)/-.*?-/|--[^\n]*','',path.read_text())
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b',code):
            raise ValueError('Unexpected extension declaration in '+name)
        (src/path.name).write_bytes(path.read_bytes())

    def compile_one(name):
        deps = {}
        for dep in modules[name]['imports']:
            root = new if dep in modules else old_extra if dep in previous else old_base if dep in base_modules else None
            if root is None:
                continue
            checksum = digest(tree(root,dep))
            if read(root/'logs'/(dep+'.json'))['object']!=checksum:
                raise ValueError('Imported object differs for '+dep)
            deps[dep] = checksum
        source = src/(name+'.lean')
        output = tree(new,name)
        stamp,log = (logs/(name+suffix) for suffix in ('.json','.log'))
        inputs = dict(source=digest(source),imports=deps,upstream=UPSTREAM,lean=version,
                      lake_manifest=digest(library/'lake-manifest.json'))
        if resume and all(p.is_file() for p in (stamp,output,log)):
            if read(stamp)==dict(inputs=inputs,object=digest(output),log=digest(log)):
                return 'verified'
        with tempfile.TemporaryDirectory(dir=obj) as tmp:
            fresh = Path(tmp)/(name+'.olean')
            with log.open('w') as stream:
                status = subprocess.run([lean,'-j1','-M','8500','-R',str(src),'-o',str(fresh),str(source)],
                    cwd=library,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
            if status or 'sorryAx' in log.read_text():
                raise RuntimeError('Lean failed on '+name+'. See '+str(log))
            fresh.replace(output)
        stamp.write_text(json.dumps(dict(inputs=inputs,object=digest(output),log=digest(log)),indent=2)+'\n')
        return 'built'

    pending, done, running = set(modules), set(), {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            ready = sorted(n for n in pending if (set(modules[n]['imports']) & modules.keys())<=done)
            for n in ready[:jobs-len(running)]:
                pending.remove(n)
                running[pool.submit(compile_one,n)] = n
            if not running:
                raise ValueError('Inconsistent module graph')
            finished,_ = wait(running,return_when=FIRST_COMPLETED)
            for f in finished:
                n = running.pop(f)
                status = f.result()
                done.add(n)
                print(f'{len(done)}/{len(modules)} {n} {status}',flush=True)
    audited = {}
    for name in modules:
        for declaration, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(logs/(name+'.log')).read_text()):
            axioms = raw.split(', ') if raw else []
            if set(axioms)-{'propext','Classical.choice','Quot.sound'}:
                raise ValueError('Unexpected axiom in '+declaration)
            audited[declaration] = axioms
    if not AUDIT<=audited.keys():
        raise ValueError('Missing theorem audit')
    return audited


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('project',type=Path)
    ap.add_argument('--build',type=Path,required=True)
    ap.add_argument('--jobs',type=int,default=2)
    ap.add_argument('--resume',action='store_true')
    args = ap.parse_args()
    if args.jobs<1:
        ap.error('Use at least one worker')
    root = args.build.resolve()
    cmd = [sys.executable,'-B',str(PREVIOUS/'replay.py'),str(args.project.resolve()),
           '--build',str(root/'prior'),'--jobs',str(args.jobs)]
    if args.resume:
        cmd.append('--resume')
    subprocess.run(cmd,check=True)
    print(json.dumps(build_new(args.project,root,args.jobs,args.resume),indent=2))


if __name__=='__main__':
    main()
