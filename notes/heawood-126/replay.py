"""Rebuild the selected proof modules with the pinned project and Lean 4.36."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PACKET = HERE

def digest(data):
    return hashlib.sha256(data).hexdigest()

def overlay(base, objects, modules):
    # Lean picks the first root containing the package directory. Share the
    # pinned project library inside that root while reserving locally rebuilt modules.
    reserved={Path(n.replace('.','/')) for n in modules if n.startswith('PEqualNP.')}
    parents={parent for name in reserved for parent in name.parents}
    def visit(directory):
        for item in directory.iterdir():
            rel=item.relative_to(base)
            dest=objects/rel
            if item.is_dir() and rel in parents:
                if dest.is_symlink():
                    dest.unlink()
                dest.mkdir(exist_ok=True,parents=True)
                visit(item)
            elif not item.is_dir() and rel.parent/rel.name.split('.')[0] in reserved:
                if dest.is_symlink():
                    dest.unlink()
                continue
            elif not dest.exists() and not dest.is_symlink():
                dest.symlink_to(item.resolve(),target_is_directory=item.is_dir())
    (objects/'PEqualNP').mkdir(exist_ok=True,parents=True)
    visit(base/'PEqualNP')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('project',type=Path,help='built proof repository or its lean subdirectory')
    ap.add_argument('--build',type=Path,required=True,help='object, source staging and log directory')
    ap.add_argument('--packet',type=Path,default=PACKET)
    ap.add_argument('--graph',type=Path,default=HERE/'modules.json',help='module map for the chosen proof family')
    ap.add_argument('--jobs',type=int,default=1)
    ap.add_argument('--target',action='append',help='limit the replay to this module and its dependencies; repeatable')
    ap.add_argument('--resume',action='store_true',help='use modules authenticated by this replay in this directory')
    args=ap.parse_args()
    if args.jobs<1: ap.error('jobs must be positive')
    project=args.project.resolve()
    if (project/'lean/lakefile.lean').exists() or (project/'lean/lakefile.toml').exists(): project=project/'lean'
    build=args.build.resolve()
    src,obj,logs=tuple(build/p for p in ('src','objects','logs'))
    for path in (src,obj,logs): path.mkdir(parents=True,exist_ok=True)
    all_modules=json.loads(args.graph.read_text())
    modules=all_modules
    audits = {
        'NineProfile': ['Checkpoint126.Heawood.nineProfile'],
        'NinePatterns': ['Checkpoint126.Heawood.ninePatterns', 'Checkpoint126.Heawood.nineCount'],
        'NineLossFloor': ['Checkpoint126.Heawood.gateFloor', 'Checkpoint126.Heawood.shortCircuits',
                          'Checkpoint126.Heawood.postedNineLost'],
        'CycleBudget': ['Checkpoint126.Heawood.cycleBudget'],
        'CycleNumbers': ['Checkpoint126.Certificate.numerical'],
        'CycleAudit': ['Checkpoint126.Certificate.checked'],
        'CoreGeometry': ['Checkpoint126.Heawood.robust', 'Checkpoint126.Heawood.safePath'],
        'AuxiliaryPath': ['Checkpoint126.Heawood.auxiliaryPath'],
        'CherryBound': ['Checkpoint126.Cherry.lower'],
        'ZeroPruning': ['Checkpoint126.Zero.cost'],
        'LossFloor': ['Checkpoint125.Heawood.gateFloor', 'Checkpoint125.Heawood.shortCircuits',
                      'Checkpoint125.Heawood.postedEightLost'],
        'EightBoundary': ['Checkpoint125.Heawood.eightProfile'],
        'EightPatterns': ['Checkpoint125.Heawood.eightPatterns'],
        'PatternCount': ['Checkpoint125.Heawood.eightList', 'Checkpoint125.Heawood.eightCount'],
        'FiveCenters': ['Checkpoint124.Heawood.sixAtTwentyFive'],
    }
    targets = args.target or ['NinePatterns', 'PatternCount']
    if not targets:ap.error('Select at least one proof module with --target')
    selected=set()
    def include(n):
        if n in selected:return
        if n not in modules:raise ValueError('Unknown proof module '+n)
        selected.add(n)
        for dep in modules[n]['requires']:include(dep)
    for n in targets:include(n)
    modules={n:row for n,row in modules.items() if n in selected}
    for name,v in modules.items():
        origin=v['source']
        source=project/origin[9:] if origin.startswith('@project/') else args.packet.resolve()/origin
        data=source.read_bytes()
        if digest(data)!=v['sha256']:raise ValueError(f'Source checksum mismatch for {name}: {source}')
        target=(src / name.replace('.','/')).with_suffix('.lean')
        target.parent.mkdir(parents=True,exist_ok=True)
        if not target.is_file() or target.read_bytes()!=data:target.write_bytes(data)
    lean=subprocess.check_output(['lake','env','which','lean'],cwd=project,text=True).strip()
    version=subprocess.check_output([lean,'--version'],text=True).strip()
    if 'version 4.36.0' not in version: raise ValueError(version)
    lakepath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=project,text=True).strip()
    libpaths=[(project/d).resolve() for d in lakepath.split(os.pathsep)]
    base=next((d for d in libpaths if (d/'PEqualNP/Defs.olean').is_file()),None)
    if base is None:raise ValueError('Build PEqualNP.Defs in the project before replaying.')
    overlay(base,obj,all_modules)
    env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[obj,*libpaths])))
    graph_sha=digest(args.graph.read_bytes())
    build_identity={'graph':graph_sha, 'lean':version,
                    'definitions':digest((base/'PEqualNP/Defs.olean').read_bytes()),
                    'lake_manifest':digest((project/'lake-manifest.json').read_bytes())}
    completed=set()
    for name,record in modules.items():
        stamp=logs/(name+'.json');ol=(obj/name.replace('.','/')).with_suffix('.olean')
        if args.resume and stamp.is_file() and ol.is_file() and (logs/(name+'.log')).is_file():
            old=json.loads(stamp.read_text())
            if old.get('build')==build_identity and old.get('object')==digest(ol.read_bytes()):
                completed.add(name)
    def compile_one(name):
        rel=Path(name.replace('.','/'));source=(src/rel).with_suffix('.lean')
        dest=(obj/rel).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(dir=dest.parent) as d:
            tmp=Path(d)/dest.name
            with (logs/(name+'.log')).open('w') as f:
                result=subprocess.run([lean,'-j1','-R',str(src),'-o',str(tmp),str(source)],
                                      cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT)
            if result.returncode:raise RuntimeError(f'Lean failed on {name}. See {logs/(name+".log")}')
            tmp.replace(dest)
        (logs/(name+'.json')).write_text(json.dumps(dict(build=build_identity,object=digest(dest.read_bytes()))))
    remaining=set(modules)-completed
    running={}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while remaining or running:
            ready=sorted(m for m in remaining if set(modules[m]['requires'])<=completed)
            for name in ready[:args.jobs-len(running)]:
                remaining.remove(name)
                running[pool.submit(compile_one,name)]=name
            if not running:raise RuntimeError('Missing or cyclic dependencies')
            done,_=wait(running,return_when=FIRST_COMPLETED)
            for task in done:
                name=running.pop(task)
                task.result()
                completed.add(name)
                print(f'{len(completed)}/{len(modules)} {name}',flush=True)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name in sorted(modules):
        output = (logs / (name + '.log')).read_text()
        records = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
        records.update((name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", output))
        for theorem, axioms in records.items():
            unexpected = {x.strip() for x in axioms.split(',') if x.strip()} - allowed
            if unexpected:
                raise RuntimeError(f'Unexpected axioms in {theorem}: {unexpected}')
        for theorem in audits.get(name, []):
            if theorem not in records:
                raise RuntimeError('Missing theorem audit for ' + theorem)
        if name in audits or name in targets:
            print(output.strip())

if __name__=='__main__':main()
