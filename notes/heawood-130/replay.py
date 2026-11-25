"""Authenticate the preceding Lean builds and rebuild the Checkpoint 130 theorems."""
import argparse
from graphlib import TopologicalSorter
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent/'heawood-129'
UPSTREAM = '048b39bb2c5b2c21da06d44218d16366086a68d9'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def declarations(output):
    found = {}
    for line in output.splitlines():
        match = re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
        independent = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
        if match or independent:
            name = (match or independent)[1]
            axioms = match[2].split(', ') if match and match[2] else []
            if set(axioms)-STANDARD:
                raise ValueError('Unexpected axiom in '+name)
            found[name] = axioms
    return found


def extension(project, build, resume):
    lean_dir = project/'lean'
    def lake(*args):
        return subprocess.check_output(['lake', 'env', *args], cwd=lean_dir, text=True).strip()
    lean = lake('which', 'lean')
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    if 'version 4.36.0' not in version:
        raise ValueError('Wrong Lean version')
    manifests = [(127,build/'prior/prior/base','modules.json'), (128,build/'prior/prior/extension','sources.json'),
                 (129,build/'prior/extension','sources.json'), (130,build/'extension','sources.json')]
    directories = {}
    for checkpoint, root, manifest in manifests:
        modules = read(HERE.parent/f'heawood-{checkpoint}'/manifest)
        for name in modules:
            if name in directories:
                raise ValueError('Ambiguous dependency '+name)
            directories[name] = root
    current = manifests[-1][1]
    src, obj, logs = [current/k for k in ('src','objects','logs')]
    for path in (src,obj,logs):
        path.mkdir(parents=True, exist_ok=True)
    paths = [root/'objects' for _,root,_ in reversed(manifests)]
    paths.extend((lean_dir/p).resolve() for p in lake('printenv', 'LEAN_PATH').split(os.pathsep))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
    modules = read(HERE/'sources.json')
    if set(modules)!={p.stem for p in (HERE/'src').glob('*.lean')}:
        raise ValueError('Source inventory differs')
    ordered = TopologicalSorter({k:set(m['imports']) & modules.keys() for k,m in modules.items()})
    verified = {}
    for name in ordered.static_order():
        entry = modules[name]
        path = HERE/'src'/(name+'.lean')
        content = path.read_text()
        deps = re.findall(r'^import ([\w.]+)$', content, re.MULTILINE)
        clean = re.sub(r'(?s)/-.*?-/|--[^\n]*', '', content)
        if (deps!=entry['imports'] or digest(path)!=entry['sha256']
                or re.search(r'\b(sorry|admit|axiom|native_decide)\b',clean)):
            raise ValueError('Source or import mismatch in '+name)
        inputs = {}
        for dep in deps:
            home = directories[dep]
            blob = (home/'objects'/dep.replace('.','/')).with_suffix('.olean')
            checksum = digest(blob)
            if checksum!=read(home/'logs'/(dep+'.json'))['object']:
                raise ValueError('Dependency object changed in '+name)
            inputs[dep] = checksum
        source, output, log, stamp = src/path.name, obj/(name+'.olean'), logs/(name+'.log'), logs/(name+'.json')
        source.write_bytes(path.read_bytes())
        build_inputs = dict(source=digest(source), imports=inputs, upstream=UPSTREAM, lean=version,
                            lake_manifest=digest(lean_dir/'lake-manifest.json'))
        def receipt():
            return dict(inputs=build_inputs, object=digest(output), log=digest(log))
        cached = resume and all(p.is_file() for p in (output,log,stamp)) and read(stamp)==receipt()
        if not cached:
            with tempfile.TemporaryDirectory(dir=obj) as temp:
                fresh = Path(temp)/output.name
                with log.open('w') as f:
                    subprocess.run([lean,'-j1','-M','8500','-R',str(src),'-o',str(fresh),str(source)],
                                   cwd=lean_dir, env=env, stdout=f, stderr=subprocess.STDOUT, check=True)
                fresh.replace(output)
            stamp.write_text(json.dumps(receipt(),indent=2)+'\n')
        audited = declarations(log.read_text())
        if sorted(audited)!=entry['audited'] or 'sorryAx' in log.read_text():
            raise ValueError('Theorem audit differs for '+name)
        verified.update(audited)
        print(name, 'verified' if cached else 'built', flush=True)
    return verified


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('project', type=Path)
    ap.add_argument('--build', type=Path, required=True)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--resume', action='store_true')
    args = ap.parse_args()
    project, build = args.project.resolve(), args.build.resolve()
    cmd = [sys.executable,'-B',str(PREVIOUS/'replay.py'),str(project),'--build',str(build/'prior'),
           '--jobs',str(args.jobs)]
    subprocess.run(cmd+(['--resume'] if args.resume else []), check=True)
    print(json.dumps(extension(project,build,args.resume),indent=2))


if __name__ == '__main__':
    main()
