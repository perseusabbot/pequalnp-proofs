"""Restart the 22-gate Heawood search one disjoint first-gate branch at a time."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

from journal import lock_directory

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / 'heawood-132'
sys.path.insert(0, str(PREVIOUS))
from reduced_search import instance, lift

# Earlier receipts recorded the Python driver alone. Its generated C++ search
# must also match before those results can be reused by a newer driver.
INITIAL_DRIVER='c6560fc83915effeb3db9be111366698fb2e765b1d3a21e4a7fcb23b1993af28'
INITIAL_SEARCH='763c05dff79235ff268bba27d2ca99a0cdbeea74480b991aa1a93c4e84a34cc6'

ENTRY = 'if (primaryKeep && search(active,left-1,next,childGroup)) return true;'
SPLIT = """bool explore = primaryKeep;
                        if (explore && left == cap) {
                            Word support = 0;
                            for (int id : live) support |= Word(1) << id;
                            const Word key = (((support * 32 + a) * 32 + b) * 2 + isOr) * 4 + keep;
                            if (listBranches) std::cerr << key << ' ' << support << ' ' << a << ' ' << b
                                                        << ' ' << isOr << ' ' << keep << '\\n';
                            explore = !listBranches && (!restrictBranch || key == branchKey);
                        }
                        if (explore && search(active,left-1,next,childGroup)) return true;"""


def build(folder):
    source = (PREVIOUS / 'symmetry_search.cpp').read_text()
    if source.count(ENTRY) != 1 or source.count('    bool reference;') != 1:
        raise ValueError('The first-gate branch point differs from Checkpoint 132')
    source = '#include <cstdlib>\n' + source.replace('    bool reference;', """    bool reference;
    bool listBranches = std::getenv("HEAWOOD_LIST") != nullptr;
    bool restrictBranch = std::getenv("HEAWOOD_KEY") != nullptr;
    Word branchKey = restrictBranch ? std::stoull(std::getenv("HEAWOOD_KEY")) : 0;""").replace(ENTRY,SPLIT)
    path = folder / 'sharded.cpp'
    path.write_text(source)
    binary = folder / 'sharded'
    subprocess.run([os.environ.get('CXX','c++'),'-O3','-std=c++17',str(path),'-o',str(binary)],check=True)
    return binary


def run(binary, data, key=None, listing=False):
    env = {k:v for k,v in os.environ.items() if k not in ('HEAWOOD_KEY','HEAWOOD_LIST')}
    if listing:
        env['HEAWOOD_LIST']='1'
    if key is not None:
        env['HEAWOOD_KEY']=str(key)
    return subprocess.run([binary],text=True,input=data,capture_output=True,env=env,check=True)


def branches(binary,data):
    result=run(binary,data,listing=True)
    if not result.stdout.startswith('NO '):
        raise ValueError('Target already available before a first gate')
    rows=[list(map(int,line.split())) for line in result.stderr.splitlines()]
    if len({r[0] for r in rows})!=len(rows) or any(len(r)!=6 for r in rows):
        raise ValueError('First-gate keys must be distinct')
    return rows


def store(path, value):
    temporary=path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value,indent=2)+'\n')
    temporary.replace(path)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory',type=Path)
    ap.add_argument('--list-only',action='store_true')
    ap.add_argument('--stop-after',type=int,help='Pause after this many additional completed branches')
    args=ap.parse_args()
    if args.stop_after is not None and args.stop_after<0:
        raise ValueError('Negative stop count')
    folder=args.directory.resolve()
    folder.mkdir(parents=True,exist_ok=True)
    lock=lock_directory(folder,'heawood.py')
    saved=folder/'status.json'
    binary=build(folder)
    search_hash=sha256((folder/'sharded.cpp').read_bytes()).hexdigest()
    data,columns=instance(22)
    digest=sha256(data.encode()).hexdigest()
    verified=json.loads((PREVIOUS/'verification.json').read_text())
    if digest!=verified['reduced_instance_sha256']:
        raise ValueError('Unexpected 22-gate instance')
    # Exercise both a positive and a negative split search on signed truth tables.
    for small,expected in [('1 1 2 2 0\n3 5\n','YES'),('1 2 2 2 0\n5 6\n','NO')]:
        ordinary=run(binary,small).stdout.split()[0]
        pieces=[run(binary,small,r[0]).stdout.split()[0] for r in branches(binary,small)]
        if ordinary!=expected or ('YES' in pieces)!=(expected=='YES'):
            raise ValueError('First-gate controls disagree')
    rows=branches(binary,data)
    inventory={str(key):[mask,a,b,op,keep] for key,mask,a,b,op,keep in rows}
    store(folder/'branches.json',dict(input_sha256=digest,branches=inventory))
    if args.list_only:
        print(len(rows),'first-gate branches')
        return
    done=folder/'completed'
    done.mkdir(exist_ok=True)
    program=sha256(Path(__file__).read_bytes()).hexdigest()
    def progress(current=None,candidate=None,paused=False,found=False):
        completed=sum((done/(str(key)+'.json')).is_file() for key,*_ in rows)
        store(folder/'status.json',dict(input_sha256=digest,driver_sha256=program,search_sha256=search_hash,
              observed_utc=datetime.now(timezone.utc).isoformat(),pid=os.getpid(),total=len(rows),
              excluded=completed,current=current,candidate=candidate,
              status='candidate' if found or candidate is not None else 'complete' if completed==len(rows) else 'paused' if paused else 'running'))
    candidate=folder/'candidate.json'
    if candidate.is_file():
        record=json.loads(candidate.read_text())
        if json.loads(json.dumps(lift(record['local'])))!=record or len(record['local'])>22 or not record['fits_posted_gate_budget']:
            raise ValueError('Incorrect saved Heawood candidate')
        old=json.loads(saved.read_text()) if saved.is_file() else {}
        key=old.get('candidate')
        progress(candidate=key if key is not None else old.get('current'),found=True)
        return
    completed_now=0
    # Fewer retained gate inputs tend to settle earlier. The key includes the support.
    for key,mask,a,b,op,keep in sorted(rows,key=lambda r:(r[-1].bit_count(),r[1].bit_count(),r[0])):
        receipt=done/(str(key)+'.json')
        if receipt.is_file():
            old=json.loads(receipt.read_text())
            same_source=old.get('search_sha256')==search_hash
            if 'search_sha256' not in old:
                same_source=old.get('driver_sha256')==INITIAL_DRIVER and search_hash==INITIAL_SEARCH
            if (old['key'],old['input_sha256'],old['possible'])!=(key,digest,False) or not same_source:
                raise ValueError('A saved first-gate result has a different source or input')
            continue
        if completed_now==args.stop_after:
            progress(paused=True)
            return
        progress(current=key)
        output=run(binary,data,key).stdout.splitlines()
        answer,roots,states=output[0].split()
        if answer=='YES':
            gates=[]; wires=columns.copy()
            for line in output[1:]:
                x,y,o,z=map(int,line.split())
                if o not in (0,1) or z!=(x|y if o else x&y):
                    raise ValueError('Incorrect reported gate')
                gates.append(['OR' if o else 'AND',wires.index(x),wires.index(y)])
                wires.append(z)
            witness=lift(gates)
            if len(gates)>22 or not witness['fits_posted_gate_budget']:
                raise ValueError('Candidate exceeds the posted budget')
            store(folder/'candidate.json',witness);progress(candidate=key)
            return
        if answer!='NO' or len(output)!=1:
            raise ValueError('Unrecognized branch record')
        store(receipt,dict(input_sha256=digest,driver_sha256=program,search_sha256=search_hash,key=key,possible=False,roots=int(roots),states=int(states)))
        completed_now+=1
    progress()


if __name__=='__main__':
    main()
