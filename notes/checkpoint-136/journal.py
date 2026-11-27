"""Serialize resumable searches, including a worker started before directory locking."""
import fcntl
import json
import os
from pathlib import Path


def lock_directory(folder, driver):
    lock=(folder/'run.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX | fcntl.LOCK_NB)
    status=folder/'status.json'
    if status.is_file():
        previous=json.loads(status.read_text())
        if previous.get('status')=='running' and previous.get('pid')!=os.getpid():
            proc=Path('/proc')/str(previous['pid'])
            try:
                argv=[os.fsdecode(a) for a in (proc/'cmdline').read_bytes().split(b'\0') if a]
                cwd=(proc/'cwd').resolve(strict=True)
            except (FileNotFoundError,PermissionError,ProcessLookupError):
                argv=[]
            if any(Path(a).name==driver for a in argv) and any((cwd/a).resolve()==folder for a in argv):
                lock.close()
                raise RuntimeError(f'{driver} is already running in {folder}')
    return lock
