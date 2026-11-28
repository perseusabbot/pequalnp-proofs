"""Audit the new theorems after rebuilding their unchanged dependencies on the pinned board."""
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
if __name__=='__main__':
    spec=spec_from_file_location('pnp_proof_audit',HERE.parent/'checkpoint-135/replay.py')
    audit=module_from_spec(spec)
    spec.loader.exec_module(audit)
    with TemporaryDirectory() as temp:
        stage=Path(temp)
        (stage/'src').mkdir()
        files=[HERE.parent/'checkpoint-138/src/Board.lean',HERE.parent/'checkpoint-138/src/Degrees.lean',
               HERE.parent/'checkpoint-137/src/Overlaps.lean',*sorted((HERE/'src').glob('*.lean'))]
        for p in files:shutil.copyfile(p,stage/'src'/p.name)
        audit.HERE=stage
        audit.main()
