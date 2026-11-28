"""Rebuild and audit the proofs against the pinned upstream board and mathlib."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

HERE = Path(__file__).resolve().parent
if __name__ == '__main__':
    spec = spec_from_file_location('checkpoint_proof_audit', HERE.parent/'checkpoint-135/replay.py')
    audit = module_from_spec(spec)
    spec.loader.exec_module(audit)
    audit.HERE = HERE
    audit.main()
