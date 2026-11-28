"""Check positive and negative inputs with the independent rectangle-hull solver."""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
from replay import HERE, check_controls, geometry, program, require

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    with TemporaryDirectory() as folder:
        root = Path(folder)
        board = root / 'board'
        board.write_text(geometry())
        report = check_controls(program('hulls', root), board)
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    else:
        require(report == json.loads((HERE/'hull-controls.json').read_bytes()), 'Hull controls differ')
    print(len(report), 'positive and negative hull controls checked')
