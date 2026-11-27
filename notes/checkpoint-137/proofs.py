"""Compare the numerical board with the pinned Lean source, then run its proof auditor."""
from ast import literal_eval
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import re
import sys

from rectangles import BOARD, HERE, ROWS, require, six_rectangles


def original_board(upstream):
    path = upstream/'lean/PEqualNP/Outside/L_meta_9338.lean'
    source = path.read_text()
    incidence = literal_eval(re.search(r'^def incidence : List Nat := (\[.*?\])$',source,re.M)[1])
    require([BOARD ^ row for row in incidence] == list(ROWS),'The posted board differs')
    oval_literals = re.search(r'def ovals : Array \(Nat × Nat\) := #(\[.*?\])',source,re.S)[1]
    ovals = literal_eval(oval_literals)
    require(ovals == six_rectangles(),'The posted maximum rectangles differ')
    witness = json.loads((HERE/'witnesses.json').read_text())['cover_16']
    formal = (HERE/'src/MaximumRectangles.lean').read_text()
    ids = literal_eval(re.search(r'\((\[[\d,]+\]) : List H\).getD',formal)[1])
    require([list(ovals[i]) for i in ids] == witness,'Lean and numerical witnesses differ')
    print('All 441 source entries, 168 maximum rectangles and 16 witness IDs match.',flush=True)


if __name__ == '__main__':
    # The common auditor owns its command-line interface, including --help.
    import argparse
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('upstream',type=Path)
    parser.add_argument('--build',type=Path)
    parser.add_argument('--jobs',type=int)
    if '--help' not in sys.argv and '-h' not in sys.argv:
        original_board(parser.parse_args().upstream)
    spec = spec_from_file_location('proof_replay_135',HERE.parent/'checkpoint-135'/'replay.py')
    prior = module_from_spec(spec)
    spec.loader.exec_module(prior)
    prior.HERE = HERE
    prior.main()
