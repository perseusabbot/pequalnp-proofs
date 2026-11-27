"""Verify the public input tables, then compile and audit the proofs on the pinned board."""
import argparse
from ast import literal_eval
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import re
import sys

from local_data import HERE, require, six_rectangles, tables


def load_module(path, name):
    spec = spec_from_file_location(name,path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


if __name__ == '__main__':
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('upstream',type=Path)
    parser.add_argument('--build',type=Path)
    parser.add_argument('--jobs',type=int)
    if not any(x in sys.argv for x in ('-h','--help')):
        upstream = parser.parse_args().upstream
        prior = load_module(HERE.parent/'checkpoint-137/proofs.py','board_137')
        prior.original_board(upstream)
        require(tables(upstream) == (HERE/'src/LocalData.lean').read_text(),'Normalization data differ')
        source = (HERE/'src/NearWitness.lean').read_text()
        ids = literal_eval(re.search(r'\((\[[\d,]+\]) : List H\).getD',source)[1])
        known = json.loads((HERE.parent/'checkpoint-137/witnesses.json').read_text())['near_15']
        boxes = six_rectangles()
        require([list(boxes[i]) for i in ids] == known,'Near-cover witness differs')
        print('Normalization words, local incidence tables and the 334-cell witness match.',flush=True)
    auditor = load_module(HERE.parent/'checkpoint-135/replay.py','audit_135')
    auditor.HERE = HERE
    auditor.main()
