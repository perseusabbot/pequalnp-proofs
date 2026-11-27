"""Check the six degree-four cases at size 14 by an independent direct SAT encoding."""
import argparse
import gzip
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from rectangles import HERE, ROWS, bits, require, six_rectangles


class Formula:
    def __init__(self, variables):
        self.variables = variables
        self.clauses = []

    def fresh(self):
        self.variables += 1
        return self.variables

    def at_most(self, lits, k):
        # Forward unary counter. If at least j inputs in a prefix are true,
        # slot j in that prefix must be true. The overflow clause forbids k+1.
        prev = []
        for lit in lits:
            curr = [self.fresh() for _ in range(min(k,len(prev)+1))]
            self.clauses.append([-lit,curr[0]])
            for j,used in enumerate(prev):
                self.clauses.append([-used,curr[j]])
                if j+1 < k:
                    self.clauses.append([-used,-lit,curr[j+1]])
                else:
                    self.clauses.append([-used,-lit])
            prev = curr

    def dimacs(self):
        return (f'p cnf {self.variables} {len(self.clauses)}\n' +
                ''.join(' '.join(map(str,row))+' 0\n' for row in self.clauses))


def check_rup(clauses, path):
    """Check each learned LRAT clause by the indicated unit propagations."""
    known = dict(enumerate(clauses,1))
    derived = 0
    empty = False
    reader = gzip.open if path.suffix == '.gz' else open
    with reader(path,'rt') as stream:
        for line in stream:
            fields = line.split()
            if len(fields) > 1 and fields[1] == 'd':
                for token in fields[2:-1]:
                    known.pop(int(token),None)
                require(fields[-1] == '0','Malformed deletion')
                continue
            step = list(map(int,fields))
            split = step.index(0,1)
            ident, conclusion, hints = step[0], step[1:split], step[split+1:-1]
            require(step[-1] == 0 and ident not in known and hints,'Malformed derivation')
            # Negate the conclusion, then unit-propagate each explicit premise.
            true = {-lit for lit in conclusion}
            conflict = any(-lit in true for lit in true)
            for hint in hints:
                require(not conflict and 0 < hint < ident and hint in known,'Invalid RUP premise')
                premise = known[hint]
                require(all(lit not in true for lit in premise),'Satisfied RUP premise')
                undecided = [lit for lit in premise if -lit not in true]
                require(len(undecided) <= 1,'Non-unit RUP premise')
                if undecided:
                    true.add(undecided[0])
                else:
                    conflict = True
            require(conflict,'Clause does not follow by reverse unit propagation')
            known[ident] = conclusion
            derived += 1
            empty |= not conclusion
    require(empty,'Missing contradiction')
    return derived


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--solver',default='cadical')
    ap.add_argument('--output',type=Path)
    traces = ap.add_mutually_exclusive_group()
    traces.add_argument('--proof-dir',type=Path,help='Save the checked LRAT traces here')
    traces.add_argument('--verify-traces',type=Path,help='Check saved LRAT or gzipped LRAT files directly')
    args = ap.parse_args()
    boxes = six_rectangles()
    roots = json.loads((HERE/'results.json').read_text())['geometry']['pure_roots']
    # Across the 21 rows, degree at least four and at most 14 selected boxes
    # force degree exactly four at each row. The same applies to the columns.
    base = Formula(len(boxes))
    for r,row in enumerate(ROWS):
        for c in bits(row):
            base.clauses.append([i+1 for i,(a,b) in enumerate(boxes) if a >> r & 1 and b >> c & 1])
    for axis in range(2):
        for p in range(21):
            base.at_most([i+1 for i,b in enumerate(boxes) if b[axis] >> p & 1],4)
    # Local upper bounds alone allow degree-three completions. Enforce the
    # lower bound at each label by requiring a box outside each covering triple.
    for axis in range(2):
        other = [sum(1 << r for r in range(21) if ROWS[r] >> c & 1) for c in range(21)]
        domains = ROWS if axis == 0 else other
        for p, domain in enumerate(domains):
            ids = [i for i,box in enumerate(boxes) if box[axis] >> p & 1]
            for i,j,k in combinations(ids,3):
                if boxes[i][1-axis] | boxes[j][1-axis] | boxes[k][1-axis] == domain:
                    base.clauses.append([h+1 for h in ids if h not in (i,j,k)])
    report = []
    with TemporaryDirectory() as temp:
        path = Path(temp)/'case.cnf'
        for root in roots:
            if len(root['ids']) != 4:
                continue
            start = len(base.clauses)
            base.clauses.extend([[i+1] for i in root['ids']])
            data = base.dimacs()
            path.write_text(data)
            name = 'root-'+'-'.join(map(str,root['ids']))+'.lrat'
            if args.verify_traces:
                proof = args.verify_traces/name
                if not proof.exists():
                    proof = args.verify_traces/(name+'.gz')
            else:
                proof = Path(temp)/'case.lrat'
                result = subprocess.run([args.solver,'-q','--plain','--lrat','--no-binary',str(path),str(proof)],
                                        capture_output=True,text=True)
                require(result.returncode == 20 and 's UNSATISFIABLE' in result.stdout,'Unexpected SAT result')
            derived = check_rup(base.clauses,proof)
            if args.proof_dir:
                args.proof_dir.mkdir(parents=True,exist_ok=True)
                (args.proof_dir/name).write_bytes(proof.read_bytes())
            del base.clauses[start:]
            report.append(dict(ids=root['ids'],dimacs_sha256=sha256(data.encode()).hexdigest(),
                               variables=base.variables,clauses=start+4,decision='UNSAT'))
            print(root['ids'],'UNSAT',derived,'RUP clauses checked',flush=True)
    rendered = json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.write_text(rendered)
    else:
        require(rendered == (HERE/'sat-results.json').read_text(),'SAT receipt differs')


if __name__ == '__main__':
    main()
