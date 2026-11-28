"""Build the published board and induce its checked symmetries on the 168 maximum rectangles."""
from hashlib import sha256
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'checkpoint-137'))
from rectangles import ROWS, bits, group, perm_mask, require, six_rectangles


def geometry():
    maximum = six_rectangles()
    index = {a | b << 21: j for j, (a, b) in enumerate(maximum)}
    elements = group()
    generators = elements[1:6]
    lines = [list(ROWS), *maximum, [len(generators)]]
    for g in generators:
        for r in range(21):
            for c in range(21):
                a, b = sorted((g[r], g[c + 21]))
                require(a < 21 <= b and ROWS[a] >> (b - 21) & 1 == ROWS[r] >> c & 1,
                        'Generator changes a board entry')
        move = perm_mask(g)
        lines.append([index[move(a | b << 21)] for a, b in maximum])
    return ''.join(' '.join(map(str, row)) + '\n' for row in lines)


if __name__ == '__main__':
    path = Path(sys.argv[1])
    path.write_text(geometry())
    print(sha256(path.read_bytes()).hexdigest(), path)
