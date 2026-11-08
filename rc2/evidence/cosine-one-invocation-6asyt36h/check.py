"""Certify one 400-cell binary64 hex dump against 1 + cos(pi*(2*i+1)/800)/2."""
import hashlib
import json
import re
import sys
from fractions import Fraction as F
from math import ceil
from pathlib import Path


def atan_interval(q):
    # Alternating series at 1/q. Consecutive partial sums enclose atan(1/q).
    partial = sum(F((-1)**j, (2*j+1)*q**(2*j+1)) for j in range(32))
    return partial, partial + F(1, 65*q**65)


def pi_interval():
    # Machin identity: pi = 16 atan(1/5) - 4 atan(1/239).
    a, b = atan_interval(5)
    c, d = atan_interval(239)
    return 16*a - 4*d, 16*b - 4*c


def hex_value(token):
    m = re.fullmatch(r'0[xX]([0-9A-Fa-f]+)(?:\.([0-9A-Fa-f]*))?[pP]([+-]?\d+)', token)
    if not m:
        raise ValueError(f'Expected positive finite C hex float, got {token!r}')
    frac = m[2] or ''
    return int(m[1] + frac, 16) * F(2)**(int(m[3]) - 4*len(frac))


def certify(raw):
    cells = [hex_value(t) for t in raw.decode('ascii').split()]
    if len(cells) != 400:
        raise ValueError('Expected exactly 400 cells')
    lo, hi = pi_interval()
    scale = 2**128
    p = F((lo*scale).__floor__(), scale)
    upper = F(0)
    worst = 0
    for i, cell in enumerate(cells):
        w = F(2*i+1, 800)
        x = w*p
        term = total = F(1)
        for j in range(1, 23):
            term *= -x*x / ((2*j-1)*(2*j))
            total += term
        # Degree 45 Taylor polynomial (odd coefficients zero); derivative bounded by 1.
        remainder = abs(term)*x*x/(45*46)
        # |cos(w*pi)-cos(w*p)| <= w*(hi-p).
        error = abs(cell - 1 - total/2) + (remainder + w*(hi-p))/2
        if error > upper:
            worst, upper = i, error
    rounded_up = F(ceil(upper * 10**32), 10**32)
    limit = F(24854, 10**20)
    return dict(accepted=rounded_up <= limit, dump_sha256=hashlib.sha256(raw).hexdigest(),
                cells=len(cells), max_upper_index=worst, exact_upper=str(rounded_up),
                exact_limit=str(limit), exact_margin=str(limit-rounded_up))


if __name__ == '__main__':
    result = certify(Path(sys.argv[1]).read_bytes())
    print(json.dumps(result, indent=2))
    sys.exit(0 if result['accepted'] else 1)
