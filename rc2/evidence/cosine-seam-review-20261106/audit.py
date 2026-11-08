"""Audit one preserved cosine build. The replay checks only this measured trajectory."""
import csv
import hashlib
import io
import json
import runpy
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SEAM = Path(r"D:\LeanWork\staging\FluxWitness_L3_SeamData_20261105")
BUILD = SEAM.parent / "FluxWitness_L3_LoopNorm_20261105" / "cmp"
BASE = HERE.parent / "initial-array-rational-20261105"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def bits(x):
    return struct.pack(">d", x).hex()


def initial(raw):
    return [float.fromhex(line) for line in raw.decode("ascii").splitlines()]


def euler(u, dt, dx2):
    result = []
    for i, center in enumerate(u):
        left = u[max(0, i-1)]
        right = u[min(len(u)-1, i+1)]
        laplacian = ((right - 2.0*center + left) / dx2)
        result.append(center + dt*(0.01*laplacian))
    return result


def main():
    raw = (SEAM/"u0_hex.txt").read_bytes()
    prev = (BASE/"observed.hex").read_bytes()
    u = initial(raw)
    if len(u) != 400 or len(initial(prev)) != 400:
        raise ValueError("Expected two complete 400-cell dumps")
    init_check = runpy.run_path(str(BASE/"check.py"))["certify"](raw)
    initial_differences = [i for i,(a,b) in enumerate(zip(u,initial(prev))) if bits(a)!=bits(b)]
    final_csv = (BUILD/"a.out").read_bytes()
    rows = list(csv.DictReader(io.StringIO(final_csv.decode("ascii"))))
    if len(rows) != 400:
        raise ValueError("Expected 400 final CSV rows")
    final = [float(row["u"]) for row in rows]
    dx, dt = 6.0/400, 1.0/223
    expected = [("dx",bits(dx)), ("dx2",bits(dx*dx)), ("dt",bits(dt)), ("N","223")]
    expected += [("u0",str(i),bits(x)) for i,x in enumerate(u)]
    expected += [("uN",str(i),bits(x)) for i,x in enumerate(final)]
    actual = [tuple(line.split()) for line in (SEAM/"seam_data.txt").read_text().splitlines()
              if line and not line.startswith("#")]
    for _ in range(223):
        tmp = euler(euler(u,dt,dx*dx),dt,dx*dx)
        u = [0.5*old + 0.5*next_value for old,next_value in zip(u,tmp)]
    differences = [i for i,(a,b) in enumerate(zip(u,final)) if bits(a)!=bits(b)]
    files = [SEAM/name for name in ("dump.sh","prep.py","seam_data.txt","u0_hex.txt")]
    files += [BUILD/name for name in ("cmd.txt","versions.txt","run.sh","a","a.out","b.out")]
    report = dict(accepted=init_check["accepted"] and actual==expected and not differences,
                  initial=init_check, previous_initial_bit_differences=initial_differences,
                  csv_outputs_byte_identical=final_csv==(BUILD/"b.out").read_bytes(),
                  seam_rows_match=actual==expected, final_bit_differences=differences,
                  compiler=(BUILD/"versions.txt").read_text().strip(),
                  build_recipe=(BUILD/"cmd.txt").read_text().splitlines(),
                  hashes={str(path):sha(path.read_bytes()) for path in files})
    print(json.dumps(report,indent=2))
    return 0 if report["accepted"] else 1


if __name__=="__main__":
    sys.exit(main())
