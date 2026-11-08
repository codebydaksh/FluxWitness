import re, subprocess, sys, csv
from fractions import Fraction as F
exe_h, csrc, outdir = sys.argv[1:4]
src = open(csrc, encoding="utf-8", errors="replace").read()
def macro(name):
    m = re.search(r'^[ \t]*#[ \t]*define[ \t]+' + name + r'[ \t]+([^\s/]+)', src, re.M)
    if not m: raise SystemExit("macro not found: " + name)
    return float(m.group(1).strip("()"))
D = macro("D_DIFF"); NX = int(macro("NX"))
r = subprocess.run([exe_h], capture_output=True, text=True, check=True)
steps, params, cur = {}, None, None
for line in r.stdout.splitlines():
    if line.startswith("PARAMS"): params = line.split()[1:]
    elif line.startswith("STEP"): cur = int(line.split()[1]); steps[cur] = []
    elif line.strip(): steps[cur].append(float.fromhex(line.strip()))
dx = float.fromhex(params[0]); dt = float.fromhex(params[1]); N = int(params[2])
q = dx * dx                                  # the C's dx2: a stored double
Dx, qx, dtx = F(D), F(q), F(dt)
def L(u):
    n = len(u); out = []
    for i in range(n):
        l = u[0] if i == 0 else u[i - 1]
        r_ = u[n - 1] if i == n - 1 else u[i + 1]
        out.append(Dx * (r_ - 2 * u[i] + l) / qx)
    return out
ue = [F(v) for v in steps[0]]                # exact image of the C's own initial doubles
rows = []
for k in range(1, N + 1):
    L1 = L(ue); U1 = [ue[i] + dtx * L1[i] for i in range(NX)]; L2 = L(U1)
    ue = [F(1, 2) * ue[i] + F(1, 2) * (U1[i] + dtx * L2[i]) for i in range(NX)]
    if k in steps:
        err = max(abs(F(steps[k][i]) - ue[i]) for i in range(NX))
        ok = err <= k * F(271, 10**17)
        rows.append((k, float(err), k * 2.71e-15))
        print("k=%3d  max exact error = %.4e   bound k*2.71e-15 = %.4e   within bound: %s" % (k, float(err), k * 2.71e-15, ok), flush=True)
with open(outdir + "/error_vs_k.csv", "w", newline="") as f:
    w = csv.writer(f); w.writerow(["k", "max_error_exact", "lean_bound_k_times_271e-17"]); w.writerows(rows)
try:
    import matplotlib; matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    ks = [r_[0] for r_ in rows]
    plt.figure(figsize=(9, 5.4))
    plt.semilogy(ks, [r_[1] for r_ in rows], "bs-", label="C binary64 vs exact Heun, stored parameters (exact-rational error)")
    plt.semilogy(ks, [r_[2] for r_ in rows], "r--", label="Lean bound: k * 2.71e-15")
    plt.xlabel("Time steps (k)"); plt.ylabel("max cell error (log scale)")
    plt.title("Rounding error of the C evolution vs the proved cumulative bound")
    plt.grid(True, which="both", alpha=0.3); plt.legend()
    plt.savefig(outdir + "/error_plot_from_c.png", dpi=200, bbox_inches="tight")
    print("saved plot")
except ImportError:
    print("matplotlib missing: CSV written, plot skipped")