"""C1 COMPANION - CERTIFIED admissibility table for the hCq gate
(charter docs/C1-CHARTER.md, judge J-C1-2; interval arithmetic,
python-flint arb, prec 120).

THE OBJECTS (pinned Lean definitions, read at this desk from
YangMills/RG/AppendixFSecondUrsellGeometry.lean:35-42 and
YangMills/RG/AppendixFSecondUrsellLeafSummation.lean:901-903):

  gate      G(d,k0) = (3^d)^2 * e^{-k0} * 2^{3^d+1}      (hCq: G < 1)
  root sum  RS(d,k0) = (1 - G)^{-1}
  moment    M(d,k0)  = max(1, 1/k0, RS)
  leaf      Lf(d,k0) = 4 * M^2
  radius    eps*(d,k0) = 1/Lf   (the geometric series in the paper
                                 has ratio Lf * eps; certified
                                 activity radius for the endpoints)

Every printed enclosure carries ball + boolean (regime pt 7); the
gate booleans are TRI-STATE (PASS only when G < 1 is PROVABLE in
the balls; FAIL only when 1 <= G is provable; else UNDECIDED).

WHAT THIS RUN JUDGES (registered in the charter BEFORE this script
existed):
  band d=2: k0 >= 16 admissible  (charter predicted crossover 15.72)
  band d=3: k0 >= 33 admissible  (charter predicted crossover 32.60)
The script ALSO computes the true crossover k*(d) = ln((3^d)^2 *
2^{3^d+1}) and the charter's registered expression
ln((3^d)^4 * 2^{3^d+1}) side by side: if they disagree, the
registration carried a hand-assembly slip and this transcript is
the measured evidence (ghost #23 class; correction only AFTER this
run, with the transcript cited - the B_nF /8->/16 pattern).

Exactness notes: 3^d and 2^{3^d+1} are exact integers in arb;
e^{-k0} and logs are balls; decimal k0 values are given as exact
decimal strings.
"""
import hashlib
import sys

from flint import arb, ctx

ctx.prec = 120

def blo(z):
    return arb(z.mid()) - arb(z.rad())

def bhi(z):
    return arb(z.mid()) + arb(z.rad())

print("=== C1 COMPANION: certified hCq admissibility (arb) ===")
print("script sha256 : %s"
      % hashlib.sha256(open(__file__, "rb").read()).hexdigest())
try:
    import flint
    fv = getattr(flint, "__version__", "unknown")
except Exception:
    fv = "unknown"
print("python-flint %s  python %s  prec %d bits"
      % (fv, sys.version.split()[0], ctx.prec), flush=True)

ONE = arb(1)

def gate(d, k0):
    """G(d,k0) with exact integer powers; k0 an arb."""
    p3 = arb(3)**d          # exact
    p2 = arb(2)**(3**d + 1)  # exact
    return p3*p3 * (-k0).exp() * p2

def row(d, k0s):
    k0 = arb(k0s)
    G = gate(d, k0)
    gate_pass = bool(G < ONE)
    gate_fail = bool(ONE <= G)
    verdict = ("PASS" if gate_pass else
               ("FAIL" if gate_fail else "UNDECIDED"))
    line = ("  d=%d  k0=%-6s | G in [%s, %s]  gate %s"
            % (d, k0s, blo(G).str(8), bhi(G).str(8), verdict))
    if not gate_pass:
        print(line, flush=True)
        return
    RS = ONE/(ONE - G)
    # M = max(1, 1/k0, RS); reduce by PROVABLE comparisons only:
    b_rs_gt1 = bool(ONE < RS)         # holds iff G > 0, always here
    b_inv_lt = bool(ONE/k0 < RS) and bool(ONE/k0 < ONE)
    assert b_rs_gt1 and b_inv_lt, "M-reduction not provable"
    M = RS
    Lf = 4*M*M
    eps = ONE/Lf
    print(line, flush=True)
    print("       M  in [%s, %s]  (== RS; 1<RS %s, 1/k0<min %s)"
          % (blo(M).str(8), bhi(M).str(8), b_rs_gt1, b_inv_lt))
    print("       Lf in [%s, %s]   eps* in [%s, %s]"
          % (blo(Lf).str(8), bhi(Lf).str(8),
             blo(eps).str(8), bhi(eps).str(8)), flush=True)

print("\n--- admissibility table ---")
for d, ks in [(2, ['8', '11', '11.5', '12', '16', '20', '24', '32']),
              (3, ['20', '24', '25', '26', '26.5', '28', '33', '40'])]:
    for k0s in ks:
        row(d, k0s)

print("\n--- crossover audit: true k*(d) vs charter-registered ---")
for d in (2, 3):
    p3 = arb(3)**d
    p2 = arb(2)**(3**d + 1)
    ktrue = (p3*p3*p2).log()
    kreg = (p3*p3*p3*p3*p2).log()
    print("  d=%d  true k* = ln((3^d)^2 2^(3^d+1)) in [%s, %s]"
          % (d, blo(ktrue).str(10), bhi(ktrue).str(10)))
    print("       charter expr ln((3^d)^4 2^(3^d+1)) in [%s, %s]"
          % (blo(kreg).str(10), bhi(kreg).str(10)))
    agree = bool(abs(ktrue - kreg) < arb('1e-6'))
    print("       agree(1e-6): %s%s"
          % (agree, "" if agree else
             "  -> REGISTERED PREDICTION DOES NOT RE-DERIVE"),
          flush=True)

print("\n--- registered bands (the judge) ---")
b2 = bool(gate(2, arb(16)) < ONE)
b3 = bool(gate(3, arb(33)) < ONE)
print("  d=2, k0=16: gate PROVABLY < 1 : %s" % b2)
print("  d=3, k0=33: gate PROVABLY < 1 : %s" % b3)
print("  BANDS %s" % ("HOLD" if (b2 and b3) else "BROKEN"), flush=True)
