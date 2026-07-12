"""Arb certificate lane for W(t,beta)/t^3 on the left edge.

This is design code until an exhaustive manifested run is committed.  It
uses the exact order-three zero of the odd W at t=0 and never divides an Arb
ball containing zero.
"""

from fractions import Fraction
import hashlib
from math import comb, factorial
from pathlib import Path
import platform
import subprocess
import sys

import flint
from flint import arb, ctx

import certify_bulk_beta_taylor_arb as bulk


class LeftEdgeBox:
    def __init__(self, beta_lo: Fraction, beta_hi: Fraction,
                 order: int = 12, t_order: int = 9, prec: int = 140):
        self.box = bulk.BetaTaylorBox(
            beta_lo, beta_hi, prec=prec, order=order, t_order=t_order
        )
        self.order = order
        self.t_order = t_order
        self.beta_rad = (beta_hi-beta_lo)/2
        self.beta_hi = beta_hi
        self.M = self.box.M
        self.prec = prec
        self._hi_abs = self._absolute_sums_at_hi(order+1, 4)

    def _absolute_sums_at_hi(self, max_q: int, max_power: int):
        M, k = self.M, self.M+1
        jets = [None]*(M+2)
        for m in range(1, M+2):
            jets[m] = bulk.coefficient_jets(m, self.beta_hi, max_q)
        xhi = bulk.aq(self.beta_hi)
        ratio = bulk.coefficient_tail_ratio(xhi, k)
        rows = []
        for q in range(max_q+1):
            row = []
            for power in range(max_power+1):
                sa = sum((arb(m)**power*jets[m][0][q]
                          for m in range(1, M+1)), arb(0))
                sb = sum((arb(m)**power*jets[m][1][q]
                          for m in range(1, M+1)), arb(0))
                sa += bulk.general_derivative_tail(
                    jets[k][0][0], k, ratio, self.box.beta_lo, q, power)
                sb += bulk.general_derivative_tail(
                    jets[k][1][0], k, ratio, self.box.beta_lo, q, power)
                row.append((sa, sb))
            rows.append(row)
        return rows

    @staticmethod
    def _abs_mixed(rows, q: int, r: int) -> arb:
        out = arb(0)
        for j in range(q+1):
            for ell in range(r+1):
                aj, _ = rows[j][ell]
                atj, _ = rows[j][ell+1]
                _, bk = rows[q-j][r-ell]
                _, btk = rows[q-j][r-ell+1]
                out += arb(comb(q, j)*comb(r, ell))*(atj*bk+aj*btk)
        return 2*out

    def normalized_W(self, t_lo: Fraction, t_hi: Fraction) -> arb:
        """Enclose W/t^3 on 0<=t_lo<=t_hi<=3/5."""
        ctx.prec = self.prec
        if t_lo < 0 or t_hi < t_lo or t_hi > Fraction(3, 5):
            raise ValueError("left-edge t box is outside [0,3/5]")
        T0 = arb(0)
        fourier = {}
        for family in ("a", "b"):
            for q in range(self.order+1):
                for r in range(self.t_order+2):
                    fourier[family, q, r] = self.box.fourier_derivative(
                        T0, q, r, family
                    )
        Hb = bulk.hull(-bulk.aq(self.beta_rad), bulk.aq(self.beta_rad))
        T = bulk.hull(bulk.aq(t_lo), bulk.aq(t_hi))
        out = arb(0)
        hb_power = arb(1)
        for q in range(self.order+1):
            t_power = arb(1)
            for r in range(3, self.t_order+1):
                if r > 3:
                    t_power *= T
                mixed = self.box.mixed_W(fourier, q, r)
                out += (mixed*hb_power*t_power
                        /arb(factorial(q)*factorial(r)))
            # Taylor remainder after t_order, divided by t^3.
            rt = self.t_order+1
            t_error = (bulk.aq(t_hi)**(rt-3)
                       * self.box.abs_mixed_center(q, rt)
                       /arb(factorial(rt)))
            out += hb_power*t_error*bulk.pm1()/arb(factorial(q))
            hb_power *= Hb

        # Beta Taylor remainder.  Since W(0)=W_t(0)=W_tt(0)=0 for every
        # beta, Taylor's theorem in t bounds W_beta^(q)/t^3 by its third
        # t derivative divided by 3!.
        qb = self.order+1
        beta_error = (bulk.aq(self.beta_rad)**qb/arb(factorial(qb))
                      * self._abs_mixed(self._hi_abs, qb, 3)/arb(6))
        return out+beta_error*bulk.pm1()


def cover_normalized(box: LeftEdgeBox, lo=Fraction(0), hi=Fraction(1, 5),
            min_width=Fraction(1, 1_000_000)) -> int:
    count = 0
    stack = [(lo, hi)]
    while stack:
        a, b = stack.pop()
        value = box.normalized_W(a, b)
        if value < 0:
            count += 1
        elif b-a <= min_width:
            raise RuntimeError("left-edge failure near t=%s" % float(a))
        else:
            mid = (a+b)/2
            stack.append((mid, b)); stack.append((a, mid))
    return count


def cover_regular(box: LeftEdgeBox, lo=Fraction(1, 5),
                  hi=Fraction(3, 5),
                  min_width=Fraction(1, 1_000_000)) -> int:
    count = 0
    stack = [(lo, hi)]
    while stack:
        a, b = stack.pop()
        value = box.box.W(a, b)
        if value < 0:
            count += 1
        elif b-a <= min_width:
            raise RuntimeError("regular left-edge failure near t=%s" % float(a))
        else:
            mid = (a+b)/2
            stack.append((mid, b)); stack.append((a, mid))
    return count


def cover_t(box: LeftEdgeBox) -> tuple[int, int]:
    """Certified splice: normalized [0,.2], regular [.2,.6]."""
    return cover_normalized(box), cover_regular(box)


def fq(value: str) -> Fraction:
    return Fraction(value)


def provenance():
    path = Path(__file__).resolve()
    root = path.parents[1]
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True,
            stderr=subprocess.DEVNULL).strip()
    except Exception:
        head = "UNAVAILABLE"
    return {
        "script": str(path.relative_to(root)).replace("\\", "/"),
        "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "git_head": head,
        "python": platform.python_version(),
        "python_flint": getattr(flint, "__version__", "UNKNOWN"),
        "arb_prec_bits": 140,
        "bulk_dependency_sha256": hashlib.sha256(
            Path(bulk.__file__).read_bytes()).hexdigest(),
    }


def cover_beta(beta_lo: Fraction, beta_hi: Fraction,
               step: Fraction = Fraction(1, 10)) -> tuple[int, int, int]:
    cursor = beta_lo
    beta_boxes = normalized_total = regular_total = 0
    while cursor < beta_hi:
        upper = min(cursor+step, beta_hi)
        try:
            box = LeftEdgeBox(cursor, upper)
            normalized, regular = cover_t(box)
            print("beta-box [%s,%s]: normalized=%d regular=%d" %
                  (float(cursor), float(upper), normalized, regular),
                  flush=True)
            beta_boxes += 1
            normalized_total += normalized
            regular_total += regular
            cursor = upper
        except RuntimeError as error:
            if step <= Fraction(1, 1_000_000):
                raise
            step /= 2
            print("narrowing beta step to %s at beta=%s (%s)" %
                  (float(step), float(cursor), error), flush=True)
    return beta_boxes, normalized_total, regular_total


if __name__ == "__main__":
    b1 = fq(sys.argv[1]); b2 = fq(sys.argv[2])
    step = fq(sys.argv[3]) if len(sys.argv) > 3 else Fraction(1, 10)
    for key, value in provenance().items():
        print("PROVENANCE %s=%s" % (key, value), flush=True)
    print("CONFIG beta_order=12 t_order=9 splice=1/5 initial_db=%s" %
          float(step), flush=True)
    beta_boxes, normalized, regular = cover_beta(b1, b2, step)
    print("CERTIFIED (left-edge, Arb): W<0 on (0,0.6] x [%s,%s]; "
          "beta_boxes=%d normalized_boxes=%d regular_boxes=%d" %
          (float(b1), float(b2), beta_boxes, normalized, regular),
          flush=True)
