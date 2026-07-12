"""Arb design lane for the compact moving right edge.

The certified quantity is W(pi-d,beta)/d^3.  Values at pi are assembled
from exact Fourier parity, so the order-three endpoint zero is removed
before interval evaluation and no Arb ball containing zero is divided.
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


CWIN = Fraction(3, 2)
SPLICE = Fraction(1, 500)


class RightEdgeBox:
    def __init__(self, beta_lo: Fraction, beta_hi: Fraction,
                 order: int = 12, d_order: int = 9, prec: int = 140):
        self.box = bulk.BetaTaylorBox(
            beta_lo, beta_hi, prec=prec, order=order, t_order=d_order
        )
        self.beta_lo = beta_lo
        self.beta_hi = beta_hi
        self.beta_rad = (beta_hi-beta_lo)/2
        self.order = order
        self.d_order = d_order
        self.prec = prec
        self.M = self.box.M
        self._hi_abs = self._absolute_sums_at_hi(order+1, 4)

    def _absolute_sums_at_hi(self, max_q: int, max_power: int):
        M, k = self.M, self.M+1
        jets = [None]*(M+2)
        for m in range(1, M+2):
            jets[m] = bulk.coefficient_jets(m, self.beta_hi, max_q)
        ratio = bulk.coefficient_tail_ratio(bulk.aq(self.beta_hi), k)
        rows = []
        for q in range(max_q+1):
            row = []
            for power in range(max_power+1):
                sa = sum((arb(m)**power*jets[m][0][q]
                          for m in range(1, M+1)), arb(0))
                sb = sum((arb(m)**power*jets[m][1][q]
                          for m in range(1, M+1)), arb(0))
                sa += bulk.general_derivative_tail(
                    jets[k][0][0], k, ratio, self.beta_lo, q, power)
                sb += bulk.general_derivative_tail(
                    jets[k][1][0], k, ratio, self.beta_lo, q, power)
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

    def fourier_derivative_at_pi(self, q: int, r: int,
                                 family: str) -> arb:
        """Exact-parity t derivative of F_A or F_B at pi."""
        if r % 2 == 0:
            return arb(0)
        jets = self.box.aj if family == "a" else self.box.bj
        phase = 1 if r % 4 == 1 else -1
        out = sum((arb(phase*(-1)**m)*arb(m)**r*jets[m][q]
                   for m in range(1, self.M+1)), arb(0))
        tail = bulk.general_derivative_tail(
            self.box.ac[self.M+1] if family == "a"
            else self.box.bc[self.M+1],
            self.M+1, self.box.r, self.box.beta_mid, q, r)
        return out+bulk.pm1()*tail

    def normalized_W(self, d_lo: Fraction, d_hi: Fraction) -> arb:
        """Enclose W(pi-d,beta)/d^3 for 0<=d_lo<=d_hi."""
        ctx.prec = self.prec
        if d_lo < 0 or d_hi < d_lo or d_hi > CWIN/self.beta_lo:
            raise ValueError("right-edge d box exceeds its moving wedge")
        fourier = {}
        for family in ("a", "b"):
            for q in range(self.order+1):
                for r in range(self.d_order+2):
                    fourier[family, q, r] = self.fourier_derivative_at_pi(
                        q, r, family)
        hb = bulk.hull(-bulk.aq(self.beta_rad), bulk.aq(self.beta_rad))
        d = bulk.hull(bulk.aq(d_lo), bulk.aq(d_hi))
        out = arb(0)
        hb_power = arb(1)
        for q in range(self.order+1):
            d_power = arb(1)
            for r in range(3, self.d_order+1):
                if r > 3:
                    d_power *= d
                sign = -1 if r % 2 else 1
                out += (arb(sign)*self.box.mixed_W(fourier, q, r)
                        * hb_power*d_power
                        / arb(factorial(q)*factorial(r)))
            rt = self.d_order+1
            d_error = (bulk.aq(d_hi)**(rt-3)
                       * self.box.abs_mixed_center(q, rt)
                       / arb(factorial(rt)))
            out += hb_power*d_error*bulk.pm1()/arb(factorial(q))
            hb_power *= hb

        qb = self.order+1
        beta_error = (bulk.aq(self.beta_rad)**qb/arb(factorial(qb))
                      * self._abs_mixed(self._hi_abs, qb, 3)/arb(6))
        return out+beta_error*bulk.pm1()

    def fourier_derivative_at_d(self, d_value: Fraction, q: int, r: int,
                                family: str) -> arb:
        """t derivative at t=pi-d, using exact Fourier parity."""
        d = bulk.aq(d_value)
        jets = self.box.aj if family == "a" else self.box.bj
        out = arb(0)
        for m in range(1, self.M+1):
            md = arb(m)*d
            s = arb((-1)**(m+1))*md.sin()
            c = arb((-1)**m)*md.cos()
            trig = self.box.trig_derivative(s, c, r)
            out += arb(m)**r*jets[m][q]*trig
        tail = bulk.general_derivative_tail(
            self.box.ac[self.M+1] if family == "a"
            else self.box.bc[self.M+1],
            self.M+1, self.box.r, self.box.beta_mid, q, r)
        return out+bulk.pm1()*tail

    def regular_W(self, d_lo: Fraction, d_hi: Fraction) -> arb:
        """Enclose W(pi-d,beta) by a Taylor expansion centered in d."""
        ctx.prec = self.prec
        d_mid, d_rad = (d_lo+d_hi)/2, (d_hi-d_lo)/2
        fourier = {}
        for family in ("a", "b"):
            for q in range(self.order+1):
                for r in range(self.d_order+2):
                    fourier[family, q, r] = self.fourier_derivative_at_d(
                        d_mid, q, r, family)
        hb = bulk.hull(-bulk.aq(self.beta_rad), bulk.aq(self.beta_rad))
        hd = bulk.hull(-bulk.aq(d_rad), bulk.aq(d_rad))
        out = arb(0)
        hb_power = arb(1)
        for q in range(self.order+1):
            hd_power = arb(1)
            for r in range(self.d_order+1):
                sign = -1 if r % 2 else 1
                out += (arb(sign)*self.box.mixed_W(fourier, q, r)
                        *hb_power*hd_power/arb(factorial(q)*factorial(r)))
                hd_power *= hd
            hb_power *= hb

        qb = self.order+1
        abs_wq = arb(0)
        for j in range(qb+1):
            sa, sb, sma, smb = self.box.abs_sums[j]
            ta, tb, tma, tmb = self.box.abs_sums[qb-j]
            abs_wq += 2*arb(comb(qb, j))*(sma*tb+sa*tmb)
        beta_error = (bulk.aq(self.beta_rad)**qb*abs_wq
                      /arb(factorial(qb)))
        rt = self.d_order+1
        d_error = sum((
            bulk.aq(self.beta_rad)**q/arb(factorial(q))
            *bulk.aq(d_rad)**rt/arb(factorial(rt))
            *self.box.abs_mixed_center(q, rt)
            for q in range(self.order+1)), arb(0))
        return out+(beta_error+d_error)*bulk.pm1()


def _cover_lane(box: RightEdgeBox, lo: Fraction, hi: Fraction,
                evaluator, min_width: Fraction) -> int:
    count = 0
    stack = [(lo, hi)]
    while stack:
        a, b = stack.pop()
        value = evaluator(a, b)
        if value < 0:
            count += 1
        elif b-a <= min_width:
            raise RuntimeError("right-edge failure near d=%s" % float(a))
        else:
            mid = (a+b)/2
            stack.append((mid, b)); stack.append((a, mid))
    return count


def cover_d(box: RightEdgeBox,
            min_width: Fraction = Fraction(1, 1_000_000)) -> tuple[int, int]:
    d_hi = CWIN/box.beta_lo
    normalized_hi = min(SPLICE, d_hi)
    normalized = _cover_lane(
        box, Fraction(0), normalized_hi, box.normalized_W, min_width)
    regular = 0
    if d_hi > SPLICE:
        regular = _cover_lane(
            box, SPLICE, d_hi, box.regular_W, min_width)
    return normalized, regular


def cover_beta(beta_lo: Fraction, beta_hi: Fraction,
               step: Fraction = Fraction(1, 10)) -> tuple[int, int, int]:
    cursor = beta_lo
    base_step = step
    beta_boxes = normalized_total = regular_total = 0
    while cursor < beta_hi:
        trial_step = min(base_step, beta_hi-cursor)
        upper = cursor+trial_step
        try:
            box = RightEdgeBox(cursor, upper)
            normalized, regular = cover_d(box)
            print("beta-box [%s,%s]: normalized=%d regular=%d" %
                  (float(cursor), float(upper), normalized, regular), flush=True)
            beta_boxes += 1
            normalized_total += normalized
            regular_total += regular
            cursor = upper
        except RuntimeError as error:
            if trial_step <= Fraction(1, 1_000_000):
                raise
            base_step, saved_base = trial_step/2, base_step
            print("narrowing beta step to %s at beta=%s (%s)" %
                  (float(base_step), float(cursor), error), flush=True)
            try:
                nested_boxes, nested_normalized, nested_regular = cover_beta(
                    cursor, min(cursor+trial_step, beta_hi), base_step
                )
            finally:
                base_step = saved_base
            beta_boxes += nested_boxes
            normalized_total += nested_normalized
            regular_total += nested_regular
            cursor = upper
    return beta_boxes, normalized_total, regular_total


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


def fq(value: str) -> Fraction:
    return Fraction(value)


if __name__ == "__main__":
    b1 = fq(sys.argv[1]); b2 = fq(sys.argv[2])
    step = fq(sys.argv[3]) if len(sys.argv) > 3 else Fraction(1, 10)
    for key, value in provenance().items():
        print("PROVENANCE %s=%s" % (key, value), flush=True)
    print("CONFIG beta_order=12 d_order=9 CWIN=3/2 splice=1/500 initial_db=%s" %
          float(step), flush=True)
    beta_boxes, normalized, regular = cover_beta(b1, b2, step)
    print("CERTIFIED (right-edge, Arb): W<0 on "
          "pi-1.5/beta<=t<pi x [%s,%s]; beta_boxes=%d "
          "normalized_boxes=%d regular_boxes=%d" %
          (float(b1), float(b2), beta_boxes, normalized, regular), flush=True)
