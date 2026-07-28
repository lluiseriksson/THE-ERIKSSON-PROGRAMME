"""Diagnostic t-quotient normalization for the finite-beta seam."""

from fractions import Fraction
from math import comb, factorial

from flint import arb, ctx

import certify_bulk_beta_taylor_scaled_sign_rows_cwin3p2_high as high
from certify_surface_scaled_bulk_common_scale_design import CommonScaleBox, install


class SinNormalizedBox(CommonScaleBox):
    def _sin_min(self, t_lo, t_hi):
        lo = high.scaled.bulk.aq(t_lo).sin()
        hi = high.scaled.bulk.aq(t_hi).sin()
        out = lo if lo.lower() < hi.lower() else hi
        assert out.lower() > 0, (t_lo, t_hi, out)
        return out

    @staticmethod
    def _divide_jet(raw, sine):
        out = [raw[0] / sine[0]]
        for n in range(1, len(raw)):
            value = raw[n]
            for k in range(1, n + 1):
                value -= arb_comb(n, k) * out[n-k] * sine[k % 4]
            out.append(value / sine[0])
        return out

    @staticmethod
    def _divide_abs_jet(raw, denominator):
        out = [raw[0] / denominator]
        for n in range(1, len(raw)):
            value = raw[n]
            for k in range(1, n + 1):
                value += arb_comb(n, k) * out[n-k]
            out.append(value / denominator)
        return out

    def W(self, t_lo, t_hi):
        ctx.prec = self.prec
        t_mid = (t_lo + t_hi) / 2
        t_rad = (t_hi - t_lo) / 2
        T = high.scaled.bulk.aq(t_mid)
        sine = [T.sin(), T.cos(), -T.sin(), -T.cos()]
        smin = self._sin_min(t_lo, t_hi)
        fourier = {}
        for family in ("a", "b"):
            for q in range(self.order + 1):
                raw = [self.fourier_derivative(T, q, r, family)
                       for r in range(self.t_order + 2)]
                normalized = self._divide_jet(raw, sine)
                for r, value in enumerate(normalized):
                    fourier[family, q, r] = value

        Hb = high.scaled.bulk.hull(-high.scaled.bulk.aq(self.beta_rad), high.scaled.bulk.aq(self.beta_rad))
        Ht = high.scaled.bulk.hull(-high.scaled.bulk.aq(t_rad), high.scaled.bulk.aq(t_rad))
        out = arb(0)
        Hbpow = arb(1)
        for q in range(self.order + 1):
            Htpow = arb(1)
            for r in range(self.t_order + 1):
                out += (self.mixed_W(fourier, q, r) * Hbpow * Htpow
                        / arb(factorial(q) * factorial(r)))
                Htpow *= Ht
            Hbpow *= Hb

        norm_sums = []
        for Sa, Sb, Sma, Smb in self.abs_sums:
            norm_sums.append((Sa / smin, Sb / smin,
                              Sma / smin + Sa / smin**2,
                              Smb / smin + Sb / smin**2))
        q = self.order + 1
        absWq = arb(0)
        for j in range(q + 1):
            Sa, Sb, Sma, Smb = norm_sums[j]
            Ta, Tb, Tma, Tmb = norm_sums[q-j]
            absWq += 2 * arb(comb(q, j)) * (Sma * Tb + Sa * Tmb)
        remainder = high.scaled.bulk.aq(self.beta_rad)**q * absWq / arb(factorial(q))

        norm_center = []
        for q in range(self.order + 1):
            norm_center.append([])
            for family_index in range(2):
                raw = [self.abs_center[q][r][family_index]
                       for r in range(self.t_order + 3)]
                norm = self._divide_abs_jet(raw, smin)
                if family_index == 0:
                    norm_center[q].append(norm)
                else:
                    norm_center[q].append(norm)

        def abs_mixed(qb, rt):
            value = arb(0)
            for j in range(qb + 1):
                for ell in range(rt + 1):
                    Aj = norm_center[j][0][ell]
                    Bj = norm_center[j][1][ell]
                    Atj = norm_center[j][0][ell + 1]
                    Ak = norm_center[qb-j][0][rt-ell]
                    Bk = norm_center[qb-j][1][rt-ell]
                    Btk = norm_center[qb-j][1][rt-ell + 1]
                    value += arb(comb(qb, j) * comb(rt, ell)) * (
                        Atj * Bk + Aj * Btk)
            return 2 * value

        rt = self.t_order + 1
        t_remainder = arb(0)
        for qb in range(self.order + 1):
            t_remainder += (high.scaled.bulk.aq(self.beta_rad)**qb
                            / arb(factorial(qb))
                            * high.scaled.bulk.aq(t_rad)**rt / arb(factorial(rt))
                            * abs_mixed(qb, rt))
        return out + (remainder + t_remainder) * high.scaled.bulk.pm1()


def arb_comb(n, k):
    return arb(comb(n, k))


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--lo", default="3258/32")
    parser.add_argument("--hi", default="3259/32")
    parser.add_argument("--t-lo", default="31268/10000")
    parser.add_argument("--t-hi", default="312686/100000")
    parser.add_argument("--order", type=int, default=30)
    parser.add_argument("--t-order", type=int, default=37)
    parser.add_argument("--prec", type=int, default=180)
    args = parser.parse_args()
    lo, hi = Fraction(args.lo), Fraction(args.hi)
    t_lo, t_hi = Fraction(args.t_lo), Fraction(args.t_hi)
    install()
    high.CWIN = Fraction(3, 2)
    high.ORDER = args.order
    high.T_ORDER = args.t_order
    high.PREC = args.prec
    high.install_cached_backend()
    # install_cached_backend replaces the base W method; restore the
    # quotient-normalized override on the subclass after that hook.
    high.scaled.bulk.BetaTaylorBox = SinNormalizedBox
    box = SinNormalizedBox(lo, hi, prec=args.prec,
                           order=args.order, t_order=args.t_order)
    value = box.W(t_lo, t_hi)
    print("SIN-NORMALIZED STRESS", lo, hi, t_lo, t_hi)
    print("W_UPPER", value.upper().str(50))
    print("W_LOWER", value.lower().str(50))
    print("FINITE", value.is_finite())
    print("SCOPE single-box diagnostic only; no G2/G6 promotion")


if __name__ == "__main__":
    main()
