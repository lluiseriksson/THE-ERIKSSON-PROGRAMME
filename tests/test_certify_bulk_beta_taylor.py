from fractions import Fraction
import importlib.util
from pathlib import Path

import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "bulk_beta_taylor", ROOT / "scripts" / "certify_bulk_beta_taylor_arb.py")
MOD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MOD)


def mid(x):
    return float(x.mid())


def test_coefficient_beta_derivatives_against_independent_mpmath():
    mp.mp.dps = 60
    beta = Fraction(15, 2)
    M = 12
    I = [MOD.enc_I(m, beta) for m in range(M+4)]
    a, b, da, db = MOD.coefficient_arrays(I, M)
    for m in (1, 2, 5, 10):
        def aa(x):
            return mp.besseli(m, x)**2 * (
                (m-1)*mp.besseli(m-1, x)**2
                + (m+1)*mp.besseli(m+1, x)**2)
        def bb(x):
            return m*mp.besseli(m, x)**4
        for got, want in ((da[m], mp.diff(aa, float(beta))),
                          (db[m], mp.diff(bb, float(beta))),
                          (a[m], aa(float(beta))),
                          (b[m], bb(float(beta)))):
            rel = abs(mid(got)-float(want))/max(1.0, abs(float(want)))
            assert rel < 2e-14


def test_higher_coefficient_jets_against_independent_mpmath():
    mp.mp.dps = 70
    x = Fraction(37, 5)
    for m in (1, 4, 9):
        aj, bj = MOD.coefficient_jets(m, x, 5)
        def aa(y):
            return mp.besseli(m, y)**2 * (
                (m-1)*mp.besseli(m-1, y)**2
                + (m+1)*mp.besseli(m+1, y)**2)
        def bb(y):
            return m*mp.besseli(m, y)**4
        for q in range(6):
            for got, fun in ((aj[q], aa), (bj[q], bb)):
                want = mp.diff(fun, mp.mpf(37)/5, q)
                rel = abs(mid(got)-float(want))/max(1.0, abs(float(want)))
                assert rel < 4e-14


def test_tail_ratio_majorizes_actual_coefficient_ratios():
    x = Fraction(15, 1)
    M = 90
    I = [MOD.enc_I(m, x) for m in range(M+4)]
    a, b, _, _ = MOD.coefficient_arrays(I, M)
    r = MOD.coefficient_tail_ratio(MOD.aq(x), 61)
    for m in range(61, 89):
        assert a[m+1] < r*a[m]
        assert b[m+1] < r*b[m]


def test_high_beta_pilot_box_is_certified():
    bb = MOD.BetaTaylorBox(Fraction(149, 10), Fraction(15, 1))
    # A representative interior interval and a near-moving-edge interval.
    assert bb.W(Fraction(3, 2), Fraction(150001, 100000)) < 0
    edge = MOD.PI_UP-MOD.CWIN/Fraction(15, 1)
    assert bb.W(edge-Fraction(1, 50), edge) < 0


def test_pilot_enclosure_contains_independent_point_values():
    mp.mp.dps = 70
    bb = MOD.BetaTaylorBox(Fraction(149, 10), Fraction(15, 1))
    tlo, thi = Fraction(3, 1), Fraction(151, 50)
    enclosure = bb.W(tlo, thi)
    lo = float(enclosure.lower()); hi = float(enclosure.upper())
    for beta in (mp.mpf('14.9'), mp.mpf('14.95'), mp.mpf('15')):
        for t in (mp.mpf('3'), mp.mpf('3.01'), mp.mpf('3.02')):
            FA = FB = FAt = FBt = mp.mpf('0')
            for m in range(1, 90):
                Im = mp.besseli(m, beta)
                a = Im**2*((m-1)*mp.besseli(m-1, beta)**2
                           +(m+1)*mp.besseli(m+1, beta)**2)
                b = m*Im**4
                FA += a*mp.sin(m*t); FB += b*mp.sin(m*t)
                FAt += m*a*mp.cos(m*t); FBt += m*b*mp.cos(m*t)
            value = float(2*(FAt*FB-FA*FBt))
            assert lo <= value <= hi


def test_moving_boundary_outer_rounding_contract():
    assert MOD.aq(MOD.PI_UP) > MOD.arb.pi()
    for beta in (Fraction(6), Fraction(10), Fraction(15)):
        assert (MOD.aq(MOD.PI_UP-MOD.CWIN/beta)
                > MOD.arb.pi()-MOD.aq(MOD.CWIN/beta))
