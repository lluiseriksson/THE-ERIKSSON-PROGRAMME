from pathlib import Path
import importlib.util

from flint import arb, ctx
import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]


def _load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


GAP = _load("surface_bessel_gap_taylor_test", "surface_bessel_gap_taylor.py")
CARRIER = _load(
    "surface_remainder_centered_delta_carrier_test",
    "surface_remainder_centered_delta_carrier.py",
)


def test_gap_derivatives_contain_independent_endpoint_values():
    ctx.prec = 180
    mp.mp.dps = 80
    definitions = {
        "A": lambda z: mp.exp(-z) * mp.besseli(1, z) / z,
        "B": lambda z: mp.exp(-z) * mp.besseli(2, z) / z**2,
    }
    for family, function in definitions.items():
        for lo, hi in (("4.01", "4.02"), ("10", "10.1"), ("19.8", "19.9")):
            enclosure = GAP.derivative_enclosures(
                GAP.hull(arb(lo), arb(hi)), family, order=4
            )
            assert all(value.is_finite() for value in enclosure)
            for endpoint in (lo, hi):
                point = mp.mpf(endpoint)
                for order, value in enumerate(enclosure):
                    expected = arb(str(mp.diff(function, point, order)))
                    assert value.contains(expected), (family, lo, hi, order, value, expected)


def test_authoritative_dispatcher_uses_gap_branch_without_crossing():
    ctx.prec = 160
    # A positive-width interval wholly inside 4<z<20 must now be accepted;
    # a cell crossing a branch boundary must remain rejected for subdivision.
    value = CARRIER.scaled_bessel_jet(
        CARRIER.tjet(GAP.hull(arb("10"), arb("10.1"))), "A"
    )
    assert all(component.is_finite() for component in value.derivatives())
    try:
        CARRIER.scaled_bessel_jet(
            CARRIER.tjet(GAP.hull(arb("3.9"), arb("4.1"))), "A"
        )
    except ValueError:
        pass
    else:
        raise AssertionError("cross-boundary Bessel cell must be subdivided")
