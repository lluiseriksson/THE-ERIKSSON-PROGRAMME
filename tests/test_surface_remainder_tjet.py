import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/"scripts"))


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/"scripts"/(name+".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MOD = load("surface_remainder_tjet")
SPATIAL = load("surface_remainder_spatial_jet3")


def test_tjet_chain_rules():
    ctx.prec = 140
    x = MOD.tjet(arb("0.3"), arb(1))
    value = ((x.sin()*x.exp())/(1+x**2)).sqrt()
    expected = ((x.v.sin()*x.v.exp())/(1+x.v**2)).sqrt()
    assert (value.v-expected).contains(0)
    numerator = x.v.sin()*x.v.exp()
    numerator_d = x.v.exp()*(x.v.sin()+x.v.cos())
    direct = (numerator_d/(1+x.v**2)
              -numerator*2*x.v/(1+x.v**2)**2)/(2*expected)
    assert (value.d-direct).contains(0)

    simple = x.sin().exp()
    simple_d2 = x.v.sin().exp()*(x.v.cos()**2-x.v.sin())
    assert (simple.d2-simple_d2).contains(0)


def test_spatial_jet_accepts_tjet_coefficients():
    x = MOD.tjet(arb("0.2"), arb(1))
    result = SPATIAL.jexp(SPATIAL.variable_x(x))
    assert (result.get(0, 0).v-arb("0.2").exp()).contains(0)
    assert (result.get(0, 0).d-arb("0.2").exp()).contains(0)
    assert (result.get(0, 0).d2-arb("0.2").exp()).contains(0)
