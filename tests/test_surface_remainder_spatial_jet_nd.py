from flint import arb

import surface_remainder_spatial_jet_nd as nd


def test_four_variable_product_coefficients():
    variables = [nd.variable(k+1, k) for k in range(4)]
    value = nd.jmul(nd.jadd(variables[0], variables[1]),
                    nd.jadd(variables[2], variables[3]))
    assert value.get((1, 0, 1, 0)) == arb(1)
    assert value.get((0, 1, 0, 1)) == arb(1)


def test_exp_derivative_normalization():
    x = nd.variable(0, 0)
    value = nd.jexp(x)
    assert value.get((5, 0, 0, 0)).overlaps(arb(1)/120)
