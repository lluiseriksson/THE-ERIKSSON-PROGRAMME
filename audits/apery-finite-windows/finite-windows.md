# Finite detection of an Apéry moment obstruction

For the sequence A_k(x) of Apéry polynomials, consider the two leading Gram matrices of monomials from degree 0 through n, one with moments A_(i+j) and one with A_(i+j+1). A negative quadratic form is a finite certificate against a Stieltjes measure. We locate the first degree at which either form is negative and give a polynomial certificate that works on a closed interval around each test parameter.

| x | First degree, both tests considered | Shift of first witness | Size of first failing matrix |
|---|---:|---:|---:|
| 1/2 | 8 | 0 | 9 |
| 9/10 | 22 | 1 | 23 |
| 19/20 | 35 | 0 | 36 |
| 24/25 | 39 | 1 | 40 |
| 39/40 | 53 | 0 | 54 |
| 49/50 | 61 | 0 | 62 |

The shift that detects failure first switches three times along the four increasing sample values 9/10, 19/20, 24/25, 39/40. Thus either fixed choice of shift can delay detection at these resolutions. A switch between samples describes the discrete ordering at those samples; there may be more switches in between. At 49/50 the unshifted test first fails in degree 61 and the shifted test in degree 63. The degree-61 witness is strictly negative throughout [6271/6400,6273/6400]. Minimality is established at the rational center. The table gives finite observations; an asymptotic upper bound remains open in this investigation.

The generator constructs primitive integer orthogonal polynomials using q^k A_k(p/q). Signs of the squared norms determine definiteness because the basis transformation is triangular with nonzero diagonal. For an interval witness it expands the same quadratic form in the parameter and checks the signs of all Bernstein coefficients after clearing a positive denominator. The coefficients in the compressed JSON describe P(qt), with coefficients of P in ascending order, and the shift multiplies the squared polynomial by t^s. Reproduce the table with python apery-witness.py. The separate checker takes the frozen results and certificates, recomputes the leading determinant signs by symmetric fraction-free elimination with GMP, and verifies interval negativity by a separate expansion. Run python apery-check.py and python -O apery-check.py on Linux with g++, GMP and Python 3.

The two calibration points reproduce prior certificates. Li and Yeroushalmi already prove that every fixed-size collection passes near 1. Davis supplies exact rational examples as well as analytical results. The earlier research and the distinction between this finite result and the published classification are documented in comparison.md. The larger points and the interval witnesses should be read with those antecedents. No priority claim is made here.
