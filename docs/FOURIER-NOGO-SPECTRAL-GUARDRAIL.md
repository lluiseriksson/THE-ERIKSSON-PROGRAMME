# Spectral guardrail after the Fourier no-go v1.1

Date: 2026-08-02

## Status

The v1.1 paper proves an exact Fourier witness with Rayleigh quotient

    lambda_L = 4 sin^2(pi/L)

for every `L >= 2`, every fixed positive `N'`, and `Nc >= 2`.  It does not
claim that this witness minimizes the flat Hodge form on
`ker Q_L ∩ ker delta`.

The tempting strengthening

    inf_{A != 0, Q_L A = 0, delta A = 0}
      <A, K0 A> / ||A||^2 = 4 sin^2(pi/L)

is false in this generality.

## Exact finite counterexample

Take `L = 2`, `N' = 2`, two distinct directions `i != j`, and a nonzero
internal vector `w`.  On the fine `j`-cycle of length four use

    f = (1, -1 | -1, 1),

where the vertical bar separates the two length-two coarse blocks, and set

    A(x, mu) = f(x_j) w   if mu = i,
               0          otherwise.

Each block sum is zero:

    1 + (-1) = 0,
    (-1) + 1 = 0.

Transverse line shifts do not change `x_j`, hence `Q_2 A = 0`.  Since the
only nonzero component points in direction `i` and depends only on `x_j`,
`delta A = 0` as well.

Around the four-cycle the successive squared differences are

    4, 0, 4, 0.

Thus the one-dimensional energy is `8`, while the one-dimensional norm
squared is `4`.  All remaining site coordinates and `||w||^2` factor out,
so

    <A, K0 A> / ||A||^2 = 2.

But the within-block periodic Fourier eigenvalue used in v1.1 is

    lambda_2 = 4 sin^2(pi/2) = 4.

Therefore

    inf_{A != 0, Q_2 A = 0, delta A = 0}
      <A, K0 A> / ||A||^2 <= 2 < lambda_2.

## Consequence for the next project

Do not promote the v1.1 witness bound to a spectral-minimizer statement.
The true restricted bottom depends on coupling across coarse-block
interfaces and may depend on `N'` as well as `L`.

A valid spectral continuation must:

1. Fourier transform in the coarse-block coordinate.
2. Keep the `L` within-block coordinates and impose the exact block-sum
   constraints.
3. Diagonalize the resulting constrained `L x L` Bloch family.
4. Minimize over coarse quasi-momentum and transverse polarizations.
5. Only then state the bottom of `K0` on `ker Q_L ∩ ker delta`.

The counterexample above should be formalized as the first oracle-clean test
before attempting a general Bloch theorem.  It does not weaken the v1.1
no-go, which needs only one explicit family whose quotient tends to zero.
