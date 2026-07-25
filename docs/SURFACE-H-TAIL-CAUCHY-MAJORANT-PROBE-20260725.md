# H_tail finite-order Cauchy probe (2026-07-25)

Status: `DESIGN_ONLY`; no H_tail, G2, or G6 promotion.

The executable `scripts/probe_surface_h_tail_cauchy_majorant.py` evaluates the
existing order-five absolute moment majorants on the registered circle
`rho=7/100`. It also recomputes the endpoint budget:

\[
 q=\frac{1/15}{7/100},\qquad
 M\,\rho^{-4}\frac{q^5}{1-q}\le \beta_1\Theta_3(1).
\]

Thus the required normalized circle supremum is `M < 0.0001680`.
Before the geometric tail multiplier is applied, the corresponding `C_4`
budget is `beta1*Theta3*rho^4 < 0.0027632`.

The probe reports a finite raw bilinear numerator for the four moment
carriers. This is conditioning evidence, not the required `M`: the raw
quantity is unnormalised and the source modules provide neither the omitted
coefficient tail on the complex circle nor a joint complex lower bound for
the denominator. The script therefore ends with three explicit `UNSUPPLIED`
lines and `NO_H_TAIL_PROMOTION`.

The next admissible closure artifact must supply both missing charges in the
same complex-domain transcript, with production/replay hashes and an
independent validator. A finite-order value estimate, an outer spatial tail,
or the real-axis mass floor alone cannot be substituted for that joint bound.
