# Bessel--Amos / Feynman--Hellmann 2D note (v7, corrected continuous-order version)

**Sharp Continuous-Order Comparison for Modified-Bessel Ratios: a Riccati
Proof, the Optimal Real-Order Domain, and Lean Verification** -- Lluis
Eriksson, August 2026.

Contents: `bessel_amos_fh.tex` / `.pdf`, the original unit-step audit
`verify_fh.py`, the fractional adversarial audit
`../../scripts/audit49_fractional_bessel.py`, and the integrated Lean module
`../../AmosClosure/FractionalOrder.lean`.

Status and corrected scope:

- For `rho_a(x)=I_{a+1}(x)/I_a(x)`, the paper proves
  `0 < rho_mu-rho_nu < (nu-mu)/x` for `0 <= mu < nu`, and classifies the
  natural real-order domain: for `-1 < mu < nu`, the upper bound holds for
  every `x>0` exactly when `mu+nu >= 0`.
- The nonnegative-order logarithmic-derivative monotonicity and a
  first-contact proof are already in Freitas--Laugesen, Lemma 10
  (Amer. J. Math. 143 (2021), DOI 10.1353/ajm.2021.0024). Version 6's claim
  that fractional steps did not follow from the method was false and is
  explicitly corrected.
- The candidate-new content is the sharp ratio formulation, optimal
  negative-order boundary/obstruction, and machine verification. Priority
  remains subject to independent external review.
- `AmosClosure/FractionalOrder.lean` proves the complete nonnegative-order
  upper theorem on C4's Gamma-series Bessel implementation, with no `sorry`.
  Colab Pro+ materialization on 2026-08-04 used Lean 4.29.0-rc6 and Mathlib
  `07642720480157414db592fa85b626dafb71355b`; all five oracle entries return
  `[propext, Classical.choice, Quot.sound]`.
- The 2D Wilson `U(1)` and `SU(2)` Feynman--Hellmann sector-gap corollary is
  retained. Nothing is claimed about the open 4D mass-gap bracket.

Audit record: `../../docs/BESSEL-FRACTIONAL-STEP-AUDIT-20260804.md` and
`../../docs/audit-artifacts/bessel-fractional-step-49/FREEZE.md`.
