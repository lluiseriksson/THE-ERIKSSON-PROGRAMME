# Bessel--Amos / Feynman--Hellmann 2D note (v8, priority-corrected synthesis)

**An Explicit Optimal-Domain Synthesis for Modified-Bessel Ratios: a
Recurrence-Only Riccati Proof and Lean Verification** -- Lluis Eriksson,
August 2026.

Contents: `bessel_amos_fh.tex` / `.pdf`, the original unit-step audit
`verify_fh.py`, the fractional adversarial audit
`../../scripts/audit49_fractional_bessel.py`, and the integrated Lean module
pair `../../AmosClosure/BesselNegative.lean` and
`../../AmosClosure/FractionalOrderOptimal.lean`.

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
- The v8 priority sweep found a decisive classical route. Garofalo,
  Proposition 8.8 (arXiv:1810.09756), already gives the exact unit-shift
  threshold `nu >= -1/2`, citing Yuan--Kalbfleisch (2000). For arbitrary
  shifts, Freitas--Laugesen on nonnegative orders plus the standard
  connection formula `I_-a = I_a + (2/pi) sin(pi a) K_a` and the
  `I_a,K_a` Wronskian prove sufficiency when `mu+nu >= 0`; the classical
  large-argument expansion proves failure when `mu+nu < 0`.
- Accordingly, the optimal-domain theorem is no longer claimed as new.
  The contribution retained is the explicit synthesis, the alternative
  recurrence-only proof, and its end-to-end machine verification.
- The two new Lean modules prove the full optimal-domain iff, both strict
  inequalities, and an existential upper-bound failure below the boundary,
  with no `sorry`. Colab Pro+ materialization on 2026-08-04 used Lean
  4.29.0-rc6 and Mathlib
  `07642720480157414db592fa85b626dafb71355b`; the registered oracle entries
  return `[propext, Classical.choice, Quot.sound]`.
- The 2D Wilson `U(1)` and `SU(2)` Feynman--Hellmann sector-gap corollary is
  retained. Nothing is claimed about the open 4D mass-gap bracket.

Audit record: `../../docs/BESSEL-FRACTIONAL-STEP-AUDIT-20260804.md` and
`../../docs/audit-artifacts/bessel-fractional-step-49/FREEZE.md`.
