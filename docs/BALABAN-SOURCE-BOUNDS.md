# BAŁABAN / DIMOCK SOURCE BOUNDS — faithful transcriptions for the UV campaign

**Date:** 2026-06-12.  Source material received and transcribed (uploads
2026-06-12).  This file records the **exact** cited bounds the U1/U2/S2
campaign targets, so G5 is *specifiable* from sources rather than
reconstructed from memory.  **Honest caveats are flagged in bold.**

## 1. Fluctuation-covariance bound (Bałaban CMP 95 (1984), Prop 1.1/1.2)

CMP 95 Part I gives the Green/propagator `G_k` estimates; the
fluctuation-covariance `C_k` formulation is the standard RG
rescaling of these.  The stable bound, constants `c, m > 0` independent
of `k`, volume, lattice spacing:

* **Pointwise exponential decay** (block units):
  `|C_k(x,y)| ≤ c·e^{−m|x−y|}` (microscopic units:
  `|C_k(x,y)| ≤ c·e^{−m|x−y|/L^k}`).
* **ℓ²/operator-norm scaling** (the key quantitative item):
  `‖∇^r C_k ∇^{*s}‖_{2→2} ≤ c·L^{2−r−s}`, `r+s ≤ 2`.  In particular
  `‖C_k‖_{2→2} ≤ c·L²`, `‖∇C_k‖, ‖C_k∇*‖ ≤ c·L`, `‖∇C_k∇*‖ ≤ c`.
* **Localized (block `Δ,Δ'`)**:
  `‖1_Δ ∇^r C_k ∇^{*s} 1_{Δ'}‖_{2→2} ≤ c·L^{2−r−s}·e^{−m·dist(Δ,Δ')/L}`.

Exact uploaded-paper analogue (CMP 95 Part I): the uniform `L²` Green
bound (eq 1.89) `‖GJ‖,‖∇GJ‖,‖G∇*J‖,‖∇G∇*J‖,… ≤ γ₀⁻¹‖J‖`, and the
localized exponential estimate (eq 1.114)
`‖ζGJ‖,… ≤ O(1)·e^{−δ₀|y−y'|}·‖ζ‖·‖J‖`.

**Lean encoding (the stable covariance bound, the S2/G5 input).**  This
is the hypothesis consumed by `RG/GaussianStep.covarianceBilinDual_map_le`
(brick G4): `∃ B ≥ 0, ∀ M, Cov(μ)[M,M] ≤ B·‖M‖²`, with `B = c·L²` the
`r=s=0` case.  G4 then gives `Cov(μ.map Q)[L,L] ≤ B·‖Q‖²·‖L‖²`, and the
deterministic `linAvg_l2_le` (`‖Q‖² ≤ L^{2−d}`) supplies the contraction.

## 2. Single-scale `R`-term bound (Bałaban CMP 122-II, Theorem 1)

**HONEST CAVEAT — this is the most important correction.**  Bałaban's
Theorem 1 does **NOT** state a bare scalar `|R_k| ≤ M·rᵏ`.  It states
that, assuming all effective couplings stay in `]0, γ]` for small `γ`,
the effective densities `ρ_k` satisfy the **polymer-localized** bounds of
Bałaban [III] §2:

* `R_k(U_k) = Σ_{j=1}^k [R^{(j)}(Λ_j, U_k) − R^{(j)}(Λ_j, 1)]`, with
  `|R^{(j)}(X, (U,J))| ≤ g_j^{κ₀}·exp(−κ·d_j(X))`  (eq 2.31 [III]),
  `κ₀` arbitrarily large after fixing other parameters;
* the new `k`-th contribution: `|R'^{(k)}(X,(U,J))| ≤ exp(−p₀(g_k))·exp(−κ·d_k(X))`  (eq 1.100).

The faithful "safe" compressed form is the **summed polymer bound**
`Σ_{X: d_k(X) ≥ n} |R'^{(k)}(X,…)| ≤ M·exp(−p₀(g_k))·e^{−κn}`.

**A genuine `|R_k| ≤ M·rᵏ` form is NOT stated by Bałaban.**  It follows
only after an *extra* geometric-scale assumption on the coupling flow,
e.g. `g_k^{κ₀} ≤ C·rᵏ` or `exp(−p₀(g_k)) ≤ C·rᵏ`.  **Consequence for
this repo:** `Paper.uv_geometric_summation` / `lattice_mass_gap_of_per_scale_uv`
(`docs/UV-SINGLE-SCALE-PLAN.md`, U0) take `|R_k| ≤ M·rᵏ` as their
hypothesis — this is therefore a **simplified surrogate** of the true
Bałaban bound, valid only under the coupling-flow assumption above.  The
honest carried obligation is the polymer-localized bound (2.31[III]/1.100)
*plus* the coupling-flow assumption, not the bare `M·rᵏ`.  Recorded so
the Clay-distance accounting stays honest.

## 3. Method shape (Dimock II, "RG according to Bałaban", arXiv:1212.5562; JMP 54, 092301 (2013))

The scalar `φ⁴` (3D) fluctuation-integral RG step, the architecture to
mirror for G5 (region-indexed, **not** a global high-mode integral):

  block average + rescale → small/large-field split (partition of unity)
  → expand at the minimizer → Gaussian fluctuation integral (covariance
  `C'_{k,Ω}`) → localize (replace nonlocal `C^{1/2}` by a local
  approximation) → cluster expansion *with holes* (large-field
  complements) → next-scale polymer activities `E_{k+1}(X)`.

Key §§: 3.8 (fluctuation integral / covariance `C'_{k,Ω}`), 3.13–3.14
(localization + cluster expansion).  Large-field suppression factor
`exp(−O(1)·p_k²·|Ω_{k+1}^c|_M)`.

**Lean objects to mirror** (the structured-density RG step
`StructuredDensity_k → StructuredDensity_{k+1}`): region history `Π`,
small-field region `Ω_k`, good core `Λ_k`, block average `Q`, background
minimizer, fluctuation `Z ∼ C'_{k,Ω}`, localized fluctuation field `W_k`,
polymer activity `E_k(X)`, large-field factor.  Lemmas:
`BlockAverage_preserves_integral`, `SmallLarge_partition_of_unity`,
`LargeField_suppression`, `Minimizer_solves_variational_equation`,
`Quadratic_expansion_at_minimizer`, `Fluctuation_covariance_identification`,
`Covariance_localization`, `Fluctuation_integral_normalization`,
`DeltaE_localization`, `ClusterExpansion_with_holes`,
`RGStep_preserves_density_class`.

## Honest scope

These bounds make G5 *specifiable*; they do not make it short.  G5 (the
interacting fluctuation integral with the large-field split) is the
months-scale analytic core, and even its completion plus U2 yields only
the *lattice* mass gap — M4/M5 (continuum limit, OS reconstruction)
remain untouched, so direct Clay distance stays ~0% (<0.1%).
