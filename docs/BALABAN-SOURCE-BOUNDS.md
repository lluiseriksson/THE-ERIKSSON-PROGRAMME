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

## 4. Coupling-flow decay — the `hg` input (sources received 2026-06-12)

**Irrelevant / super-renormalizable case (geometric, ENCODED).**  Faria
da Veiga–O'Carroll, *Asymptotics for some logistic maps and the RG*,
Physica Scripta 99 (2024) 095262: the canonically-irrelevant logistic
map `λ_{k+1} = r·λ_k·(1 − β·λ_k)` (`0 < r < 1`, `0 ≤ βλ_k ≤ 1`) gives
`λ_{k+1} ≤ r·λ_k`, hence `λ_k ≤ λ_0·rᵏ`.  Goswami (AHP 2019): irrelevant
remainders `V^{irr}_{k+1} = L^{−2}·V^{irr}_k + O(·²)`, so
`V^{irr}_k ≤ C·rᵏ`, `r = L^{−2}`.  **This is now an oracle-clean Lean
theorem** (`RG/CouplingFlow.logistic_geometric_decay`,
`remainder_geometric_of_logistic`, ledger Add. 49), discharging the
bridge's `hg` for the irrelevant mechanism.

**4D marginal case (LOGARITHMIC, NOT geometric — honesty caveat).**  Same
reference, marginal case `α = 1`: `λ_{n+1} = λ_n(1 − βλ_n)` telescopes via
`1/λ_{k+1} − 1/λ_k = β/(1−βλ_k)` to `1/λ_0 + βn ≤ 1/λ_n ≤ 1/λ_0 + βn/(1−βλ_0)`,
i.e. `λ_n ∼ 1/(βn)` — **logarithmic decay, independent of `λ_0`**
(asymptotic freedom).  So `g_k ≤ C·rᵏ` is **FALSE for the 4D marginal
gauge coupling**.  In 4D Bałaban the geometric remainder contraction
`|R_k| ≤ M·rᵏ` is supplied by the **irrelevant operators' scaling**
(the `e^{−κ d(X)}` / `L^{−2k}` factors), with the marginal coupling only
a logarithmic prefactor.  Hence `RG/CouplingFlow`'s `hrec` models the
*irrelevant remainder operators*, `r` their contraction factor — not the
marginal coupling.  Coupling-recursion sources: Bałaban CMP 109 (1987)
pp. 249–301 (4D, `1/g²_{j−1} = 1/g²_j + β_j φ_j`, the inverse-square /
`O(g³)` form); Bałaban 1988 "Convergent Renormalization Expansions" eq
(2.24); Bałaban–Imbrie–Jaffe CMP 114 (1988) (Abelian Higgs).

## 5. Cluster expansion with holes — the `hpoly` input (Dimock)

Reusable theorem: **Dimock II, Appendix F** (NOT only §3.13–3.14, which
*apply* it).  If `|H(X,Φ',Φ)| ≤ H_0·e^{−κ d_M(X, mod Ω^c)}` with
`H_0 ≤ c_0` and `κ ≥ 3κ_0+3`, then `Ξ = exp(Σ_Y H^#(Y,Φ'))` with
`|H^#(Y,Φ')| ≤ O(1)·H_0·e^{−(κ−3κ_0−3) d_M(Y, mod Ω^c)}`.  Convergence is
phrased as `H_0 ≤ c_0 ∧ κ ≥ 3κ_0+3` (the source-level replacement for the
informal `C_d e^{−κ} < 1`).  Geometric substrate: `Σ_{X ⊇ □} e^{−κ_0 d_M(X, mod Ω^c)} ≤ K_0`
(Part II `D_k(mod Ω_k^c)`).  Normalization: Dimock II Theorem 3.1 item 1
`Z_{k+1} = Z_k·N^{−1}_{a,T¹}·(2π)^{|T⁰|/2}·(det C_k)^{1/2}`, and
`dμ*_{Λ_{k+1}}(W_k) = (N^w)^{−1}χ^w_k dμ_{Λ_{k+1}}(W_k)`,
`N^w = exp(−ε⁰_k·Vol(Λ_{k+1}))`.  Sources: Dimock I arXiv:1108.1335
(small-field CE + normalization); Dimock II arXiv:1212.5562 (holes CE,
Appendix F, §§3.8/3.13–3.18).

**Compatibility audit (2026-06-19).**  Direct extraction of Dimock II
Appendix F (PDF pp. 91–92) shows that the with-holes cluster relation is
not ordinary full-polymer overlap/touching.  Dimock says the modified
notion is `Ω`-connected: `X₁ ∩ Ω` and `X₂ ∩ Ω` have nonempty
intersection, equivalently `X₁ ∩ X₂ ∩ Ω ≠ ∅`; `Ω`-disjoint does **not**
imply disjoint.  In Lean, the active region `Ω` is represented by
`skeleton H X`, so the source-facing relation is intersection of
skeletons.  The existing `holePolymerSystem` is the stronger touching
hard-core lattice system used by already-verified local-KP consumers; the
new `omegaHolePolymerSystem` records the Appendix-F-facing active relation
separately.  Future P3 work must use this source-facing system or prove a
comparison theorem before reusing the touching-system consumers.

## 6. Connection to the existing `KP` layer (architectural finding, 2026-06-12)

The repository **already contains an abstract Kotecký–Preiss
cluster-expansion framework** in `YangMills/KP/**`, built for the IR
polymer gas but **general**:

* `KP.PolymerSystem` — an abstract polymer gas (polymer type,
  incompatibility relation, activities);
* `KP.kp_per_size_bound` (`KP/KPBound.lean`):
  `clusterWeight P n ≤ (∑_y ‖activity y‖)·(e·A)ⁿ` — the per-size /
  animal-weighted bound, the Kotecký–Preiss output;
* `KP.Convergence` / `cluster_series_summable` — the geometric summation
  `∑_n b_n ≤ ∑_n C·rⁿ` for `b_n ≤ C·rⁿ`.

This is exactly the abstract polymer-CE machinery the RG `hpoly`/`hwK`
branch needs.  The new `RG/PolymerRemainder.geometric_size_summability`
(Add. 51) is the standalone convergence core aligned with
`KP.Convergence`.  **The genuine path to discharge `hwK`** (for a future
worker) is to instantiate the RG remainder polymers as a `KP.PolymerSystem`
(with the `mod Ω^c` holes metric) and reuse `kp_per_size_bound` —
NOT to rebuild cluster-expansion convergence from scratch.

**What remains genuinely months-scale and Mathlib-empty:** the
*activity-decay* bound `hact` itself — the renormalized polymer activity
estimate `|H_k(X)| ≤ amplitude·e^{−κ d_M(X, mod Ω^c)}` produced by the
Dimock fluctuation integral + the holes localization (Dimock II/III) — and
the raw lattice-animal count in the holes metric.  These are the
constructive-QFT core; the convergence/summation scaffolding around them
is now in place (KP layer + the RG-UV bricks).

## Honest scope

These bounds make G5 *specifiable*; they do not make it short.  G5 (the
interacting fluctuation integral with the large-field split) is the
months-scale analytic core, and even its completion plus U2 yields only
the *lattice* mass gap — M4/M5 (continuum limit, OS reconstruction)
remain untouched, so direct Clay distance stays ~0% (<0.1%).
