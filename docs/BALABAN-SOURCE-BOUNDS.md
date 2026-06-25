# BAŁABAN / DIMOCK SOURCE BOUNDS — faithful transcriptions for the UV campaign

**Date:** 2026-06-12.  Source material received and transcribed (uploads
2026-06-12).  This file records the **exact** cited bounds the U1/U2/S2
campaign targets, so G5 is *specifiable* from sources rather than
reconstructed from memory.  **Honest caveats are flagged in bold.**

Companion audit: [`SOURCE-CLAIM-AUDIT.md`](SOURCE-CLAIM-AUDIT.md) records
contradicted claims, source-pending statements, local-PDF provenance, and the
requirements for promoting an extraction to a source-verified input.  This file
remains the positive quantitative transcription ledger.

Structured lookup: [`SOURCE-CITATIONS.md`](SOURCE-CITATIONS.md) and
`docs/source-citations/*.json` define stable citation keys for the primary-source
anchors below.  Use `python scripts/source_citations.py show <key>` before
opening OCR or rendered pages.

**Source-targeting audit (2026-06-20, corrected).**  For the remaining
`hRpoly` Yang-Mills activity/locality package, do not cite mirror metadata
without checking the Springer/DOI record and the paper text.  Web downloads
were blocked from the automation environment: Project Euclid downloads
returned Incapsula pages, SciSpace returned 403, and Springer PDF endpoints
served subscription HTML.  A later local-source search found user-provided
PDFs for the Balaban spine below, and the worker copied text extracts,
rendered page images, and the split CMP 119 paper into the persistent
runtime source cache.  The blocker is therefore no longer "all PDFs
unavailable"; it is the more precise extraction of support/locality and
raw-activity hypotheses from the now-available primary text.

Primary Balaban targets for `hRpoly`:

* T. Balaban, "Renormalization group approach to lattice gauge field
  theories. I. Generation of effective actions in a small field
  approximation and a coupling constant renormalization in four dimensions",
  Comm. Math. Phys. 109 (1987), 249-301, DOI `10.1007/BF01215223`.
* T. Balaban, "Renormalization group approach to lattice gauge field
  theories. II. Cluster expansions", Comm. Math. Phys. 116 (1988), 1-22,
  DOI `10.1007/BF01239022`.
* T. Balaban, "Convergent renormalization expansions for lattice gauge
  theories", Comm. Math. Phys. 119 (1988), 243-285,
  DOI `10.1007/BF01217741`.
* T. Balaban, "Large field renormalization. I. The basic step of the R
  operation", Comm. Math. Phys. 122 (1989), 175-202,
  DOI `10.1007/BF01257412`.
* T. Balaban, "Large field renormalization. II. Localization,
  exponentiation, and bounds for the R operation", Comm. Math. Phys. 122
  (1989), 355-392, DOI `10.1007/BF01238433`.

Lean-facing extraction request: the first pages/equations for
fluctuation-integral locality/support containment, localized effective
actions, and Yang-Mills polymer activity decay are now located below.  The
remaining gap is the source-to-Lean translation from Balaban's localized
domains/components to `LocalActivity.fluctuationSupport`, `HoleFamily`,
`activeSupport`, and `discreteModifiedMetric`.  Until that translation is
formalized, keep the activity/locality package as explicit hypotheses.

Visually confirmed source anchors already located:

* CMP 116 (1988), PDF pages 12--13 / printed pages 12--13, eqs.
  (2.5)--(2.6): after localizing a cluster term to a domain `Z0` and
  conditioning the correlated fluctuation Gaussian, Balaban makes the
  linear change of variables `B' = (C^(k))^(1/2) X`.  The resulting
  expression is written against the ultralocal product standard Gaussian
  `dmu0(X)`, while the covariance/root-dependent factors are absorbed into
  the function `G`.  This is the primary-source anchor for the Lean
  product-Gaussian interface `balabanCMP116Dmu0` and the source field
  `PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussian_pushforward`.
  It still leaves the coordinate/dictionary identification,
  determinant/Jacobian normalization, and post-(2.6) localization proof as
  explicit obligations; see `docs/SOURCE-CLAIM-AUDIT.md` row B5a.
* CMP 116 (1988), PDF pages 13--14 / printed pages 13--14, eqs.
  (2.7)--(2.10): after (2.6), the expression is still global through the
  propagators and operators in `G`.  Balaban localizes it again by introducing
  parameters `s`, generalized random-walk expansions, and a resolvent/series
  expansion of `(C^(k))^(1/2)`.  Equations (2.8)--(2.9) rewrite the
  product-Gaussian integral as localized quantities `H(Z,Z0)` and `H(Z)`, and
  (2.10) records component factorization.  This is the source anchor for the
  Lean `hrootPieces` activity-local agreement shape, but it still leaves the
  domain/enlargement translation and root-piece reconstruction theorem
  explicit; see `docs/SOURCE-CLAIM-AUDIT.md` row B5b.
* CMP 116 (1988), PDF pages 15--20 / printed pages 15--20, eqs.
  (2.14)--(2.38): the subsequent estimates bound terms of the resummed
  localized activity `H(Z)`.  They culminate in Lemma 3 / (2.38), not in an
  exact finite reconstruction theorem for `(C^(k))^(1/2)`.  This points the
  Lean interface toward a source-side `local_physical_activity_construction`
  and `raw_pointwise_decay` theorem, while finite root-piece sums should remain
  truncations or auxiliary approximations unless a separate exact
  activity-support equality theorem is found; see `docs/SOURCE-CLAIM-AUDIT.md`
  row B5c.
* CMP 116 (1988), PDF page 20, Lemma 3 / eq. (2.38): the cluster-expansion
  activity `H(Z)` for `Z in D_{k+1}` satisfies
  `|H(Z)| <= C_3 eps_1 exp(-(1 - 8 delta) * (1/2) * L * kappa * d_{k+1}(Z))`.
  This is an activity-decay anchor for the localized fluctuation-integral
  expansion, not yet the full Lean support theorem.
* CMP 116 (1988), PDF page 21, eqs. (2.39)--(2.41): Lemma 3's `H(Z)` bound is
  inserted into the exponentiated polymer series and converted into the
  effective-action estimate
  `|E^(k+1)(X)| <= O(1) C_3 eps_1 exp(-(1 - 10 delta)^(1/2) L kappa d_{k+1}(X))`.
  The text then fixes `(1 - 10 delta)^(1/2) L = 1`, assumes
  `O(1) C_3 eps_1 <= E_0/2`, and treats the extra `log Z` normalization term by
  a separate generalized random-walk expansion.  This is the source anchor for
  the post-Lemma-3 effective-action consumer; see `docs/SOURCE-CLAIM-AUDIT.md`
  row B5d.
* CMP 119 (1988), PDF page 18 / printed page 260, eq. (2.31): localized
  `R`-terms satisfy
  `|R^(j)(X,(U,J))| <= g_j^kappa_0 exp(-kappa d_j(X))`, with
  `kappa_0` selectable large after fixing the other parameters.  PDF page
  19 / printed page 261, eq. (2.42), gives the analogous localized
  boundary-term bound
  `|B^(j)(X,(U,J),A,{S_i cap X})| < B_0 exp(-kappa d_j(X))`.
* CMP 122-I (1989), PDF page 18 / printed page 192, eq. (1.70): the
  intermediate large-field `C_k^(n)` terms satisfy
  `|C_k^(n)(X,(U,J))| <= C_0 exp(-(1 + 3 beta) kappa d_m(X))` for
  `X in D_m`.
* CMP 122-II (1989), PDF page 36 / printed page 390, eqs. (1.98)-(1.100):
  the exponentiated `R'^(k)` cluster expansion separates boundary terms
  from the second-group `R`-terms, and those second-group terms satisfy
  `|R'^(k)(X,(U,J))| <= exp(-p_0(g_k)) exp(-kappa d_k(X))`.
  This is the sharp local large-field `R`-operation bound; it should not be
  relabeled as a global scalar mass-gap estimate.

Support/locality extraction pass (2026-06-20):

* CMP 116 (1988), PDF pages 4-5, derives the one-step component
  localization used before the cluster bound.  A source term indexed by a
  connected component `Y0` is built from propagators and fields restricted
  to `Y0`; the term depends only on the gauge/source variables restricted
  to that localized set together with the base cube.  This is the source
  analogue of the Lean support-containment input, but it is not yet a Lean
  theorem because the paper's component `Y0` and base-cube enlargement must
  still be mapped to `activeSupport` and `fluctuationSupport`.
* CMP 116 (1988), PDF page 21, eqs. (2.39)-(2.41), records how the
  localized cluster estimate following Lemma 3 is converted into the
  effective-action bound `(I.1.18)`, after choosing the `delta,L`
  normalization and making the small constant `O(1) C_3 eps_1` fit the
  `E_0/2` budget.  This supplies the missing post-Lemma-3 bridge; the
  remaining Lean obligation is to express those constants as a pointwise
  modified-metric activity majorant.
* CMP 116 (1988), PDF pages 18-20, gives the restrictions feeding Lemma 3.
  The proof extracts factors of the form `alpha_6 exp(-delta kappa d_k(Y))`,
  uses the geometric inequalities (2.27), (2.30), (2.32), the summability
  input (2.29), and the scale-transfer inequality (2.36).  It introduces
  `eps_2 = 2 E_0 eps_1 C_1 alpha_4^-1 alpha_6^-1 M^q exp(C_2 kappa_1)` and
  then defines
  `C_3 = 2 (L+2)^4 O(1) 2 E_0 C_1 alpha_4^-1 alpha_6^-1 M^q exp(C_2 kappa_1)`.
  The restrictions include smallness of `eps_2`, smallness of
  `(L+2)^4 O(1) eps_2`, a bound of the form
  `2 (L+2)^4 O(1) eps_2 exp(5 kappa) <= 1`, the scale condition
  `(kappa_1 - 1)/2 >= 2 L kappa`, and boundedness of
  `(LM)^4 alpha_0`, `(LM)^4 alpha_1`, `(LM)^4 alpha_4`, `(LM)^4 gamma_2`.
  These are source restrictions for the activity-decay constant, not yet a
  formal Lean parameter hierarchy.
* CMP 119 (1988), split PDF pages 15-17 / printed pages 257-259, gives the
  localized density decomposition.  Large-field operations factor over
  connected large-field regions, the effective action is decomposed into
  regular `E`, remainder `R`, and boundary/large-field-near `B` pieces, and
  the regular terms have a representation by domains `X` whose kernels
  depend only on the gauge field restricted to `X`.
* CMP 119 (1988), split PDF pages 18-19 / printed pages 260-261, extends
  the same localized-domain representation to `R` and `B` terms and supplies
  the already-recorded decay bounds (2.31) and (2.42).  This confirms that
  the source-level package is polymer-local and scale-local; it does not by
  itself identify Balaban's domains with the current Lean hole-polymer
  metric.

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
separately.  Its local KP consumer
`omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp` now proves
that a skeleton-pinned local activity window feeds KP convergence for this
literal `Ω`-connected relation.  Future P3 work should feed that
source-facing consumer directly, or prove a comparison theorem before reusing
the touching-system consumers.  The follow-up theorem
`omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`
derives the active local window from the Dimock-shaped pointwise modified
metric majorant and the discrete modified-metric summability, leaving the
model-specific activity estimate as the remaining analytic input.

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
