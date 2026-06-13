# UV single-scale bound — precise shopping list

**Date:** 2026-06-12.  **Status:** source material RECEIVED and audited
(2026-06-12, later) — see §7 for the source-grounded mapping and the
revised honest scope.  The headline outcome of the audit: the
**fixed-lattice** clustering is now UNCONDITIONAL in Lean
(`sun_lattice_exponential_clustering`, ledger Add. 22), and the §6.3
bound is confirmed to be a **continuum-only** obstruction equal to
Balaban's full UV-stability theorem for 4D non-Abelian gauge theory.

This document is the output of a research-grade investigation of the
UV frontier (the sole carried hypothesis of the M3 lattice mass gap).
It states **exactly** what external mathematical content is needed to
discharge the §6.3 bound *non-vacuously and core-cleanly*, and why the
material currently in the tree cannot be used.

## 1. The investigation finding (why we are blocked, honestly)

The only UV-side material in the repository is the abstract
`ClayCore` Balaban scaffolding (`BalabanH1H2H3.lean`,
`SmallFieldBound.lean`, `LargeFieldBound.lean`, `MultiscaleDecoupling.lean`,
`OscillationBound.lean`, `CouplingControl.lean`).  An audit shows it is
**physically vacuous** and therefore unusable for honest progress:

* `BalabanH1.h_sf : ∀ n, ∃ R, 0 ≤ R ∧ R ≤ E0·g²·e^{−κn}` is satisfied by
  `R = 0`.  It is an existential upper bound on an *unconstrained*
  nonnegative real — it constrains nothing.
* `SmallFieldActivityBound` bundles `activity : Nat → Real` as an
  **arbitrary** sequence (inhabited by `fun _ => 0`); it is never tied
  to the Wilson action, the gauge measure, or an RG step.
* `MultiscaleDecoupling.lean` and the rest contain **no occurrence** of
  `gaugeMeasureFrom`, `WilsonAction`, `sunHaarProb`, or any integral —
  they are disconnected from the actual lattice gauge theory.
* Consequently `balaban_combined_bound : BalabanHyps ⟹ …` is a sound
  but **empty** implication: `BalabanHyps` is trivially inhabited
  (all activities `0`), so the theorem says nothing about Yang–Mills.

This is exactly why these files are **excluded from `YangMillsCore`**
(the core's import-closure audit was correct).  Wiring them into the
assembly would produce a green theorem that proves nothing — the
hollow-progress pattern this project forbids.  **Do not connect this
scaffolding to the mass-gap assembly.**

What the repo DOES have, non-vacuously and tied to the real measure:
the entire IR/strong-coupling side (cluster expansion, area laws,
`gibbs_truncated_correlation_bound`), and the clean conditional
`lattice_mass_gap_of_per_scale_uv` (ledger Add. 19) that reduces the
carried UV hypothesis to a per-scale RG contraction
`|R_{t,k}| ≤ (C₂ e^{−c₀t})·rᵏ` with `covUV t = ∑_{k<n(t)} R_{t,k}`.
The missing content is the **non-vacuous definition of `R_{t,k}` as an
actual RG contribution to the two-point function, and the proof of its
bound.**

## 2. What is genuinely needed (the mathematical objects)

To build the UV side core-cleanly and non-vacuously, the following
must be DEFINED (tied to the existing `gaugeMeasureFrom`/`sunHaarProb`
core) and the stated estimates PROVED:

**(D1) Block-spin transformation on SU(N) lattice gauge fields.**
The averaging map `C : {fields at spacing a} → {fields at spacing La}`
on link variables, including the *specific* gauge-covariant averaging
Balaban uses (not canonical — needs the exact construction).  Needed:
its precise definition, the background/fluctuation split
`U = U_bg · exp(fluctuation)`, and the minimization characterising the
background.

**(D2) The scale-k effective action and fluctuation covariance.**
The renormalized action `A_k` after `k` block steps; the Gaussian
(quadratic) part and the fluctuation propagator `Γ_k` with its range
`~ a_k = L^k a` and decay.

**(D3) The multiscale decomposition of the truncated two-point
function** giving `covUV(t) = ∑_k R_{t,k}` with `R_{t,k}` the
scale-k contribution at separation `t`, and the scale–distance
dictionary (`a_k = a*/L^{k*−k}`, `t = R/a*`) that the §6.3 summation
note references.

**(E1) Small-field single-scale estimate (Balaban H1, *real* version).**
On the small-field region (`|fluctuation| ≤ p₀(g) = A₀(log g^{−2})^{p*}`),
the per-step renormalized error satisfies `|R_{t,k}^{sf}| ≤ E₀ g_k²·(decay)`.
Source content: the analyticity of the fluctuation integral as a
perturbation of the Gaussian + the running-coupling control.

**(E2) Large-field single-scale estimate (Balaban H2, *real* version).**
On the large-field region the Gaussian weight gives suppression
`e^{−p₀(g)}` per large-field block, beating the placement entropy:
`|R_{t,k}^{lf}| ≤ e^{−p₀(g)}·(decay)`.  This is the genuine analytic
core (a Peierls/large-deviations estimate against the gauge measure).

## 3. Precise source request (papers / sections / equations)

In priority order for a formalization effort:

1. **The Eriksson paper itself** (cited in-tree as "[55] Eriksson
   2602.0069") — the FULL statements and proofs of **Theorem 6.2**
   (single-scale bound), **Theorem 6.3** (§6.3 summation over scales),
   and **Theorem 8.5 / §8.1, Eq (51)–(52)** (the large-field profile
   `p₀(g)` and activity bound).  The Lean comments target these exact
   results; their precise hypotheses and constants are needed to state
   them non-vacuously.  **This is the single most useful item.**

2. **T. Bałaban, "Renormalization group approach to lattice gauge field
   theories", Comm. Math. Phys. 116 (1988)** — the small-field stability
   estimate (E1).  The in-tree comment cites "Balaban CMP 116".

3. **T. Bałaban, Comm. Math. Phys. 122 (1989), Part II, Eq (1.98)–(1.100)**
   — the large-field suppression estimate (E2).  Cited in
   `LargeFieldBound.lean`.

4. **J. Dimock, "The renormalization group according to Balaban" I–III**
   (J. Math. Phys. 54–55, 2013–2014) — the cleanest modern exposition of
   (D1)–(D3); strongly preferred as the *formalization* reference because
   it makes the block-spin map, fluctuation covariance, and small/large-
   field decomposition explicit and self-contained.

5. The precise definition of `covUV(t)` used in the paper's M3 assembly
   (how the truncated plaquette two-point function is split into IR and
   UV parts, and the scale decomposition of the UV part) — needed to
   make `lattice_mass_gap_of_per_scale_uv`'s `covUV`/`R_{t,k}` concrete.

## 4. Honest scope statement

Even with all of the above formalized, the result is the **M3 lattice**
mass gap, unconditionally.  It does NOT establish the continuum limit,
OS/Wightman reconstruction, or the continuum mass gap (M4/M5) — those
remain open mathematics.  Distance to the Clay prize would remain
**~0% (<0.1%)**; the named reduced obstruction would shrink from
"{§6.3 UV bound} ∪ {M4/M5}" to "{M4/M5}".

This is a large, genuine constructive-QFT formalization (Balaban RG has
never been fully formalized).  It should be opened as its own campaign
once the source material above is in hand; reconstructing the gauge
block-spin construction from memory is NOT responsible and is declined
on honesty grounds.

## 7. SOURCE-GROUNDED MAPPING (2026-06-12, after receiving the papers)

The user supplied: the Balaban gauge series (CMP **95**, **96** —
propagators/RG transformations; **98** — averaging operations; **99**,
**102** — regular-config spaces, gauge fixing, the variational/background
field; **109** — effective actions, small field; **116** — cluster
expansions; **122-I**, **122-II** — large-field renormalization), the
**Dimock** trilogy ("RG according to Balaban" I/II/III, arXiv
1108.1335 / 1212.5562 / 1304.0705), and the Eriksson AQFT collection
(`Master4.pdf`).  Audit findings, precise:

* **The target estimate IS Balaban's UV-stability theorem.**  CMP
  122-II states (abstract, verbatim) that it "complete[s] the proof of
  the ultraviolet stability of four-dimensional pure gauge field
  theories, as formulated in Theorem 1," and is "the main result of
  the whole sequence of papers... on non-Abelian gauge field theories."
  The §6.3 UV bound is therefore not a single lemma but the culmination
  of Balaban's ~10-paper programme; the cited "(1.98)–(1.100)" point to
  formula (1.100) of paper **[IV]** of that chain, i.e. the estimate
  depends transitively on the whole series.

* **Dimock is the cleanest *method* reference, but it is scalar φ⁴ in
  d = 3, NOT gauge.**  Dimock I, Theorem 1 (the stability bound):
  `exp(−c·Vol(T_M)) ≤ Z_{M,N}/Z_{M,N}(0) ≤ exp(c·Vol(T_M))`, uniformly
  in the UV cutoff `L^{−N}` — the partition-function stability that
  underlies the continuum limit.  Dimock explicitly notes φ⁴ "is a
  special case of the scalar QED model treated by Balaban"; the pure
  Yang–Mills case is harder still (gauge fixing, the non-Abelian
  background-field variational problem of CMP 99/102, the R operation).
  Dimock is invaluable for the *shape* of the formalization (block-spin
  `Q`, fluctuation covariance, small/large-field split, cluster
  expansion, convergence) but does not itself discharge the YM bound.

* **Lean-facing target statement (the honest shape).**  The continuum
  UV input the assembly ultimately needs has the Dimock/Balaban
  stability shape: with `Q_k` the `k`-fold block average and `Γ_k` the
  fluctuation covariance, the renormalized single-scale error `R_k`
  (small-field + large-field) obeys `|R_k| ≤ M·r^k` (`docs/UV-SINGLE-
  SCALE-PLAN.md` (UV-core)), which `lattice_mass_gap_of_per_scale_uv`
  already turns into the gap.  Stating this NON-vacuously requires
  first DEFINING, against the existing `gaugeMeasureFrom` core: the
  gauge-covariant block average (CMP 98), the background field /
  variational problem (CMP 99/102), and the fluctuation effective
  action (CMP 109).  None are in the core.

* **What is genuinely missing (and is NOT being faked).**  The entire
  gauge RG construction.  Even the first object — Balaban's
  gauge-covariant averaging operator on SU(N) link configurations
  (CMP 98) — is a substantial definitional commitment whose precise
  form must match the later estimates; it is the natural first brick of
  a dedicated multi-month campaign, not a session-sized task.

* **What WAS achieved instead (real, unconditional).**  The audit
  established that the fixed-lattice clustering does not need any of
  this: `sun_lattice_exponential_clustering` (ledger Add. 22) proves
  exponential decay of the connected two-plaquette correlator with NO
  carried hypothesis, at strong coupling, directly from the banked
  cluster expansion.  The §6.3/Balaban content is thereby correctly
  localized to the continuum (lattice-spacing → 0) limit — the M4
  problem — alongside OS/Wightman reconstruction (M5).  Clay distance
  is UNCHANGED (~0%, <0.1%): this clarifies and strengthens the lattice
  side without reducing any continuum obstruction.
