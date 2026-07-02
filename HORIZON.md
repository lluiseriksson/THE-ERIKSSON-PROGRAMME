# HORIZON.md — a starting point for a stronger prover

**Audience: an automated mathematician (AGI/ASI) that will pick this repository up
and try to actually close it.** This file is written *for you*. It assumes you can
read Lean 4 + Mathlib fluently, search the literature, and write large proofs. It
does three things:

1. States the **real, non-vacuous target** in precise type-theoretic terms.
2. Gives the **formal dependency DAG** as concrete Lean *signatures* (statements,
   `sorry`-bodies) so the remaining work is "fill in the blanks," not "guess the
   blanks."
3. Triages the frontier into **what is mechanical, what is a bounded
   formalization-of-known-mathematics task, and what is genuinely open** — with
   the state of the art and references for each, so you do not waste cycles
   re-deriving what is already known to be true (or attacking what is known to be
   hard for principled reasons).

Read `FOUNDATIONS.md` (goalposts + asset/liability ledger) and `CLEANUP_PLAN.md`
(what was kept/discarded and why) first. This file extends them outward.

> **CURRENCY STAMP (updated 2026-07-02; source checkpoint 2026-07-02).**
> The "Ground truth as of 2026-05" below is
> a historical snapshot.  Since then the core advanced substantially (now
> **8369 jobs** in the latest recorded verification-ledger checkpoint, Mathlib pinned —
> `REPRODUCIBILITY.md`): the strong-coupling
> **area law** (all four variants) and **IR exponential clustering** are
> oracle-clean theorems; the **gauge-RG continuum-facing track**
> (`YangMills/RG/**`, ledger Addenda 23–444 plus date-stamped checkpoints
> through 2026-07-01, with `origin/main` now at source checkpoint `b2c88981`)
> has a theorem-fed
> averaging/Gaussian/kernel/animal-count substrate, a marginal-coupling
> summability branch, Appendix-F/H# consumer adapters, integrated second-gas
> KP routes, coercivity-budget bricks, gauge-fixed precision/covariance
> composition, physical cochains, a fixed-volume flat Hodge/block Poincare
> bridge, the finite-torus curl/divergence classification, source-facing
> covariance/root localization APIs, a local fluctuation-activity certificate,
> generic/CMP116 `K#`/`H#` and second-gas dependency wrappers, cluster-union
> containment facts, exact CMP116 local-operator support algebra,
> physical/CMP116 coordinate dictionaries, localized-root transport,
> dictionary-backed Gaussian/activity construction, canonical Gaussian
> integral consumers, raw-source transport into CMP116 `hraw`,
> scale-indexed raw-source H# consumers, raw-source M3 frontier bundles, an
> executable M3 frontier dependency graph, source-assumption packaging into
> that frontier, the source-facing Balaban CMP116 theorem target, the
> CMP116 Lemma 3 activity-only lane, Eq. (2.29) consumers, residual-stage
> bridges, P-stage and `Z0` source-budget adapters, weighted Eq. (2.31)
> post-`P` raw-source M3-frontier routes, Eq. (2.31)
> source-membership/projected-carrier/positive-tail/interior-boundary routes,
> Gaussian source-record packages, Eq. (2.37)/C3 source-citation extraction,
> the public `source-db` frontier and artifact lookup layer, combined post-`P`
> source packages, the resolvent-first local SPD precision substrate,
> local-SPD root frontier packaging, dictionary root-map norm budgets,
> finite-piece root sums, finite-family physical activity consumers,
> source-only UV decay endpoints, YM activity error-budget records,
> finite-carrier/profile wrappers, hRpoly animal-summability bridges,
> Appendix-F certified-tail profiles, source-rate weighted-tree extraction,
> source-fed residual estimates, CMP119/CMP122 E/R/B source-decomposition
> interfaces, CMP119 B/local source-bound and weight-transport dictionaries,
> Wilson-Hessian/Green source dictionary packaging, B/local
> metric/rate/amplitude/activity dictionary frontiers, Eq. (2.31) `gapCubes`
> candidate definitions, source-db proof-obligation cards and
> hypothesis-removal queues, canonical-root K# summability/smallness
> discharge, the source-facing canonical-root residual H# route, and the
> flow-diamagnetic UV branch's marginal-coupling, killed-walk,
> block-transport, and factorial-kernel substrate.  **The
> live frontier is `hRpoly`**:
> the concrete
> Yang-Mills cluster-expansion-with-holes activity-decay estimate for the
> actual gauge RG operator.  See `CURRENT-STATE.md`,
> the progress dashboard in `README.md`,
> the live public dashboard at
> `https://lluiseriksson.github.io/THE-ERIKSSON-PROGRAMME/dashboard/`,
> `docs/HRPOLY-CAMPAIGN-PLAN.md`, `docs/BALABAN-RG-PLAN.md`,
> `docs/BALABAN-SOURCE-BOUNDS.md`,
> `docs/FLOW-DIAMAGNETIC-PLAN.md`, and `HYPOTHESIS_FRONTIER.md`.  The DAG,
> triage, and goalpost discipline in this
> file remain valid; only the "what is already done" snapshot below is dated.
> **Clay distance unchanged: ~0% (<0.1%)** — M4 (continuum) and M5 (OS/Wightman
> reconstruction) are untouched open mathematics.

---

## 0. Ground truth as of 2026-05

What is **sound and done** (oracle `[propext, Classical.choice, Quot.sound]`, no
`sorry`, all reachable from `YangMillsCore.lean`):

- Lattice + gauge scaffolding (`L0_Lattice`), the lattice Gibbs measure (`L1`),
  SU(N) compactness + Haar state construction (`P8_PhysicalGap.SUN_*`).
- The **centre-symmetry programme** on SU(N) Haar:
  - `∫ tr U = 0` for N≥2 (`SchurZeroMean.lean`) — F0.
  - `∫ (tr U)^k = 0` for `N∤k` (`SchurMomentVanishing.lean`) — pure N-ality.
  - `∫ (tr U)^a · conj(tr U)^b = 0` for `N∤(a−b)` (`SchurMixedMomentVanishing.lean`)
    — the **full Z_N grading** at the character level (new; **verified** — `lake build YangMillsCore` green, oracle clean).
  - `∫ (∏ U_{iₛjₛ})·(∏ conj U_{kₜlₜ}) = 0` for `N∤(n−m)` (`SchurEntryNAlitySelection.lean`)
    — the selection rule lifted to the **matrix-coefficient** layer, Peter–Weyl-free;
    the leading constraint on the Weingarten integrand (new; **verified** — `lake build YangMillsCore` green, oracle clean).
  - **The engine** (`CenterVanishing.lean`): `∫ f dHaar = 0` whenever
    `f(ω·I·U) = c·f(U)` with `c ≠ 1` (no integrability hypothesis). All four rules
    above are two-line corollaries. **Reach for this on any new centre-symmetric
    integrand** — including open Wilson lines (next; see below) — instead of
    reproving the averaging argument (new; **verified** — `lake build YangMillsCore` green, oracle clean).
  - `∫ tr(U^p) = 0` for `N∤p` (`SchurPowerSumVanishing.lean`) — the Newton
    **power sums** (trace of the matrix power), generators of the character ring
    and building blocks of the F5 character expansion. Engine corollary,
    eigenvalue `ω^p` (new; **verified** — `lake build YangMillsCore` green, oracle clean).
  - **The general engine** (`LeftInvariantVanishing.lean`): the same principle for
    *any* left-invariant `μ` on *any* group — `∫ f dμ = 0` if `f(g·x)=c·f(x)`,
    `c≠1`. Typeclasses verified against Mathlib's `integral_mul_left_eq_self`.
    The SU(N) engine is a one-line specialisation; this is the form that reaches
    U(1) and the lattice product measure (new; **verified** — `lake build YangMillsCore` green, oracle clean).
  - `∫ tr(U^p)·conj(tr(U^q)) = 0` for `N∤(p−q)` (`SchurMixedPowerSumVanishing.lean`)
    — the **bigraded power-sum (covariance) rule**: the vanishing part of the
    Diaconis–Shahshahani power-trace covariance, i.e. the second-moment data the
    F5–F6 connected correlator is built from. Engine corollary, eigenvalue
    `ω^p ω̄^q` (new; **verified** — `lake build YangMillsCore` green, oracle clean).
  - **U(1) character orthogonality** `∫ fourier n dHaar = δ_{n,0}`
    (`U1FourierOrthogonality.lean`) — on the *correct* U(1) (`AddCircle`). The
    **first non-vacuous exact value** (a genuine `= 1` at `n=0`). Closes F0–F1 for
    U(1), Peter–Weyl-free. Also `SUOneDegenerate.lean` certifies SU(1) is trivial,
    explaining the `N_c ≥ 2` hypotheses and the U(1)-as-SU(1) degeneracy
    (new; **verified** — `lake build YangMillsCore` green, oracle clean).
- `∫ ‖tr U‖² ≤ N` (`SchurL25.lean`) — L2.5 (loose; see §3.1 for the sharp form).
- The `L^p → L·log·L` envelope lemma (`MemLpLogIntegrability.lean`).

What is **vacuous and to be ignored**: `ClayYangMillsTheorem := ∃ m>0`,
`ClayYangMillsStrong`, and the entire LSI / Bakry–Émery / Balaban-RG pipeline
that routes only to them (it carries one false-direction `sorry` and one live
axiom; `CLEANUP_PLAN.md` deletes it).

**External fact you should re-verify, not assume (checked 2026-05):** Mathlib has
finite-group character orthogonality (`RepresentationTheory.Character.char_orthonormal`)
and Haar-measure *existence* on locally compact groups
(`MeasureTheory.Measure.Haar.Basic`), but **Peter–Weyl for compact groups is not
formalized**. That gap (node F3 below) is the single highest-leverage missing
Mathlib theorem on the critical path. Confirm against current Mathlib before
planning around it.

---

## 1. The real target, precisely

The non-vacuous goal lives in `L8_Terminal/ClayPhysical.lean` (Stage-2 cleanup
extracts it into a sprawl-free `YangMills/Target/`):

```lean
def IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat : Prop :=
  ∃ C ≥ 0, ∀ N p q,
    |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * Real.exp (-m_lat N * distP N p q)

def ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP : Prop :=
  ∃ m_lat, IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat
         ∧ HasContinuumMassGap m_lat
```

This is bounding the **Wilson connected correlator** of the *given* measure, so a
constant profile no longer closes it. Two leaks must be sealed in the **type**,
not in prose (`FOUNDATIONS.md §3`):

- **Leak A (degenerate observable).** An upper bound on `|corr|` is free when the
  correlator is `≡ 0` (constant `F`, point-mass `μ`, or `β` killing the connected
  part). Encode non-degeneracy as a hypothesis class:

  ```lean
  -- TARGET SIGNATURE (does not yet exist): non-degeneracy carried in the type.
  structure IsNondegenerateYM
      (μ : …) (plaquetteEnergy : …) (β : ℝ) (F : WilsonObservable) : Prop where
    measure_is_wilson_gibbs : μ = wilsonGibbs plaquetteEnergy β            -- the real μ
    observable_nonconstant  : ¬ (∃ c, ∀ U, F U = c)                        -- F not constant
    connected_part_nonzero  : ∃ p q, wilsonConnectedCorr μ plaquetteEnergy β F p q ≠ 0
  ```

  The honest theorem is `IsNondegenerateYM … → ClayYangMillsPhysicalStrong …`,
  with the witness measure forced to be the genuine Wilson–Gibbs measure.

- **Leak B (continuum by fiat).** `HasContinuumMassGap` currently divides the
  lattice mass by the *same* hand-chosen spacing the profile was built from — a
  coordinate artifact. A real statement must tie spacing to the coupling along
  the renormalization-group trajectory; see §4.

> **Boundary, restated for honesty (`FOUNDATIONS.md §7`):** even
> `ClayYangMillsPhysicalStrong` with both leaks sealed is a **lattice** mass-gap
> theorem. The Clay prize additionally requires *constructing* the continuum 4D
> SU(N) theory (Osterwalder–Schrader reconstruction, reflection positivity,
> restoration of rotation invariance) and proving its spectral gap. Keep that
> boundary visible in every claim.

---

## 2. The formal dependency DAG (fill-in-the-blanks skeleton)

Each node is a precise Lean statement. `[DONE]` nodes exist and are sound.
`[STUB]` nodes are the work; the signature is the contract. Arrows = "needs".
Types are written against the existing `sunHaarProb N_c` /
`Matrix.specialUnitaryGroup (Fin N_c) ℂ` API so they should typecheck with at
most cosmetic edits.

```
F0  [DONE]  ∫ tr U = 0                         SchurZeroMean
F0' [DONE]  ∫ (tr U)^k = 0,  N∤k               SchurMomentVanishing
F0''[DONE]  ∫ (tr U)^a conj^b = 0, N∤(a−b)     SchurMixedMomentVanishing   (new)
L25 [DONE]  ∫ ‖tr U‖² ≤ N                       SchurL25
 │
 ├─► F1  [DONE]  ∫ ‖tr U‖² = 1  (sharp L25)               ◄ SchurNormOne
 │
 ├─► F2  [PARTIAL] matrix-coefficient L² API on Haar       ◄ Mathlib-grade
 │        │  ├ generic continuous-unitary matrix API DONE:
 │        │  │  ContinuousUnitaryRep (coefficients/characters in C(G) and L²;
 │        │  │  algebraic Representation bridge; scalar Schur intertwiners)
 │        │  ├ fundamental SU(N) case DONE: SchurFundamentalOrthogonality
 │        │  │  (continuous/L² coefficients, exact δᵢₖδⱼₗ/N inner products,
 │        │  │   and the normalized orthonormal family)
 │        │  └ selection-rule fragment DONE: SchurEntryNAlitySelection (∫∏U_{ij}∏conj=0, N∤(n−m))
 │        │
 │        ├─► F3 [STUB] Peter–Weyl for compact Lie groups  ◄ THE bottleneck
 │        │        └─► F4 [DONE] generic Schur orthogonality
 │        │             (inequivalent coefficients vanish; same-representation
 │        │              coefficients have exact δᵢₖδⱼₗ/dim normalization)
 │        │
 │        └─► F4 ───► F5 [STUB] character expansion of exp(−β Re tr U)
 │                         └─► F6 [STUB] Kotecký–Preiss cluster expansion
 │                                  └─► F7 [STUB] ConnectedCorrDecay for the real μ
 │                                           └─► F8 [STUB] seal Leak A
 │                                                    └─► F9 [STUB] seal Leak B
 └─► (Weingarten calculus — §3.2 — is an alternative, F3-free route to F5/F6 moments)
```

### F1 — sharp second moment (do this first; it is cheap and it pays)

```lean
-- The fundamental character has unit L²-norm: ∫ |tr U|² = 1, not merely ≤ N.
-- For SU(2)/U(1) provable now via the explicit Weyl integration formula;
-- in general it is the ρ = fundamental case of F4.
-- Proved in SchurNormOne.lean:
-- theorem sunHaarProb_trace_normSq_integral_eq_one (N_c : ℕ) [NeZero N_c] :
--     ∫ U : ↥(Matrix.specialUnitaryGroup (Fin N_c) ℂ),
--       ‖U.val.trace‖ ^ 2 ∂(sunHaarProb N_c) = 1
```

Why it matters: `L25` (`≤ N`) is loose by a factor of `N`. The sharp value `= 1`
is the first quantitative Schur-orthogonality fact and the base case of F4. It
also exposes whether the existing Haar normalisation (`sunHaarProb` a probability
measure) is wired correctly end-to-end.

### F2 — matrix coefficients as an L² object

```lean
-- For an f.d. unitary rep ρ of SU(N_c), its matrix coefficients ρ_{ij}(U) are in
-- L²(Haar); package the map and its continuity/measurability.
def matrixCoeff (ρ : Representation ℂ G V) (i j : ι) : G → ℂ := fun g => (ρ g) i j
-- Fundamental SU(N) specialization DONE in SchurFundamentalOrthogonality.lean:
-- `fundamentalMatrixCoeff`, `fundamentalMatrixCoeffL2`, and
-- `inner_fundamentalMatrixCoeffL2`, capped by
-- `orthonormal_normalizedFundamentalMatrixCoeffL2`.
-- Generic matrix-realized continuous unitary representation API DONE in
-- ContinuousUnitaryRep.lean, including a bridge to Mathlib's algebraic
-- `Representation`, irreducibility, and intertwiner API. Algebraic Schur is
-- consumable: irreducible intertwiners are zero/bijective and self-intertwiners
-- are scalar. Generic Haar averaging and orthogonality between inequivalent
-- irreducibles are DONE in GenericSchurOrthogonality.lean, as is the exact
-- same-representation 1/dim normalization. STUB: Peter-Weyl completeness.
```

### F3 — Peter–Weyl (the bottleneck; likely a standalone Mathlib contribution)

```lean
-- Density of the span of matrix coefficients of irreducibles in C(G) (sup norm),
-- hence in L²(G,haar); equivalently an orthogonal Hilbert-space decomposition
-- L²(G) ≅ ⊕_{ρ irred} (V_ρ ⊗ V_ρ*).
theorem peter_weyl_dense (G : Type*) [compact Lie group …] :
    Dense (Submodule.span ℂ { matrixCoeff ρ i j | ρ irreducible, i j }) (C(G,ℂ)) := by
  sorry
```

This is decades-old mathematics but **not in Mathlib**. It is the single change
that unlocks F4→F7 in full generality. If you can land it as a Mathlib PR, you
help far more than this repo. If not, route around it via U(1)/SU(2) (§5) and the
Weingarten calculus (§3.2), both of which avoid generic Peter–Weyl.

### F4 — Schur orthogonality

**DONE for the matrix-realized irreducible API:**
`GenericSchurOrthogonality.lean` constructs the Haar-averaged intertwiner,
proves that coefficients of inequivalent irreducibles are orthogonal, and uses
probability-Haar trace normalization to identify the self-average as
`(tr A / dim ρ) I`. Hence matrix coefficients satisfy the exact
`δᵢₖ δⱼₗ / dim ρ` formula. This does not prove Peter-Weyl completeness or
classify the irreducible representations of `SU(N)`.

```lean
theorem schur_orthogonality
    (ρ σ : irreducible reps) (i j k l) :
    ∫ U, (matrixCoeff ρ i j U) * conj (matrixCoeff σ k l U) ∂haar
      = if ρ ≅ σ then (if i = k ∧ j = l then (1 / (finrank ℂ V_ρ : ℂ)) else 0) else 0 := by
  sorry
```

Note F0'' (`SchurMixedMomentVanishing`) is exactly the centre-graded *diagonal*
shadow of this; it constrains which `(a,b)` can be nonzero before any rep theory.

### F5–F7 — from characters to exponential clustering

```lean
-- F5: strong-coupling character (Fourier–Weyl) expansion of the Boltzmann weight.
theorem boltzmann_character_expansion (N_c) (β : ℝ) (U) :
    Real.exp (-β * (U.val.trace).re)
      = ∑' ρ, (charCoeff N_c β ρ) * (character ρ U) := by
  sorry
-- F6: Kotecký–Preiss / Brydges–Kennedy polymer expansion convergence at small β,
--     yielding |connected correlator| ≤ C · r(β)^{dist},  r(β) → 0 as β → 0.
theorem kp_cluster_decay (small β) : … ≤ C * (r β) ^ (dist p q) := by sorry
-- F7: assemble into ConnectedCorrDecay for the genuine Wilson–Gibbs measure.
theorem connectedCorrDecay_of_smallBeta (small β) (F nondegenerate) :
    ConnectedCorrDecay (wilsonGibbs …) … β F distP := by sorry
```

### F8/F9 — seal the leaks (definition + analysis work)

F8 = supply a concrete non-degenerate Wilson observable + the real measure into
`IsNondegenerateYM` (§1). F9 = make `HasContinuumMassGap` honest (§4).

---

## 3. New mathematical assets to mine (beyond what is formalized)

### 3.1 The exact second moment, and why `≤ N` is wasteful

For SU(N) with N≥2 the fundamental representation is irreducible, so by Schur its
character `χ(U) = tr U` has `‖χ‖_{L²(haar)} = 1`. Hence

  **`∫_{SU(N)} |tr U|² dHaar = 1`  (exactly).**

Sanity check on SU(2): eigenvalues `e^{±iθ}`, Weyl measure `(2/π) sin²θ dθ` on
`[0,π]`, `tr U = 2cos θ`. Then
`∫ (2cosθ)² (2/π) sin²θ dθ = (8/π)∫₀^π cos²θ sin²θ dθ = (8/π)(π/8) = 1`. ✓

The current `SchurL25` bound `≤ N` is therefore loose by a factor of N. Proving
`= 1` (F1) is the cheapest genuinely new quantitative result and the entry point
to F4.

### 3.2 The full moment / Weingarten structure (an F3-free route)

The polynomial integrals you actually need for the cluster expansion are computed
by the **Weingarten calculus**, which does not require generic Peter–Weyl — only
the symmetric-group combinatorics already largely present in Mathlib:

- **Diaconis–Shahshahani (1994):** for U(N), `∫ |tr U|^{2k} dHaar = k!` for all
  `k ≤ N` (and the `tr U^j` are asymptotically independent complex Gaussians).
- **Collins–Śniady Weingarten formula:**
  `∫ U_{i₁j₁}…U_{iₖjₖ} \bar U_{i'₁j'₁}…\bar U_{i'ₖj'ₖ} dHaar
     = Σ_{σ,τ∈Sₖ} Wg(στ⁻¹,N) ∏ δ ∏ δ`,
  with the Weingarten function `Wg` an explicit class function on `Sₖ`.
- **SU(N) vs U(N):** the two agree until the determinant constraint bites at
  `k ≥ N`; the *difference* is precisely the N-ality corrections that
  `SchurMixedMomentVanishing` detects (the `N∣(a−b)` resonances). Formalizing
  `Wg` for SU(N) gives every moment you need for F5/F6 in closed form.

**Recommendation:** a `Weingarten.lean` proving the U(N) formula for small `k`
(or all `k` via the Schur–Weyl/Jucys–Murphy route) is a high-value, F3-free asset
that turns F5/F6 from "expand and estimate" into "evaluate a finite sum."

### 3.3 The centre grading as the skeleton of confinement

`SchurMixedMomentVanishing` says only N-ality-zero observables survive Haar
averaging. This is the algebraic core of the **area law**: at strong coupling the
leading nonzero contribution to `⟨W(C)⟩` is the minimal tiling of `C` by
plaquettes (each plaquette carries a fundamental, and only centre-blind closed
surfaces contribute), giving `⟨W(C)⟩ ∼ exp(−σ·Area)`. Making this rigorous *is*
F5–F7 specialised to Wilson loops; the selection rule is the part that is already
done.

**Immediate engine application (closed 2026-06-27).** The open Wilson-line
centre selection rule now exists in the concrete SU(N) lattice layers:
`wilsonLineSU_centerAct_val` proves the pointwise matrix eigenvalue identity,
and `integral_wilsonLineSU_entry_eq_zero` proves that every Wilson-line matrix
coefficient has zero expectation for a positively oriented edge list whose
length has non-trivial `Z_n` charge under product Haar.  The interacting Gibbs
lift `integral_wilsonLineSU_entry_gibbs_eq_zero` gives the same coefficient
vanishing at any coupling and plaquette energy, using exact center invariance of
the Wilson action.  The mixed charged-correlator endpoint
`integral_wilsonLineSU_entry_mul_wilsonLoopSU_listProd_gibbs_eq_zero` adds an
arbitrary finite product of Wilson loops and vanishes whenever the combined
open-line plus loop-product charge is non-trivial; the connected companion
`connected_wilsonLineSU_entry_mul_wilsonLoopSU_listProd_gibbs_eq_zero` gives
the same vanishing for the centered mixed observable.  The conjugate
loop-product variants
`integral_wilsonLineSU_entry_mul_star_wilsonLoopSU_listProd_gibbs_eq_zero` and
`connected_wilsonLineSU_entry_mul_star_wilsonLoopSU_listProd_gibbs_eq_zero`
cover the corresponding `W_open · star(∏ W_loop)` observables when the two
center charges differ.  These theorems are entrywise because the current
measure stack integrates into normed scalar targets; they are the intended
representation-valued selection rules without adding a whole-matrix Bochner
target.

**The precise remaining bridge.** The lattice product measure already exists:
`gaugeMeasureFrom μ := Measure.map gaugeConfigEquiv (Measure.pi (fun _:PosEdge => μ))`
in `L1_GibbsMeasure.GibbsMeasure`. Two things are missing, both bounded:

1. *(group + invariance)* register a group structure on the configuration space
   and the instance `IsMulLeftInvariant (gaugeMeasureFrom μ)` under the diagonal
   centre action `A ↦ (e ↦ ω·A e)`. (`Measure.pi` of left-invariant measures is
   left-invariant under the product group; transport along `gaugeConfigEquiv`.)
   Alternatively, prove the **single-coordinate marginal** identity
   `(gaugeMeasureFrom μ).map (fun A => A e₀) = μ` and reduce to the SU(N) results
   directly — likely the lower-friction route.
2. *(eigenvalue identity)* `W((ω·)·A) = ω^{L} · W(A)` for the open line of length
   `L`, then `c = ω^L ≠ 1` when `N ∤ L`.

Historical target signature:

```lean
theorem open_wilson_line_expectation_zero
    (N d Nv : ℕ) [NeZero N] [NeZero d] [NeZero Nv]
    (path : OpenPath …) (hL : ¬ N ∣ path.length) :
    ∫ A, wilsonLine path A ∂(gaugeMeasureFrom (sunHaarProb N)) = 0 := by
  sorry  -- feed the eigenvalue identity (2) + invariance (1) to the general engine
```

This was the most physically meaningful corollary reachable from the centre
engine at the time; the concrete entrywise Wilson-line version is now
machine-checked.

**UPDATE 2026-05-30 — this bridge is now DONE** (`ClayCore/GaugeMarginal.lean`,
`GaugeEdgeExpectation.lean`, all oracle-clean, wired into `YangMillsCore`). Route 1's
**marginal** sub-option (the "lower-friction route" flagged above) was the one taken:

- `gaugeMeasureFrom_map_eval` — the single-coordinate marginal
  `(gaugeMeasureFrom μ).map (configToPos · e) = μ`, exactly as proposed in item 1.
- `integral_single_edge` / `integral_single_edge_eq_zero` — a one-edge observable reduces
  to a group integral, and a zero group mean forces a zero gauge expectation.
- `gauge_single_edge_trace_eq_zero` — the SU(N) instance `∫ tr(A e) dμ_gauge = 0` (N ≥ 2).
- `integral_prod_edges` — the edge-product Fubini factorization `∫ ∏ₑ fₑ(A e) = ∏ₑ ∫ fₑ`.
- `integral_prod_edges_eq_zero` — the **open Wilson line vanishing**
  (`open_wilson_line_expectation_zero` above) for any edge-product observable carrying a
  zero-mean factor — proved without the eigenvalue/invariance machinery of route 2, using
  the marginal + Fubini instead.

What remains (`LG6`–`LG8`). **Caveat discovered 2026-05-30 (do not repeat my near-miss):**
the Wilson *loop* observable is `tr(U(e₀)·U(e₁)·U(e₂)·U(e₃))` — the trace of a **matrix
product**, which is *not* a scalar product `∏ₑ fₑ(A e)` over edges, so `integral_prod_edges`
does **not** apply to it, and a closed loop does **not** vanish (under `U_e ↦ ω·U_e` it
picks up `ω^{loop length}`; for a closed plaquette `ω⁴`, and the loop is the *leading*
nonzero contributor — that is the whole point of the area law). The Fubini corollaries
`LG4/LG5` correctly cover only **scalar** edge-product observables (e.g. open lines whose
trace genuinely factorizes, or characters), not matrix-product loop traces.

- **LG6** `[PARTIAL]` define `wilsonLine`/`wilsonLoop` honestly: the open line that *does*
  factorize as a scalar edge product → close via `LG5`; the closed loop trace needs the
  **centre eigenvalue argument** (route 2 of §3.3): establish `IsMulLeftInvariant` of
  `gaugeMeasureFrom` under the diagonal centre action, then `tr(ω·loop) = ω^L·tr(loop)`
  gives vanishing only when `N ∤ L` (so a single plaquette, `L = 4`, does **not** vanish
  unless `N ∣ 4`).
  - **Algebraic core DONE** (`ClayCore/WilsonLoopCenter.lean` + `WilsonLine.lean`, oracle
    `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`):
    - `plaquetteHolonomy_center_smul` — `plaquetteHolonomy (z·A) p = z⁴·plaquetteHolonomy A p`
      (the `L=4` plaquette case, via the monoid lemma `center_smul_prod_four`).
    - `wilsonLine` (ordered edge-list product) + `wilsonLine_center_smul` — the
      arbitrary-length scaling `wilsonLine (z·A) es = z^(es.length) · wilsonLine A es`
      (via `center_listProd_scaling`).
    - `wilsonLoop` (trace of the closed line) + `trace_scalarPow_mul`
      (`tr((ω·1)^L·M) = ω^L·tr M`), assembled into
      **`wilsonLoop_scalarCenter_smul`**: `wilsonLoop (z·A) es = ω^(es.length)·wilsonLoop A es`
      for a scalar centre `z = ω·1`. This is the *complete* algebraic Wilson-loop centre
      eigenvalue — the full `route 2` eigenvalue identity, only the measure step remains.
  - **Measure-theoretic plumbing now DONE for product Haar centre action**
    (`L1_GibbsMeasure/CenterInvariance.lean`, `SUNSelectionRule.lean`):
    `integral_centerAct`, `wilsonLineSU_centerAct_val`,
    `integral_wilsonLineSU_entry_eq_zero`, and
    `integral_wilsonLoopSU_eq_zero` give the concrete free product-Haar
    Wilson-line/loop centre selection rules.  The interacting open-line
    coefficient theorem `integral_wilsonLineSU_entry_gibbs_eq_zero`, the mixed
    open-line/loop-product theorem, plus the loop-product and connected
    selection rules, are handled in `GibbsSelectionRule.lean`.
- **LG7** `[OPEN]` strong-coupling character/heat-kernel expansion of `exp(−β·S)`; the
  area-law leading term. Needs the SU(N) class-function expansion (Peter–Weyl, F3).
- **LG8** `[BLOCKED]` area law `⟨W(C)⟩ ≤ e^{−σ·Area(C)}` at small β; blocked on LG7 + the
  KP cluster expansion (Targets A/B).

Still lattice / finite-volume — **~0% toward Clay**.

---

## 4. Leak B / continuum limit — the precise open statement

`HasContinuumMassGap` must stop being a rescaling identity. The honest content:

- The bare coupling and inverse temperature are linked by `β = 2N/g²`.
- **Asymptotic freedom** fixes the lattice spacing `a` as a function of `g`
  through the RG β-function: `a(g) ∝ Λ⁻¹ exp(−1/(2b₀ g²)) · g^{−b₁/b₀²}(1+…)`,
  `b₀ = 11N/(48π²) > 0` for pure SU(N). So the continuum limit is `g→0`
  (`β→∞`, `a→0`), **not** a free choice of spacing.
- A genuine `HasContinuumMassGap m_lat` must assert: along the trajectory
  `β ↦ a(β)`, the physical mass `m_phys(β) = m_lat(N,β)/a(β)` has a positive
  limit (or liminf) as `β→∞`. Formal target:

```lean
def HasContinuumMassGapHonest (m_lat : ℕ → ℝ → ℝ) (a : ℝ → ℝ) : Prop :=
  (∀ β, 0 < a β) ∧ Filter.Tendsto a Filter.atTop (𝓝 0) ∧
  0 < Filter.liminf (fun β => m_lat N β / a β) Filter.atTop ∧
  -- a is the asymptotic-freedom spacing, not a free parameter:
  AsymptoticFreedomSpacing a
```

This is **open even on paper** for non-abelian 4D: controlling the gap *uniformly*
through `β→∞` is the heart of the unsolved problem. Tadeusz Bałaban's program
(1980s, ~10 papers) is the deepest rigorous attempt at the weak-coupling
continuum control; it has not been completed to a mass-gap theorem. Do not expect
to discharge F9 by formalization alone — it likely needs new mathematics. The
realistic milestone is **strong-coupling (fixed β, fixed a) exponential
clustering** (F5–F7), which *is* a theorem (next section).

---

## 5. Triage — what to attack, in order

**Tier 0 — mechanical, do immediately (hours–days):**
1. `lake build YangMillsCore`; fix any breakage in `SchurMomentVanishing` /
   `SchurMixedMomentVanishing` (the integer-cast steps are the only risk).
   `#print axioms` the headline lemmas.
2. Prove F1 (`∫|tr U|² = 1`) for SU(2) via the Weyl integration formula.
3. Run `docs/legacy/cleanup_and_push.ps1` once the core is green.

**Tier 1 — bounded formalization of known mathematics (weeks–months each):**
4. **U(1) end-to-end.** Peter–Weyl for U(1) *is* Fourier series on the circle,
   already in Mathlib (`Analysis.Fourier.AddCircle`). Close F0–F7 for U(1)
   lattice gauge theory and produce the **first honestly non-vacuous
   `ClayYangMillsPhysicalStrong`** in the project (leaks sealed, lattice only).
   This bypasses F3 entirely and is the highest expected-value single target.

   **Use the correct substrate.** Do *not* reuse the repo's `AbelianU1Witness`,
   which models U(1) as `specialUnitaryGroup (Fin 1) ℂ` — that group is **trivial**
   (`SUOneDegenerate.lean` proves `SU(1) = {1}`, so its Haar is a point mass and
   the witness is vacuous, Leak A in extremis). Real U(1) is the circle
   `unitaryGroup (Fin 1) ℂ ≅ Circle ≅ AddCircle 1`. Mathlib gives it for free:
   `AddCircle.haarAddCircle` (a probability Haar measure), the characters
   `fourier n`, and their orthonormality `orthonormal_fourier`. On this substrate
   the abelian analogue of the centre rules is the *complete* Fourier
   orthogonality `∫ zⁿ dHaar = δ_{n,0}` — the vanishing for `n ≠ 0` is the additive
   form of `LeftInvariantVanishing` (`integral_add_left_eq_self`), and the value
   `1` at `n = 0` is just total mass. That `= 1` is the **first honestly
   non-vacuous exact value** in reach, and U(1) is special precisely because it is
   its own centre (no centre-blind non-trivial irreps, unlike SU(N) for N ≥ 2).
   **DONE** (`U1FourierOrthogonality.lean`): both `∫ fourier n = δ_{n,0}` and the
   full orthonormality `∫ fourier m · conj(fourier n) = δ_{m,n}` (F0–F1 + F4 for
   U(1), Peter–Weyl-free).

   **The remaining U(1) blocker is the correlator, and it is a Mathlib gap.** The
   `d=2` U(1) connected two-plaquette correlator decays as `(I_1(β)/I_0(β))^dist`
   — but **modified Bessel functions `I_n` are not in Mathlib** (verified
   2026-05-29: no Bessel-function theory, only incidental mentions). So F5–F7 for
   U(1) cannot be done via the explicit Bessel route yet. Two honest paths:
   (a) build the modified-Bessel theory in Mathlib (a sizeable, self-contained
   contribution, useful well beyond this repo); or (b) work *abstractly*: set
   `r := ⟨fourier 1⟩_{Gibbs}`, prove `|r| < 1` from the strict triangle inequality
   for integrals (the genuine analytic origin of the gap — the Gibbs weight has
   full support, so `z` is not a.e. constant, so `|∫ z| < ∫|z| = 1`), and derive
   geometric clustering from the `d=2` plaquette factorisation. Path (b) still
   needs the lattice product-measure plumbing (the `gaugeMeasureFrom` marginal /
   invariance bridge of §3.3).
5. **SU(2).** Explicit `S³`/`θ` parameterization, `χ_n(θ)=sin((n+1)θ)/sin θ`,
   `exp(−β cos θ)` Bessel expansion. Closes F1, F4, F5 concretely; skips generic
   Peter–Weyl.
6. **Weingarten.lean** (§3.2) — F3-free moments.

**Tier 2 — large but known-true (the real lattice prize):**
7. **Strong-coupling cluster expansion → lattice mass gap** (F5–F7 for SU(N),
   small β). This is **Osterwalder–Seiler (1978)** + standard polymer-expansion
   technology (**Kotecký–Preiss 1986**, **Brydges–Kennedy**). It is a
   *formalization* task — the theorem is true and the proof is in the books —
   but a large one. Landing it gives an unconditional, non-vacuous SU(N)
   *lattice* mass gap at strong coupling.

**Tier 3 — genuinely open (Clay-level; expect to need new mathematics):**
8. Leak B / continuum limit through asymptotic freedom (F9; §4). Bałaban program.
9. Full Clay: continuum 4D construction + OS reconstruction + spectral gap.

The honest message: Tiers 0–2 are *reachable* and would make this a genuinely
valuable, non-vacuous formalization. Tier 3 is the actual Millennium Problem and
should be labelled as such in every public claim.

---

## 6. Invariants you must preserve

- Report progress **only** against `ClayYangMillsPhysicalStrong` + Leak A + Leak B.
  Treat `ClayYangMillsTheorem` / `ClayYangMillsStrong` as deprecated/vacuous.
- **Never launder a missing theorem into an axiom by dropping its hypotheses**
  (the "wrong-axiom trap"; see `docs/phase1-llogl-obstruction.md` for the L·log·L
  instance). If a step needs a Sobolev/Dirichlet premise, carry the premise.
- No `sorry` and no project axioms in core declarations; keep the oracle
  `[propext, Classical.choice, Quot.sound]`. `#print axioms` before reporting any
  node closed.
- Never reintroduce a dependency on the discarded LSI/Balaban sprawl.
- Keep `lattice mass gap ≠ Clay prize` visible in every public statement.

---

## 7. Key references (for the prover to pull)

- K. Osterwalder, E. Seiler, *Gauge field theories on a lattice*, Ann. Phys. 110
  (1978) — strong-coupling clustering / mass gap (Tier 2 target).
- E. Seiler, *Gauge Theories as a Problem of Constructive QFT and Statistical
  Mechanics*, LNP 159 (1982).
- R. Kotecký, D. Preiss, *Cluster expansion for abstract polymer models*, CMP 103
  (1986); D. Brydges, T. Kennedy, cluster-expansion convergence.
- P. Diaconis, M. Shahshahani, *On the eigenvalues of random matrices*, J. Appl.
  Prob. 31A (1994) — `∫|tr U|^{2k}=k!`.
- B. Collins, P. Śniady, *Integration with respect to the Haar measure on U(n)…*,
  CMP 264 (2006) — Weingarten calculus.
- T. Bałaban, series on renormalization of lattice gauge theories, CMP (1984–89)
  — weak-coupling continuum control (Tier 3).
- A. Jaffe, E. Witten, *Quantum Yang–Mills Theory*, Clay problem statement — the
  actual prize and its precise requirements.

---

Lluis Eriksson — The Eriksson Programme. This file is meant to be edited: when you
close a `[STUB]`, move it to `[DONE]`, record the file, and tighten the triage.
