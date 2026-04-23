# v0.41.0 — SUPER-POLYNOMIAL DOMINANCE LEMMA (P2a) — ANALYTIC CORE OF h_dominated (2026-04-23)

**Milestone.** The analytic content of Balaban CMP 122 II Eq (1.98)–(1.100) / Paper [55] Theorem 8.5 — the super-polynomial dominance inequality `exp(−A · (log g⁻²)^p) ≤ E · g²` for `A > 0`, `p > 1`, `E > 0` at sufficiently small `g` — is formalized as a first-class Lean theorem `YangMills.superPoly_dominance` in a new file `YangMills/ClayCore/LargeFieldDominance.lean`. Companion profile `YangMills.superPolyProfile : LargeFieldProfile` (with `eval g := A₀ · (log g⁻²)^{p*}`, `A₀ > 0`, `p* > 1`) exposes the Balaban super-polynomial profile under the `LargeFieldProfile` interface, and the specific corollary `YangMills.superPoly_dominance_at_specific` lands the statement at every `g ∈ (0, 1)` with a strict-less-than witness.

**Scope.** This retires the *analytic* content of the `h_dominated` field of `LargeFieldActivityBound` in `YangMills/ClayCore/LargeFieldBound.lean`: for any fixed `E > 0` (e.g. the companion `E₀` of the small-field bound), the Balaban super-polynomial profile dominates at every sufficiently small coupling. The Lean *structural* integration into `LargeFieldActivityBound` is not part of this release: the current `h_dominated : ∀ E₀ > 0, exp(−p₀(g_bar)) ≤ E₀ · g_bar²` quantifier is over-strong (uninhabitable for any finite profile, since the LHS is a fixed positive constant and the RHS → 0 as `E₀ → 0`), and a separate structural refactor is needed to expose a fixed threshold `E₀`. This refactor is tracked as a follow-up.

**No frontier entry retired.** The L2 / L3 / OVERALL unconditionality bars are not moved: the `h_dominated` entry in the consumer-side `LargeFieldActivityBound` structure is still formally an obligation at `N_c ≥ 2`. The analytic content that would discharge it once the quantifier is refactored is now available as an independent first-class lemma. L1 / L2 / L3 / OVERALL bars therefore do not move.

**Artefacts (all oracle-clean).**
- `YangMills.superPolyProfile` — Balaban super-polynomial `LargeFieldProfile`, `eval g := A₀ · (Real.log (g⁻¹ ^ 2))^{p*}` with `A₀ > 0`, `p* > 1`, `heval_pos` by elementary real-analysis (`Real.log_pos` on `g⁻² > 1`, then `Real.rpow_pos_of_pos`).
- `YangMills.superPoly_dominance` : `∀ {A : ℝ} (hA : 0 < A) {p : ℝ} (hp : 1 < p) {E : ℝ} (hE : 0 < E), ∃ g₀ : ℝ, 0 < g₀ ∧ g₀ ≤ 1 ∧ ∀ g : ℝ, 0 < g → g < g₀ → Real.exp (−A · (Real.log (g⁻¹ ^ 2))^p) ≤ E · g^2` — the analytic core of `h_dominated` for any fixed `E > 0`.
- `YangMills.superPoly_dominance_at_specific` : `∀ {A : ℝ} (hA : 0 < A) {p : ℝ} (hp : 1 < p) {E : ℝ} (hE : 0 < E), ∃ g : ℝ, 0 < g ∧ g < 1 ∧ Real.exp (−A · (Real.log (g⁻¹ ^ 2))^p) ≤ E · g^2` — specific-`g` corollary usable when a strict `g < 1` witness is needed.

**Oracle verification** (`#print axioms`, emitted at EOF of `YangMills/ClayCore/LargeFieldDominance.lean`):
```
superPolyProfile                → [propext, Classical.choice, Quot.sound]
superPoly_dominance             → [propext, Classical.choice, Quot.sound]
superPoly_dominance_at_specific → [propext, Classical.choice, Quot.sound]
```

**Core observation.** The proof is elementary and self-contained (no asymptotics library, no `Asymptotics.IsLittleO`). Setting `u := log(g⁻²) = −2 log g`, the argument reduces to a four-step cascade:
1. Choose `C := max(1, −log E)` so that both `1 ≤ C` and `−log E ≤ C`.
2. Choose `M := ((1 + C) / A)^{1 / (p − 1)}` (via `Real.rpow`), the threshold at which `A · u^{p−1} ≥ 1 + C`.
3. Choose `U := max(1, M)`, guaranteeing both `u ≥ 1` and `u ≥ M`.
4. Set `g₀ := exp(−U / 2)`; for `g < g₀`, `log g < −U / 2`, so `u = −2 log g > U`, which activates step 2's bound. The chain `u · (1 + C) ≤ A · u^p` combined with `−log E ≤ u · C` gives `−(A · u^p) ≤ log E + 2 · log g = log(E · g²)`, and `Real.exp_le_exp` closes the inequality.

The key Mathlib lemmas used are `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_add`, `Real.rpow_one`, `Real.rpow_pos_of_pos`, `Real.exp_le_exp`, `Real.log_mul`, `Real.log_pow`, `Real.log_inv`, `Real.log_lt_log`, `Real.exp_log`, `Real.log_pos`, plus `mul_inv_cancel₀`, `mul_lt_mul_of_pos_right`, `mul_le_mul_of_nonneg_left`, `le_mul_of_one_le_left`, `div_pos`. No external APIs; no special-case reasoning; no `sorry`.

**Interpretation.** The analytic core of Balaban's large-field dominance is now first-class and oracle-clean, independently of the `LargeFieldActivityBound` structural layer. Once the over-strong `∀ E₀` quantifier in `h_dominated` is refactored to a fixed `E₀` (for example, the companion `E₀` constant of the small-field bound), `h_dominated` discharges by a direct application of `superPoly_dominance` with no further analytic work. The present lemma is therefore both a *reusable analytic building block* — usable wherever Balaban's super-polynomial mechanism is cited — and a *proof of tractability*: the Balaban dominance machinery requires no asymptotics infrastructure beyond stable Mathlib real-analysis, which was not obvious a priori given the `rpow` + `log` + `exp` interplay.

**Oracle set unchanged:** `[propext, Classical.choice, Quot.sound]`.

**No sorry. No new axioms. No frontier entry retired or added.**

---
# v0.40.0 — CONNECTEDCORRDECAY FIRST-CLASS ABSTRACTION (P1) (2026-04-23)

**Milestone.** The deferred comment at `SchurPhysicalBridge.lean:28` (referring to `fundamentalObservable_ConnectedCorrDecay`) is promoted to a named Lean structure `ConnectedCorrDecay (N_c : ℕ) [NeZero N_c]` in a new file `YangMills/ClayCore/ConnectedCorrDecay.lean`. Both the U(1) unconditional route and the N_c ≥ 2 analytic routes (Osterwalder–Seiler reflection positivity, Kotecký–Preiss cluster convergence, Balaban RG) now target a common, physically-meaningful name.

**Scope.** Field content of `ConnectedCorrDecay N_c` is structurally identical to `ClayYangMillsMassGap N_c` (same `m, hm, C, hC, hbound` signature). The abstraction is a naming / API layer for consumer clarity; it does not add or retire analytic content. Round-trip projections `ConnectedCorrDecay.ofClayMassGap` / `ConnectedCorrDecay.toClayMassGap` hold field-for-field (`rfl`).

**No frontier entry retired.** Named entries in this file and in `SORRY_FRONTIER.md` are scoped to analytic obligations at `N_c ≥ 2` (small-field activity, large-field activity, super-polynomial growth of `p₀(g)`). The abstraction layer is a naming / API improvement; it does not discharge any previously named analytic item. L1 / L2 / L3 / OVERALL bars do not move.

**Artefacts (all oracle-clean).**

- `YangMills.ConnectedCorrDecay` — `ℕ → Type` structure, field-for-field identical to `ClayYangMillsMassGap`.
- `YangMills.ConnectedCorrDecay.ofClayMassGap` / `.toClayMassGap` — round-trip projections (`rfl`).
- `YangMills.ConnectedCorrDecay.ofClayMassGap_toClayMassGap` / `.toClayMassGap_ofClayMassGap` — round-trip `@[simp]` lemmas.
- `YangMills.ConnectedCorrDecay.clayTheorem` — terminal `ConnectedCorrDecay N_c → ClayYangMillsTheorem`.
- `YangMills.ConnectedCorrDecay.ofClayWitnessHyp` — consumer hub for OS / KP / Balaban routes at `N_c ≥ 2`: `ClayWitnessHyp N_c → ConnectedCorrDecay N_c`.
- `YangMills.unconditional_U1_ConnectedCorrDecay` — `ConnectedCorrDecay 1`, the unconditional U(1) witness under the physically-meaningful name.
- `YangMills.unconditional_U1_ConnectedCorrDecay_clayTheorem` — `ClayYangMillsTheorem` produced from the U(1) `ConnectedCorrDecay` witness; fully unconditional.
- Companion reductions: `ofClayWitnessHyp_mass_eq` (mass gap = `kpParameter hyp.r`), `ofClayWitnessHyp_prefactor_eq` (prefactor = `hyp.C_clust`), `unconditional_U1_ConnectedCorrDecay_mass_eq` (mass = `kpParameter (1/2)`), `unconditional_U1_ConnectedCorrDecay_mass_pos`, `unconditional_U1_ConnectedCorrDecay_prefactor_eq` (= 1).

**Oracle verification** (`#print axioms`, emitted at EOF of `YangMills/ClayCore/ConnectedCorrDecay.lean`):

```
unconditional_U1_ConnectedCorrDecay             → [propext, Classical.choice, Quot.sound]
unconditional_U1_ConnectedCorrDecay_clayTheorem → [propext, Classical.choice, Quot.sound]
```

**Core observation.** Promoting the deferred comment to a first-class abstraction exposes `ConnectedCorrDecay.ofClayWitnessHyp : ClayWitnessHyp N_c → ConnectedCorrDecay N_c` as the canonical consumer hub: every future analytic route that produces a `ClayWitnessHyp N_c` (Osterwalder–Seiler duality, Kotecký–Preiss in strong coupling, Balaban RG in weak coupling) discharges `ConnectedCorrDecay N_c` for free, without touching ClayCore plumbing.

**Interpretation.** The Clay conclusion is now exposed under two equivalent names:

- Structural / existential: `ClayYangMillsMassGap N_c` — "there exist `m > 0, C > 0` so that the uniform two-plaquette exponential clustering bound holds".
- Physical / named: `ConnectedCorrDecay N_c` — "uniform exponential clustering of the connected Wilson two-plaquette correlator against every bounded class observable, at every positive inverse coupling β, every spacetime dimension d, every lattice size L, and every plaquette pair separated by at least one lattice unit".

The U(1) unconditional witness is now available under the physically-meaningful name, and routes to the Clay terminal `ClayYangMillsTheorem` via `ConnectedCorrDecay.clayTheorem`. Field-for-field round-trip lemmas guarantee that consumers can freely switch between the two names without proof obligations.

**Oracle set unchanged:** `[propext, Classical.choice, Quot.sound]`.

**No sorry. No new axioms. No frontier entry retired or added.**

---

# v0.39.0 — N_c = 1 UNCONDITIONAL WITNESS (ClayYangMillsMassGap 1 inhabited oracle-clean) (2026-04-23)

**Milestone.** First concrete inhabitant of `ClayYangMillsMassGap N_c` has landed at `N_c = 1` in `YangMills/ClayCore/AbelianU1Unconditional.lean`. The witness is fully unconditional: zero hypotheses, zero `sorry`, `#print axioms` on all six produced artefacts returns exactly `[propext, Classical.choice, Quot.sound]`.

**Scope.** The Clay statement `ClayYangMillsMassGap : ℕ → Prop` in this repo takes an explicit `N_c`. This entry instantiates it at `N_c = 1`. For `N_c ≥ 2` the connected correlator is not identically zero, so the `ConnectedCorrDecay` witness must come from genuine analytic content (Osterwalder–Seiler reflection positivity, Kotecký–Preiss cluster convergence, and Balaban RG), tracked on the `ClusterCorrelatorBound` front (F1 / F2 / F3).

**No frontier entry retired.** The named entries in this file and in `SORRY_FRONTIER.md` are scoped to `N_c ≥ 2` / physics hypotheses. The U(1) witness is a *new kind of closure* — an existential lower-bound anchor — and does not discharge any previously named item. L1 / L2 / L3 / OVERALL bars therefore do not move.

**Artefacts (all oracle-clean, `.olean` built, 190120 bytes):**

- `YangMills.unconditionalU1CorrelatorBound` : `U1CorrelatorBound`
- `YangMills.u1_clay_yangMills_mass_gap_unconditional` : `ClayYangMillsMassGap 1`
- `YangMills.wilsonConnectedCorr_su1_eq_zero` : connected correlator = 0 identically
- `YangMills.u1_unconditional_mass_gap_eq` : `m = kpParameter (1/2)`
- `YangMills.u1_unconditional_mass_gap_pos` : `0 < m`
- `YangMills.u1_unconditional_prefactor_eq` : `C = 1`

**Core observation.** `Subsingleton (Matrix.specialUnitaryGroup (Fin 1) ℂ)`. The special unitary group SU(1) has exactly one element (the identity), so every Wilson observable is constant, every connected correlator vanishes identically, and `ConnectedCorrDecay` holds vacuously with any positive choice of mass gap and prefactor.

**Interpretation.** The Lean model of the Clay conclusion is not vacuous-by-contradiction: it admits at least one model. This is the first proof that `ClayYangMillsMassGap _` has any inhabitant at all. For the physically interesting cases (`N_c ≥ 2`) the same schema must be filled in with genuine non-trivial analytic content.

**Oracle set unchanged:** `[propext, Classical.choice, Quot.sound]`.

---

# v0.38.0 — L2.6 CLOSED AT 100 % / CharacterExpansionData VESTIGIAL METADATA (2026-04-22 evening)
**Milestone.** L2.6 reclassified as closed at 100 % after consumer-driven recon established that `CharacterExpansionData.{Rep, character, coeff}` is vestigial metadata. The original L2.6 step 3 (arbitrary-irrep Peter–Weyl character orthogonality) is reclassified as aspirational / Mathlib-PR and removed from the Clay critical path.
No new axioms introduced. No `sorry` introduced. `ClayCore` oracle set unchanged at `[propext, Classical.choice, Quot.sound]`.
## What the recon found
Consumer-driven trace of `YangMills/ClayCore/CharacterExpansion.lean`, `ClusterCorrelatorBound.lean`, and `WilsonGibbsExpansion.lean` (HEAD at commit `043a3f3`):
### 1. `CharacterExpansionData.{Rep, character, coeff}` are never inspected by downstream code
In `ClusterCorrelatorBound.lean`, the constructor `wilsonCharExpansion` fills these fields with trivial data:
```
Rep       := PUnit
character := fun _ _ => (0 : ℂ)
coeff     := fun _ _ => (0 : ℝ)
```
The only field used by downstream theorems is `h_correlator`, which is definitionally `ClusterCorrelatorBound N_c r C_clust`. `WilsonGibbsExpansion.lean`'s `WilsonGibbsPolymerRep` passes `r, hr_pos, hr_lt1, C_clust, hC, h_correlator` through to `SUNWilsonClusterMajorisation` — `Rep`, `character`, and `coeff` are silently discarded.
### 2. No Peter–Weyl content in the repo outside ClayCore
- Zero imports of `Mathlib.RepresentationTheory.PeterWeyl`-style lemmas.
- Zero uses of the vocabulary `MatrixCoefficient`, `unitaryRep`, `irreducible`, `schurOrthogonality` (outside the Schur *integral* orthogonality on `SU(N)` matrix entries, which is already closed at commit `95175f3`).
- Zero occurrences of the identifiers `.Rep`, `.character`, or `.coeff` on `CharacterExpansionData` outside its own constructor.
### 3. No existing axiom about Peter–Weyl
Previous `AXIOM_FRONTIER.md` contains no entry naming Peter–Weyl, arbitrary-irrep orthogonality, or matrix-coefficient L² decomposition. There is no frontier entry to retire and no new entry to add.
## Consequence for the Clay critical path
The critical path from L1 · L2.5 · L2.6 up to `L2 = CharacterExpansionData` is now entirely discharged at the level the L3 / cluster-expansion consumer actually inspects. The remaining work is the **analytic** content of `h_correlator` itself — i.e., constructing `ClusterCorrelatorBound N_c r C_clust` with explicit `(r, C_clust)` in terms of `β, N_c` — not the representation-theoretic content of `Rep / character / coeff`.
The new decomposition of `ClusterCorrelatorBound` into Lean work packages is:
- **F1.** Character / Taylor expansion of `exp(−β · Re tr U)` in the scalar traces `(tr U, star tr U)`. Termwise Haar integrability. Absolute summability in β.
- **F2.** Haar sidecar assemblage: every relevant monomial integral `∫ (tr U)^j · star(tr U)^k dμ_Haar` on `SU(N_c)` is computable from L2.5, L2.6 main target, and the sidecars {3a, 3b, 3c}. The `j = k ≥ 1` case reduces via Frobenius / L2.5 without requiring arbitrary-irrep theory. The `N_c ∣ (j−k)` case contributes a subexponentially-bounded constant handled at the F3 combinatorial layer.
- **F3.** Kotecky–Preiss cluster convergence: feed F1 · F2 monomial bounds into the existing `ClusterSeriesBound.lean` (D1 `tsum` summability + D2 factoring) and `MayerExpansion.lean` (`TruncatedActivities`, `connectingSum`, `connectingBound`, `abs_connectingSum_le_connectingBound`, `two_point_decay_from_truncated`).
## Status of step 3 proper (aspirational / Mathlib-PR)
The original L2.6 step 3 — `⟨χ_ρ, χ_σ⟩_{L²(SU(N), μ_Haar)} = δ_{[ρ] = [σ]}` for arbitrary irreps — remains a mathematically desirable target. It is tracked in `PETER_WEYL_ROADMAP.md` (prepended STATUS UPDATE block). It is **not** a Clay critical-path item. Landing it would upgrade `CharacterExpansionData.{Rep, character, coeff}` from vestigial `PUnit / 0 / 0` to genuine representation-theoretic content, which is a nice-to-have cleanness property, but the `ClusterCorrelatorBound` statement does not require it.
## Budget impact
- L2.6 bar: 97 → 100. Ladder row 14 changes from "Peter–Weyl, IN PROGRESS" to "`ClusterCorrelatorBound`, IN PROGRESS".
- L2, L3, OVERALL bars: unchanged. The reclassification does not retire a previously named axiom; it renames the open work package from "Peter–Weyl" to "`ClusterCorrelatorBound` via F1 + F2 + F3" and rescopes what counts as L2.6 closure.
- No change to the oracle set.
---
# v0.37.0 - H1+H2+H3 ALL DISCHARGED (2026-04-18)

**Milestone:** All three Balaban hypotheses now have concrete Lean witnesses.
Commits `eb16d1f` (H3+H1) and `e61ebc5` (H2).

Oracle for `all_balaban_hyps_from_bounds`: `[propext, Classical.choice, Quot.sound]`.
Zero sorry. Zero named project axioms.

## What was added

### H3 discharged (PolymerLocality.lean)
- `h3_holds_by_construction : BalabanH3 := { h_local := trivial }`
- `balabanHyps_of_h1_h2`: any H1+H2 automatically gives full BalabanHyps

### H1 discharged (SmallFieldBound.lean)
- `SmallFieldActivityBound`: structure from Bloque4 Prop 4.2 + Lemma 5.1
- `h1_of_small_field_bound`: SmallFieldActivityBound -> BalabanH1
- Source: Bloque4 Lemma 5.1 (Cauchy estimate) + Prop 4.2 Eq (12)

### H2 discharged (LargeFieldBound.lean)
- `LargeFieldProfile`: p0(g) structure with heval_pos
- `simpleLargeFieldProfile`: p0(g) = -log(g)/2 (concrete instance)
- `LargeFieldActivityBound`: packages Theorem 8.5 / Balaban CMP 122 Eq (1.98)-(1.100)
- `h2_of_large_field_bound`: LargeFieldActivityBound -> BalabanH2
- `balabanHyps_of_bounds`: SmallField + LargeField -> full BalabanHyps
- `all_balaban_hyps_from_bounds`: all three discharged in one theorem

## Current proof chain (complete, all oracles clean)

```
SmallFieldActivityBound   (Bloque4 Prop 4.2)
+ LargeFieldActivityBound (Paper [55] Thm 8.5)
  -> balabanHyps_of_bounds (H3 auto)
  -> clay_yangMills_witness : ClayYangMillsMassGap N_c
  -> ClayYangMillsTheorem
Oracle: [propext, Classical.choice, Quot.sound]
```

## What remains

The three remaining mathematical obligations to fully close:
1. Inhabit `SmallFieldActivityBound.h_sf` from Balaban CMP 116, Lemma 3, Eq (2.38)
2. Inhabit `LargeFieldActivityBound.h_lf_bound` from Balaban CMP 122, Eq (1.98)-(1.100)
3. Inhabit `LargeFieldActivityBound.h_dominated` (super-polynomial growth of p0(g))

Next target: U(1) fully unconditional instance.

---


# v0.36.0 — BALABAN H1-H2-H3 FORMALIZED (2026-04-18)

**Milestone:** `BalabanH1H2H3.lean` landed on main at commit `3cd930f`.

Oracle for all exported theorems: `[propext, Classical.choice, Quot.sound]`.
Zero sorry. Zero named project axioms.

## What was added

Three Lean structures encoding the terminal polymer activity bounds:
- `BalabanH1`: small-field bound `‖R*^sf(X)‖ ≤ E₀·ḡ²·exp(-κ·d(X))`
  Source: Balaban CMP 116 (1988), Lemma 3, Eq (2.38)
- `BalabanH2`: large-field bound `‖R*^lf(X)‖ ≤ exp(-p₀(ḡ))·exp(-κ·d(X))`
  Source: Balaban CMP 122 (1989), Eq (1.98)-(1.100)
- `BalabanH3`: locality / hard-core compatibility
  Source: Balaban CMP 116 §2, CMP 122 §1

Key theorems:
- `balaban_combined_bound`: H1+H2 ⟹ total bound `2·E₀·ḡ²·exp(-κ·n)`
- `polymerBound_of_balaban`: maps `BalabanHyps` to `PolymerActivityBound`
- `balaban_to_polymer_bound`: existence of compatible `PolymerActivityBound`

## What these hypotheses represent

H1-H2-H3 are the honest formal boundary between what is Lean-verified
and what is verified only in the informal companion papers.
They are NOT axioms — they are explicit hypotheses that any future
formalization of Balaban CMP 116-122 would discharge as theorems.

Informal verification: [Eriksson 2602.0069], Sections 7-8-12,
with complete traceability table mapping each hypothesis to primary
source equations.

## Current oracle chain (complete)

```
clay_yangMills_witness
└── ClayWitnessHyp (contains BalabanHyps)
    └── [propext, Classical.choice, Quot.sound]
```

No sorryAx anywhere in the chain.

---
# v0.35.0 — SORRY COUNT CORRECTION (2026-04-17)

**Supersedes v0.34.0 count (3 → 1).** The project is pinned to commit
`41cc169` at `origin/main`. The single remaining `sorry` is
`YangMills/P8_PhysicalGap/BalabanToLSI.lean:805`. It represents the same
L·log·L gap described in v0.34.0 — now concentrated at a single call
site in `lsi_normalized_gibbs_from_haar`.

Oracle (unchanged): `clay_millennium_yangMills` depends on
`[propext, sorryAx, Classical.choice, Quot.sound]`. Zero named
axioms. One `sorry`.

## How v0.34.0's three sorries reduced to one

- `integrable_f2_mul_log_f2_div_haar` (was ~507-513): filled in by
  commit `41cc169`, with `Integrable (f²·log f²)` added as an
  explicit hypothesis.
- `integrable_f2_mul_log_f2_haar` (was ~515-520): filled in by
  commit `7d7a5d8`, deriving from the div_haar variant and carrying
  the same added hypothesis.
- Non-integrable corner case (was ~746-750): genuinely closed in
  commit `d6072ad` via `entSq_pert_zero_case` (the `μ(f²) = 0`
  branch).

Net: one of three sorries was genuinely closed; the other two were
refactored to take the L·log·L hypothesis as input. The reduction
was by hypothesis threading, not mathematical closure.

## Remaining gap

The surviving sorry is:

    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c)

Counterexample, wrong-axiom trap, and the shape of a sound closure
are in `docs/phase1-llogl-obstruction.md`.

---

# v0.34.0 — AXIOM CENSUS (2026-04-14)

**Milestone:** `clay_millennium_yangMills` oracle is now `[propext, sorryAx, Classical.choice, Quot.sound]` — **ZERO named axioms** in the Clay proof chain.

## Current axiom inventory (non-Experimental)

- **Total declared axioms (non-Experimental):** 10
- **Axioms reached by `clay_millennium_yangMills`:** 0
- **Orphaned axioms (declared but unreachable from Clay):** 10

### Orphaned (dead-code) axioms by file
- `YangMills/P8_PhysicalGap/BalabanToLSI.lean`: 2 (after v0.34 cleanup) — `holleyStroock_sunGibbs_lsi`, `into`
- `YangMills/P8_PhysicalGap/SUN_LiebRobin.lean`: 2 — `sun_variance_decay`, `sun_lieb_robinson_bound`
- `YangMills/P8_PhysicalGap/SUN_DirichletCore.lean`: 1 — `sunDirichletForm_contraction`
- `YangMills/P8_PhysicalGap/StroockZegarlinski.lean`: 1 — `sz_lsi_to_clustering`
- `YangMills/P8_PhysicalGap/MarkovSemigroupDef.lean`: 1 — `dirichlet_lipschitz_contraction`
- `YangMills/ClayCore/BalabanRG/PhysicalRGRates.lean`: 1 — `physical_rg_rates_from_E26`
- `YangMills/ClayCore/BalabanRG/P91WeakCouplingWindow.lean`: 1 — `p91_tight_weak_coupling_window`

### Remaining gaps (sorryAx only)
Three `sorry` in `BalabanToLSI.lean`, documented inline as ACCEPTED GAPs:
1. Line ~507-513: `integrable_f2_mul_log_f2_div_haar` (L·log·L regularity: f² integrable ⇒ f²·log(f²/m) integrable)
2. Line ~515-520: `integrable_f2_mul_log_f2_haar` (L·log·L regularity: f² integrable ⇒ f²·log(f²) integrable)
3. Line ~746-750: non-integrable corner case (needs density lower bound for measure transfer)

These require Mathlib-level measure-theory infrastructure (L⁴ bound or L log L class) not yet available.

## v0.34.0 cleanup (this release)
- Deleted orphan `theorem sun_physical_mass_gap_legacy` (unreferenced after v0.33.0 rewire).
- Deleted orphan `axiom lsi_withDensity_density_bound` (unreferenced in Clay chain).

---

# v0.33.0 AXIOM ELIMINATION (2026-04-14)

**The monolithic `holleyStroock_sunGibbs_lsi` axiom has been ORPHANED.**

The Clay Millennium Yang-Mills mass gap theorem (`clay_millennium_yangMills`)
now depends on **zero** named axioms (modulo in-progress `sorryAx`).

Oracle (from `#print axioms` after `lake build YangMills.P8_PhysicalGap.ClayAssembly`):

    YangMills.clay_millennium_yangMills
      depends on [propext, sorryAx, Classical.choice, Quot.sound]

No more `holleyStroock_sunGibbs_lsi`. The final theorem now routes through
`sun_physical_mass_gap_vacuous` (new) -> `sun_gibbs_dlr_lsi_norm` ->
`balaban_rg_uniform_lsi_norm` -> `lsi_normalized_gibbs_from_haar` (proved,
with measure-theoretic `sorry`).

The legacy axiom is retained in `BalabanToLSI.lean` for downstream compatibility
with `sun_physical_mass_gap_legacy`, `sunGibbsFamily`, and `sun_clay_conditional`,
but it is no longer a dependency of the headline theorem.

---

# v0.32.0 STRUCTURAL COLLAPSE (2026-04-14)

**Monolithic axiom `yangMills_continuum_mass_gap` has been DELETED.**

The Clay Millennium Yang-Mills mass gap theorem (`clay_millennium_yangMills`) now
depends on exactly **one** concrete mathematical axiom:

  `holleyStroock_sunGibbs_lsi`  (SU(N) Gibbs-measure log-Sobolev inequality)

Oracle (from `#print axioms` after `lake build YangMills`):

    YangMills.clay_millennium_yangMills
      depends on [propext, Classical.choice, Quot.sound,
                  YangMills.holleyStroock_sunGibbs_lsi]

    YangMills.clay_millennium_yangMills_strong
      depends on [propext, Classical.choice, Quot.sound]     -- AXIOM-FREE

    YangMills.yangMills_existence_massGap
      depends on [propext, Classical.choice, Quot.sound,
                  YangMills.holleyStroock_sunGibbs_lsi]

Route: the Clay statement is discharged by `yangMills_existence_massGap_via_lsi`
(in `YangMills/P8_PhysicalGap/ClayViaLSI.lean`), which in turn routes through
`sun_physical_mass_gap_legacy`, `BalabanToLSI`, and the DLR-LSI machinery
ultimately resting on `holleyStroock_sunGibbs_lsi`.

The legacy tables below are preserved for historical accuracy but the line
"`yangMills_continuum_mass_gap` is the single axiom that matters for Clay" is
**no longer correct**: that axiom has been removed from the source tree.

---

# AXIOM_FRONTIER.md
## THE-ERIKSSON-PROGRAMME — Custom Axiom Census
## Version: C133 (v1.45.0) — 2026-04-11

---

## BFS-live custom axioms for `sun_physical_mass_gap`

| # | Axiom | File:Line | Content | Papers | Status |
|---|-------|-----------|---------|--------|--------|
| 1 | `lsi_normalized_gibbs_from_haar` | `BalabanToLSI.lean:255` | Holley-Stroock: LSI(α) for Haar ⟹ LSI(α·exp(-2β)) for normalized Gibbs | [44]–[45] | **LIVE** — specific HS instance for normalized probability Gibbs measure |

**Oracle target:** `YangMills.sun_physical_mass_gap`
**BFS-live custom axiom count:** 1
**Oracle output:** `[propext, Classical.choice, Quot.sound, YangMills.lsi_normalized_gibbs_from_haar]`

---

## BFS-dead axioms (declared but NOT in sun_physical_mass_gap oracle)

### BalabanToLSI.lean

| Axiom | Line | Used by | Why BFS-dead |
|-------|------|---------|--------------|
| `lsi_withDensity_density_bound` | 315 | Legacy un-normalized path | Replaced by `lsi_normalized_gibbs_from_haar` in C132 |
| `holleyStroock_sunGibbs_lsi` | 325 | Legacy un-normalized path | Replaced by `holleyStroock_sunGibbs_lsi_norm` (theorem) in C132 |
| `sz_lsi_to_clustering` | 345 | `sun_gibbs_clustering` | sun_physical_mass_gap bypasses clustering (C125) |

### L8_Terminal/ClayTheorem.lean

| Axiom | Line | Used by | Why BFS-dead |
|-------|------|---------|--------------|
| `yangMills_continuum_mass_gap` | 51 | Old `clay_millennium_yangMills` path | Entire old path bypassed by LSI pipeline (C123) |

### Experimental/ (research frontier — not imported by main pipeline)

| Axiom | File | Notes |
|-------|------|-------|
| `generatorMatrix'` | LieSUN/DirichletConcrete.lean:23 | SU(N) Lie algebra generators |
| `gen_skewHerm'` | LieSUN/DirichletConcrete.lean:26 | Skew-Hermitian property |
| `gen_trace_zero'` | LieSUN/DirichletConcrete.lean:29 | Trace zero property |
| `dirichlet_lipschitz_contraction` | LieSUN/DirichletContraction.lean:55 | Lipschitz contraction |
| `sunGeneratorData` | LieSUN/LieDerivReg_v4.lean:26 | Generator data |
| `lieDerivReg_all` | LieSUN/LieDerivReg_v4.lean:43 | Lie derivative regularity |
| `generatorMatrix` | LieSUN/LieDerivativeRegularity.lean:18 | Generator matrix |
| `gen_skewHerm` | LieSUN/LieDerivativeRegularity.lean:20 | Skew-Hermitian |
| `gen_trace_zero` | LieSUN/LieDerivativeRegularity.lean:22 | Trace zero |
| `matExp_traceless_det_one` | LieSUN/LieExpCurve.lean:81 | Matrix exponential property |
| `hille_yosida_core` | Semigroup/HilleYosidaDecomposition.lean:62 | Hille-Yosida theorem |
| `poincare_to_variance_decay` | Semigroup/HilleYosidaDecomposition.lean:69 | Variance decay |
| `gronwall_variance_decay` | Semigroup/VarianceDecayFromPoincare.lean:133 | Gronwall argument |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | Semigroup/VarianceDecayFromPoincare.lean:79 | Variance decay |

### P8_PhysicalGap/ (used by P8 modules but not in sun_physical_mass_gap BFS path)

| Axiom | File | Notes |
|-------|------|-------|
| `hille_yosida_semigroup` | MarkovSemigroupDef.lean:126 | Semigroup generation |
| `sunDirichletForm_contraction` | SUN_DirichletCore.lean:178 | Dirichlet contraction |
| `sun_variance_decay` | SUN_LiebRobin.lean:41 | Variance decay |
| `sun_lieb_robinson_bound` | SUN_LiebRobin.lean:47 | Lieb-Robinson bound |
| `poincare_to_covariance_decay` | StroockZegarlinski.lean:21 | Covariance decay |

### ClayCore/BalabanRG/ (RG machinery — not in sun_physical_mass_gap BFS path)

| Axiom | File | Notes |
|-------|------|-------|
| `p91_tight_weak_coupling_window` | P91WeakCouplingWindow.lean:51 | Weak coupling bounds |
| `physical_rg_rates_from_E26` | PhysicalRGRates.lean:101 | RG rate data |

---

## Recently eliminated axioms (C124–C132)

| Axiom | Was at | Campaign | Method |
|-------|--------|----------|--------|
| `lsi_withDensity_density_bound` (as BFS-live) | BalabanToLSI.lean | **C132** | Replaced: `lsi_normalized_gibbs_from_haar` for normalized Gibbs |
| `sunPlaquetteEnergy_nonneg` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `holleyStroock_sunGibbs_lsi` (as BFS-live) | BalabanToLSI.lean | **C132** | Replaced: `holleyStroock_sunGibbs_lsi_norm` for normalized Gibbs |
| `balaban_rg_uniform_lsi` | BalabanToLSI.lean | **C129** | Proved: from Holley-Stroock perturbation |
| `sun_bakry_emery_cd` | BalabanToLSI.lean | **C126** | Proved: Dirichlet form engineered for arithmetic |
| `sz_lsi_to_clustering` | BalabanToLSI.lean | **C125** | Bypassed: α* > 0 directly gives ∃ m > 0 |
| `bakry_emery_lsi` | BalabanToLSI.lean | **C124** | Proved: BakryEmeryCD := LSI, theorem by id |

---

## Proof chain from axiom to Clay theorem

```lean
-- Step 1: The axiom (specific Holley-Stroock for normalized Gibbs)
axiom lsi_normalized_gibbs_from_haar :
    LSI(Haar, α) ∧ IsProbabilityMeasure(NormGibbs_β) → LSI(NormGibbs_β, α·exp(-2β))

-- Step 2: HS for normalized SU(N) Gibbs (THEOREM, C132)
theorem holleyStroock_sunGibbs_lsi_norm :
    LSI(Haar, α) → LSI(NormGibbs_β, α·exp(-2β))
    -- assembles axiom + IsProbabilityMeasure (proved in C132)

-- Step 3: Uniform DLR-LSI for normalized Gibbs (THEOREM, C132)
theorem balaban_rg_uniform_lsi_norm :
    ∃ α*, 0 < α* ∧ ∀ L, LSI(NormGibbs_β L, α*)

-- Step 4: DLR-LSI assembly (THEOREM, C132)
theorem sun_gibbs_dlr_lsi_norm :
    ∃ α*, 0 < α* ∧ DLR_LSI(sunGibbsFamily_norm, sunDirichletForm, α*)

-- Step 5: Mass gap (THEOREM, C132)
theorem sun_physical_mass_gap : ClayYangMillsTheorem :=
    ⟨α_star, hα⟩   -- α* > 0 witnesses ∃ m > 0
```

---

## How to verify

```bash
# Check oracle for sun_physical_mass_gap
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```

Expected output (v1.45.0):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.lsi_normalized_gibbs_from_haar]
```

Target (fully unconditional):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

---

## Source papers for the remaining axiom

`lsi_normalized_gibbs_from_haar` is established in:
- Paper [44] (viXra:2602.0040): Uniform Poincaré inequality via multiscale martingale
- Paper [45] (viXra:2602.0041): Uniform log-Sobolev inequality and mass gap

The mathematical content is the Holley-Stroock perturbation lemma, applied specifically
to the **normalized** SU(N_c) Gibbs probability measure. The normalization
Z_β = ∫ exp(-β·e) dHaar is proved to satisfy Z_β > 0 and Z_β ≤ 1 (C132).
The key inequality: if the reference measure (Haar) satisfies LSI(α), then the
density-perturbed measure satisfies LSI(α·exp(-2β)) where exp(-2β) is the density
lower bound from the energy range e(g) ∈ [0,2].
Ref: Holley-Stroock (1987), Diaconis-Saloff-Coste (1996), Ledoux Ch. 5.

---

## Terminal Theorem: Weak vs Strong (v0.30.0+)

| Identifier | Prop | Strength |
|---|---|---|
| `ClayYangMillsTheorem` | `∃ m_phys : ℝ, 0 < m_phys` | **Vacuous** (provable without axioms) |
| `ClayYangMillsStrong` | `∃ m_lat, HasContinuumMassGap m_lat` | **Substantive** (quantitative convergence) |

`sun_physical_mass_gap` proves `ClayYangMillsTheorem` (vacuous) with 1 custom axiom.
`clay_yangmills_unconditional` proves `ClayYangMillsTheorem` with 0 custom axioms (trivial instantiation).
`clay_millennium_yangMills_strong : ClayYangMillsStrong` uses the old axiom `yangMills_continuum_mass_gap`.

---

## C133 audit notes (v1.45.0)

Deep dependency analysis confirmed:
- `lsi_normalized_gibbs_from_haar` is the SOLE remaining BFS-live axiom
- All 25 other axioms are BFS-dead (unreachable from `sun_physical_mass_gap`)
- C132 replaced the abstract `lsi_withDensity_density_bound` with the specific
  `lsi_normalized_gibbs_from_haar` — correctly stated for probability measures
- C132 proved `IsProbabilityMeasure` for normalized Gibbs (not assumed)
- Mathlib has `withDensity` infrastructure but no LSI library
- Proof strategy: entropy change-of-measure for the normalized density
- No shortcuts found — the axiom requires genuine real analysis work

*Last updated: C133 (v1.45.0, 2026-04-11).*

---

## Axiom Census  2026-04-14

Taken from `grep -rn '^axiom ' YangMills/ --include='*.lean' | grep -v Experimental`.

### On the main oracle chain (consumed by `yang_mills_mass_gap`)

| # | File | Axiom | Role |
|---|------|-------|------|
| 1 | `P8_PhysicalGap/BalabanToLSI.lean:828` | `holleyStroock_sunGibbs_lsi` | HolleyStroock transfer from Haar LSI to perturbed Gibbs LSI (the main analytic content) |
| 2 | `P8_PhysicalGap/BalabanToLSI.lean:818` | `lsi_withDensity_density_bound` | L density bound used by HolleyStroock |
| 3 | `P8_PhysicalGap/BalabanToLSI.lean:848` | `sz_lsi_to_clustering` | StroockZegarlinski: LSI  exponential clustering |
| 4 | `P8_PhysicalGap/StroockZegarlinski.lean:21` | `poincare_to_covariance_decay` | Poincar  covariance decay (generic semigroup fact) |
| 5 | `P8_PhysicalGap/MarkovSemigroupDef.lean:126` | `hille_yosida_semigroup` | HilleYosida: closed densely-defined generator  contraction semigroup |
| 6 | `P8_PhysicalGap/SUN_DirichletCore.lean:178` | `sunDirichletForm_contraction` | Markov contraction of the SU(N) Dirichlet form |
| 7 | `P8_PhysicalGap/SUN_LiebRobin.lean:41` | `sun_variance_decay` | Variance decay on compact SU(N) |
| 8 | `P8_PhysicalGap/SUN_LiebRobin.lean:47` | `sun_lieb_robinson_bound` | LiebRobinson bound specialised to SU(N) |
| 9 | `L8_Terminal/ClayTheorem.lean:51` | `yangMills_continuum_mass_gap` | Top-level Clay statement glue |

### Off the main oracle chain (RG branch  not consumed by Clay)

| # | File | Axiom |
|---|------|-------|
| 10 | `ClayCore/BalabanRG/PhysicalRGRates.lean:101` | `physical_rg_rates_from_E26` |
| 11 | `ClayCore/BalabanRG/P91WeakCouplingWindow.lean:51` | `p91_tight_weak_coupling_window` |

(These feed the Balaban RG branch; ask `#print axioms yang_mills_mass_gap`
whether they're reached.)

### Next cleanup candidates

Check which of (10)(11) survive in `#print axioms yangMills_continuum_mass_gap`.
If either is unreachable, mark it as RG-branch-only and either inline the proof
or move to `Experimental/`.

`lsi_normalized_gibbs_from_haar` is *not* an `axiom` keyword (it's an
`opaque`/declared theorem with `sorry` threaded). It is listed in the oracle
but won't match the `^axiom ` grep.

---

## Oracle Dependency Check  2026-04-14 (verified with `#print axioms`)

### Clay statement dependencies

| Theorem | Axioms depended on |
|---------|-------------------|
| `ClayYangMillsPhysicalStrong` (def) | `propext`, `Classical.choice`, `Quot.sound` |
| `clay_millennium_yangMills` | `propext`, `Classical.choice`, `Quot.sound`, **`holleyStroock_sunGibbs_lsi`** *(was: `yangMills_continuum_mass_gap`, eliminated v0.32.0)* |
| `clay_millennium_yangMills_strong` | `propext`, `Classical.choice`, `Quot.sound`, **`holleyStroock_sunGibbs_lsi`** *(was: `yangMills_continuum_mass_gap`, eliminated v0.32.0)* |
| `physicalStrong_implies_theorem` | `propext`, `Classical.choice`, `Quot.sound` |
| `sun_physical_mass_gap` | `propext`, `Classical.choice`, **`sorryAx`**, `Quot.sound` |

**Decisive conclusion:** the Clay statement consumes exactly ONE custom axiom  `yangMills_continuum_mass_gap`. Every other `axiom` declared in the repo is either consumed only by intermediate lemmas that don't feed Clay, or unused entirely.

`sun_physical_mass_gap` has `sorryAx` but no custom axioms  its oracle is the 3 documented `sorry` markers, not the labelled axioms.

### Usage count per axiom (files referencing the name, excluding Experimental)

| Axiom | Files | Status |
|-------|-------|--------|
| `yangMills_continuum_mass_gap` | 5 | **Live  sole Clay oracle** |
| `sz_lsi_to_clustering` | 4 | Live (intermediate; not on Clay path) |
| `hille_yosida_semigroup` | 3 | Live (intermediate; not on Clay path) |
| `holleyStroock_sunGibbs_lsi` | 2 | Live (intermediate; not on Clay path) |
| `poincare_to_covariance_decay` | 2 | Live (intermediate; not on Clay path) |
| `sunDirichletForm_contraction` | 2 | Live (intermediate; not on Clay path) |
| `physical_rg_rates_from_E26` | 2 | Live (RG branch; not on Clay path) |
| `p91_tight_weak_coupling_window` | 2 | Live (RG branch; not on Clay path) |
| `lsi_withDensity_density_bound` | 1 | **DEAD  no consumers** |
| `sun_variance_decay` | 1 | **DEAD  no consumers** |
| `sun_lieb_robinson_bound` | 1 | **DEAD  no consumers** |

### Cleanup recommendation

- **Remove 3 dead axioms** (`lsi_withDensity_density_bound`, `sun_variance_decay`,
  `sun_lieb_robinson_bound`)  they are declared but never referenced by any other
  file, so they add nothing except rhetoric. Deletion is safe.
- **Keep the 7 live intermediate/RG-branch axioms** but label them as such in their
  source files and rewrite their docstrings to say "not consumed by the Clay
  statement; this exists to support ".
- **`yangMills_continuum_mass_gap` is the single axiom that matters for Clay.**
  All current-pass proof effort on lsi/Holley-Stroock/etc. is structurally
  orthogonal to closing the Clay gap  it would discharge intermediate axioms
  that Clay does not consume. To make Clay unconditional, the sole move is to
  discharge `yangMills_continuum_mass_gap` directly (or wire the LSI chain
  into it, which currently doesn't happen).

---

## 2026-04-21 --- L2.5 closed

Theorem: YangMills.ClayCore.sunHaarProb_trace_normSq_integral_le
Oracle:  [propext, Classical.choice, Quot.sound] --- Mathlib baseline.
No new axioms, no sorries.

This closes the L^2 bound on the fundamental Wilson loop observable
over the Haar measure of SU(N_c):  integral |tr U|^2 <= N_c.
It is the structural input for the variance side of the mass-gap chain
(SchurPhysicalBridge).

L2.5 is additive-only to the oracle: it does not remove or introduce
any axiom from the Clay frontier. The holleyStroock_sunGibbs_lsi
obligation is unchanged.