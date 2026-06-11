# README FOR THE NEXT MODEL — complete foundations of THE-ERIKSSON-PROGRAMME

You are a (more powerful) AI being handed this Lean 4 / Mathlib repository to advance. This
single file is self-contained: it gives you the project's purpose, the build/verify loop,
the iron rules, the complete map of what is proved, and the exact open targets. Read it once,
top to bottom, before editing anything. (Companion docs: `AGENT-ONBOARDING.md`,
`FOUNDATIONS.md`, `HORIZON.md`, `ROADMAP.md`, `docs/HANDOFF-KP.md`.)

---

## 0. Purpose and the honesty mandate

The project formalizes mathematics around the **Yang–Mills mass gap** (a Clay Millennium
Problem) in Lean 4 on top of Mathlib. Its defining principle is **honesty over progress**:

- Every result is machine-checked. Ground truth = the compiler + the axiom oracle.
- The boundary between **proved** and **assumed/open** is kept razor-sharp.
- Hard unproved inputs are carried as **explicit hypotheses of a theorem, never as `axiom`**.
- **No `sorry`** anywhere in the verified core.

**Honest distance to the Clay prize: ~0% (<0.1%), and this will not change by formalization
alone.** Everything proved here lives on the **lattice, in finite volume**. The Clay problem
requires the **continuum limit (4D) + Osterwalder–Schrader/Wightman axioms + continuum mass
gap** — open mathematics that nobody has completed for the non-abelian case. *You cannot
formalize what is unproved.* If you find yourself "proving Clay", you have either written a
vacuous statement, laundered a theorem into an axiom, or used `sorry` — all forbidden (see §3).
The realistic reachable summit is **M3: the strong-coupling lattice mass gap
(Osterwalder–Seiler, 1978)**, a *known* theorem and therefore formalizable.

---

## 1. Coordinates

| | |
|---|---|
| Git remote | `https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git` |
| Branch | `main` |
| Local path | `C:\Users\lluis\Downloads\CoworkYangMills\THE-ERIKSSON-PROGRAMME` |
| Toolchain | `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`) |
| Build system | Lake (`lakefile.lean`); Mathlib pinned in `lake-manifest.json` |
| Verified root | `YangMillsCore.lean` (imports everything sound) |

### Setup
```bash
git clone https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git
cd THE-ERIKSSON-PROGRAMME
elan toolchain install leanprover/lean4:v4.29.0-rc6
lake exe cache get          # fetch prebuilt Mathlib oleans — do NOT build Mathlib from source
lake build YangMillsCore    # ~8200 jobs; fast with warm cache
```

---

## 2. The verify loop (run on every result)

```bash
lake build YangMillsCore
echo 'import YangMillsCore
#print axioms <fully.qualified.name>' > _oc.lean
lake env lean _oc.lean
rm _oc.lean
```
**Required oracle:** `[propext, Classical.choice, Quot.sound]` (purer is fine:
`[propext, Quot.sound]`, `[propext]`). **Any project-local axiom ⇒ the discipline was broken;
reject/revert.**

**Never push broken code.** Guard commits on a green build:
```bash
lake build YangMillsCore && git add <files> && git commit -m "..." && git push
```

---

## 3. The iron rules (from `FOUNDATIONS.md`) — violating any of these ruins the project

1. **No `sorry`** in anything reachable from `YangMillsCore`.
2. **No project axioms.** Hard inputs (KP cluster bound, Balaban estimates, analyticity
   radius `R*`, OS1/O(4) covariance) are **hypotheses**, never `axiom`s.
3. **No vacuous targets.** If a statement can be closed by a point mass, a constant
   observable, the trivial group, or `⟨1, one_pos⟩`, it is worthless — do not count it.
4. **No laundering** a hard theorem by dropping its premises.
5. **Keep the map honest:** update `ROADMAP.md §0` and `HORIZON.md` as nodes close; never
   report a number `#print axioms` + an adversarial audit would not support.
6. **"Lattice mass gap ≠ Clay prize"** stays visible. ~0% to Clay is the honest statement,
   not a failure — the central difficulty is unsolved by humanity.

---

## 4. What is proved (map of the verified core)

All oracle-clean, no `sorry`, no project axioms, reachable from `YangMillsCore`.

**SU(N) Haar / centre-symmetry engine** — `YangMills/ClayCore/Schur*.lean`,
`CenterVanishing.lean`, `LeftInvariantVanishing.lean`:
Z_N centre selection rules `∫ (tr U)^a · conj(tr U)^b dHaar = 0` for `N ∤ (a−b)`;
`∫ |tr U|² ≤ N`; SU(1) triviality; exact U(1) Fourier orthogonality
`∫ fourier n = δ_{n,0}`; the general left-invariant eigenvalue-vanishing engine.

**Kotecký–Preiss / Mayer cluster expansion** — `YangMills/KP/`:
`PolymerSystem`, `partition` + factorization; incompatibility graph + `IsCluster`; Ursell
coefficient `ursell` with verified values φ(K₁)=+1, φ(K₂)=−1, φ(K₃)=+2; the cluster sum
`clusterSum` (Mayer RHS) supported on clusters; the empty / linear-order / **single-polymer**
cases of `Ξ = exp(clusterSum)` (single-polymer is a complete theorem conditional on Target A);
the KP smallness criterion `KPCriterion` with base bounds (`kp_activity_le`,
`kp_neighbor_sum_le`); the geometric-convergence back-half (`cluster_series_summable`,
`cluster_sum_le`); the Mayer log series (real + complex).

**Lattice gauge observables** — `ClayCore/GaugeMarginal.lean`, `GaugeEdgeExpectation.lean`,
`GaugeMeasureProps.lean`, `WilsonLine.lean`, `WilsonLoopCenter.lean`:
single-edge marginal of the product gauge measure (`gaugeMeasureFrom_map_eval`);
single-edge and multi-edge Wilson expectations; the full Z_N N-ality grading on a lattice
edge (`gauge_single_edge_trace_mixedPow_eq_zero` and pure/conjugate specializations);
`wilsonLine`/`wilsonLoop` algebra (composition, append, flatten, gauge-action, centre scaling
`z^L`, scalar-centre eigenvalue `ω^L`); second-moment bound in `[0,N]`.

**Paper §4/§6/§7 conditional skeleton + M3 bridge** — `YangMills/Paper/`:
`coupling_control` (§4), `telescoping` (§6.1), `uv_geometric_summation` (§6.3),
`mass_gap_bound` (§7); and `ClusteringToGap.lean`:
- `clustering_gives_exponential_decay` — a geometric cluster bound `|cov d| ≤ C·rᵈ` *is*
  exponential decay with strictly positive mass `m* = -log r`;
- `lattice_mass_gap_of_clustering` (+ `_uniform`) — **full M3 assembly**: IR geometric
  cluster bound + UV suppression ⟹ connected correlator decays with positive gap;
- finite-susceptibility corollaries (`∑_d |cov d| < ∞`, `≤ C/(1−r)`).

**T3 / centre symmetry, CLOSED (2026-06-10)** — `YangMills/L1_GibbsMeasure/`
`CenterInvariance.lean`, `SUNSelectionRule.lean`, `GibbsSelectionRule.lean`,
`WilsonObservable.lean`: gauge measure centre-invariant; Wilson action *exactly*
centre-symmetric (plaquette signs `(+,+,−,−)`); Z_n N-ality selection rules at genuine
SU(n) Haar — free, interacting (any β), and two-loop correlators — with the Wilson loop
proved bounded/measurable/integrable so all expectations are honest integrals.

**Polymer representation + lattice KP convergence, PROVED (2026-06-10)** —
`PolymerExpansion.lean`, `PolymerFactorization.lean`, `LatticePolymerSystem.lean`:
high-temperature expansion `e^{−βS} = ∑_S ∏ f_p`; `|f_p| ≤ e^{|β|B}−1`; locality;
two-block/gauge-level/iterated independence; `latticePolymerSystem` and
`connectedLatticePolymerSystem` instantiating `PolymerSystem`; KP criteria (binomial
entropy, volume-dependent) and **convergence of the lattice Mayer series**
(`latticeClusterSum_summable`, `connectedLatticeClusterSum_summable`); quantitative
`|Z−1|` bound and `Z > 0` at small coupling.

**VOLUME-UNIFORMITY (criterion level), PROVED (2026-06-10)** — `ConnectedEntropy.lean`:
local degree bound (≤ `16d` touching plaquettes), walk counting (≤ `Δ^L`), splice lemma,
covering-walk theorem (connected sets = ranges of lazy closed walks), **lattice-animal
entropy bound** `card_connectedPolymers_le` (≤ `(16d+1)^{2n}` connected polymers of size
`n+1` through a point — volume-free), and
**`connectedLatticePolymerSystem_kpCriterion_volumeUniform`**: the KP criterion for the
connected gas under β-smallness depending only on the dimension.  Surviving
volume-dependence is isolated in one hypothesis (`e·t·#P < 1`) of the convergence
corollary — see `docs/SHARP-KP-PLAN.md`.

---

## 5. The open frontier — where to actually push (priority order)

Each is carried with **no axiom**; closing one discharges a hypothesis or proves an open
lemma. Full details + Lean signatures in `docs/HANDOFF-KP.md` and `HORIZON.md`.

- **T1 — `ursellComplete_recurrence` — CLOSED (2026-06-09).** Proved unconditionally in
  `YangMills/KP/UrsellRecurrence.lean` (component-of-vertex-0 decomposition: `reachSet`
  fibering + edge-toggle involution + `Fin.succAbove` relabeling). The closed form
  `ursellComplete_eq` (`φ(K_{n+1}) = (−1)ⁿ·n!`) and the n=1 Mayer identity
  (`partition_singlePolymer_eq_exp`) are now hypothesis-free and oracle-clean.
- **T2 — `kp_per_size_bound` — CLOSED (2026-06-10).** The full KP convergence chain is
  proved unconditionally: Penrose tree-graph inequality (`abs_ursell_le_card_spanningTrees`,
  via the greedy BFS partition scheme), tree counting (`treeCount_le_pow`, parent-function
  injection), the per-tree activity walk (`tree_walk_bound`), and the per-size estimate
  `clusterWeight P n ≤ (∑‖z‖)·(e·A)ⁿ` with corollaries `kp_convergence` and
  `kp_norm_clusterSum_le` (`e·A < 1`; uniform smallness — slightly stronger than sharp KP).
  See `docs/DEPENDENCY-GRAPH.md`. Remaining toward M3: the polymer representation
  (lattice Gibbs ⇄ polymer system) and the UV bound. *(Historical text below.)*
  Original entry: (Penrose tree-graph inequality: size-`n` cluster weight decays
  geometrically). Feeds the verified convergence back-half and supplies the cluster bound that
  `lattice_mass_gap_of_clustering` assumes. Needs spanning-tree counting (Cayley) — **not in
  Mathlib**, may need its own development.
- **T3 — CLOSED (2026-06-10).** Centre invariance, exact action symmetry, and the Z_n
  selection rules (free / interacting / correlator) are proved end to end at genuine
  SU(n) Haar; see §4 above and `docs/VERIFICATION-LEDGER.md` addenda 1–3.
- **SHARP KP — CLOSED (2026-06-10; `docs/SHARP-KP-PLAN.md` §5h).** The full
  weight-respecting Kotecký–Preiss bound is machine-checked end to end:
  `kp_pinned_cluster_bound` / `pinned_cluster_summable_sharp` (KP/SharpShell.lean),
  `kp_convergence_sharp` / `kp_norm_clusterSum_le_sharp` (KP/SharpKP.lean), and the
  campaign goal **`connectedLatticeClusterSum_summable_volumeUniform`**
  (L1_GibbsMeasure/ConnectedEntropy.lean): the Mayer series of the connected lattice
  gas converges absolutely under β-smallness depending ONLY on the dimension — no
  volume hypothesis anywhere.  `docs/VERIFICATION-LEDGER.md` addendum 6 has the
  oracle outputs.
- **THE MAYER–URSELL INVERSION — CLOSED (2026-06-10;
  `KP/MayerInversion.lean`).** `Ξ = exp(clusterSum)`
  (`partition_eq_exp_clusterSum(_of_kp)`) — the fundamental theorem of
  cluster expansions, the "months-long crux" of `Expansion.lean`, is
  machine-checked end to end: the partition identity
  (`ursell_partition_identity`), the finite resummation
  (`admissible_card_sum_eq`, `partition_univ_eq_cluster_layers`), and
  the analytic shell (power Fubini, master sigma-sum, size layers).
  Also closed: Half A of the correlation chain
  (`connectedLattice_pinned_tail_volumeUniform` — exponential
  size-tail decay).  `docs/VERIFICATION-LEDGER.md` addendum 7;
  `docs/CLUSTER-CORRELATION-PLAN.md` is the campaign log.
- **HALF B GEOMETRY + THE `Z = Ξ` GATE — CLOSED (2026-06-10/11).**
  `connecting_cluster_decay` (L1_GibbsMeasure/ClusterGeometry.lean):
  pinned cluster sums restricted to clusters touching a distant
  plaquette decay exponentially in the touching-distance, all
  constants volume-free.  And **`partitionFunction_eq_partition`**
  (L1_GibbsMeasure/PolymerRepresentation.lean): `(Z : ℂ) =
  KP.partition(connected gas, univ)` — the measure-side
  identification, via the component bijection (`plaqComponents` +
  `componentFamily`).  Composed with the Mayer–Ursell inversion:
  `Z = exp(clusterSum)` at high temperature; in particular `Z ≠ 0`.
  `docs/VERIFICATION-LEDGER.md` addendum 8;
  `docs/CLUSTER-CORRELATION-PLAN.md` §2e.
- **B2, THE COVARIANCE IDENTITY — CLOSED (2026-06-11,
  `covariance_identity` in L1_GibbsMeasure/PolymerRepresentation.lean).**
  The full weighted-gas campaign (W1–W4c, `WeightedGas.lean` +
  PolymerRepresentation): arbitrary bounded measurable LOCAL weight
  families satisfy `Z[w] = Ξ[w] = exp(K[w])` volume-uniformly;
  multiplicative observables absorb into deformed weights
  (`weightedPartition_deform`); the four-gas inclusion–exclusion
  `K_{FG}+K−K_F−K_G` is supported on CONNECTING tuples
  (`clusterSum_inclusion_exclusion`); and
  **`Z[FG]·Z = Z[F]·Z[G]·exp(connecting cluster sum)`** — the
  division-free covariance identity.
  `docs/CLUSTER-CORRELATION-PLAN.md` §2e (the W-campaign log).
- **B4 — THE IR CLUSTERING BOUND — CLOSED (2026-06-11,
  `truncated_correlation_bound` in
  L1_GibbsMeasure/PolymerRepresentation.lean).**  For multiplicative
  local observables with supports at touching-distance `≥ 2k`:
  `‖Z[FG]·Z − Z[F]·Z[G]‖ ≤ C·e^{−ε·k}`, `C` explicit and volume-free.
  This discharges the `hIRbound` hypothesis of
  `lattice_mass_gap_of_clustering_uniform` at the lattice level — the
  ENTIRE cluster-correlation campaign (sharp KP → Mayer–Ursell →
  `Z = Ξ` → weighted gases → covariance identity →
  inclusion–exclusion → symmetrization → connecting decay) is
  machine-checked end to end.  `docs/VERIFICATION-LEDGER.md`
  addendum 10 (ten oracle lines);
  `docs/CLUSTER-CORRELATION-PLAN.md` is the complete campaign log.
- **THE T4 SHORTCUT — CLOSED, THROUGH THE SU(N) CAPSTONE
  (2026-06-11, `L1_GibbsMeasure/TwoPlaquetteCorrelator.lean`).**
  The full chain, all oracle-clean: `two_plaquette_correlator_bound`
  (the `kp_cluster_decay`-shaped endpoint of `PETER_WEYL_ROADMAP.md`
  Layer 4, WITHOUT Peter–Weyl/Schur/character expansion);
  `two_plaquette_correlator_bound_normalized` (`Z`-free constants);
  **`sun_two_plaquette_correlator_bound`** — exponential clustering
  of two-point functions for the GENUINE SU(N_c) Wilson lattice
  theory (actual group, actual Haar `sunHaarProb`, actual plaquette
  energy `Re tr U`), constants in `d, N_c, β, s, t, ε` only; and the
  non-vacuity witnesses `clustering_window_nonempty` /
  `sun_clustering_window_nonempty` (explicit `β₀ > 0` windows).
  Also: `lattice_mass_gap_of_exp_clustering_uniform` — the M3
  assembly's IR hypothesis is THEOREM-FED; the §6.3 UV single-scale
  bound is the SOLE remaining carried hypothesis (Balaban, by
  design).  `docs/VERIFICATION-LEDGER.md` addenda 8–10 (seventeen
  oracle lines); `HYPOTHESIS_FRONTIER.md` current-state addendum.
- **NEXT TARGET — the AREA-LAW CAMPAIGN (`docs/AREA-LAW-PLAN.md`,
  designed 2026-06-11):** the strong-coupling area law
  `|⟨W_C⟩| ≤ C₀·r^{Area(C)}` via the banked N-ality selection rules
  (per-edge balance) + NEW discrete surface theory (ℤ-chain boundary
  maps, the spanning lower bound) + the banked expansion/entropy
  engines.  **Peter–Weyl is off the critical path** (needed only for
  sharp constants/character-expansion bookkeeping).  **Status
  2026-06-11 (ledger Addendum 12):** AL1+AL2 CLOSED (ring-generic
  chain complex, `ChainComplex.lean`), AL3 closed by audit (banked
  selection rule), AL4 substrate+expansion CLOSED
  (`EdgeFactorization.lean`, `WilsonLoopExpansion.lean`), AL5
  interface CLOSED (`chainArea_le_card_of_support_subset`).  **Open:
  the AL4.5 join brick** — plan §4 has the full one-unbalanced-edge
  design (TE/DB/K/J); start with TE (the trace-expansion `Matrix`
  lemma, self-contained) and `loopChain`.  Then AL6 (banked
  patterns).  Alternative frontiers:
  Peter–Weyl proper (`PETER_WEYL_ROADMAP.md`) or the Balaban
  single-scale UV estimate (class-C, outside the current plan).
- **UV bound (§6.3 single-scale suppression):** content from the paper not yet in the
  repo; needed for the other M3 hypothesis.
- **T4 — strong-coupling character expansion → area law (LG7/8).** Needs **Peter–Weyl for
  compact groups**, NOT in Mathlib — a major standalone formalization (or a Weingarten route
  for low moments). Only needed for the Wilson-loop form of M3.
- **Beyond — M4/M5, the Clay wall:** continuum limit + OS/Wightman reconstruction. Open
  mathematics. Do not formalize until it exists on paper (`HORIZON.md §4`).

The sharp-KP campaign is **done**. The Mayer–Ursell inversion and the
`Z = Ξ` gate are **done**. T4 is a project. M4/M5 is original research.
Read `docs/DEPENDENCY-GRAPH.md` and `docs/VERIFICATION-LEDGER.md` (8 addenda)
for the complete machine-checked state.

---

## 6. Gotchas already paid for (save yourself the failures)

- Verify Mathlib lemma names against the pinned source in `.lake/packages/mathlib` before
  using them. Known renames in this toolchain: `div_lt_iff₀`, `abs_add_le`,
  `Finset.eq_empty_iff_forall_notMem`, `Units.val_pow_eq_pow_val`.
- Non-commutative ordered products ⇒ `List.prod`, never `Finset.prod` (which needs `CommMonoid`).
- The Wilson **loop** is `tr(matrix product)` — NOT a scalar edge product. The Fubini
  factorization does NOT apply, and a closed loop does NOT vanish in general (it carries `ω^L`
  — the area-law contributor). Do not "prove" it vanishes.
- `Multiplicative (AddCircle T)` has no `MeasurableSpace` instance — don't route the U(1)
  edge case through it.
- `#print axioms` is the only honesty check that matters; run it on every headline result.

---

## 7. How your performance will be judged

The honest score is **the number of audited `[STUB]→[DONE]` conversions on the non-vacuous
path (T1–T4)** — each verified by `lake build` + `#print axioms` + an adversarial audit that
the statement is non-vacuous and axiom-free. One genuine T1 or T2 closure outweighs any
amount of routine API. Do **not** optimize for theorem count; optimize for closing real open
lemmas without breaking §3. And keep `~0% to Clay` honest — a model that claims to close the
prize by adding an axiom or a vacuous target has failed the actual test, which is integrity.

— The Eriksson Programme. Build truthfully.
