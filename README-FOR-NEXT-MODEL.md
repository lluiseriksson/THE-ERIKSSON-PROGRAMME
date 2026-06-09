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
- `lattice_mass_gap_of_clustering` — **full M3 assembly**: IR geometric cluster bound + UV
  suppression ⟹ connected correlator decays with positive gap `min(m*, c₀)`;
- finite-susceptibility corollaries (`∑_d |cov d| < ∞`, `≤ C/(1−r)`).

---

## 5. The open frontier — where to actually push (priority order)

Each is carried with **no axiom**; closing one discharges a hypothesis or proves an open
lemma. Full details + Lean signatures in `docs/HANDOFF-KP.md` and `HORIZON.md`.

- **T1 — `ursellComplete_recurrence` — CLOSED (2026-06-09).** Proved unconditionally in
  `YangMills/KP/UrsellRecurrence.lean` (component-of-vertex-0 decomposition: `reachSet`
  fibering + edge-toggle involution + `Fin.succAbove` relabeling). The closed form
  `ursellComplete_eq` (`φ(K_{n+1}) = (−1)ⁿ·n!`) and the n=1 Mayer identity
  (`partition_singlePolymer_eq_exp`) are now hypothesis-free and oracle-clean.
- **T2 — `kp_per_size_bound`** (Penrose tree-graph inequality: size-`n` cluster weight decays
  geometrically). Feeds the verified convergence back-half and supplies the cluster bound that
  `lattice_mass_gap_of_clustering` assumes. Needs spanning-tree counting (Cayley) — **not in
  Mathlib**, may need its own development.
- **T3 — LG6 measure step:** `IsMulLeftInvariant (gaugeMeasureFrom μ)` under the diagonal
  centre action, then combine with the proved `wilsonLoop_scalarCenter_smul` (gives `ω^L`) to
  get the Wilson-loop selection rule. Instance/transport plumbing on `GaugeConfig`.
- **T4 — strong-coupling character expansion → area law (LG7/8).** Needs **Peter–Weyl for
  compact groups**, NOT in Mathlib — a major standalone formalization (or a Weingarten route
  for low moments). The genuine analytic content of M3.
- **Beyond — M4/M5, the Clay wall:** continuum limit + OS/Wightman reconstruction. Open
  mathematics. Do not formalize until it exists on paper (`HORIZON.md §4`).

T1–T3 are realistically reachable with **interactive Lean** (you, ideally, running Lean
locally and iterating on goals). T4 is a project. M4/M5 is original research.

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
