# ROADMAP — pushing the boundary toward an unconditional Yang–Mills mass gap

> **STATUS STAMP (2026-06-12, latest).** Core green at **8252 jobs**,
> Mathlib pinned (see `REPRODUCIBILITY.md`).  Since this roadmap was first
> written (2026-06-09) several tracks closed: the area-law track (all four
> variants — finite-volume/volume-uniform × linearized/exact-activity,
> ledger Addenda 12–18d); the IR clustering bound (theorem-fed, M3 IR side
> done); and the **gauge-RG continuum track** (`YangMills/RG/**`, 36
> oracle-clean bricks, Addenda 23–52) — the local averaging-operator theory
> is complete and the §6.3 UV branch is now ONE oracle-clean conditional
> `lattice_mass_gap_of_cluster_and_coupling` on two carried Bałaban inputs
> (`hRpoly`, `hg`).  **The current frontier is those two inputs** (the
> Dimock cluster-expansion-with-holes and the coupling-flow decay), the
> genuine months-scale work; see `docs/BALABAN-RG-PLAN.md`,
> `docs/UV-SINGLE-SCALE-PLAN.md`, `docs/BALABAN-SOURCE-BOUNDS.md`.  The
> §3 "immediate next moves" and §4 "Target B" notes below are
> **superseded** (kept as a historical 2026-05/06 record); the measurement
> discipline (§0, §2) is unchanged and still governs.  Clay distance
> **~0% (<0.1%)**, unchanged.

This file is the honest, measurable plan for advancing the project, written so that
a later (possibly stronger) automated prover can pick the next move, attempt it,
and have its progress *measured against reality* rather than against a vacuous
target. Read it together with `HORIZON.md` (the formal dependency DAG with
fill-in-the-blanks Lean signatures) and `FOUNDATIONS.md` (what "proved" means).

---

## 0. The honest distance to Clay (calibrated 2026-05-29)

Define **100% = a complete, machine-checked proof of the Clay statement**:
construct a quantum Yang–Mills theory on ℝ⁴ for a compact simple gauge group
satisfying the Osterwalder–Schrader/Wightman axioms, and prove it has a mass gap
`Δ > 0`.

| Target | Honest progress | Why |
|---|---|---|
| **Full Clay** (continuum 4D + OS axioms + Δ>0) | **~0% (<0.1%)** | The continuum construction is *open mathematics*. Nobody has done it, even on paper, for 4D non-abelian. You cannot formalize what is unproved. |
| Unconditional **strong-coupling lattice** mass gap, SU(N) | ~3% | A *known theorem* (Osterwalder–Seiler 1978), so formalizable — but the analytic core (character + cluster expansion) is unstarted. |
| **U(1), d=2** lattice mass gap, end-to-end (exactly solvable) | ~15% | Infrastructure + exact U(1) Fourier orthogonality exist; blocked on modified Bessel functions in Mathlib. |
| Reusable **SU(N) Haar / character** infrastructure | ~25% | What this session built: selection rules, the engines, L2.5. Full Peter–Weyl/Schur (F2–F4) not yet. |

**Read the top row literally.** Being near 0% toward Clay is not failure; it is the
honest statement that the central difficulty is unsolved by humanity. The project's
value is (a) a clean, compiler-verified base, (b) an honest map, and (c) reusable
infrastructure — *not* proximity to the prize.

### What "pushing the boundary" can and cannot mean

* **Can** (in scope for an automated prover): formalize *known-but-unformalized*
  mathematics (Peter–Weyl, Weingarten, Osterwalder–Seiler lattice clustering), and
  contribute *small genuinely-new* lemmas that compile clean. This session did the
  latter (the Z_N selection rules were new to the repo and are oracle-verified).
* **Cannot** (out of scope for any current system): solve the *open* mathematics of
  the continuum limit (M4) or the full Clay construction (M5). Treat any claim to
  have done so as a bug until independently audited.

So the honest experiment is **M1 → M3**: how far up the known-but-unformalized
ladder can systems climb autonomously, with `lake build` + `#print axioms` + an
adversarial audit as ground truth.

---

## 1. Milestones (each with a measurable "done" test)

**M0 — Sound SU(N)·Haar core. ✅ DONE (verified 2026-05-29).**
Center-symmetry engine (SU(N) + general left-invariant), the Z_N selection rules
(trace, powers, mixed moments, matrix-coefficient monomials, power sums, the
bigraded covariance rule), `∫|tr U|² ≤ N`, SU(1) triviality, exact U(1) Fourier
orthogonality.
*Done-test (passes):* `lake build YangMillsCore` green; `oracle_check.lean` shows
`[propext, Classical.choice, Quot.sound]` on all results.

**M1 — Full character theory on SU(N) Haar (HORIZON F2–F4).**
Matrix-coefficient L² API; **Peter–Weyl for compact groups** (the bottleneck — not
in Mathlib); Schur orthogonality `∫ ρ_{ij} \overline{σ_{kl}} = δδδ/dim`.
*Done-test:* a Lean theorem `schur_orthogonality` for SU(N) irreducibles, green +
oracle-clean. Sub-milestone with high payoff: the **sharp** `∫|tr U|² = 1`
(currently only `≤ N`).
*Route-around:* a `Weingarten.lean` giving polynomial Haar integrals in closed
form avoids generic Peter–Weyl for the moments F5/F6 need.

**M2 — U(1), d=2, end-to-end non-vacuous mass gap.**
The exactly-solvable warm-up; the first honestly non-vacuous mass-gap-type result.
*Blocker (verified):* **modified Bessel functions `I_n` are not in Mathlib.** Two
routes: (a) build the Bessel theory (a self-contained, broadly useful contribution);
(b) work abstractly — prove `|⟨fourier 1⟩_Gibbs| < 1` from the strict triangle
inequality (the analytic origin of the gap), then geometric clustering from the d=2
plaquette factorisation (needs the `gaugeMeasureFrom` marginal/invariance bridge,
`HORIZON.md §3.3`).
*Done-test:* `ClayYangMillsPhysicalStrong` (leaks sealed) instantiated for U(1) in
d=2, green + oracle-clean + audited non-vacuous.

**M3 — SU(N) strong-coupling unconditional lattice mass gap (Osterwalder–Seiler).**
The real, *reachable* prize: a genuine, unconditional, non-vacuous SU(N) **lattice**
mass gap at small β. Needs M1 + Kotecký–Preiss/Brydges–Kennedy cluster expansion +
`ConnectedCorrDecay` for the real Wilson–Gibbs measure.
*Done-test:* `ConnectedCorrDecay (sunHaarProb N) (wilsonPlaquetteEnergy N) β F distP`
proved for a genuine non-degenerate `F`, small β, green + oracle-clean + audited.
This is *known mathematics* (Osterwalder–Seiler 1978, Seiler LNP 159), hence a pure
formalization task — large, but not open.

**M4 — Continuum limit via asymptotic freedom. ⛔ OPEN MATH.**
`m_phys(β) = m_lat/a(β)` with `a(β)` on the RG trajectory `β = 2N/g²`,
`a ∝ exp(−1/(2b₀g²))`, `liminf m_phys > 0` as `β→∞`. **Open even on paper** for 4D
non-abelian (Bałaban program incomplete). Not a formalization task until the
mathematics exists. Seal Leak B of `FOUNDATIONS.md §3` only when it does.

**M5 — Full Clay. ⛔ OPEN MATH.** Continuum 4D construction + OS reconstruction +
reflection positivity + rotation-invariance restoration + continuum mass gap.

```
M0 ✅ ──► M1 ──► M2 (U(1) toy, non-vacuous) ──► M3 (SU(N) lattice gap, KNOWN math)
                                                     │
                                                     ▼
                                              M4 ⛔ continuum (OPEN)  ──► M5 ⛔ Clay (OPEN)
```

---

## 2. The boundary-pushing experiment (protocol for a prover)

To test whether a system can genuinely advance the work — and to leave an auditable
trail — follow this loop. **Ground truth is the compiler and an adversarial audit,
never the model's own say-so.**

1. **Pick** the lowest open `[STUB]` node in `HORIZON.md` (cheapest first). Current
   front line, in order: sharp `∫|tr U|²=1` (SU(2), via Weyl integration) → a
   `Weingarten.lean` for low moments → the U(1) marginal/invariance lattice bridge.
2. **State** the target as a precise Lean signature first (type, no proof).
3. **Prove** it. The attempt counts only if:
   - `lake build YangMillsCore` (or the relevant target) is **green**, AND
   - `#print axioms <thm>` = `[propext, Classical.choice, Quot.sound]` (no `sorry`,
     no new axioms), AND
   - the statement is **non-vacuous** — checked against the real target, not
     `∃ m>0`. (Apply the FOUNDATIONS vacuity tests: can it be closed by a point
     mass / constant observable / trivial group? If yes, it's vacuous.)
4. **Audit** with an independent pass (ideally a different model/agent): is the
   theorem genuine or cosmetic? Are the hypotheses laundering a missing theorem
   into an axiom (the "wrong-axiom trap")?
5. **Record** the `[STUB]→[DONE]` conversion in `HORIZON.md`, move on.

**The honest score is the number of audited `[STUB]→[DONE]` conversions on the
non-vacuous path M1–M3** — not a self-reported percentage. A single genuine M2
closure (U(1) non-vacuous gap) would be worth more than the entire pre-cleanup
history of this repo.

### Anti-patterns the audit must reject (lessons already paid for)

- A target that type-checks but is **vacuous** (`∃ m>0`, closed by `⟨1,one_pos⟩`).
- Modelling a **non-trivial group by a trivial one** (U(1) as `SU(1)`; see
  `SUOneDegenerate.lean`).
- **Laundering** a hard analytic fact into a hypothesis/axiom by dropping its
  premises (the `L·log·L` `sorry`; `docs/phase1-llogl-obstruction.md`).
- Resting a "green" build on **cached oleans of bit-rotted files** (e.g.
  `SchurEntryOffDiag.lean`, excluded from the verified core pending repair).

---

## 3. Immediate next moves (concrete, in priority order)

> **SUPERSEDED (see status stamp).** The list below is the 2026-05/06
> SU(N)-Haar-era front line; it has been overtaken by the area-law and
> gauge-RG tracks.  The current frontier is the two carried Bałaban inputs
> `hRpoly`/`hg` of `lattice_mass_gap_of_cluster_and_coupling` (the Dimock
> cluster expansion with holes + coupling-flow decay).  Items 1–5 below are
> retained as a historical record of lower-priority hygiene/warm-up tasks.

1. **Repair `SchurEntryOffDiag.lean`** against current Mathlib (`star_mul`
   disambiguation, `Filter.EventuallyEq.of_forall` rename, `NeZero` synthesis), or
   re-derive its content; then re-add it to `YangMillsCore`. *(Hygiene, low risk.)*
2. **Sharp second moment** `∫|tr U|² = 1` for SU(2) via the Weyl integration
   formula. First genuinely *quantitative* Schur fact; base case of M1. *(Medium.)*
3. **`Weingarten.lean`** — U(N) Haar polynomial integrals in closed form for small
   k; F3-free route to the moments M3 needs. *(Medium–high.)*
4. **U(1) lattice bridge** — `(gaugeMeasureFrom μ).map (eval e) = μ` (single-edge
   marginal; Mathlib has `measurePreserving_eval`), then `⟨open Wilson line⟩ = 0`
   via the general engine. First statement about a genuine gauge observable.
5. Then attack **M2** (U(1) d=2 gap) by whichever route (Bessel vs. abstract `|r|<1`)
   the prover can carry.

---

## 4. Paper-formalization log (honest, conditional)

Pieces of the Eriksson paper ("Exponential Clustering and Mass Gap for 4D SU(N)
Lattice Yang–Mills", Feb 2026) formalized as **explicitly conditional** theorems —
Balaban's imported inputs carried as *hypotheses*, never axioms.

| Paper result | Lean | Status |
|---|---|---|
| §4 Prop. 4.1, coupling-control induction (`u_k ≥ u_0 + k·b₀/2`) | `YangMills/Paper/CouplingControl.lean` (`coupling_control`) | ✅ **verified** (oracle clean). Conditional on the β-function recursion + remainder bound `|r_k|≤C/u_k` as hypotheses. |
| §6.1 Prop. 6.1, multiscale telescoping (algebraic core) | `YangMills/Paper/MassGapAssembly.lean` (`telescoping`) | ✅ **verified** (oracle clean). Proved outright (no hypotheses) — the law-of-total-covariance telescoping stripped to `S 0 = S n + Σ (S k − S (k+1))`. |
| §6.3 Thm 6.3, UV summation over scales (`|∑R_k| ≤ M(1−r)⁻¹`) | `YangMills/Paper/UVSummation.lean` (`uv_geometric_summation`) | ✅ **verified** (oracle clean). **Unconditional** real analysis (geometric-tail bound); proved outright. The analytic core of the §6 "core new contribution" — the summability/finite-tail mechanism. |
| §7 Thm 7.1, mass-gap bound assembly (`|Cov| ≤ (C₁+C₂)e^{−min(m*,c₀)t}`) | `YangMills/Paper/MassGapAssembly.lean` (`mass_gap_bound`) | ✅ **verified** (oracle clean). Conditional on the IR clustering bound (§5) and UV suppression bound (§6.3) as hypotheses. |

**What the log certifies and does not:** each entry machine-checks the *internal
logic* of a paper step *given* its imported inputs as hypotheses. It does **not**
discharge those inputs (the uniform analyticity radius `R*`, the value `b₀`, the
KP/polymer bounds, OS1/O(4) covariance) — those remain the hard, unclosed content.
The honest reading: the paper's conditional *bookkeeping* is becoming verified; its
*foundations* (and the unconditional Clay claim) are not.

Next paper target (the big one): **Appendix A / §5 — KP ⇒ exponential clustering**,
which requires building a polymer cluster-expansion layer that Mathlib lacks. A
concrete, layered construction plan (types, lemmas, milestones KP0–KP4, honest
difficulty) is in **`docs/kp-cluster-expansion-plan.md`**. This is milestone M3:
large but *known* mathematics; landing it would turn the §5 input of
`mass_gap_bound` from an assumed hypothesis into a derived theorem.

### KP cluster-expansion layer — progress (2026-05-30)

Built and verified in `YangMills/KP/` (all oracle-clean, wired into `YangMillsCore`;
full build 8195 jobs green). ~20 theorems:

- **KP0/KP1** (`Basic.lean`): `PolymerSystem`, `partition`, `partition_empty`,
  `partition_singleton`, `partition_union` (factorization over compatible blocks).
- **KP2a** (`Cluster.lean`, `Ursell.lean`): incompatibility graph, `IsCluster`, the
  Ursell/Mayer coefficient with verified values φ(K₁)=+1, φ(K₂)=−1, φ(K₃)=+2, and
  `ursell_eq_zero_of_not_isCluster`.
- **KP2b identity side** (`Expansion.lean`, `SinglePolymer.lean`): the cluster sum
  (Mayer RHS), its support on clusters, and the empty / linear-order / **single-polymer**
  cases of `Ξ = exp(clusterSum)`. The n=1 identity
  (`partition_eq_exp_clusterSum_singlePolymer`) is a **complete theorem conditional on
  Target A**.
- **KP2b convergence side** (`Criterion.lean`, `Convergence.lean`): the KP smallness
  criterion + base estimates (`kp_activity_le`, `kp_neighbor_sum_le`) and the
  convergence back-half (`cluster_series_summable`, `cluster_sum_le`: geometric per-size
  bound ⇒ summable, sum ≤ C/(1−r)).
- **Bridges** (`Convergence.lean`): `mayer_log_series` (real) and `mayer_log_series_complex`
  (`∑ (−1)ⁿzⁿ⁺¹/(n+1) = log(1+z)`), and `closed_form_of_recurrence` (recurrence ⇒
  `(−1)ⁿn!`).

- **Target A — DONE (2026-06-09, `UrsellRecurrence.lean`).**
  `ursellComplete_recurrence` (`d(n+1) = −n·d(n)`) is **proved unconditionally**
  by the component-of-vertex-0 decomposition: the all-subgraphs signed sum on
  `K_{n+1}` (= 0 for n ≥ 1, `allSubgraphs_signedSum`) is fibered by the
  `reachSet` of vertex 0; fibers with ≥ 2 missing vertices vanish under a
  sign-reversing edge-toggle involution; the full fiber is `d(n+1)`; each of the
  `n` codimension-one fibers transports to `d(n)` along `Fin.succAbove`.
  Consequences now hypothesis-free (oracle `[propext, Classical.choice, Quot.sound]`):
  `ursellComplete_eq` (`φ(K_{n+1}) = (−1)ⁿ·n!`),
  `clusterSum_singlePolymer_eq_log`, `partition_singlePolymer_eq_exp`
  (the n=1 Mayer identity `Ξ = exp(clusterSum)`).
- **Target B — CLOSED** (superseding the "OPEN" note that was here).
  `kp_per_size_bound` (`KP/KPBound.lean`): `clusterWeight P n ≤
  (∑_y ‖activity y‖)·(e·A)ⁿ`, the geometric per-size bound via BFS-Penrose
  tree counting — proved oracle-clean, no axiom (ledger; the KP convergence
  back-half is now theorem-fed).  This is exactly the abstract
  Kotecký–Preiss framework the gauge-RG `hwK`/animal-count branch reuses
  (see `docs/BALABAN-SOURCE-BOUNDS.md` §6).

This is genuine M3 progress, all on the lattice / finite-volume side — **still ~0%
toward Clay** (§0), whose difficulty is the untouched continuum limit (M4–M5).

---

Lluis Eriksson — The Eriksson Programme. Update the percentage ledger (§0) and the
milestone done-tests (§1) honestly as nodes close; never report a number that a
`#print axioms` and an adversarial audit would not support.
