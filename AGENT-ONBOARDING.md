# AGENT ONBOARDING — everything another AI needs to advance this project

> **STATUS STAMP (2026-06-12).** This brief is current as of 2026-06-09; the
> repository has advanced since. Completed after this file was written: the
> finite-volume area law (linearized, ledger Addenda 12–15) and the
> **exact-activity area law** `finite_volume_area_law_exp` (Addendum 16) —
> core now green at **8235 jobs**. The live frontier is the volume-uniform
> constant (`docs/AREA-LAW-VU-PLAN.md`, start at V0). For the always-current
> picture read, in order: `CLAUDE.md` (hard rules) →
> `README-FOR-NEXT-MODEL.md` (live frontier) →
> `docs/VERIFICATION-LEDGER.md` (the record). Everything below remains valid
> as background.

This file is the **single complete brief** for an autonomous prover (AI or human) picking
up `THE-ERIKSSON-PROGRAMME`. It tells you exactly where the project is, how to build and
verify it, what is proved vs. open, the iron rules, and the precise next targets. Read it
top to bottom once before touching anything.

---

## 0. What this project is (and is not)

A Lean 4 / Mathlib formalization around the **Yang–Mills mass gap** (a Clay Millennium
Problem). The discipline is **honesty above progress**: every result is machine-checked,
the boundary between *proved* and *assumed/open* is kept razor-sharp, and hard unproved
inputs are carried as **explicit hypotheses, never as axioms**.

**Honest distance to the Clay prize: ~0% (<0.1%).** Everything proved here is on the
**lattice, in finite volume**. The Clay problem requires the **continuum limit** (4D) +
Osterwalder–Schrader/Wightman axioms + continuum mass gap — open mathematics nobody has
done for non-abelian 4D. *You cannot formalize what is unproved.* Do not attempt to "close
Clay"; attempts to do so are bugs until independently audited. The realistic reachable goal
is **M3: the strong-coupling lattice mass gap (Osterwalder–Seiler 1978)** — a *known*
theorem, hence formalizable.

---

## 1. Where it is / how to get it

- **Git remote:** `https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git`
- **Branch:** `main`  (always build/commit on `main` unless told otherwise)
- **Local path (this machine):** `C:\Users\lluis\Downloads\CoworkYangMills\THE-ERIKSSON-PROGRAMME`
- **Toolchain (pinned):** `leanprover/lean4:v4.29.0-rc6` (see `lean-toolchain`)
- **Build system:** Lake (`lakefile.lean`); Mathlib is a dependency (pinned in
  `lake-manifest.json`). Mathlib `.olean`s are cached under `.lake/packages/mathlib`.

### First-time setup
```powershell
git clone https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git
cd THE-ERIKSSON-PROGRAMME
elan toolchain install leanprover/lean4:v4.29.0-rc6   # if not present
lake exe cache get        # fetch prebuilt Mathlib oleans (do this; building Mathlib from source takes hours)
lake build YangMillsCore  # ~8200 jobs; fast if cache is warm
```

---

## 2. How to verify ANY result (the ground-truth loop)

Ground truth is the compiler + the axiom oracle, never anyone's say-so. To check a theorem
`Foo`:
```powershell
cd <repo>
lake build YangMillsCore
"import YangMillsCore`n#print axioms <fully.qualified.name.of.Foo>" | Set-Content _oc.lean
lake env lean _oc.lean
Remove-Item _oc.lean
```
**Required oracle on every result:** `[propext, Classical.choice, Quot.sound]` (some pure
algebra/induction lemmas are cleaner: `[propext, Quot.sound]` or `[propext]`). **Any other
axiom — especially a project-local one — means the honesty discipline was broken: reject /
revert.**

`YangMillsCore.lean` is the root: everything sound and reachable is imported there. If your
new file is not imported into `YangMillsCore`, it is not part of the verified core — wire it
in.

### Commit pattern (do not push broken code)
```powershell
lake build YangMillsCore; if ($?) { git add <files>; git commit -m "..."; git push }
```
The `if ($?)` guard ensures a failed build never reaches the remote.

---

## 3. The iron rules (FOUNDATIONS.md — do not violate)

1. **No `sorry`.** Ever, in anything imported by `YangMillsCore`.
2. **No project axioms.** Hard inputs (KP cluster bound, Balaban estimates, OS1/O(4),
   analyticity radius) enter as **explicit hypotheses** of a theorem, never as `axiom`.
3. **No vacuous targets.** A statement that type-checks but is trivially true is worthless.
   Apply the vacuity tests: can it be closed by a point mass / constant observable / the
   trivial group / `⟨1, one_pos⟩`? If yes, it is vacuous — do not count it.
4. **No laundering.** Dropping a hard theorem's premises to "prove" it is the wrong-axiom
   trap; forbidden.
5. **Keep the map honest.** Update `ROADMAP.md` §0 ledger and `HORIZON.md` DAG as nodes
   close; never report a number `#print axioms` + an adversarial audit would not support.
6. **`~0% to Clay` stays visible** in public statements. Lattice mass gap ≠ Clay prize.

---

## 4. Map of the verified core (what is proved)

Read these docs first: `FOUNDATIONS.md` (goalposts), `HORIZON.md` (formal DAG with Lean
signatures), `ROADMAP.md` (honest %-ledger + milestones), `docs/HANDOFF-KP.md` (the two
heavy KP targets), `docs/SESSION-2026-05-30.md` (latest session log).

**SU(N) Haar / centre-symmetry engine** (`YangMills/ClayCore/Schur*`, `CenterVanishing`,
`LeftInvariantVanishing`): the Z_N centre selection rules `∫ (tr U)^a·conj(tr U)^b = 0` for
`N ∤ (a−b)`, `∫|tr U|² ≤ N`, exact U(1) Fourier orthogonality, the general
eigenvalue-vanishing engine.

**KP / Mayer cluster expansion** (`YangMills/KP/`): polymer system, partition function +
factorization, incompatibility graph, Ursell coefficient (values φ(K₁,K₂,K₃)=+1,−1,+2),
the cluster sum (Mayer RHS), the empty/linear/**single-polymer** cases of `Ξ=exp(clusterSum)`,
the Kotecký–Preiss criterion + base bounds, and the geometric-convergence back-half.

**Lattice gauge observables** (`ClayCore/GaugeMarginal`, `GaugeEdgeExpectation`,
`GaugeMeasureProps`, `WilsonLine`, `WilsonLoopCenter`): single-edge marginal of the product
gauge measure, single-edge / multi-edge Wilson observable expectations, the full Z_N N-ality
grading on a lattice edge, `wilsonLine`/`wilsonLoop` algebra (composition, flatten,
gauge-action, centre scaling `z^L`, scalar-centre eigenvalue `ω^L`), and the second-moment
bound in `[0,N]`.

**Paper §4/§6/§7 conditional skeleton + M3 bridge** (`YangMills/Paper/`): `coupling_control`,
`telescoping`, `uv_geometric_summation`, `mass_gap_bound`, and **`ClusteringToGap.lean`**:
`clustering_gives_exponential_decay` (geometric cluster bound ⟹ exp decay, mass `m*=-log r>0`),
`lattice_mass_gap_of_clustering` (full M3 assembly: IR cluster bound + UV suppression ⟹
positive gap), and finite-susceptibility corollaries.

---

## 5. The open targets (where to actually push — in priority order)

These are the genuine frontier. Each is carried with **no axiom** — closing one discharges a
hypothesis or proves an open lemma.

**T1 — KP Target A: `ursellComplete_recurrence` — CLOSED (2026-06-09).**
Proved unconditionally in `YangMills/KP/UrsellRecurrence.lean` (component-of-vertex-0
decomposition: `reachSet` fibering + sign-reversing edge-toggle involution +
`Fin.succAbove` relabeling). `ursellComplete_eq` (`φ(K_{n+1}) = (−1)ⁿ·n!`) and the n=1
Mayer identity (`partition_singlePolymer_eq_exp`) are now hypothesis-free, oracle-clean,
and wired into `YangMillsCore`.

**T2 — KP Target B: `kp_per_size_bound`** (`docs/HANDOFF-KP.md`).
Goal: the size-`n` cluster weight obeys a geometric bound (the Penrose tree-graph inequality).
Feeding it into the verified back-half (`cluster_series_summable`/`cluster_sum_le`) closes KP
convergence — and supplies the cluster bound that `lattice_mass_gap_of_clustering` takes as
hypothesis. Needs spanning-tree enumeration (Cayley-type counting), **not in Mathlib**; may
need its own development. **Needs interactive Lean.**

**T3 — LG6 measure step:** `IsMulLeftInvariant (gaugeMeasureFrom μ)` under the diagonal centre
action, then combine with `wilsonLoop_scalarCenter_smul` (already proved, gives the `ω^L`
eigenvalue) to get the Wilson-loop selection rule `⟨W⟩ = 0 ⟺ N ∤ L`. Instance/transport
plumbing on `GaugeConfig`. **Needs interactive Lean.**

**T4 — LG7 (large): strong-coupling character expansion** → area law. Needs **Peter–Weyl for
compact groups**, which is NOT in Mathlib — this is a major standalone formalization (or a
Weingarten-calculus route for low moments). The genuine analytic content of M3.

**Beyond (M4–M5, the Clay wall): continuum limit + OS/Wightman.** Open mathematics. Do not
attempt to formalize until it exists on paper. See `HORIZON.md §4` for the precise open
statement and why Bałaban's program is the deepest incomplete attempt.

---

## 6. Practical notes / gotchas (paid for already)

- Mathlib renames: `div_lt_iff₀` (not `div_lt_iff`), `abs_add_le` (not `abs_add`),
  `Finset.eq_empty_iff_forall_notMem`. Check the pinned Mathlib source in `.lake/packages/mathlib`
  for exact names before using a lemma — this avoids most build failures.
- Non-commutative ordered products need `List.prod`, NOT `Finset.prod` (which needs `CommMonoid`).
- The Wilson **loop** is `tr(matrix product)`, NOT a scalar edge product — the Fubini
  factorization (`integral_prod_edges`) does NOT apply to it, and a closed loop does NOT vanish
  in general (it carries `ω^L`; that is the area-law contributor). See `HORIZON.md` LG6.
- `#print axioms` is the only honesty check that matters. Run it on every new headline result.
- Build is ~8200 jobs; with a warm Mathlib cache an incremental build is fast.

---

## 7. The autonomy experiment (what to measure)

The honest score is **the number of audited `[STUB]→[DONE]` conversions on the non-vacuous
path** (T1–T4), each verified by `lake build` + `#print axioms` + an adversarial audit that
the statement is non-vacuous and axiom-free. A single genuine T1 or T2 closure is worth more
than any amount of routine API. Do **not** optimize for theorem count; optimize for closing
the real open lemmas without breaking §3.

— The Eriksson Programme. Keep it honest.
