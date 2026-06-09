# Verification ledger — release audit of the KP/Penrose campaign

**Date:** 2026-06-10 · **Commit range audited:** `360bf3d..a3343f1` (30 commits)
**Build:** `lake build YangMillsCore` — **8209 jobs, green.**
**Source scan:** zero literal `sorry`/`axiom` declarations in `YangMills/KP/`
(and `YangMillsCore`'s import closure avoids `Experimental/` entirely).

## Oracle outputs (verbatim, single batch run)

Every headline result of the campaign, checked in one `lake env lean` pass:

```
'YangMills.KP.ursellComplete_recurrence'            [propext, Classical.choice, Quot.sound]
'YangMills.KP.ursellComplete_eq'                    [propext, Classical.choice, Quot.sound]
'YangMills.KP.partition_singlePolymer_eq_exp'       [propext, Classical.choice, Quot.sound]
'YangMills.KP.interval_signed_sum'                  [propext, Classical.choice, Quot.sound]
'YangMills.KP.abs_signedSum_le_of_scheme'           [propext, Classical.choice, Quot.sound]
'YangMills.KP.penroseTree_mem_spanningTrees'        [propext, Classical.choice, Quot.sound]
'YangMills.KP.penrose_hfiber'                       [propext, Classical.choice, Quot.sound]
'YangMills.KP.abs_ursell_le_card_spanningTrees'     [propext, Classical.choice, Quot.sound]
'YangMills.KP.abs_ursell_le_treeCount'              [propext, Classical.choice, Quot.sound]
'YangMills.KP.treeCount_le_pow'                     [propext, Classical.choice, Quot.sound]
'YangMills.KP.succ_pow_le_exp_mul_factorial'        [propext, Classical.choice, Quot.sound]
'YangMills.KP.tree_walk_bound'                      [propext, Classical.choice, Quot.sound]
'YangMills.KP.tree_assignment_sum_le'               [propext, Classical.choice, Quot.sound]
'YangMills.KP.kp_per_size_bound'                    [propext, Classical.choice, Quot.sound]
'YangMills.KP.kp_convergence'                       [propext, Classical.choice, Quot.sound]
'YangMills.KP.kp_norm_clusterSum_le'                [propext, Classical.choice, Quot.sound]
'YangMills.KP.norm_clusterSum_le'                   [propext, Classical.choice, Quot.sound]
'YangMills.lattice_mass_gap_of_clustering_uniform'  [propext, Classical.choice, Quot.sound]
```

No declaration depends on anything beyond Lean's three standard axioms.

## What these are (plain language, with references)

* **Target A (closed):** the Ursell/Mayer coefficient on complete graphs
  satisfies `d(n+1) = −n·d(n)`, hence `φ(K_{n+1}) = (−1)ⁿ·n!`; the n=1 Mayer
  identity `Ξ = exp(clusterSum)` follows unconditionally.  [Classical
  cluster-expansion combinatorics; see e.g. Friedli–Velenik, *Statistical
  Mechanics of Lattice Systems*, Ch. 5.]
* **Penrose tree-graph inequality (closed):** `|φ(X)| ≤ #spanning trees of
  the incompatibility graph` — O. Penrose, *Convergence of fugacity
  expansions for fluids and lattice gases*, J. Math. Phys. 4 (1963) /
  partition-scheme form 1967; proved here via the greedy BFS scheme with
  Boolean-interval fibers.
* **Tree counting (closed):** `treeCount (m+1) ≤ (m+1)^(m+1)` by injectivity
  of the greedy parent map — sufficient (with `(n+1)ⁿ ≤ eⁿ·n!`) for the KP
  bound; no Prüfer bijection required.
* **Target B (closed):** the Kotecký–Preiss per-size estimate
  `clusterWeight P n ≤ (∑‖z‖)·(e·A)ⁿ` and convergence of the Mayer series
  for `e·A < 1` — R. Kotecký & D. Preiss, *Cluster expansion for abstract
  polymer models*, Comm. Math. Phys. 103 (1986); proved here under the
  **uniform** smallness `e·max(a) < 1` (slightly stronger than sharp KP;
  refinable).
* **M3 bridge (conditional, proved):** geometric IR cluster bound + UV
  suppression ⟹ uniform exponential decay with one positive gap
  (Osterwalder–Seiler-type assembly; the IR/UV inputs remain explicit
  hypotheses pending the polymer representation and UV bound).

## Addendum (2026-06-10, autonomous overnight session): T3 closed

Additional headline results, each `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, core green at 8212 jobs:

```
'YangMills.integral_centerAct'                       (gauge measure centre-invariant)
'YangMills.integral_wilsonLoop_eq_zero'              (selection rule, matrix units, abstract)
'YangMills.integral_wilsonLoopSU_eq_zero'            (selection rule at genuine SU(n) Haar)
'YangMills.wilsonAction_centerAct'                   (exact centre symmetry of the Wilson action)
'YangMills.integral_centerAct_gibbs'                 (interacting Gibbs measure centre-invariant)
'YangMills.integral_wilsonLoopSU_gibbs_eq_zero'      (Z_n selection rule, interacting, any β)
```

Plain language: the centre `Z_n ⊂ SU(n)` acts on lattice gauge fields by
multiplying every positively-oriented edge by `ω = e^{2πi/n}`; the product
Haar measure is invariant (Haar), and the Wilson action is *exactly*
invariant because every plaquette crosses two edges forward and two backward
(net centre charge zero).  A Wilson loop of length `L` is an eigenfunction
with eigenvalue `ω^L`, so its expectation — free **or interacting, at any
coupling** — vanishes unless `n | L`.  This is the lattice N-ality selection
rule (centre symmetry; cf. 't Hooft's centre-symmetry analyses and standard
LGT texts, e.g. Montvay–Münster §3), now machine-checked end to end.
Loops here are positively-oriented edge lists; the signed-length
generalization is routine and noted in `docs/T3-LG6-PLAN.md`.

## Addendum 2 (2026-06-10, continued autonomous session): polymer rep. step 1

Headline results, each `#print axioms` = `[propext, Classical.choice, Quot.sound]`:

```
'YangMills.boltzmann_eq_sum_plaquetteSets'           (exp(-βS) = Mayer sum over plaquette sets)
'YangMills.partitionFunction_eq_sum_plaquetteSets''  (Z as polymer-gas sum, UNCONDITIONAL for
                                                      bounded measurable energies)
'YangMills.abs_plaquetteWeight_le'                   (|f_p| ≤ e^{|β|B} − 1, KP smallness seed)
'YangMills.measurable_plaquetteHolonomy'             (holonomies measurable)
'YangMills.integrable_boltzmann'                     (Boltzmann weight integrable, bounded pe)
'YangMills.partitionFunction_pos''                   (Z > 0, integrability hypothesis ELIMINATED)
'YangMills.gibbsMeasure_isProbability''              (Gibbs probability, hypothesis ELIMINATED)
```

Plain language: the Gibbs weight expands as `∏_p (1 + f_p)` with Mayer
weights `f_p = e^{-βE_p} − 1`, turning the partition function into a gas of
plaquette sets with activities uniformly `≤ e^{|β|B} − 1` — the
high-temperature polymer representation (standard; e.g. Montvay–Münster,
Seiler, *Gauge Theories as a Problem of Constructive QFT*), step 1 of
connecting the verified KP convergence to the lattice Gibbs theory.  The
integrability hypotheses previously carried by `partitionFunction_pos` and
`gibbsMeasure_isProbability` are now discharged for bounded measurable
plaquette energies (e.g. `Re tr` on a compact group).

## Scope statement (the honest line)

Everything above is **lattice, finite-volume, M3-side**.  None of it reduces
any M4/M5/Clay obstruction (continuum limit, OS/Wightman reconstruction,
continuum mass gap — open mathematics).  Distance to the Clay prize:
**~0% (<0.1%), unchanged.**

Reproduce this audit:
```powershell
lake build YangMillsCore
# then #print axioms on any name above via lake env lean
```
