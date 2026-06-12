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

## Addendum 3 (2026-06-10, autonomous loop, final): observables + correlators

Each `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
core green at 8214 jobs:

```
'YangMills.norm_wilsonLoopSU_le'                     (|W| ≤ n: trace bound on SU(n))
'YangMills.measurable_wilsonLoopSU'                  (W measurable; SU(n) MeasurableMul₂/Inv
                                                      instances built componentwise)
'YangMills.integrable_wilsonLoopSU_gibbs'            (W integrable under Gibbs — the
                                                      selection-rule expectations are
                                                      well-defined integrals)
'YangMills.integral_wilsonLoopSU_mul_gibbs_eq_zero'  (CORRELATOR selection rule: two-loop
                                                      Gibbs correlators vanish unless
                                                      n | L+L', any coupling)
```

Status of the M3 campaign after this run: T1 ✓, T2 (full KP convergence) ✓,
T3 (selection rules, free + interacting + correlator, with integrability) ✓,
polymer representation step 1 ✓ with three integrability hypotheses
eliminated.  Remaining: polymer step 2 (connected grouping + independence
factorization of the product measure — next campaign, multi-session),
UV bound, T4.  M4/M5: class C, open mathematics.

## Addendum 4 (2026-06-10, continued loop): the lattice gas, end to end

Each `#print axioms` = `[propext, Classical.choice, Quot.sound]`:

```
'YangMills.plaquetteWeight_congr' / 'prod_plaquetteWeight_congr'   (locality)
'YangMills.integral_mul_of_disjoint_deps'                          (two-block independence,
                                                                    product measures, no hypotheses)
'YangMills.integral_prod_plaquetteWeight_mul_of_disjoint'          (gauge-level factorization)
'YangMills.integral_prod_prod_plaquetteWeight_of_pairwiseDisjoint' (iterated/component form)
'YangMills.latticePolymerSystem' (+ Fintype)                       (the physical polymer system)
'YangMills.norm_latticePolymerSystem_activity_le'                  (‖z(c)‖ ≤ (e^{|β|B}−1)^{|c|})
'YangMills.latticePolymerSystem_kpCriterion'                       (KP criterion, a = |c|)
'YangMills.latticePolymerSystem_kpCriterion_scaled'                (KP criterion, a = t|c|)
'YangMills.latticeClusterSum_summable'                             (LATTICE MAYER SERIES CONVERGES)
'YangMills.norm_latticeClusterSum_le'                              (explicit bound)
'YangMills.abs_partitionFunction_sub_one_le'                       (|Z−1| ≤ (e^{|β|B})^{#P} − 1)
'YangMills.partitionFunction_pos_of_small'                         (quantitative Z > 0)
```

Plain language: the cluster expansion of finite-volume SU(N) lattice gauge
theory at small coupling is now machine-checked from the Boltzmann factor to
absolute convergence with explicit constants, with the partition function
quantitatively pinned near 1.  Thresholds are volume-dependent; the
volume-uniform refinement (connected polymers, lattice-animal entropy) is
the scoped remaining step.  All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 5 (2026-06-10, continued loop): VOLUME-UNIFORMITY

The entropy campaign (`ConnectedEntropy.lean`), opened and **closed** in one
session.  Each `#print axioms` = `[propext, Classical.choice, Quot.sound]`:

```
'YangMills.FinBox.shift_injective' / 'mem_plaquetteSupport_iff'   (local geometry)
'YangMills.card_plaquettesThroughEdge_le'                         (≤ 4d plaquettes per edge)
'YangMills.card_plaquettesTouching_le'                            (DEGREE BOUND: ≤ 16d, volume-free)
'YangMills.card_relWalks_le'                                      (walk counting: ≤ Δ^L walks)
'YangMills.IsLazyClosedWalk.extend'                               (splice lemma)
'YangMills.exists_adj_crossing_of_walk'                           (first-exit crossing)
'YangMills.exists_covering_lazyWalk'                              (COVERING-WALK THEOREM)
'YangMills.isConnectedPolymer_crossing'                           (crossing for connected polymers)
'YangMills.card_connectedPolymers_le'                             (LATTICE-ANIMAL ENTROPY BOUND:
                                                                   ≤ (16d+1)^{2n} animals of size n+1
                                                                   through a point, volume-free)
'YangMills.sum_connectedPolymers_through_le'                      (per-plaquette geometric bound)
'YangMills.connectedLatticePolymerSystem_kpCriterion_volumeUniform'
                                                                  (THE VOLUME-UNIFORM KP CRITERION)
```

Plain language: connected plaquette sets are ranges of lazy closed walks
(greedy growth via splicing), walks are counted by the degree bound `16d`,
so there are at most `(16d+1)^{2n}` connected polymers of size `n+1` through
any plaquette — **independent of the lattice volume** (standard
lattice-animal counting; cf. Friedli–Velenik Ch. 5/6, Simon, *The
Statistical Mechanics of Lattice Gases*).  Consequently the Kotecký–Preiss
criterion for the connected lattice gas holds under smallness conditions on
`β` depending **only on the dimension** — the volume-dependence caveat of
addendum 4 is **eliminated at the criterion level**.

~~Honest remaining caveat: composing this with our formalized KP
*convergence* theorem still passes through the uniform bound `a(c) ≤ A`~~
**RESOLVED — see addendum 6.**

## Addendum 6 (2026-06-10, the sharp-KP completion) — VOLUME-UNIFORM
CONVERGENCE, the campaign endpoint

**Build:** `lake build YangMillsCore` — 8223 jobs, green, at `708d318`.
**Source scan:** zero `sorry`/`axiom` in `YangMills/KP/` (unchanged).

Oracle outputs (verbatim):

```
'YangMills.KP.per_k_bound'                            [propext, Classical.choice, Quot.sound]
'YangMills.KP.rho_sum_le_price'                       [propext, Classical.choice, Quot.sound]
'YangMills.KP.treeSumRaw_succ_le'                     [propext, Classical.choice, Quot.sound]
'YangMills.KP.treeSumB_succ_le'                       [propext, Classical.choice, Quot.sound]
'YangMills.KP.treeSumB_le_kpMajorant'                 [propext, Classical.choice, Quot.sound]
'YangMills.KP.treeSumB_le_exp'                        [propext, Classical.choice, Quot.sound]
'YangMills.KP.kp_pinned_cluster_bound'                [propext, Classical.choice, Quot.sound]
'YangMills.KP.pinned_cluster_summable_sharp'          [propext, Classical.choice, Quot.sound]
'YangMills.KP.kp_clusterWeight_summable_sharp'        [propext, Classical.choice, Quot.sound]
'YangMills.KP.kp_convergence_sharp'                   [propext, Classical.choice, Quot.sound]
'YangMills.KP.kp_norm_clusterSum_le_sharp'            [propext, Classical.choice, Quot.sound]
'YangMills.connectedLatticeClusterSum_summable_volumeUniform'
                                                      [propext, Classical.choice, Quot.sound]
'YangMills.connectedLatticeClusterSum_norm_le_volumeUniform'
                                                      [propext, Classical.choice, Quot.sound]
```

Plain language: the **sharp (weight-respecting) Kotecký–Preiss bound is
fully machine-checked** — `∑_n (truncated pinned cluster sums) ≤
‖z(c)‖·e^{a(c)}` under the bare criterion, with NO uniform majorant of
the weights and NO geometric smallness hypothesis (FV Thm 5.4-level,
via the shell decomposition of `SharpShell.lean`: Penrose domination →
rooted depth-`D` tree-sums → block factorization priced by the
multinomial → the Borel-sum recursion `B_{D+1} ≤ exp(∑ ‖z‖·B_D)` →
induction to the `kpMajorant` → `e^{a(c)}`).  Composed with the
volume-uniform criterion (addendum 5), the Mayer cluster series of the
connected lattice polymer gas **converges absolutely under β-smallness
depending only on the dimension** — the `hA` caveat of addendum 5 is
eliminated; nothing in the convergence hypotheses references the
lattice volume.  All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 7 (2026-06-10, the Mayer–Ursell inversion) — THE
FUNDAMENTAL THEOREM OF CLUSTER EXPANSIONS

**Build:** `lake build YangMillsCore` — green at `b8dd5ee`.
**Source scan:** zero `sorry`/`axiom` in `YangMills/KP/` (unchanged).

Oracle outputs (verbatim, the headline chain of
`KP/MayerInversion.lean`):

```
'YangMills.KP.ursell_partition_identity'              [propext, Classical.choice, Quot.sound]
'YangMills.KP.sum_compat_eq_ordp'                     [propext, Classical.choice, Quot.sound]
'YangMills.KP.admissible_card_sum_eq'                 [propext, Classical.choice, Quot.sound]
'YangMills.KP.partition_univ_eq_cluster_layers'       [propext, Classical.choice, Quot.sound]
'YangMills.KP.tsum_pow_eq_tsum_pi'                    [propext, Classical.choice, Quot.sound]
'YangMills.KP.summable_H'                             [propext, Classical.choice, Quot.sound]
'YangMills.KP.exp_tsum_eq_tsum_H'                     [propext, Classical.choice, Quot.sound]
'YangMills.KP.tsum_H_eq_tsum_layers'                  [propext, Classical.choice, Quot.sound]
'YangMills.KP.partition_eq_exp_clusterSum'            [propext, Classical.choice, Quot.sound]
'YangMills.KP.partition_eq_exp_clusterSum_of_kp'      [propext, Classical.choice, Quot.sound]
```

Plain language: **`Ξ = exp(clusterSum)` is fully machine-checked** —
for every finite polymer system with absolutely convergent cluster
series, and outright under the bare KP criterion (the sharp theory of
addendum 6 supplies the convergence).  This was the "months-long crux"
recorded in `Expansion.lean`'s header (E3, the deferred Mayer–Ursell
inversion).  The proof: the partition identity (sums of block-Ursell
products over all `Finpartition`s = the compatibility indicator,
via component-partition fibrations of the alternating subgraph sums),
the π-collapse to ordered partitions, the exact function-space split,
the multinomial count `#ordp(m)·∏mᵢ! = N!`, the injective collapse to
admissible sets, and the analytic shell (power Fubini, the master
sigma-sum, size regrouping with finite layers, tail-kill).  This
unlocks the cluster-correlation chain (`docs/CLUSTER-CORRELATION-PLAN.md`
Half B): correlators as differences of `log Ξ`-type quantities are now
expressible through cluster sums with the proved volume-uniform decay
engine (Half A).  All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 8 (2026-06-11, the connecting decay + the `Z = Ξ` gate)

**Build:** `lake build YangMillsCore` — green at `6bba786` (8227 jobs).
**Source scan:** zero `sorry`/`axiom` in
`YangMills/L1_GibbsMeasure/` and `YangMills/KP/` (unchanged).

Oracle outputs (verbatim):

```
'YangMills.cluster_dist_le'                           [propext, Classical.choice, Quot.sound]
'YangMills.connecting_cluster_decay'                  [propext, Classical.choice, Quot.sound]
'YangMills.plaqComponents_biUnion'                    [propext, Classical.choice, Quot.sound]
'YangMills.plaqComponents_not_touching'               [propext, Classical.choice, Quot.sound]
'YangMills.plaqComponents_support_disjoint'           [propext, Classical.choice, Quot.sound]
'YangMills.plaqComponents_isConnectedPolymer'         [propext, Classical.choice, Quot.sound]
'YangMills.plaqComponents_biUnion_eq'                 [propext, Classical.choice, Quot.sound]
'YangMills.plaqComponents_disjoint'                   [propext, Classical.choice, Quot.sound]
'YangMills.mem_componentFamily_iff'                   [propext, Classical.choice, Quot.sound]
'YangMills.prod_componentFamily'                      [propext, Classical.choice, Quot.sound]
'YangMills.partitionFunction_eq_partition'            [propext, Classical.choice, Quot.sound]
'YangMills.partitionFunction_eq_exp_clusterSum'       [propext, Classical.choice, Quot.sound]
```

Plain language: two campaign endpoints.  (1) **The volume-uniform IR
decay mechanism** (`connecting_cluster_decay`,
`L1_GibbsMeasure/ClusterGeometry.lean`): the total pinned cluster sum
over clusters through `p` that also touch `q` is bounded by
`exp(−ε·d(p,q)/2)·x/(1−(16d+1)²x)` — every constant depends only on
`d, B, β, t, ε`.  (2) **The measure-side identification**
(`partitionFunction_eq_partition`,
`L1_GibbsMeasure/PolymerRepresentation.lean`): the Wilson-action
partition function equals the polymer-gas partition function of the
connected lattice gas — proved by the component bijection
(`plaqComponents`: parts of the reachability partition of the
touching graph; `componentFamily`: their instance-free polymer lift),
with values matched by the polymer factorization integral.  Composed
with addendum 7: **`Z = exp(clusterSum)` at high temperature**, hence
`Z ≠ 0`, with volume-uniform constants.  What remains for the IR
hypothesis of `lattice_mass_gap_of_clustering_uniform`: B2 (the
covariance identity for deformed gases) + B4 (assembly).  All M3
lattice-side; M4/M5/Clay untouched.

## Addendum 9 (2026-06-11, the weighted gas + THE COVARIANCE IDENTITY)

**Build:** `lake build YangMillsCore` — green at `c700d42` (8228 jobs).
**Source scan:** zero `sorry`/`axiom` (unchanged).

Oracle outputs (verbatim):

```
'YangMills.integral_prod_prod_weight_of_pairwiseDisjoint'  [propext, Classical.choice, Quot.sound]
'YangMills.weightedPartition_eq_sum'                  [propext, Classical.choice, Quot.sound]
'YangMills.weightedPartition_plaquetteWeight'         [propext, Classical.choice, Quot.sound]
'YangMills.weightedPartition_eq_partition'            [propext, Classical.choice, Quot.sound]
'YangMills.weightedLatticePolymerSystem_kpCriterion_volumeUniform'
                                                      [propext, Classical.choice, Quot.sound]
'YangMills.weightedPartition_eq_exp_clusterSum'       [propext, Classical.choice, Quot.sound]
'YangMills.weightedPartition_deform'                  [propext, Classical.choice, Quot.sound]
'YangMills.cluster_term_four_cancel'                  [propext, Classical.choice, Quot.sound]
'YangMills.clusterSum_inclusion_exclusion'            [propext, Classical.choice, Quot.sound]
'YangMills.covariance_identity'                       [propext, Classical.choice, Quot.sound]
```

Plain language: the entire `Z = Ξ = exp(K)` chain now holds for
**arbitrary bounded measurable local weight families**, volume-uniformly
(`WeightedGas.lean` + `PolymerRepresentation.lean`).  Multiplicative
local observables `∏_{p∈T}(1+g_p)` absorb into deformed weights, the
four-gas inclusion–exclusion `K_{FG}+K−K_F−K_G` cancels termwise off
clusters connecting the two regions, and the endpoint is

    Z[FG]·Z = Z[F]·Z[G]·exp(connecting cluster sum)

— **the covariance identity**, division-free, with all constants
depending only on `d`, the weight bounds, and `t`.  Remaining for the
IR side of M3: bound the connecting sum by the (already proved,
Wilson-gas) exponential decay mechanism transported to the weighted
gas, and assemble `hIRbound`.  All M3 lattice-side; M4/M5/Clay
untouched.

## Addendum 10 (2026-06-11, B4 complete) — THE IR CLUSTERING BOUND,
END TO END

**Build:** `lake build YangMillsCore` — green at `e1de69b`.
**Source scan:** zero `sorry`/`axiom` (unchanged).

Oracle outputs (verbatim, the B4 chain):

```
'YangMills.sum_connecting_le_succ_mul_pinned'         [propext, Classical.choice, Quot.sound]
'YangMills.weighted_unitTilt_kpCriterion_volumeUniform'
                                                      [propext, Classical.choice, Quot.sound]
'YangMills.weighted_unitTilt_connecting_pinned_le_GE' [propext, Classical.choice, Quot.sound]
'YangMills.weighted_connecting_cluster_decay''        [propext, Classical.choice, Quot.sound]
'YangMills.connecting_layer_le_pinned'                [propext, Classical.choice, Quot.sound]
'YangMills.weighted_nfac_pinned_le_GE'                [propext, Classical.choice, Quot.sound]
'YangMills.weighted_connecting_sum_decay'             [propext, Classical.choice, Quot.sound]
'YangMills.weighted_connecting_sum_summable'          [propext, Classical.choice, Quot.sound]
'YangMills.covariance_exponent_norm_bound'            [propext, Classical.choice, Quot.sound]
'YangMills.truncated_correlation_bound'               [propext, Classical.choice, Quot.sound]
'YangMills.wilson_truncated_correlation_bound'        [propext, Classical.choice, Quot.sound]
'YangMills.gibbs_truncated_correlation_bound'         [propext, Classical.choice, Quot.sound]
```

The final form (`gibbs_truncated_correlation_bound`): for observables
`O_R = ∏_{p∈R}(1+g_p)` over disjoint supports `S, T` at
touching-distance `≥ 2k`, in genuine Gibbs integrals over the Wilson
Boltzmann weight,

    |∫O_S·O_T·e^{−βS}·Z − ∫O_S·e^{−βS}·∫O_T·e^{−βS}| ≤ C·e^{−ε·k},

real absolute values, `C` explicit and volume-free.  Divide by
`Z² > 0` (`partitionFunction_pos'`) for the normalized covariance.

And the M3 adapter (`lattice_mass_gap_of_exp_clustering_uniform`,
`Paper/ClusteringToGap.lean`, oracle clean): the uniform lattice mass
gap consuming the IR bound in exactly this `e^{−εk}` shape
(`r := e^{−ε}`).  **The IR hypothesis of the strong-coupling lattice
mass gap is now fed by a theorem; the only hypothesis-carried input
left in the M3 assembly is the §6.3 single-scale UV bound (the
Balaban input, deliberately carried — never an axiom).**

And the T4 shortcut (`two_plaquette_correlator_bound`,
`L1_GibbsMeasure/TwoPlaquetteCorrelator.lean`, oracle clean at
`[propext, Classical.choice, Quot.sound]`): the connected
two-plaquette correlator of ANY bounded measurable holonomy
observable decays exponentially in the touching-distance at small
`β`, volume-free — the `kp_cluster_decay`-shaped endpoint of
`PETER_WEYL_ROADMAP.md` Layer 4, reached WITHOUT Peter–Weyl, Schur
orthogonality, or the Osterwalder–Seiler character expansion (those
layers were routes to polymer bounds the weighted-Mayer campaign
produced directly).  Peter–Weyl remains the route for the
area-law/Wilson-loop form.

And the normalized finale
(`two_plaquette_correlator_bound_normalized`, oracle clean): dividing
by `Z² > 0` cancels the partition function from the constant —

    |⟨f_p·f_q⟩ − ⟨f_p⟩·⟨f_q⟩| ≤ (8·M·(1+s)²/s²)·e^{−ε·k},

the genuine Gibbs covariance of bounded local holonomy observables,
with the constant depending only on `d, β, B, s, t, ε` — independent
of the lattice volume AND of `Z`.  **Exponential clustering of the
lattice gauge theory's two-point functions at small coupling is
machine-checked end to end.**

Non-vacuity (adversarial audit, `clustering_window_nonempty`, oracle
clean): at `t = ε = 1` the three smallness hypotheses are
simultaneously satisfiable for every dimension, with explicit
`δ₀(d) = ((K²+64d+8)·e³)⁻¹ > 0`; the `(β, s)`-window is nonempty —
the clustering theorems are not vacuous.

And the SU(N) capstone (`sun_two_plaquette_correlator_bound`, oracle
clean at `[propext, Classical.choice, Quot.sound]`): the clustering
bound instantiated at the **genuine** Yang–Mills data — the gauge
group `SU(N_c)`, the Haar probability measure `sunHaarProb`, the
Wilson plaquette energy `Re tr U` (bounded by `N_c`).  **Exponential
clustering of two-point functions for the SU(N) Wilson lattice gauge
theory at strong coupling — actual group, actual measure, actual
action — with constants in `d, N_c, β, s, t, ε` only.**  Still M3
lattice-side; the continuum (M4/M5/Clay) untouched.

With its own non-vacuity witness
(`sun_clustering_window_nonempty`, oracle clean): for every `d, N_c`
an EXPLICIT coupling window `β₀ = log(1+δ₁/4)/N_c > 0` and scaling
`s = δ₁/4` (with `δ₁ = min(δ₀(d), 1)`) in which every hypothesis of
the SU(N) capstone holds, at `t = ε = 1`, for every separation.

Plain language: **the infrared clustering bound of the strong-coupling
lattice theory is machine-checked end to end.**  For multiplicative
local observables with supports at touching-distance `≥ 2k`,

    ‖Z[FG]·Z − Z[F]·Z[G]‖ ≤ C·e^{−ε·k},

`C` explicit (`8|S||T|·y'/(1−Ky')·‖Z[F]‖·‖Z[G]‖`) and volume-free,
under high-temperature smallness depending only on the dimension and
the weight bounds.  The chain: the covariance identity (`Z = Ξ =
exp(K)` for all four deformed gases), the inclusion–exclusion
(supported on connecting clusters), the symmetrization (`(n+1)`
absorbed into a unit tilt), the per-layer pinning, and the
volume-uniform connecting decay.  Dividing by `Z² > 0` gives
`|⟨FG⟩−⟨F⟩⟨G⟩| ≤ C'·e^{−εk}` — exactly the `hIRbound` hypothesis of
`lattice_mass_gap_of_clustering_uniform` (M3's IR input).  The
remaining M3 inputs are the UV single-scale bound (§6.3, content not
yet in the repo) and the Wilson-loop/area-law route (T4).  All M3
lattice-side; M4/M5/Clay untouched.

## Addendum 12 (2026-06-11, area-law campaign: AL1–AL3 closed, AL4
mostly closed, AL5 interface closed)

**Builds:** `lake build YangMillsCore` — green at `ad58393` (8229),
`9f3c322` (8230), `9dea6c1` (8231), `c985d45`/`4f1a534` (8232 jobs).
**Source scan:** zero `sorry`/`axiom` (unchanged).

Oracle outputs (verbatim, the area-law bricks):

```
'YangMills.chainBoundary₁_plaquetteChain'              [propext, Classical.choice, Quot.sound]
'YangMills.chainBoundary₁_comp_chainBoundary₂'         [propext, Classical.choice, Quot.sound]
'YangMills.chainArea_le'                               [propext, Classical.choice, Quot.sound]
'YangMills.exists_minimal_spanning'                    [propext, Classical.choice, Quot.sound]
'YangMills.chainBoundary₁_eq_zero_of_spans'            [propext, Classical.choice, Quot.sound]
'YangMills.chainArea_le_card_of_support_subset'        [propext, Classical.choice, Quot.sound]
'YangMills.chainSupport_indicatorChain_subset'         [propext, Classical.choice, Quot.sound]
'YangMills.integral_mul_of_disjoint_deps_complex'      [propext, Classical.choice, Quot.sound]
'YangMills.integral_single_coord_marginal'             [propext, Classical.choice, Quot.sound]
'YangMills.integral_mul_prod_one_add'                  [propext, Classical.choice, Quot.sound]
```

Content (`docs/AREA-LAW-PLAN.md` for the design):

* **AL1+AL2** (`L0_Lattice/ChainComplex.lean`): the lattice chain
  complex over an arbitrary `CommRing R` — `∂₁∘∂₂ = 0` from the
  `FiniteLatticeGeometry` square-closure axioms; `chainArea` as the
  minimal spanning-surface size with its defining bound, attainment,
  and closedness of spannable chains.  `R := ℤ` is the integral
  theory, `R := ZMod N_c` the `N`-ality theory the Haar selection
  rule feeds.
* **AL3** — closed by audit: `sunHaarProb_fundMonomial_integral_zero`
  (banked) IS the per-edge balance criterion.
* **AL4 substrate + expansion** (`EdgeFactorization.lean`,
  `WilsonLoopExpansion.lean`): the `ℂ`-valued two-block independence
  factorization, the single-coordinate marginalization (the per-edge
  integration step), and the integral-level binomial expansion
  `∫ W·∏(1+f_p) = ∑_S ∫ W·∏_{p∈S} f_p`.
* **AL5 interface**: a spanning chain supported in `S` bounds the
  (`N`-ality) area by `|S|`.

Open in the campaign: the per-edge monomial bookkeeping connecting a
non-vanishing expansion term to a balanced `ZMod N_c` chain (the
AL4/AL5 join), then AL6 (entropy + tail + non-vacuity window).  All
M3 lattice-side; M4/M5/Clay untouched.

## Addendum 13 (2026-06-11, AL4.5 join: kill pipeline closed end to
end — the β=0 Wilson-loop selection rule)

**Builds:** `lake build YangMillsCore` — green at `9430b58` (8233),
`4377f85`/`71fdc0f`/`9a200a4` (8233), `95083ba`/`f001d4e` (8234 jobs).
**Source scan:** zero `sorry`/`axiom` (unchanged).

Oracle outputs (verbatim, the join bricks):

```
'YangMills.list_prod_apply'                            [propext, Quot.sound]
'YangMills.trace_list_prod_eq_sum_pathSum'             [propext, Quot.sound]
'YangMills.loopChain_reverse'                          [propext, Classical.choice, Quot.sound]
'YangMills.loopChain_append'                           [propext, Classical.choice, Quot.sound]
'YangMills.prod_comp_eq_prod_fiber'                    [propext, Classical.choice, Quot.sound]
'YangMills.integral_positionProduct_eq_zero'           [propext, Classical.choice, Quot.sound]
'YangMills.sunHaarProb_decoratedEntryProduct_integral_zero'
                                                       [propext, Classical.choice, Quot.sound]
'YangMills.pathSum_eq_sum_vertexSeq'                   [propext, Classical.choice, Quot.sound]
'YangMills.trace_list_prod_eq_sum_closedSeq'           [propext, Classical.choice, Quot.sound]
'YangMills.pathSum_map_eq_sum_vertexSeq'               [propext, Classical.choice, Quot.sound]
'YangMills.trace_prod_map_eq_sum_closedSeq'            [propext, Classical.choice, Quot.sound]
'YangMills.sun_inv_val_apply'                          [propext, Classical.choice, Quot.sound]
'YangMills.posToFun_val_apply'                         [propext, Classical.choice, Quot.sound]
'YangMills.wilsonLine_val'                             [propext, Classical.choice, Quot.sound]
'YangMills.trace_wilsonLine_eq_sum_decorated'          [propext, Classical.choice, Quot.sound]
'YangMills.integral_trace_wilsonLine_eq_zero'          [propext, Classical.choice, Quot.sound]
```

The headline (`integral_trace_wilsonLine_eq_zero`,
`ClayCore/WilsonLoopMonomial.lean`): **for the SU(N_c) lattice gauge
theory under the product Haar measure (β = 0), the expectation of any
Wilson-line trace vanishes as soon as one positive edge has
`N_c`-unbalanced signed traversal count** — in particular every open
line and every fundamental loop traversing some edge exactly once.
This is the first end-to-end run of the area-law kill pipeline:
trace → closed vertex sequences (`trace_wilsonLine_eq_sum_decorated`,
itself via the `Fin`-indexed path expansion and the entry decoration
`posToFun_val_apply`: forward traversal = entry, backward = conjugated
transposed entry by unitarity) → per-edge fiber grouping
(`prod_comp_eq_prod_fiber`) → one-unbalanced-edge kill
(`integral_positionProduct_eq_zero`) → `Finset`-indexed `N`-ality
selection rule (`sunHaarProb_decoratedEntryProduct_integral_zero`).
Plus `loopChain` (TE-2) feeding the `ZMod N_c` chain complex for the
remaining DB-2/J-3 join (`docs/AREA-LAW-PLAN.md` §4).  All M3
lattice-side; M4/M5/Clay untouched.

## Addendum 14 (2026-06-12, AL4.5 join complete through assembly)

**Builds:** `lake build YangMillsCore` — green at `7649482`, `5325e0e`,
`93c32f2`, `a161531`, and this commit (8234 jobs throughout).
**Source scan:** zero `sorry`/`axiom` (unchanged).

Oracle outputs (verbatim, the join's chain-side completion):

```
'YangMills.integral_prod_trace_wilsonLine_eq_zero'     [propext, Classical.choice, Quot.sound]
'YangMills.card_filter_get_eq_count'                   [propext, Classical.choice, Quot.sound]
'YangMills.signed_count_eq_loopChain'                  [propext, Classical.choice, Quot.sound]
'YangMills.loopChain_zmod_eq_intCast'                  [propext, Classical.choice, Quot.sound]
'YangMills.integral_trace_wilsonLine_eq_zero_of_loopChain_ne_zero'
                                                       [propext, Classical.choice, Quot.sound]
'YangMills.card_filter_sigma_eq_sum'                   [propext, Classical.choice, Quot.sound]
'YangMills.sigma_signed_count_eq_sum_loopChain'        [propext, Classical.choice, Quot.sound]
'YangMills.integral_prod_trace_wilsonLine_eq_zero_of_sum_loopChain_ne_zero'
                                                       [propext, Classical.choice, Quot.sound]
'YangMills.loopChain_plaquette_list'                   [propext, Classical.choice, Quot.sound]
'YangMills.sum_mul_loopChain_plaquette_list'           [propext, Classical.choice, Quot.sound]
'YangMills.sum_mul_loopChain_plaquette_list_eq_chainBoundary₂A'
                                                       [propext, Classical.choice, Quot.sound]
'YangMills.chainAreaA_le'                              [propext, Classical.choice, Quot.sound]
'YangMills.chainAreaA_le_card_of_support_subset'       [propext, Classical.choice, Quot.sound]
```

Content: the β=0 `N`-ality selection rule now holds for PRODUCTS of
Wilson-line traces with the hypothesis in CHAIN form — a product
survives Haar integration only if `∑ⱼ loopChain (L j) = 0` over
`ZMod N_c` at every positive edge
(`integral_prod_trace_wilsonLine_eq_zero_of_sum_loopChain_ne_zero`);
plaquette Wilson lists supply the antisymmetrized boundary columns
(`sum_mul_loopChain_plaquette_list_eq_chainBoundary₂A`), and the
`N`-ality area against that boundary has its spanning bound
(`chainAreaA_le_card_of_support_subset`).  For the strong-coupling
family `loop C :: plaquette-loops-of-S`, the survival condition is
verbatim the chain equation; what remains of the area law is the
expansion-term formalization (the σ-sign bookkeeping) and the AL6
entropy/tail assembly (banked patterns).  All M3 lattice-side;
M4/M5/Clay untouched.

**Same-day completion — THE JOIN (AL5 discharged):**

```
'YangMills.loopChain_reverse_list'                     [propext, Classical.choice, Quot.sound]
'YangMills.chainBoundary₂A_neg'                        [propext, Classical.choice, Quot.sound]
'YangMills.chainSupport_neg'                           [propext, Classical.choice, Quot.sound]
'YangMills.chainAreaA_neg'                             [propext, Classical.choice, Quot.sound]
'YangMills.chainBoundary₂A_reverse'                    [propext, Classical.choice, Quot.sound]
'YangMills.chainAreaA_loopChain_le_of_integral_ne_zero'
                                                       [propext, Classical.choice, Quot.sound]
```

The last line is the **area-law join**: if the β=0 Haar expectation
of a Wilson loop times `m` σ-signed plaquette traces does not vanish,
the loop's `N`-ality area (`chainAreaA` of its `loopChain`, over
`ZMod N_c`) is at most `m`.  Every surviving term of the
strong-coupling expansion spans a discrete surface — machine-checked,
unconditional, no sorry, no axioms beyond the standard three.  The
spanning-surface lower bound (AL5, the campaign's single
high-novelty item) is hereby DISCHARGED; only AL6's quantitative
entropy/tail assembly (banked patterns) separates the repo from
`|⟨W_C⟩| ≤ C₀·r^{Area}`.

## Addendum 15 (2026-06-12, THE FINITE-VOLUME AREA LAW)

**Build:** `lake build YangMillsCore` — green (8234 jobs).
**Source scan:** zero `sorry`/`axiom` (unchanged).

Oracle outputs (verbatim, the AL6 ladder):

```
'YangMills.GaugeConfig.wilsonLine_reverse_list'        [propext, Quot.sound]
'YangMills.star_trace_wilsonLine'                      [propext, Classical.choice, Quot.sound]
'YangMills.norm_trace_wilsonLine_le'                   [propext, Classical.choice, Quot.sound]
'YangMills.measurable_trace_wilsonLine'                [propext, Classical.choice, Quot.sound]
'YangMills.integrable_prod_trace_wilsonLine'           [propext, Classical.choice, Quot.sound]
'YangMills.integral_trace_mul_prod_traces_eq_zero'     [propext, Classical.choice, Quot.sound]
'YangMills.integrable_trace_mul_prod_traces'           [propext, Classical.choice, Quot.sound]
'YangMills.norm_integral_trace_mul_prod_traces_le'     [propext, Classical.choice, Quot.sound]
'YangMills.finite_volume_area_law'                     [propext, Classical.choice, Quot.sound]
```

The headline (`finite_volume_area_law`): **for the SU(N_c) lattice
gauge theory with linearized plaquette activities of size `≤ δ`,
`2δN_c ≤ 1`, the Wilson-loop expectation obeys**

    ‖∫ tr(W_C)·∏_p(1 + c_p·tr Hₚ + c_p'·conj tr Hₚ) dμ_Haar‖
        ≤ N_c · 2^{#P} · (2δN_c)^{Area(C)},

**with `Area(C) = chainAreaA (loopChain C)` the `N`-ality area over
`ZMod N_c` — exponential decay in the minimal discrete spanning
surface.**  Every sub-area expansion term vanishes EXACTLY (the
join); survivors are bounded by `N_c^{|S|+1}` and counted.  The
constant is finite-volume (`2^{#P}`); volume-uniformity is a
post-campaign refinement.  The area-law campaign
(`docs/AREA-LAW-PLAN.md`, AL1–AL6) is COMPLETE in this form: lattice
chain complex, N-ality selection rules, the spanning-surface join,
and the quantitative tail — all without Peter–Weyl, all
unconditional.  All M3 lattice-side (Osterwalder–Seiler);
M4/M5/Clay untouched.

## Addendum 16 (2026-06-12, THE EXACT-ACTIVITY AREA LAW — campaign
complete)

**Build:** `lake build YangMillsCore` — green (8235 jobs; the
`ExpActivityExpansion` module entered the core with the previous
commit and the count is unchanged by this one).
**Source scan:** zero `sorry`/`axiom` (unchanged).

Oracle outputs (verbatim, the exact-activity ladder,
`YangMills/ClayCore/WilsonLoopMonomial.lean` +
`YangMills/L1_GibbsMeasure/ExpActivityExpansion.lean`):

```
'YangMills.norm_integral_exp_term_le'                  [propext, Classical.choice, Quot.sound]
'YangMills.finite_volume_area_law_exp'                 [propext, Classical.choice, Quot.sound]
```

**What is now machine-checked, headline form: for SU(N_c) lattice
gauge theory with the TRUE Wilson Boltzmann factor — activities
`exp(zₚ)`, `zₚ = c_p·tr Hₚ + c_p'·conj tr Hₚ`, `‖c_p‖,‖c_p'‖ ≤ δ`,
ANY `δ ≥ 0` (no smallness hypothesis) —**

    ‖∫ tr(W_C)·∏_p exp(zₚ) dμ_Haar‖
        ≤ N_c · 2^{#P} · (e^{2δN_c}−1)^{Area(C)} · (e^{2δN_c})^{#P},

**with `Area(C) = chainAreaA (loopChain C)` the `N`-ality area over
`ZMod N_c`.**  At Wilson-action coupling (`c_p = c_p' = β/(2N_c)`,
i.e. `2δN_c = β`) the bound is
`N_c·2^{#P}·(e^β−1)^{Area}·e^{β·#P}` — genuine area-law decay for
`β < ln 2`, recovering the linearized law `(2δN_c)^{Area}` to first
order.  Route (all bricks oracle-clean, `docs/AREA-LAW-EXACT-PLAN.md`
E1–E4b-2): pointwise exp-series (Pi-Cauchy product) → dominated
`∫↔∑'` interchange → per-multiplicity dichotomy (binomial split +
the multiplicity join kill below the area; direct `(2δN_c)^{Σm}/m!`
bound above it) → exact per-surface tail factorization
`(e^x−1)^{#S}·(e^x)^{#P−#S}` with the `powersetCard` union bound.
The exact-activity campaign is COMPLETE; the surviving refinements
(volume-uniform constant via connected-support resummation;
Peter–Weyl proper) are recorded, not promised.  All M3 lattice-side
(Osterwalder–Seiler); M4/M5/Clay untouched.

## Addendum 17 (2026-06-12, VU campaign V0-1: support-disjoint
factorization)

**Build:** `lake build YangMillsCore` — green (**8236 jobs**; +1 for
the new module `L1_GibbsMeasure/SupportFactorization.lean`).
**Source scan:** zero `sorry`; zero `axiom` in the core tree
(now CI-enforced by `scripts/check_consistency.py`).

Oracle outputs (verbatim):

```
'YangMills.integral_mul_of_disjoint_pos_deps'          [propext, Classical.choice, Quot.sound]
'YangMills.integral_mul_prod_of_disjoint_support'      [propext, Classical.choice, Quot.sound]
'YangMills.integral_wilson_obs_mul_prod_split'         [propext, Classical.choice, Quot.sound]
'YangMills.dependsOnPos_comp_wilsonLine'               [propext, Classical.choice, Quot.sound]
```

**Content (the volume-uniform campaign's opening brick,
`docs/AREA-LAW-VU-PLAN.md` V0-1):** the β = 0 gauge measure is the
per-positive-edge product measure, so observables with disjoint
positive-edge supports are independent.  `DependsOnPos` formalizes
"reads only the coordinates in `S`" (with a `mono`/`mul`/`finset_prod`
calculus); `dependsOnPos_comp_wilsonLine` certifies in one stroke that
every post-composed Wilson-line observable `φ(W_es)` — the loop trace,
linearized activities, and the exact `exp` activities alike — depends
only on `edgeSupport es`; `integral_mul_of_disjoint_pos_deps`
transports the banked two-block factorization along
`gaugeConfigMEquiv`; and `integral_mul_prod_of_disjoint_support` /
`integral_wilson_obs_mul_prod_split` give the campaign shape: a loop
observable times any activities supported away from the loop
factorizes.  This is the mechanism by which far-from-the-loop polymer
components will cancel against `Z` (V1).  All M3 lattice-side.

**Addendum 17b (same day, V0-2 opening).**  Build green (8236 jobs),
oracle clean:

```
'YangMills.plaquettePosSupport_eq'                     [propext, Classical.choice, Quot.sound]
'YangMills.dependsOnPos_plaquette_obs''                [propext, Classical.choice, Quot.sound]
```

The signed/positive support seam feared in the plan DISSOLVED:
`PolymerExpansion.plaquetteSupport` was already positive-edge-level,
and `plaquettePosSupport_eq` is an outright Finset equality — so
`ClusterGeometry`'s component combinatorics
(`plaqComponents_support_disjoint`, `_not_touching`) and V0-1's
independence calculus now speak about the same sets.  Next: the
regrouping identity (split `S` by components touching the loop).

**Addendum 17c (same day, V0-2 closed — V0 COMPLETE).**  Build green
(8236 jobs), oracle clean:

```
'YangMills.integral_wilson_obs_regroup'                [propext, Classical.choice, Quot.sound]
'YangMills.near_far_support_disjoint'                  [propext, Classical.choice, Quot.sound]
'YangMills.farLoop_disjoint_edgeSupport'               [propext, Classical.choice, Quot.sound]
```

**The component regrouping:** for any plaquette activities `f_p` local
to their support, every powerset term of the loop-tagged expansion
factorizes as
`∫ φ(W_C)·∏_{p∈S} f_p = (∫ φ(W_C)·∏_{nearLoop es S} f_p)·(∫ ∏_{S∖nearLoop} f_p)`
— `nearLoop` collects the `plaqComponents` of `S` touching the loop's
edge support; far components are support-disjoint from both the loop
and the near block (`plaqComponents_support_disjoint` + the V0-1
independence).  V0 of `docs/AREA-LAW-VU-PLAN.md` is COMPLETE; the
campaign's center of mass (V1, the `Z`-ratio cancellation) is next.

**Addendum 17d (same day, V1-a: the far resummation).**  Build green
(8236 jobs), oracle clean:

```
'YangMills.prod_one_add_eq_sum_powerset'               [propext, Classical.choice, Quot.sound]
'YangMills.sum_integral_prod_eq_integral_prod_one_add' [propext, Classical.choice, Quot.sound]
```

Summing the far factor of the V0 regrouping over all far subsets
reconstitutes the RESTRICTED partition function:
`∑_{T⊆F} ∫ ∏_{p∈T} f_p = ∫ ∏_{p∈F}(1+f_p)` — the `Z_{F}` object the
V1 ratio cancellation divides against.  Remaining in V1: the fiber
bijection `S ↔ (S₀, T)` (needs `plaqComponents` stability under
support-disjoint unions — the campaign's hard graph brick) and the
`Z`-ratio bound via the cluster expansion.

**Addendum 17e (same day, V1-b steps 1–5: THE STABILITY THEOREM).**
Build green (8236 jobs), oracle clean:

```
'YangMills.mem_nearLoop_iff_reachable'                 [propext, Classical.choice, Quot.sound]
'YangMills.walk_confined'                              [propext, Classical.choice, Quot.sound]
'YangMills.reachable_union_of_reachable'               [propext, Classical.choice, Quot.sound]
'YangMills.reachable_descend'                          [propext, Classical.choice, Quot.sound]
'YangMills.nearLoop_union_far'                         [propext, Classical.choice, Quot.sound]
```

The campaign's hard graph brick is DISCHARGED:
`nearLoop es (S₀ ∪ T) = S₀` for pinned `S₀` and far `T` — adjoining
far plaquettes never changes the near part.  Proved via the
reachability characterization of `nearLoop`, walk confinement, and
witness lifting along the inclusion hom.  Remaining in V1-b: only the
`Finset.sum_nbij'` fiber reindexing (`nearLoop_idem` + bookkeeping);
then V1-c, the `Z`-ratio bound.

**Addendum 17f (same day, `nearLoop` idempotence).**  Build green
(8236 jobs), oracle clean:

```
'YangMills.nearLoop_walk_descend'                      [propext, Classical.choice, Quot.sound]
'YangMills.nearLoop_idem'                              [propext, Classical.choice, Quot.sound]
```

A walk to a loop-touching plaquette has all its vertices near, so it
descends into the near part's own touching graph; hence
`nearLoop es (nearLoop es S) = nearLoop es S` — the forward fiber map
lands in the pinned sets.  V1-b now lacks only the `sum_nbij'`
reindexing bookkeeping.

**Addendum 17g (same day, V1-b COMPLETE — the fiber reindexing).**
Build green (8236 jobs), oracle clean:

```
'YangMills.disjoint_farRegion'                         [propext, Classical.choice, Quot.sound]
'YangMills.sum_powerset_fiber'                         [propext, Classical.choice, Quot.sound]
```

**The fiber decomposition of the loop-tagged powerset expansion:**

    ∑_{S ⊆ P} g(S) = ∑_{S₀ pinned} ∑_{T ⊆ farRegion(S₀)} g(S₀ ∪ T)

— every subset splits uniquely as a pinned near part plus an arbitrary
far subset (`sum_nbij'` with the V1-b stability/idempotence theorems
as the two inverse laws).  **V1-b is COMPLETE.**  Combined with the V0
regrouping and the V1-a far resummation, the numerator now has the
campaign's target shape
`∑_{S₀ pinned} (∫ φ(W_C)·∏_{S₀} f) · Z_{farRegion(S₀)}`
(assembly + the `Z`-ratio bound = V1-c, the campaign's last analytic
stretch).

**Addendum 17h (same day, THE LOOP-TAGGED EXPANSION — V1-c
assembly).**  Build green (8236 jobs), oracle clean:

```
'YangMills.integral_wilson_loop_tagged_expansion'      [propext, Classical.choice, Quot.sound]
```

**The campaign's structural identity is machine-checked:** for any
plaquette activities `f_p` local to their support (with the two
natural integrability families),

    ∫ φ(W_C)·∏_{p∈P}(1+f_p)
        = ∑_{S₀ pinned} (∫ φ(W_C)·∏_{p∈S₀} f_p) · Z_{farRegion(S₀)}

— the unnormalized loop expectation is a PINNED sum, each term
carrying the restricted partition function of its far region.  One
proof chains all of V0/V1-a/V1-b: pointwise binomial →
`integral_finset_sum` → the fiber reindexing → per-fiber
support-disjoint factorization → the far resummation.  Compiled first
try on the banked bricks.  What remains of V1 is purely analytic: the
volume-free bound on `Z_{farRegion(S₀)}/Z` via the difference of
cluster sums (clusters meeting the loop's neighbourhood) and the
pinned KP tail.  All M3 lattice-side; M4/M5/Clay untouched.

**Addendum 17i (same day, R1 partition transfer — `KP/Restriction.lean`
enters the core).**  Build green (**8237 jobs**, +1 for the new
module), oracle clean:

```
'YangMills.KP.partition_restrict'                      [propext, Classical.choice, Quot.sound]
```

`PolymerSystem.restrict P Λ` (polymers = `↥Λ`, inherited structure)
with `partition P Λ = partition (P.restrict Λ) univ` — the
volume-restricted Mayer inversion now reduces to the banked
univ-version applied to the restricted system.  Remaining in R1: the
`KPCriterion` transfer; then R2 (the cluster-sum difference) and R3
(the restricted lattice gate).

**Addendum 17j (same day, R1 COMPLETE — the volume-restricted Mayer
inversion).**  Build green (8237 jobs), oracle clean:

```
'YangMills.KP.KPCriterion.restrict'                    [propext, Classical.choice, Quot.sound]
'YangMills.KP.partition_eq_exp_clusterSum_restrict'    [propext, Classical.choice, Quot.sound]
```

Under the ambient KP criterion, EVERY finite-volume partition function
is the exponential of its restricted system's cluster sum:
`partition P Λ = exp(clusterSum (P.restrict Λ))` — so a ratio of
partition functions over two volumes is the exponential of a
difference of cluster sums.  Remaining: R2 (bound that difference by
the pinned tail over the small region) and R3 (the restricted lattice
gate `∫∏_F(1+f) = partition gas (polymersIn F)`).

**Addendum 17k (same day, R2 difference identity + exponent bound).**
Build green (8237 jobs), oracle clean:

```
'YangMills.KP.clusterTerm_restrict'                    [propext, Classical.choice, Quot.sound]
'YangMills.KP.clusterSum_sub_restrict'                 [propext, Classical.choice, Quot.sound]
'YangMills.KP.norm_diffTerm_le'                        [propext, Classical.choice, Quot.sound]
'YangMills.KP.norm_clusterSum_sub_restrict_le'         [propext, Classical.choice, Quot.sound]
```

Under the KP criterion the cluster sums of the full and restricted
systems differ exactly by the tuple sums MEETING `Λᶜ`
(`clusterSum_sub_restrict`), and that difference is bounded in norm by
the off-region weight tail (`norm_clusterSum_sub_restrict_le`):
**`‖log(Z_Λ/Z)‖ ≤ ∑'_n offRegionClusterWeight P Λ n`.**  Remaining in
R2: render the right side volume-free via the swap-reindex union bound
(`ursell_comp_equiv`) and the tilted pinned tails; then R3.

**Addendum 17l (same day, R2(b3) — the union bound).**  Build green
(8237 jobs), oracle clean:

```
'YangMills.KP.offRegionClusterWeight_le_pinned'        [propext, Classical.choice, Quot.sound]
```

`offRegionClusterWeight P Λ n ≤ (n+1)·∑_{c ∉ Λ} pinnedClusterWeight P c n`
— every escaping tuple is charged to a pinned polymer OUTSIDE `Λ` by
swapping its escaping index to position 0 (`ursell` is
permutation-invariant) and fibering.  The `Z`-ratio exponent is now a
sum over `Λᶜ`-pinned weights up to the `(n+1)` factor, which the
tilted pinned tails absorb (R2(b4), the last analytic step of R2).

**Addendum 17m (same day, R2 COMPLETE — the volume-free `Z`-ratio
bound).**  Build green (8237 jobs), oracle clean:

```
'YangMills.KP.pinnedClusterWeight_scale'               [propext, Classical.choice, Quot.sound]
'YangMills.KP.tsum_offRegionClusterWeight_le'          [propext, Classical.choice, Quot.sound]
```

**The abstract `Z`-ratio theory is DONE.**  Under the `e^t`-tilted KP
criterion (`KPCriterion (P.scaleActivity (exp t)) a` — exactly the
form the lattice gas verifies),

    ‖log(Z_Λ / Z)‖ = ‖clusterSum P − clusterSum (P.restrict Λ)‖
        ≤ ∑'_n offRegionClusterWeight P Λ n
        ≤ t⁻¹ · ∑_{c ∉ Λ} e^t · ‖z(c)‖ · e^{a(c)}

— a sum over the polymers OUTSIDE `Λ` only: volume-free when `Λᶜ` is
the loop's neighbourhood.  Chained: the restricted Mayer inversion
(R1), the difference identity (R2a), the off-region majorant (R2b1–2),
the swap-reindex union bound (R2b3), the scalar tilt absorbing `(n+1)`
(R2b4).  Remaining in V1: R3, the restricted lattice gate.

**Addendum 17n (same day, R3 truncation substrate —
`L1_GibbsMeasure/RestrictedGate.lean` enters the core).**  Build green
(**8238 jobs**, +1), oracle clean:

```
'YangMills.prod_one_add_truncWeight'                   [propext, Classical.choice, Quot.sound]
'YangMills.truncated_activity_eq_zero'                 [propext, Classical.choice, Quot.sound]
'YangMills.truncated_activity_eq'                      [propext, Classical.choice, Quot.sound]
```

The truncation device's substrate: `truncWeight w F = w·1_F` with the
pointwise identity `∏_F(1+w) = ∏_univ(1+w·1_F)`, inherited
`IsLocalWeight`/measurability/bound, and the truncated gas's
activities — ZERO off the `F`-polymers, EQUAL to the original gas's on
them.  Remaining in R3: the assembly chain (banked weighted gate at
`truncWeight` + `partition_eq_of_activity_eq_zero` + the activity
congruence) into `Z_F = partition (gas w) (polymersIn F)`.

**Addendum 17o (same day, R3 COMPLETE — THE RESTRICTED LATTICE
GATE).**  Build green (8238 jobs), oracle clean:

```
'YangMills.restricted_weightedPartition_eq_partition'  [propext, Classical.choice, Quot.sound]
```

**`∫ ∏_{p∈F}(1+w_p) = Ξ_{gas(w)}(polymersIn F)`** — the
region-restricted lattice partition function IS the polymer partition
function over the `F`-polymers of the ORIGINAL gas, by the truncation
device (truncate, apply the banked 3.2M-heartbeat gate unchanged, drop
the vanished activities, restore the originals).  **R1 + R2 + R3: the
`Z`-ratio machinery of V1 is COMPLETE** — every restricted `Z_F` is an
`exp(clusterSum)` (R1), the log-ratio is a difference of cluster sums
(R2a), bounded volume-free by the `Λᶜ`-pinned tilted tails (R2b).
Remaining to close V1 outright: the lattice glue (instantiate at
`Λ := polymersIn (farRegion es S₀)` with the banked tilted KP
criterion) and the neighbourhood-geometry count.  All M3 lattice-side.

**Addendum 17p (same day, THE V1 CAPSTONE — the instantiated
`Z`-ratio bound).**  Build green (8238 jobs), oracle clean:

```
'YangMills.KP.KPCriterion.of_activity_norm_le'         [propext, Classical.choice, Quot.sound]
'YangMills.weighted_scale_kpCriterion'                 [propext, Classical.choice, Quot.sound]
'YangMills.restricted_partition_log_ratio_bound'       [propext, Classical.choice, Quot.sound]
```

**The `Z`-ratio cancellation is assembled at the lattice.**  For the
weighted gas at strong coupling (the banked volume-uniform window in
`d, δ, t, ε`), for EVERY plaquette region `F`:

    Z_F = exp(clusterSum(gas|_{polymersIn F}))   and
    ‖log Z − log Z_F‖ ≤ ∑_{c ⊄ F} e·‖z(c)‖·e^{t·|c|}

— the log-ratio of the full and region-restricted partition functions
is bounded by a sum over the polymers NOT contained in `F` alone.
Instantiated at `F := farRegion es S₀`, the right side runs over
polymers meeting the loop's neighbourhood — the volume-free quantity
the campaign was built to reach.  What remains of V1 is bookkeeping
(the neighbourhood polymer count via `ConnectedEntropy`); V2 (the
pinned area tail) then closes the campaign.  All M3 lattice-side;
M4/M5/Clay untouched.

**Addendum 17q (same day, V1 COMPLETE — the neighbourhood count).**
Build green (8238 jobs), oracle clean:

```
'YangMills.offRegion_polymer_sum_le'                   [propext, Classical.choice, Quot.sound]
```

**V1 — THE `Z`-RATIO CANCELLATION, THE CAMPAIGN'S CENTER OF MASS, IS
COMPLETE.**  The exponent sum is bounded by
`#Fᶜ · e·(δe^t)/(1−(16d+1)²·δe^t)` — every escaping polymer charged to
a plaquette outside `F` it contains, the through-plaquette sums
volume-uniform by the banked lattice-animal entropy
(`sum_connectedPolymers_through_le`).  Chained with Addendum 17p:

    ‖log(Z/Z_{farRegion(S₀)})‖ ≤ #(P ∖ farRegion(S₀)) · C(d, δ, t)

— the log-ratio is linear in the size of the loop's neighbourhood,
with constants in `d, δ, t` only.  V0 + V1 are COMPLETE; V2 (the
pinned area tail: the N-ality kill + pinned entropy, both mechanisms
already proved in the area-law campaigns) closes the volume-uniform
area law.  All M3 lattice-side; M4/M5/Clay untouched.

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
