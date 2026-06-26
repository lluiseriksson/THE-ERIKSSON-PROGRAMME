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

## Addendum 17r (2026-06-12, V2-3b′ COMPLETE — THE NORMALIZED PINNED
BOUND: the `Z`-ratio cancellation executed at the lattice)

**Build:** green (8238 jobs).  Oracle outputs (verbatim, the V2 ladder
since Addendum 17q — `WilsonLoopMonomial.lean`, `KP/Restriction.lean`,
`RestrictedGate.lean`):

```
'YangMills.integral_prod_one_add_ofReal'               [propext, Classical.choice, Quot.sound]
'YangMills.card_compl_farRegion_le'                    [propext, Classical.choice, Quot.sound]
'YangMills.norm_integral_pinned_term_le'               [propext, Classical.choice, Quot.sound]
'YangMills.KP.norm_exp_div_norm_exp_le'                [propext, Classical.choice, Quot.sound]
'YangMills.norm_integral_wilson_loop_le_pinned_sum'    [propext, Classical.choice, Quot.sound]
'YangMills.KP.norm_div_le_pinned_sum_exp'              [propext, Classical.choice, Quot.sound]
'YangMills.wilsonLine_congr_of_configToPos_eq'         [propext, Classical.choice, Quot.sound]
'YangMills.isLocalWeight_reActivity'                   [propext, Classical.choice, Quot.sound]
'YangMills.measurable_reActivity'                      [propext, Classical.choice, Quot.sound]
'YangMills.reActivity_bound'                           [propext, Classical.choice, Quot.sound]
'YangMills.one_add_conjPair_eq_cast'                   [propext, Classical.choice, Quot.sound]
'YangMills.integral_conjPair_prod_eq_cast'             [propext, Classical.choice, Quot.sound]
'YangMills.norm_normalized_wilson_loop_le_pinned_sum'  [propext, Classical.choice, Quot.sound]
```

**The normalized Wilson-loop expectation is machine-checked in pinned
form, volume-free in every factor:** for the conjugate-pair linearized
activities (`c' = conj c`, `‖c‖ ≤ δ`), in the banked strong-coupling
window,

    ‖(∫ tr(W_C)·∏(1+f)) / Z‖
      ≤ ∑_{S₀ pinned} ite(Area ≤ #S₀)(N_c·(2δN_c)^{#S₀})(0)
          · exp((#loopSupp·4d + #S₀·16d)·K(d,δ,t))

— the kill annihilates every sub-area pinned term, each survivor
carries its geometric weight times a loop-neighbourhood exponential,
and `Z` cancelled against the far factors through the restricted
cluster expansion (the entire V0+V1 machinery executing in one
statement).  Integrability of the finite products is carried as two
explicit hypothesis families (standard, to be discharged at
instantiation).  Remaining for the campaign headline (V2-3c): pull
`r^{Area}` out of the pinned sum and resum the loop-anchored component
gas into the perimeter prefactor `e^{c·|C|}`.  All M3 lattice-side;
M4/M5/Clay untouched.

## Addendum 17s (2026-06-12, V2-3c: THE PINNED GAS RESUMMATION —
`∑_{pinned} σ^{#S₀} ≤ ∏_{loop-touching}(1+σ^{#c})`)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`SupportFactorization.lean`):

```
'YangMills.plaqComponents_touches_of_pinned'  [propext, Classical.choice, Quot.sound]
'YangMills.sum_pinned_pow_le_prod'            [propext, Classical.choice, Quot.sound]
```

**The pinned gas resums into a polymer-gas product over loop-touching
connected components.**  `plaqComponents_touches_of_pinned`: every
connected component of a pinned set (`nearLoop es S₀ = S₀`) contains a
plaquette whose support meets the loop's edge support — pick `p ∈ c`,
`p ∈ S₀ = nearLoop` lands `p` in a touching component `c'`, and
component disjointness forces `c = c'`.  `sum_pinned_pow_le_prod`:

    ∑_{S₀ pinned} σ^{#S₀}
      ≤ ∏_{c connected, nonempty, loop-touching} (1 + σ^{#c})

via (i) the per-pinned-set factorization `σ^{#S₀} = ∏_{c ∈
plaqComponents S₀} σ^{#c}` (`card_biUnion` over the disjoint
component family), (ii) injectivity of `plaqComponents` on pinned sets
(the banked `plaqComponents_biUnion` reconstruction), (iii) the real
binomial `∏(1+x_c) = ∑_{T ⊆ …} ∏ x_c`, and (iv) the image of pinned
sets landing inside the powerset of loop-touching admissible polymers
(nonemptiness + connectedness banked in V0; touching from the new
lemma).  Elementary throughout — no KP, no measure theory.  Remaining
for the headline: `∏(1+σ^{#c}) ≤ exp(∑ σ^{#c}) ≤ e^{c(d,δ,t)·|C|}`
(the loop-edge charge + `sum_connectedPolymers_through_le`), then
compose with Addendum 17r's pinned bound and the area split
`sum_ite_pow_le`.  All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 17t (2026-06-12, **THE VU CAMPAIGN HEADLINE —
`normalized_wilson_loop_area_law`, THE VOLUME-UNIFORM AREA LAW**)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`SupportFactorization.lean` + `RestrictedGate.lean`):

```
'YangMills.prod_one_add_le_exp_sum'          [propext, Classical.choice, Quot.sound]
'YangMills.loopTouching_polymer_sum_le'      [propext, Classical.choice, Quot.sound]
'YangMills.sum_pinned_pow_le_exp'            [propext, Classical.choice, Quot.sound]
'YangMills.sum_pinned_dichotomy_le'          [propext, Classical.choice, Quot.sound]
'YangMills.normalized_wilson_loop_area_law'  [propext, Classical.choice, Quot.sound]
```

**The volume-uniform area law is machine-checked.**  For the
conjugate-pair linearized activities (`c' = conj c`, `‖c‖ ≤ δ`) in the
banked strong-coupling window, and ANY rate `σ ∈ [0,1]` with
`(16d+1)²σ < 1` and `2δN_c·e^{16d·K} ≤ σ²`:

    ‖(∫ tr(W_C)·∏(1+f)) / Z‖
      ≤ N_c · e^{#loopSupp·4d·K} · σ^{Area(C)} · e^{#loopSupp·4d·S(σ)}

with `K = e·(2δN_c e^t)/(1−(16d+1)²·2δN_c e^t)` and
`S(σ) = σ/(1−(16d+1)²σ)` — **area-law decay with a perimeter-only
prefactor, every constant volume-free**: the bound holds on every
finite lattice uniformly.  The chain: the loop-tagged expansion (V0),
the restricted-`Z` cancellation (V1), the N-ality kill + pinned
dichotomy (V2-2/3a), the `Z`-ratio exponentials (3b′), the
`√ρ` area split (`sum_ite_pow_le`), and the pinned gas resummation
(17s) exponentiated by `prod_one_add_le_exp_sum` and charged to the
loop by `loopTouching_polymer_sum_le` (the loop-touching plaquette set
is exactly `(farRegion es ∅)ᶜ`, so the V2-1 count gives
`#loopSupp·4d`).

**Non-vacuity audit:** the hypothesis window is jointly satisfiable
for every `d, N_c` — e.g. `d=4, N_c=2, t=1, ε=0, δ=10⁻¹⁰, σ=2·10⁻⁴`
checks `hr`, `hsmall`, `hrσ`, `hρσ` simultaneously (binding constraint
`(16d+1)²σ < 1`; `δ` shrinks to fit `σ²`).  The conclusion is
non-trivial: `σ^{Area}` decays exponentially in the area against a
perimeter-exponential prefactor.  Carried hypotheses: the two
integrability families of finite products (standard, discharged at
instantiation — same status as 17r).  All M3 lattice-side;
M4/M5/Clay untouched.

## Addendum 17u (2026-06-12, **THE INTEGRABILITY FAMILIES DISCHARGED —
`normalized_wilson_loop_area_law_unconditional`**)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`RestrictedGate.lean`):

```
'YangMills.integrable_conjPair_prod'                       [propext, Classical.choice, Quot.sound]
'YangMills.integrable_trace_mul_conjPair_prod'             [propext, Classical.choice, Quot.sound]
'YangMills.normalized_wilson_loop_area_law_unconditional'  [propext, Classical.choice, Quot.sound]
```

The two integrability hypothesis families carried since 17r are now
THEOREMS: the integrands are measurable (the banked decorated
expansion `measurable_trace_wilsonLine`) and uniformly bounded
(`norm_trace_wilsonLine_le` through finite products — no smallness
needed, any `c, c'`), hence integrable on the Haar probability space
(`Integrable.bdd_mul`).  **The volume-uniform area law now carries NO
hypothesis families** — every remaining hypothesis is an explicit,
jointly satisfiable smallness/geometry condition (the 17t witness).
All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 18 (2026-06-12, **V4 OPENING — the exact-Wilson-factor
activity interface** for the volume-uniform area law)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`RestrictedGate.lean`):

```
'YangMills.isLocalWeight_expReActivity'  [propext, Classical.choice, Quot.sound]
'YangMills.measurable_expReActivity'     [propext, Classical.choice, Quot.sound]
'YangMills.expReActivity_bound'          [propext, Classical.choice, Quot.sound]
'YangMills.exp_conjPair_eq_cast'         [propext, Classical.choice, Quot.sound]
```

**V4** (`docs/AREA-LAW-VU-PLAN.md`) lifts the volume-uniform area law
from the linearized factor `∏(1+f_p)` to the TRUE Wilson Boltzmann
factor `∏ exp(z_p)`.  Key observation: at the conjugate pair
`c' = conj c` the exponent `z_p = 2·Re(c_p · tr H_p)` is REAL, so
`exp(z_p) = 1 + (exp(z_p) − 1)` is the linearized form with the real
activity `expReActivity := exp(2 Re(c · tr H)) − 1`.  The generic VU
pipeline (loop-tagged expansion + restricted `Z` cancellation) is
agnostic to the activity; only the per-pinned dichotomy must be
re-derived.  This addendum closes the activity interface (V4-0):
`isLocalWeight_expReActivity` (locality, via the banked reActivity
locality after a beta-reducing ascription — house note: an
`IsLocalWeight` result applied at `p A A'` is a beta-redex `rw` won't
see; ascribe the reduced equality to a `have`),
`measurable_expReActivity` (`Real.measurable_exp.comp` the banked
measurable reActivity), `expReActivity_bound`
(`|exp w − 1| ≤ exp(2δN_c) − 1` for `|w| ≤ 2δN_c`, by the elementary
AM–GM `2 ≤ e^B + e^{−B}`), and `exp_conjPair_eq_cast` (the ℂ factor
`exp(z_p)` IS the cast of the real `1 + expReActivity`, via
`Complex.add_conj` + `Complex.ofReal_exp`).  REMAINING: V4-1 (the
pinned-set exp dichotomy — the N-ality kill for `∏_{S₀}(exp z − 1)`,
reusing the banked `tsum_shifted_prod_pow_div_factorial` +
`norm_integral_exp_term_le`) and V4-2 (re-compose the headline).
All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 18a (2026-06-12, **V4-1 stage 1 — the shifted complex
exp-product expansion**)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`ExpActivityExpansion.lean`):

```
'YangMills.tsum_pow_succ_div_factorial_succ'         [propext, Classical.choice, Quot.sound]
'YangMills.prod_exp_sub_one_eq_tsum_prod_pow_succ'   [propext, Classical.choice, Quot.sound]
```

The pointwise engine for the pinned exp dichotomy.
`tsum_pow_succ_div_factorial_succ`: the complex shifted series
`∑'_k z^{k+1}/(k+1)! = exp z − 1` (the constant term removed via
`Summable.tsum_eq_zero_add`).  `prod_exp_sub_one_eq_tsum_prod_pow_succ`:
`∏_i (exp(z_i) − 1) = ∑'_{m : ι→ℕ} ∏_i z_i^{m_i+1}/(m_i+1)!` over any
`Fintype ι`, via the banked complex Pi-Cauchy product `tsum_pi_prod'`
with the succ-shifted summands (summability by
`Summable.comp_injective (add_left_injective 1)`).  The SHIFT is the
design choice: every term has exponent `m_i+1 ≥ 1`, so when this is
instantiated at `ι = ↥S₀` every contributing monomial occupies EXACTLY
`S₀` — the N-ality kill (`norm_integral_exp_term_le`) then fires
uniformly when `Area > #S₀`, with no support bookkeeping.  REMAINING in
V4-1: the ∫↔∑' swap over the pinned product (`integral_tsum_of_bounded`)
+ the per-term kill + the survivor resummation to `(e^{2δN_c}−1)^{#S₀}`
(banked `tsum_shifted_prod_pow_div_factorial`); then V4-2.
All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 18b (2026-06-12, **V4-1 CLOSED — the pinned EXP
dichotomy** `norm_integral_exp_pinned_term_le`)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`ExpActivityExpansion.lean` + `WilsonLoopMonomial.lean`):

```
'YangMills.summable_prod_pow_succ_div_factorial'  [propext, Classical.choice, Quot.sound]
'YangMills.norm_integral_exp_pinned_term_le'      [propext, Classical.choice, Quot.sound]
```

The exp analog of `norm_integral_pinned_term_le` — the single piece
the (otherwise activity-agnostic) VU pipeline needs to lift to the
exact Wilson factor:

    ‖∫ tr(W_C)·∏_{p∈S₀}(exp z_p − 1)‖
      ≤ ite(Area ≤ #S₀)(N_c·(e^{2δN_c}−1)^{#S₀})(0)

— the N-ality KILL below the area, the geometric `(e^{2δN_c}−1)^{#S₀}`
survivor bound above it.  Route (mirrors `finite_volume_area_law_exp`
but pinned to `S₀` over the subtype `↥S₀`): the shifted exp-product
expansion `prod_exp_sub_one_eq_tsum_prod_pow_succ` (every exponent
`m_q+1 ≥ 1`) → `Finset.prod_coe_sort` to cross the `S₀`↔`↥S₀` seam →
the `∫↔∑'` swap `integral_tsum_of_bounded` (dominated by
`summable_prod_pow_succ_div_factorial`) → per-multiplicity
`norm_integral_exp_term_le` at the EXTENDED multiplicity
`ext m p = if p∈S₀ then m⟨p⟩+1 else 0` (whose support is EXACTLY `S₀`,
so the kill condition `Area ≤ #supp` becomes the uniform `Area ≤ #S₀`)
→ survivor resummation `tsum_prod_pow_succ_div_factorial`
(`= (e^{2δN_c}−1)^{card ↥S₀}`, `Fintype.card_coe`).  Supporting engine
lemmas (Addendum 18a + here): `tsum_pow_succ_div_factorial_succ`,
`prod_exp_sub_one_eq_tsum_prod_pow_succ`,
`tsum_prod_pow_succ_div_factorial`, `summable_prod_pow_succ_div_factorial`.
House notes: the full-P↔subtype multiplicity bridge is
`prod_filter_mul_prod_filter_not (·∈S₀)` + `prod_attach` + `simp [q.2]`
(off-S₀ factors are `z^0/0! = 1`); the zero-area branch collapses via
`tsum_congr (fun m => if_neg hA)` + `tsum_zero`.  REMAINING: V4-2 — the
headline re-composition (the exp analogs of
`norm_normalized_wilson_loop_le_pinned_sum` and
`normalized_wilson_loop_area_law`, reusing the generic V0/V1 machinery
with the V4-0 interface and this dichotomy).
All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 18c (2026-06-12, **V4-2(a) — the EXACT pinned numerator
bound** `norm_integral_exp_wilson_loop_le_pinned_sum`)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`RestrictedGate.lean`):

```
'YangMills.integrable_exp_conjPair_prod'                [propext, Classical.choice, Quot.sound]
'YangMills.integrable_trace_mul_exp_conjPair_prod'      [propext, Classical.choice, Quot.sound]
'YangMills.norm_integral_exp_wilson_loop_le_pinned_sum' [propext, Classical.choice, Quot.sound]
```

The exp analog of `norm_integral_wilson_loop_le_pinned_sum`:

    ‖∫ tr(W_C)·∏_p exp(z_p)‖
      ≤ ∑_{S₀ pinned} ite(Area ≤ #S₀)(N_c·(e^{2δN_c}−1)^{#S₀})(0)·‖Z_far(S₀)‖

— chaining the (activity-agnostic) loop-tagged expansion
`integral_wilson_loop_tagged_expansion` at the activity
`f_p = exp(z_p) − 1` (so `∏(1 + f_p) = ∏ exp(z_p)`) with `norm_sum_le`
and the V4-1 pinned exp dichotomy.  Supporting: the exact-activity
integrability families `integrable_exp_conjPair_prod` and
`integrable_trace_mul_exp_conjPair_prod` (measurable via
`Complex.measurable_exp`, bounded by `(e^{2δN_c}+1)^{#S}` through
`Complex.norm_exp` + `Complex.re_le_norm`).  REMAINING: V4-2(b) the
normalized bound (exp analog of
`norm_normalized_wilson_loop_le_pinned_sum`, using the gate at
`w := expReActivity` + `exp_conjPair_eq_cast`) and V4-2(c) the headline
(exp analog of `normalized_wilson_loop_area_law` with
`ρ₀ := e^{2δN_c}−1`, reusing the abstract `sum_pinned_dichotomy_le`).
The far-factor cast `integral_exp_conjPair_prod_eq_cast` (the exp
analog of `integral_conjPair_prod_eq_cast`, identifying the ℂ far
factor with the cast of the real restricted `Z` of `expReActivity`
via `exp_conjPair_eq_cast` + `integral_prod_one_add_ofReal`) is also
banked (oracle clean), so every input to V4-2(b) is now in place.
All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 18d (2026-06-12, **V4 CLOSED — THE EXACT-ACTIVITY
VOLUME-UNIFORM AREA LAW** `normalized_exp_wilson_loop_area_law`)

**Build:** green (8238 jobs).  Oracle outputs (verbatim,
`RestrictedGate.lean`):

```
'YangMills.norm_normalized_exp_wilson_loop_le_pinned_sum'  [propext, Classical.choice, Quot.sound]
'YangMills.normalized_exp_wilson_loop_area_law'            [propext, Classical.choice, Quot.sound]
```

The volume-uniform area law now holds for the **TRUE Wilson
Boltzmann factor** `∏ exp(z_p)` (not just the linearized `∏(1+f_p)`).
For the conjugate-pair exponent `z_p = c_p·tr H_p + conj(c_p)·conj tr H_p
= 2 Re(c_p·tr H_p)` (`‖c_p‖ ≤ δ`) in the banked strong-coupling
window, and any rate `σ ∈ [0,1]` with `(16d+1)²σ < 1` and
`(e^{2δN_c}−1)·e^{16d·K} ≤ σ²`:

    ‖(∫ tr(W_C)·∏_p exp(z_p)) / Z‖
      ≤ N_c·e^{#loopSupp·4d·K}·σ^{Area(C)}·e^{#loopSupp·4d·S(σ)}

with `K = e·((e^{2δN_c}−1)e^t)/(1−(16d+1)²(e^{2δN_c}−1)e^t)` and
`S(σ) = σ/(1−(16d+1)²σ)` — area decay, perimeter prefactor, every
constant volume-free, `Z` cancelled through the restricted cluster
expansion.  The composition exactly mirrors the linearized headline
`normalized_wilson_loop_area_law` with the SINGLE substitution
`2δN_c ↦ e^{2δN_c}−1` (the bound on `expReActivity`): the generic V0/V1
machinery (loop-tagged expansion, restricted-`Z` gate) is
activity-agnostic, so only the per-pinned dichotomy changed.
`norm_normalized_exp_wilson_loop_le_pinned_sum` runs the `Z`-ratio
cancellation at `w := expReActivity` (gate via the V4-0 interface,
numerator via V4-2(a), far factor via
`integral_exp_conjPair_prod_eq_cast`), and the headline chains it with
the abstract `sum_pinned_dichotomy_le` at `ρ₀ := e^{2δN_c}−1`.

**NO integrability hypothesis families** — discharged internally by the
banked exact-activity integrability lemmas; every remaining hypothesis
is an explicit, jointly satisfiable smallness/geometry condition (for
every `d, N_c`, take `δ` small: `e^{2δN_c}−1 → 0`, so `hr/hsmall/hrσ/hρσ`
hold simultaneously with e.g. `σ = 2·10⁻⁴`).  **THE V4 CAMPAIGN IS
CLOSED.**  All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 19 (2026-06-12, **UV brick U0 — the per-scale reduction of
the sole carried M3 hypothesis** `lattice_mass_gap_of_per_scale_uv`)

**Build:** green (8238 jobs).  Oracle output (verbatim,
`Paper/ClusteringToGap.lean`):

```
'YangMills.lattice_mass_gap_of_per_scale_uv'  [propext, Classical.choice, Quot.sound]
```

The opening brick of the UV campaign (`docs/UV-SINGLE-SCALE-PLAN.md`).
It restates the SOLE carried M3 hypothesis at the renormalization-group
level: the covariance-level `hUV : ∀ t, |covUV t| ≤ C₂·e^{−c₀t}` is
reduced to the SHARP per-scale contraction

    ∀ t k, |R_{t,k}| ≤ (C₂·e^{−c₀t})·rᵏ        (0 ≤ r < 1)

with `covUV t = ∑_{k<n(t)} R_{t,k}` — exactly the form Balaban's
single-scale stability (Lemma 6.2) supplies.  Proof: the banked,
unconditional `Paper.uv_geometric_summation` (§6.3) collapses the scale
sum to the constant `C₂·(1−r)⁻¹`, recovering the `hUV` shape, and the
banked `lattice_mass_gap_of_exp_clustering_uniform` then delivers the
single strictly-positive gap `∃ gap > 0, ∀ t, |cov t| ≤
(C₁+C₂(1−r)⁻¹)·e^{−gap·t}`.  Still hypothesis-carried (never an axiom);
the carried object is now the RG-level per-scale bound `hRsc` rather
than the covariance-level `hUV`.  REMAINING (UV-SINGLE-SCALE-PLAN
U1–U4): define `covUV`/`R_{t,k}` concretely against the KP `clusterSum`
+ the scale dictionary (so `hcovUV` is a theorem), then discharge the
per-scale contraction itself (U2, the genuine Balaban analytic core —
a months-scale campaign).  All M3 lattice-side; M4/M5/Clay untouched.

## Addendum 20 (2026-06-12, **manifest confinement repackaging**
`area_law_to_exp_area_decay`)

**Build:** green (8238 jobs).  Oracle output (verbatim,
`RestrictedGate.lean`):

```
'YangMills.area_law_to_exp_area_decay'  [propext, Classical.choice, Quot.sound]
```

A reusable real-analysis repackaging that turns EITHER area-law
headline bound `Nc·e^{P·K}·σ^{Area}·e^{P·S}` (`P = #loopSupp·4d` the
perimeter charge, `σ < 1` the area rate — the shape of both
`normalized_wilson_loop_area_law` and
`normalized_exp_wilson_loop_area_law`) into MANIFEST exponential decay
in the area, `Nc·e^{−τ·Area}` with a strictly positive string tension
`τ = (−log σ) − λ > 0`, on any loop family whose perimeter
contribution is area-subdominant (`P·(K+S) ≤ λ·Area`, `λ < −log σ`).
Pure analysis (`σ^{Area} = e^{Area·log σ}` via `Real.rpow_def_of_pos`,
`exp` monotonicity); the inequality reduces exactly to the
subdominance hypothesis.  Makes the confinement physics (positive
string tension) of the area law explicit.  ALSO (hard rule #3,
machine-checked non-vacuity): `area_law_to_exp_area_decay_window_nonempty`
exhibits an explicit witness (`σ = 1/2`, `P = K = S = 1`, `λ = 1/2`,
`Area = 4`) with non-degenerate perimeter charge AND strictly positive
string tension `τ = log 2 − 1/2 > 0` (via `Real.log_two_gt_d9`),
certifying the confinement conclusion is genuinely non-trivial.  All M3
lattice-side; M4/M5/Clay untouched.

## Addendum 21 (2026-06-12, **UV frontier audit — negative result +
shopping list**; no Lean change, core unchanged at 8238)

A research-grade audit of the UV frontier (the sole carried M3
hypothesis) established a clean negative result: the only UV-side
material in the tree — the `ClayCore` Balaban scaffolding
(`BalabanH1H2H3`, `SmallFieldBound`, `LargeFieldBound`,
`MultiscaleDecoupling`, `OscillationBound`, `CouplingControl`) — is
**physically vacuous**.  Its hypotheses bound *unconstrained*
existential reals (`∀ n, ∃ R, 0 ≤ R ∧ R ≤ …`, met by `R = 0`); the
"activity" is an arbitrary `Nat → Real` never tied to the Wilson action;
the files contain no `gaugeMeasureFrom`/`WilsonAction`/`sunHaarProb`/
integral; so `balaban_combined_bound : BalabanHyps ⟹ …` is a sound but
EMPTY implication.  This is why the files are correctly excluded from
`YangMillsCore`, and connecting them to the assembly is forbidden
(it would manufacture a green theorem that says nothing about
Yang–Mills — the hollow-progress pattern).  Genuine progress requires
DEFINING the per-scale RG contribution `R_{t,k}` against the actual
gauge measure and PROVING its bound — the Balaban block-spin
construction + single-scale stability estimates, which are NOT in the
repo.  Per mandate, reconstructing them from memory is declined on
honesty grounds; the precise source request (Eriksson [55] Thms
6.2/6.3/8.5; Bałaban CMP 116, 122-II Eq (1.98)–(1.100); Dimock's
"RG according to Balaban" I–III; the paper's `covUV` scale
decomposition) is recorded in `docs/UV-SHOPPING-LIST.md`.  The UV
campaign is **blocked on this source material**; everything proved to
date is unchanged and remains honest.  All M3 lattice-side;
M4/M5/Clay untouched.

## Addendum 22 (2026-06-12, **UNCONDITIONAL fixed-lattice exponential
clustering** `sun_lattice_exponential_clustering`; source-material
campaign, paper audit)

**Build:** green (8238 jobs).  Oracle output (verbatim,
`L1_GibbsMeasure/TwoPlaquetteCorrelator.lean`):

```
'YangMills.sun_lattice_exponential_clustering'  [propext, Classical.choice, Quot.sound]
```

After the user supplied the Balaban gauge series (CMP 95/96/98/99/102/
109/116/122-I/122-II), the Dimock trilogy ("RG according to Balaban"
I/II/III, φ⁴), and the Eriksson AQFT collection, a paper-grounded audit
of the UV frontier produced a **decisive strategic finding**: the §6.3
Balaban single-scale bound is needed only for the **continuum**
(lattice-spacing → 0) limit; the **fixed-lattice** clustering is
already UNCONDITIONAL via the banked cluster expansion.  Concretely,
`sun_two_plaquette_correlator_bound` (no carried hypothesis, only an
explicit smallness window certified non-empty by
`sun_clustering_window_nonempty`) is combined here, at separation
`k = ⌊dist/2⌋`, into:

> **`sun_lattice_exponential_clustering`** — for every `d, N_c` there
> is an explicit `β₀ > 0` such that for all `|β| ≤ β₀`, every bounded
> measurable plaquette observable `f` (`|f| ≤ 1`), and every pair of
> distinct plaquettes `p ≠ q`, the connected (truncated) two-plaquette
> correlator of the genuine SU(N_c) Wilson Gibbs measure satisfies
> `|⟨f_p f_q⟩ − ⟨f_p⟩⟨f_q⟩| ≤ C · exp(−(1/2)·dist(p,q))`, with `C`
> depending only on `d, N_c, β` — NO carried hypothesis.

In exactly the exponential-clustering sense the M3 assembly
(`lattice_mass_gap_of_exp_clustering_uniform`) calls "the lattice mass
gap", this is that statement, UNCONDITIONALLY, at strong coupling.
Proof: `sun_two_plaquette_correlator_bound` at `t = ε = 1`, the
non-empty window for all `k`, and the elementary
`exp(−k) ≤ e^{1/2}·e^{−dist/2}` from `dist ≤ 2⌊dist/2⌋+1`.

**HONEST SCOPE (no inflation).**  This is (i) FIXED lattice spacing —
the correlation length is in lattice units; (ii) STRONG coupling
(small `β`, the cluster-expansion/confining regime), not all `β`;
(iii) a EUCLIDEAN correlation-decay statement — it is NOT a
transfer-matrix/Hamiltonian spectral gap (that needs reflection
positivity + OS), and NOT the continuum mass gap (that needs the
lattice-spacing → 0 control the Balaban §6.3 input provides, plus
OS/Wightman reconstruction — M4/M5, open mathematics).  The §6.3
carried hypothesis therefore remains the sole obstruction to the
*continuum-uniform* statement, and is correctly localized there.
Distance to the Clay prize: **~0% (<0.1%), UNCHANGED** — this
strengthens and clarifies the lattice side, reducing no M4/M5
obstruction.  The Balaban/Dimock source material and the precise
remaining targets are catalogued in `docs/UV-SHOPPING-LIST.md` and
`docs/UV-SINGLE-SCALE-PLAN.md`.

## Addendum 23 (2026-06-12, **GAUGE-RG CAMPAIGN OPENED — brick B1, the
Balaban block-lattice geometry** `YangMills.RG.blockSite`; core 8239)

**Build:** green (**8239 jobs** — first new core module of the
continuum track; the job count incremented from 8238, per the standing
rule).  Oracle outputs (verbatim, `YangMills/RG/BlockLattice.lean`):

```
'YangMills.RG.blockSite'              [propext, Classical.choice, Quot.sound]
'YangMills.RG.blockSite_eq_iff_cube'  [propext, Classical.choice, Quot.sound]
'YangMills.RG.blockSite_surjective'   [propext, Classical.choice, Quot.sound]
'YangMills.RG.mem_blockOf'            [propext, Classical.choice, Quot.sound]
```

The user supplied the full Balaban gauge series (CMP 95/96/98/99/102/
109/116/122) plus Dimock and reference material, and directed the
continuum-facing Balaban renormalization-group track.  After producing
the exact 7-brick Lean-facing ladder (`docs/BALABAN-RG-PLAN.md`, B1–B7),
this addendum closes **B1**, the block-lattice geometry, source-faithful
to **Bałaban, CMP 98 (1985) eqs (1)–(3)** (strategy/framing: **Lluis
Eriksson**, ai.viXra:2602.0088): `blockSite L N' : FinBox d (L·N') →
FinBox d N'`, coordinatewise integer division by the block size `L`
(the order-1 block map of the torus `(ℤ/(L·N'))^d → (ℤ/N')^d`), with
`blockSite_eq_iff_cube` (the half-open `L`-cube characterisation
`L·yᵢ ≤ xᵢ < L·yᵢ+L`, eq (2)), `blockSite_surjective` (every coarse
site is a block, via its lower corner), and `blockOf`/`mem_blockOf` (the
block as a `Finset`).  Pure lattice geometry — no gauge field, no
measure — built against the existing `FinBox` core and reused by every
later brick.  **B3 (the gauge-covariant averaging operator, CMP 98 eqs
(14)–(15)) is BLOCKED** on a clean scan of CMP 98 p.19–20: the uploaded
OCR mangles those formulas (request recorded in `BALABAN-RG-PLAN.md`
§"Missing source").  All M3 lattice-side; continuum (M4)/M5/Clay
untouched — this opens the continuum track but does not yet reduce any
M4/M5 obstruction; Clay distance ~0% (<0.1%), unchanged.

## Addendum 24 (2026-06-12, **gauge-RG brick B3-linear — the linear
averaging operator `Q`** `YangMills.RG.linAvg`; core 8240)

**Build:** green (**8240 jobs**).  Oracle outputs (verbatim,
`YangMills/RG/LinearAveraging.lean`):

```
'YangMills.RG.fineLineSum'  [propext, Classical.choice, Quot.sound]
'YangMills.RG.linAvg'       [propext, Classical.choice, Quot.sound]
'YangMills.RG.linAvg_add'   [propext, Classical.choice, Quot.sound]
'YangMills.RG.linAvg_smul'  [propext, Classical.choice, Quot.sound]
```

Source-faithful to **Bałaban, CMP 95 (1984) eqs (1.6)–(1.8)** (located
after the CMP 98 averaging formula (15) was found OCR-garbled; CMP 95 is
the Gaussian/abelian prototype where the averaging is the explicit
LINEAR operator).  `fineLineSum L N' A μ x` = the fine line integral
`A(Γ_{c,x}) = Σ_{k<L} A⟨shiftᵏ x, μ, +⟩` (eq (1.7)); `linAvg L N' A c`
= `L^{-d} • Σ_{x ∈ blockOf c.source} fineLineSum A c.dir x` (eq (1.8)),
the `L^{-d}`-averaged block line integral, on additive bond fields
valued in any real vector space `V` (the Lie algebra in the gauge
application).  `linAvg_add`/`linAvg_smul` prove `Q` is linear — its
defining algebraic property.  This is the **small-field linearisation**
of the non-abelian averaging operator `Ū` of CMP 98 (14)–(15)
(`log Ū(e^{iA}) = QA + O(‖A‖²)`); the full `Ū` (brick B3-full) remains
BLOCKED on a clean scan of CMP 98 p.19–20 (request in
`docs/BALABAN-RG-PLAN.md`).  Strategy/framing: **Lluis Eriksson**,
ai.viXra:2602.0069, 2602.0088.  Continuum (M4) track; reduces no M4/M5
obstruction yet; Clay distance ~0% (<0.1%), unchanged.

## Addendum 25 (2026-06-12, **gauge-RG brick B2 — coarse/fine block
maps**; + B3-full design unblocked via CMP 109; core 8241)

**Build:** green (**8241 jobs**).  Oracle outputs (verbatim,
`YangMills/RG/BlockMaps.lean`; all axiom sets ⊆ the standard three):

```
'YangMills.RG.blockBasepoint'             [propext]
'YangMills.RG.blockSite_blockBasepoint'   [propext, Classical.choice, Quot.sound]
'YangMills.RG.iterShift_apply_self'       [propext, Quot.sound]
'YangMills.RG.iterShift_apply_ne'         [propext, Quot.sound]
```

Two outcomes after auditing the new uploads (CMP 116, CMP 119 — new;
1.pdf/2.pdf = CMP 122-I/II already held; `ssrn-5836022` = a third-party
claimed Clay solution by S. Borom, set aside as unrefereed/not
source-faithful for our constructions):

1. **B3-full design UNBLOCKED.**  CMP 119 recalls the averaging by
   reference to CMP 109 §0; **CMP 109 (1987) eqs (0.5)–(0.12)** give it
   in clean *axiomatic* form (Bałaban states results hold "universally
   for all averages satisfying the above properties"): a group average
   `M({U_j})` — analytic, permutation-invariant (0.7), with
   linearisation `log M({exp A_j}) = (1/n)ΣA_j + O(‖A‖²)` (0.8) [the tie
   to the linear `Q` of Add. 24], group-closed (0.9), inhabited by the
   **Federbush average** (0.10).  This replaces the OCR-garbled CMP 98
   eq (15) blocker at the design level (recorded in
   `docs/BALABAN-RG-PLAN.md`).

2. **B2 closed** (Bałaban CMP 98 (4)–(5), CMP 109 (0.4)/(0.12)):
   `blockBasepoint` — the lower-corner section of `blockSite`
   (`blockSite_blockBasepoint`, the axial-gauge representative); and the
   iterated-shift coordinate formula `iterShift_apply_self`
   (`shiftᵏ` advances the `μ`-coordinate by `k mod M`, the arithmetic of
   the block-translated site `x(c) = x + L·e_μ`) with `iterShift_apply_ne`
   (other coordinates fixed).  Pure lattice geometry; reused by the
   averaging operator.  Strategy/framing: **Lluis Eriksson**
   (ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0%
   (<0.1%), unchanged.

## Addendum 26 (2026-06-12, **gauge-RG brick B3-full interface — the
axiomatic group average** `YangMills.RG.GroupAverage`; core 8242)

**Build:** green (**8242 jobs**).  Oracle outputs (verbatim,
`YangMills/RG/GroupAverage.lean`; all ⊆ the standard three):

```
'YangMills.RG.GroupAverage.left_equiv'   [propext, Quot.sound]
'YangMills.RG.GroupAverage.right_equiv'  [propext, Quot.sound]
'YangMills.RG.GroupAverage.conj_equiv'   [propext, Quot.sound]
```

The user supplied clean transcriptions of BOTH CMP 98 (14)–(15) and CMP
109 (0.5)–(0.12).  Per the source-faithful route, this brick formalises
**Bałaban's axiomatic group average** (CMP 109 (0.5)–(0.9)) — which he
states governs the construction "universally for all averages satisfying
the above properties": `structure GroupAverage G` over a `Group G`, with
`M : Multiset G → G`, inverse-equivariance `M({U⁻¹}) = (M)⁻¹` (0.5),
bi-equivariance `M({uUv}) = u·M·v` (0.6); permutation invariance (0.7) is
automatic (the domain is a `Multiset`) and group closure (0.9) automatic
(codomain `G`).  Derived: `left_equiv`, `right_equiv`, and the
**gauge-covariance seed** `conj_equiv : M({uU u⁻¹}) = u·M·u⁻¹` (0.6 at
`v=u⁻¹`) — the algebraic root of B4.  Non-vacuous: a constant/trivial `M`
violates (0.6).  The analytic axioms — the near-identity linearisation
(0.8) `(1/i)log M(exp iA_j) = n⁻¹ΣA_j + O(‖A‖²)` (tying `M` to the linear
operator `Q`=`linAvg` of Add. 24) and the Federbush characterisation
(0.10) — plus the averaging operator `Ū` itself (CMP 109 (0.12) / CMP 98
(15)) require a near-identity matrix-`log` framework not yet in the core;
they are carried as named obligations (never axioms), the next sub-brick.
Cross-check (honest): `linAvg` faithfully realises **CMP 95 (1.8)** (the
straight length-`L` line, `L^{-d}`); CMP 98 (14)/CMP 109 (0.12) use the
Euclidean-symmetric refined contour `Γ_{c,x}` with `L^{-(d+1)}`, so
`linAvg` is the CMP 95 prototype, not (yet) Balaban's final averaging —
not overclaimed.  `ssrn-5836022` (Borom) remains set aside.
Strategy/framing: **Lluis Eriksson** (ai.viXra:2602.0069, 2602.0088);
group average due to Bałaban (CMP 109) / Federbush.  Continuum (M4)
track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 27 (2026-06-12, **GroupAverage honesty fix + non-vacuity
certificate** `YangMills.RG.meanAverage`; core 8242)

**Build:** green (8242 jobs).  Oracle (verbatim, `RG/GroupAverage.lean`):

```
'YangMills.RG.GroupAverage.conj_equiv'  [propext, Quot.sound]
'YangMills.RG.meanAverage'              [propext, Classical.choice, Quot.sound]
```

**Adversarial self-audit (correction of Add. 26).**  The `GroupAverage`
interface as first committed (Add. 26) stated its axioms over ALL
multisets, including the empty one — where bi-equivariance (0.6) reads
`M(∅) = u·M(∅)·v` for all `u,v`, forcing the group to be trivial.  So
the unrestricted interface was **unsatisfiable for `SU(N)`, i.e. vacuous**
(any `∀ GroupAverage, …` theorem would be hollow).  Fixed by restricting
the axioms (0.5),(0.6) — and the derived `left/right/conj_equiv` — to
**nonempty** multisets (`L ≠ 0`), exactly as Bałaban states them
(`{U_j : j = 1,…,n}`, `n ≥ 1`).  **Non-vacuity now certified
constructively:** `meanAverage V` inhabits the fixed interface for the
abelian prototype `G = Multiplicative V` (`V` a real vector space) via
the arithmetic mean `M(L) = (#L)⁻¹ • Σ_j A_j`; the proofs of (0.5)/(0.6)
are the genuine mean computations (the nonempty hypothesis enters as
`(#L : ℝ) ≠ 0`).  In additive terms this is precisely the linear
average, so the linearisation axiom (0.8) holds EXACTLY (no
higher-order terms) for this inhabitant — the abelian shadow of the
non-abelian (0.8) tying `M` to `linAvg`.  The non-abelian (0.8), the
Federbush characterisation (0.10), and the operator `Ū` (CMP 109 (0.12))
remain carried obligations awaiting a near-identity matrix-`log`
framework.  Source: Bałaban CMP 109 (0.5)–(0.10); Federbush [35];
strategy **Lluis Eriksson** (ai.viXra:2602.0069).  Continuum (M4) track;
Clay distance ~0% (<0.1%), unchanged.

## Addendum 28 (2026-06-12, **gauge-RG brick B4-prep — holonomy
gauge-covariance along a path** `YangMills.RG.wilsonLine_gaugeAct_path`;
core 8243)

**Build:** green (**8243 jobs**).  Oracle (verbatim,
`YangMills/RG/HolonomyGauge.lean`; all ⊆ the standard three):

```
'YangMills.RG.pathEnd'                   [propext, Quot.sound]
'YangMills.RG.IsPathFrom'                [propext, Quot.sound]
'YangMills.RG.wilsonLine_gaugeAct_path'  [propext, Classical.choice, Quot.sound]
```

A determination first: the pinned Mathlib provides `Matrix.exp` and a
continuous-functional-calculus `log` (self-adjoint elements only) but
**no near-identity matrix logarithm with `log(exp X) = X` and BCH
bounds** — so the analytic axiom (0.8) and the operator `Ū` (CMP 109
(0.12)) genuinely require a from-scratch matrix-`log` layer (a real
sub-campaign; the BCH references are now in hand).  Rather than fake
that, this brick advances the **algebraic** B4 foundation, which needs
no matrix `log`: `wilsonLine_gaugeAct_path` — along a connected path
(`IsPathFrom a es`, the contour structure of CMP 95 (1.7)) the
gauge-transformed Wilson line conjugates by the gauge function at its
endpoints, `wilsonLine (gaugeAct u A) es = u(a)·wilsonLine A es·u(pathEnd a es)⁻¹`,
by a clean telescoping induction over the core `wilsonLine`/`gaugeAct`.
This is exactly the law (CMP 98 (11)) that, combined with
`GroupAverage.conj_equiv`/`biequiv`, makes the averaged contour variable
(0.11) — and hence `Ū` — gauge covariant (brick B4).  Strategy/framing:
**Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track; Clay
distance ~0% (<0.1%), unchanged.

## Addendum 29 (2026-06-12, **gauge-RG brick B5-linear — locality of the
linear averaging operator** `YangMills.RG.linAvg_congr`; core 8243)

**Build:** green (8243 jobs).  Oracle (verbatim, `RG/LinearAveraging.lean`):

```
'YangMills.RG.fineLineSum_congr'  [propext, Classical.choice, Quot.sound]
'YangMills.RG.linAvg_congr'       [propext, Classical.choice, Quot.sound]
```

The locality the renormalization-group cluster expansion relies on
(Bałaban CMP 116), for the linear averaging operator `Q` (needs no
matrix `log`): `linAvg A c` depends only on `A`'s values on the fine
bonds `⟨shiftᵏ x, c.dir, +⟩` for `x ∈ blockOf c.source`, `k < L` — the
fine links inside the coarse bond's block.  `fineLineSum_congr` (the
per-line version) + `linAvg_congr` (the block average) prove that two
bond fields agreeing on those bonds have equal `Q`-averages at `c`.
With B4-prep (the holonomy gauge law, Add. 28) this completes the
*algebraic* half of B4/B5 for the linear operator; the full non-abelian
`Ū` versions await the matrix-`log` layer.  Source: Bałaban CMP 95
(1.8)/116; strategy **Lluis Eriksson** (ai.viXra:2602.0088).  Continuum
(M4) track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 30 (2026-06-12, **gauge-RG brick B4 — gauge covariance of the
averaged contour variable** `YangMills.RG.averagedContour_gaugeAct`;
core 8244)

**Build:** green (**8244 jobs** — incremented, new module
`RG/AveragedContour.lean`).  Oracle (verbatim):

```
'YangMills.RG.averagedContour_gaugeAct'  [propext, Classical.choice, Quot.sound]
```

Bałaban's averaged contour variable (CMP 109 (0.11)) `U(y,x) =
M({U(Γ)}_{Γ∈G(y,x)})` — the group average of the holonomies along all
contours from `y` to `x` — is **gauge covariant**:
`Avg.M (paths.map (wilsonLine (gaugeAct u A))) =
u(y)·Avg.M (paths.map (wilsonLine A))·u(x)⁻¹`, for any group average
`Avg`, gauge transform `u`, config `A`, and any **nonempty** family
`paths` of connected contours all running `y→x`.  Proof: each contour
holonomy conjugates by `u` at the **same** endpoints (B4-prep,
`wilsonLine_gaugeAct_path`, Add. 28), so the whole `Multiset` of
holonomies is `(map (wilsonLine A)).map (W ↦ u(y)·W·u(x)⁻¹)`, and
bi-equivariance (0.6) of the average (`GroupAverage.biequiv`, Add. 26)
pulls the endpoint factors out.  Nonemptiness routed through
`Multiset.map_eq_zero` so `biequiv`'s `L ≠ 0` side condition is met
(the same non-vacuity discipline as Add. 27).

This needs **no matrix logarithm** — it is the gauge covariance (CMP 98
(11)) at the level of the averaged variable, the algebraic heart of B4.
What remains for the full field map `Ū` (brick B4-Ū) is to apply this
pointwise once `Ū` is defined (which does need the matrix-`log` layer).
Source: Bałaban CMP 109 (0.6),(0.11); CMP 98 (11).  Strategy/framing
**Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track; Clay
distance ~0% (<0.1%), unchanged.

## Addendum 31 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-1
— the near-identity logarithm: definition, convergence, norm bound**;
core 8245)

**Build:** green (**8245 jobs** — new module `RG/NearLog.lean`).
Oracle (verbatim):

```
'YangMills.RG.summable_logCoeff_smul_pow'  [propext, Classical.choice, Quot.sound]
'YangMills.RG.norm_nearLog_le'             [propext, Classical.choice, Quot.sound]
'YangMills.RG.nearLog_zero'                [propext, Classical.choice, Quot.sound]
```

The averaging operator `Ū` (CMP 109 (0.12)) is built from the logarithm
of group elements near the identity, and Mathlib provides `NormedSpace.exp`
for Banach algebras but **no logarithm**.  This opens the from-scratch
matrix-`log` layer.  In any complete normed `ℝ`-algebra `𝔸` (matrices
over `ℝ`/`ℂ`, hence the `SU(N)` Lie algebra, qualify):

* `logCoeff n = (-1)^{n+1}/n` (`0` at `n=0`); `abs_logCoeff_le_one`;
* `nearLog Y = ∑' n, logCoeff n • Y^n` (the Mercator series for
  `log(1+Y)`);
* `norm_logCoeff_smul_pow_le : ‖logCoeff n • Y^n‖ ≤ ‖Y‖^n` (`|coeff|≤1`
  + `norm_pow_le'`);
* `summable_logCoeff_smul_pow` (‖Y‖<1): absolute convergence by
  comparison with the geometric series (`Summable.of_norm_bounded`,
  `summable_geometric_of_lt_one`);
* `norm_nearLog_le : ‖nearLog Y‖ ≤ (1-‖Y‖)⁻¹` — the geometric majorant
  the BCH estimates of CMP 109/122 consume (`norm_tsum_le_tsum_norm`,
  `Summable.tsum_le_tsum`, `tsum_geometric_of_lt_one`);
* `nearLog_zero : nearLog 0 = 0`.

Non-vacuity: the inhabiting algebra (`Matrix … ℝ`, `ℂ`) is a genuine
complete normed `ℝ`-algebra, and the convergence/bound are quantitative
(not existential).  The **next** brick (M-log-2) is the local-inverse
identity `log(exp X) = X` near `0` with the `O(‖X‖²)` remainder, which
unblocks the linearisation axiom (0.8) and then `Ū`.  Source: standard
analytic construction; applied to CMP 109 (0.8),(0.12); BCH references
(BCHD.pdf) in hand.  Strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 32 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-2a
— first-order linearisation of the near-identity logarithm**
`YangMills.RG.norm_nearLog_sub_self_le`; core 8245)

**Build:** green (8245 jobs, `RG/NearLog.lean`).  Oracle (verbatim):

```
'YangMills.RG.norm_nearLog_sub_self_le'  [propext, Classical.choice, Quot.sound]
```

`‖nearLog Y - Y‖ ≤ ‖Y‖²/(1-‖Y‖)` for `‖Y‖ < 1` — i.e.
`nearLog Y = Y + O(‖Y‖²)`.  This is **exactly the `O(‖·‖²)` remainder
content of Bałaban's linearisation axiom (0.8)** (CMP 109), the tie of
the averaging operator `M` to the linear operator `Q = linAvg`
(brick B3-linear), and it is obtained directly from the `n ≥ 2` tail of
the Mercator series — it does **not** require the local-inverse identity
`log(exp X)=X` (the still-open brick M-log-2b).  Proof: split the series
with `Summable.tsum_eq_zero_add` twice (`logCoeff 0 = 0` kills the
constant term, `logCoeff 1 = 1` gives the linear term `Y`), leaving the
tail `Σ_{n≥2} logCoeff n • Y^n`; bound it by `Σ_{n≥2} ‖Y‖^n =
‖Y‖²/(1-‖Y‖)` via `norm_tsum_le_tsum_norm`, `Summable.tsum_le_tsum`,
`tsum_mul_left`, `tsum_geometric_of_lt_one`.

What remains for the full (0.8) is **M-log-2b**, `log(exp X) = X` near
`0` (composition of the `exp`/`log` power series) — the genuinely hard
analytic brick.  Source: standard; applied to CMP 109 (0.8).
Strategy/framing **Lluis Eriksson** (ai.viXra:2602.0088).  Continuum
(M4) track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 33 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-2a′
— sharp linear bound on `nearLog`** `YangMills.RG.norm_nearLog_le_linear`;
core 8245)

**Build:** green (8245 jobs).  Oracle:
`'YangMills.RG.norm_nearLog_le_linear' [propext, Classical.choice, Quot.sound]`.

`‖nearLog Y‖ ≤ ‖Y‖/(1-‖Y‖)` for `‖Y‖ < 1`.  This **supersedes**
`norm_nearLog_le` (`≤ (1-‖Y‖)⁻¹`) near the identity: the earlier bound
is `≥ 1` and does not vanish as `Y → 0`, whereas this one exhibits
`nearLog Y = O(‖Y‖)` — the correct small-field behaviour the RG analysis
requires.  Immediate from the linearisation (Add. 32) by the triangle
inequality: `‖nearLog Y‖ ≤ ‖nearLog Y - Y‖ + ‖Y‖ ≤ ‖Y‖²/(1-‖Y‖) + ‖Y‖
= ‖Y‖/(1-‖Y‖)`.

**Honest design note for M-log-2b (the next, genuinely hard brick).**
`log(exp X) = X` near `0` is the local-inverse identity.  Mathlib has
`NormedSpace.exp` (a Banach-algebra `exp`) but **no** matrix/operator
`log` and **no** Banach-algebra functional-calculus substitution lemma,
so the composition `log ∘ exp = id` is not available off the shelf.  The
viable route is the formal-power-series framework
(`FormalMultilinearSeries.comp` / formal inverse): realise the Mercator
series and `expSeries` as formal multilinear series, compose them to the
identity formally, then transfer to `nearLog`/`exp` on the radius of
convergence.  This is a multi-session sub-campaign; it is **not** faked
or stubbed here.  Until it lands, `Ū` (CMP 109 (0.12)) is **not**
defined (a `Ū` without its linearisation/covariance theorems would be
hollow, which the honesty rule forbids), and axiom (0.8) is **not**
claimed proved — only its `O(‖·‖²)` remainder (Add. 32) and the linear
bound (this addendum) are.  Strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 34 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-2c
— scalar correctness + scalar local inverse of `nearLog`**; core 8245)

**Build:** green (8245 jobs).  Oracle (verbatim):

```
'YangMills.RG.nearLog_real'             [propext, Classical.choice, Quot.sound]
'YangMills.RG.nearLog_exp_sub_one_real' [propext, Classical.choice, Quot.sound]
```

Two facts certifying the matrix-`log` layer is **not vacuous**:

* `nearLog_real : nearLog (y : ℝ) = Real.log (1 + y)` for `|y| < 1` —
  on the real line the abstract Mercator sum `nearLog` agrees with the
  genuine `Real.log`.  Proof: drop the (zero) `n=0` term
  (`hasSum_nat_add_iff' 1`), match the tail termwise (`push_cast; ring`)
  against Mathlib's real Mercator series
  `Real.hasSum_pow_div_log_of_abs_lt_one` (negated, `x := -y`), then
  `HasSum.tsum_eq`.
* `nearLog_exp_sub_one_real : nearLog (Real.exp x - 1) = x` for
  `Real.exp x < 2` — the genuine **`log(exp x) = x`** identity in the
  commutative base case (`Real.log_exp`).

This is the **scalar instance of the operator brick M-log-2b**.  It does
NOT establish the operator identity `log(exp X) = X` in a noncommutative
Banach algebra (that still needs formal-power-series composition, the
Mathlib gap), and `Ū`/(0.8) remain unclaimed — but it removes any doubt
that `nearLog` is the right object.  Source: Mathlib real-log series;
applied to CMP 109 (0.8)/(0.12).  Strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 35 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-3
— conjugation-equivariance of `nearLog`** `YangMills.RG.nearLog_conj`;
core 8245)

**Build:** green (8245 jobs).  Oracle:
`'YangMills.RG.nearLog_conj' [propext, Classical.choice, Quot.sound]`.

`nearLog (u·Y·u⁻¹) = u·(nearLog Y)·u⁻¹` for a unit `u : 𝔸ˣ` and `‖Y‖<1`.
This is the **algebraic core of B4-Ū** (gauge covariance of the field map
`Ū`, CMP 109 (0.12)): conjugation `z ↦ u·z·u⁻¹` is a continuous linear
map (`ContinuousLinearMap.mulLeftRight ℝ 𝔸 u u⁻¹`), so it commutes with
the convergent Mercator series via `ContinuousLinearMap.map_tsum`.
Proof: `(u·Y·u⁻¹)^n = u·Y^n·u⁻¹` (induction, `Units.inv_mul`), the
scalar `•` slides through (`mul_smul_comm`, `smul_mul_assoc`), then
`map_tsum` on the summable series.  Needs **no** `log(exp)=id` — so
together with B4-prep (holonomy law) and `GroupAverage.biequiv` it
supplies every algebraic ingredient of `Ū`'s gauge covariance, leaving
only the analytic linearisation (0.8, brick M-log-2b) as the carried
gap.  Source CMP 98 (11)/109 (0.12); strategy **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 36 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-3
(exponent) — conjugation-equivariance of the renormalized exponent
argument** `YangMills.RG.nearLog_sum_smul_conj`; core 8245)

**Build:** green (8245 jobs).  Oracle:
`'YangMills.RG.nearLog_sum_smul_conj' [propext, Classical.choice, Quot.sound]`.

`Σ_{i∈s} wᵢ • nearLog(u·Yᵢ·u⁻¹) = u·(Σ_{i∈s} wᵢ • nearLog Yᵢ)·u⁻¹` —
the weighted sum of near-identity logarithms forming Bałaban's `Ū`
exponent (CMP 109 (0.12), `L^{-d} Σ_x log(...)`) conjugates as a whole.
Lifts `nearLog_conj` (Add. 35) across the finite sum
(`Finset.mul_sum`/`Finset.sum_mul` + the per-term `•`-slide).
Determination recorded: Mathlib already provides the matching exp law,
`NormedSpace.exp_units_conj : exp(u·x·u⁻¹) = u·(exp x)·u⁻¹` (field-free
`NormedSpace.exp`), so the gauge covariance of the **full** `exp[ Σ … ]`
field map is now assembled from existing oracle-clean pieces —
`nearLog_sum_smul_conj` (this) ∘ `exp_units_conj` (Mathlib) — modulo
only the carried analytic linearisation (0.8, brick M-log-2b, still
open).  No `log(exp)=id` used.  Source CMP 109 (0.12); strategy **Lluis
Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track; Clay distance
~0% (<0.1%), unchanged.

## Addendum 37 (2026-06-12, **gauge-RG brick B4-Ū (algebra level) — gauge
covariance of the abstract `Ū`-block** `YangMills.RG.UbarBlock_conj`;
core 8245)

**Build:** green (8245 jobs).  Oracle:
`'YangMills.RG.UbarBlock_conj' [propext, Classical.choice, Quot.sound]`.

Bałaban's renormalized field element (CMP 109 (0.12) shape)
`Ū = exp[ Σ wᵢ • nearLog(deviationᵢ) ] · g` is **gauge covariant**:
`exp[Σ wᵢ•nearLog(u·Yᵢ·u⁻¹)]·(u·g·u⁻¹) = u·(exp[Σ wᵢ•nearLog Yᵢ]·g)·u⁻¹`
for a unit `u`.  Assembled entirely from oracle-clean pieces —
`nearLog_sum_smul_conj` (Add. 36) for the exponent and Mathlib's
`NormedSpace.exp_units_conj` for the exponential — then a base-conjugation
cancellation (`u⁻¹·u = 1`).  **No** `log(exp)=id` (covariance is pure
conjugation-equivariance).  Carries one explicit, satisfiable instance
hypothesis `[NormedAlgebra ℚ 𝔸]` (needed by `NormedSpace.exp`'s lemmas;
satisfied by `Matrix _ _ ℝ`/`ℂ`, so non-vacuous).

This closes the **algebra-level** B4-Ū: every analytic/algebraic
ingredient of the RG field map's gauge covariance is now verified.  What
remains (B4-Ū lattice) is the **definitional** bridge from the abstract
lattice group `G` to `𝔸ˣ` and instantiation on the concrete `Ū` — not an
analytic gap.  The fixed-point linearisation (0.8) still needs the
operator `log(exp)=id` (M-log-2b), which covariance does not.  Source
CMP 109 (0.12)/CMP 98 (11); strategy **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 38 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-4
— second-order remainder of the operator exponential**
`YangMills.RG.norm_exp_sub_one_sub_self_le`; core 8245)

**Build:** green (8245 jobs).  Oracle (verbatim):

```
'YangMills.RG.norm_expTerm_le'                [propext, Classical.choice, Quot.sound]
'YangMills.RG.norm_exp_sub_one_sub_self_le'   [propext, Classical.choice, Quot.sound]
```

`‖NormedSpace.exp Z - 1 - Z‖ ≤ ‖Z‖²/(1-‖Z‖)` for `‖Z‖<1`, i.e.
`exp Z = 1 + Z + O(‖Z‖²)`.  Proved from the `n ≥ 2` tail of the
exponential series (`NormedSpace.exp_eq_tsum ℝ`), mirroring
`norm_nearLog_sub_self_le`: split off the `n=0` term (`= 1`) and `n=1`
term (`= Z`), bound the remaining tail by `Σ_{n≥2} ‖Z‖^n = ‖Z‖²/(1-‖Z‖)`
(termwise `‖(n!)⁻¹•Z^n‖ ≤ ‖Z‖^n`, brick `norm_expTerm_le`).

**Significance for (0.8):** combined with `nearLog Y = Y + O(‖Y‖²)`
(Add. 32) and the sharp bound `‖nearLog Y‖ ≤ ‖Y‖/(1-‖Y‖)` (Add. 33),
this gives `exp(nearLog Y) = 1 + Y + O(‖Y‖²)` — the genuine content of
Bałaban's linearisation axiom (0.8) (the RG map is the identity to first
order) **without** the exact local-inverse identity `log(exp)=id` (brick
M-log-2b).  Carries one explicit, satisfiable instance `[NormOneClass 𝔸]`
(the `n=0` term `1` needs `‖1‖=1`; satisfied by matrix algebras).
Source standard / CMP 109 (0.8); strategy **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 39 (2026-06-12, **gauge-RG matrix-`log` layer, brick M-log-5
— the RG map linearises to the identity (quantitative axiom (0.8))**
`YangMills.RG.norm_exp_nearLog_sub_one_sub_self_le`; core 8245)

**Build:** green (8245 jobs).  Oracle:
`'YangMills.RG.norm_exp_nearLog_sub_one_sub_self_le' [propext, Classical.choice, Quot.sound]`.

For `‖Y‖ < 1/2`,
`‖exp(nearLog Y) - 1 - Y‖ ≤ ‖nearLog Y‖²/(1-‖nearLog Y‖) + ‖Y‖²/(1-‖Y‖)`,
i.e. **`exp(nearLog Y) = 1 + Y + O(‖Y‖²)`**.  This is the genuine
quantitative content of Bałaban's linearisation axiom (0.8): the
renormalization-group field map is the identity to first order plus an
explicitly-bounded quadratic correction.  Assembled by the triangle
inequality from the operator-exp remainder (M-log-4, Add. 38) applied
at `Z = nearLog Y` and the `nearLog` remainder (M-log-2a, Add. 32);
`‖nearLog Y‖<1` is discharged from `‖Y‖<1/2` via the sharp linear bound
(M-log-2a′, Add. 33).  The two quadratic contributions are kept explicit
(no constant-chasing).  Carries `[NormOneClass 𝔸]` (satisfiable, matrix
algebras).

**Strategic consequence.** The exact local-inverse identity `log(exp)=id`
(M-log-2b) is now demoted from blocker to optional polish: gauge
covariance never needed it (B4-Ū closed, Add. 37) and the (0.8)
linearisation is obtained without it (this addendum).  Source CMP 109
(0.8); strategy **Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4)
track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 40 (2026-06-12, **gauge-RG brick B4-Ū lattice bridge —
matrix realization of the gauge group + transported holonomy law**
`YangMills.RG.rep_wilsonLine_gaugeAct`; core 8246)

**Build:** green (**8246 jobs** — incremented, new module
`RG/MatrixRealization.lean`).  Oracle:
`'YangMills.RG.rep_wilsonLine_gaugeAct' [propext, Classical.choice, Quot.sound]`.

Introduces the bridge between the abstract lattice gauge group and the
matrix algebra where `Ū`'s `exp`/`log` covariance lives:

* `class MatrixRealization (G) (𝔸)` — a representation `rep : G →* 𝔸ˣ`
  of the lattice gauge group as units of a complete normed ℝ-algebra.
  Inhabited (e.g. `G = 𝔸ˣ`, identity hom), hence **non-vacuous**; the
  physical instance is `SU(N)`'s defining representation.
* `rep_wilsonLine_gaugeAct` — the lattice holonomy gauge law
  (`wilsonLine_gaugeAct_path`, Add. 28) transported into `𝔸ˣ` through
  `rep`: `rep(wilsonLine(gaugeAct u A) es) = rep(u a)·rep(wilsonLine A es)·rep(u end)⁻¹`
  (just `map_mul`/`map_inv` on the group-level law).

This connects the abstract `GaugeConfig`/`wilsonLine` core to the
algebra-level conjugation laws (`nearLog_conj`, `UbarBlock_conj`) that
make `Ū` gauge covariant.  What remains (B4-Ū full) is to assemble the
concrete lattice `Ū` from the realized contour variables and instantiate
`UbarBlock_conj` — a definitional task on top of this bridge, no analysis.
Source CMP 98 (11)/109; strategy **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 41 (2026-06-12, **gauge-RG matrix-`log` layer — small-field
stability of the renormalized field** `YangMills.RG.norm_exp_nearLog_sub_one_le`;
core 8246, U1 ingredient)

**Build:** green (8246 jobs).  Oracle:
`'YangMills.RG.norm_exp_nearLog_sub_one_le' [propext, Classical.choice, Quot.sound]`.

For `‖Y‖ < 1/2`,
`‖exp(nearLog Y) - 1‖ ≤ ‖Y‖ + (‖nearLog Y‖²/(1-‖nearLog Y‖) + ‖Y‖²/(1-‖Y‖))`,
i.e. `‖exp(nearLog Y) - 1‖ ≤ ‖Y‖ + O(‖Y‖²)`: the **renormalized field
deviation is controlled by the original deviation**, equal to it at
leading order.  This is the boundedness Bałaban's small-field
single-scale bound (UV plan **U1**) is built on — the small-field region
is preserved by the `exp ∘ nearLog` step.  Immediate from the
linearisation (M-log-5, Add. 39) by the triangle inequality.  Carries
`[NormOneClass 𝔸]`.  Source CMP 109 small-field / UV plan U1; strategy
**Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track; Clay
distance ~0% (<0.1%), unchanged.

## Addendum 42 (2026-06-12, **gauge-RG UV-U1 brick S1 — ℓ² averaging
bound for the linear operator `Q`** `YangMills.RG.norm_linAvg_sq_le`;
core 8247)

**Build:** green (**8247 jobs** — incremented, new module
`RG/AveragingL2.lean`).  Oracle:
`'YangMills.RG.norm_linAvg_sq_le' [propext, Classical.choice, Quot.sound]`.

Opens the small-field per-scale-contraction campaign
(`docs/UV-U1-SMALL-FIELD-PLAN.md`, brick S1):
`‖linAvg A c‖² ≤ (L^d)⁻¹·L · ∑_{(x,k)∈block×range L} ‖A⟨shiftᵏ x, dir, +⟩‖²`.
The certified Cauchy–Schwarz mean-square bound on the block average,
with factor `(L^d)⁻¹·L = L^{1-d}`.  **Honest calibration (adversarial
self-audit):** this is *not* a standalone contraction — the line
integral sums `L` fine bonds, so on a constant field of size `ε` the
right side is `L^{1-d}·L^{d+1}·ε² = L²ε²`, i.e. coarse-bond *growth* by
`L` (correct: a coarse bond spans `L` fine bonds).  Bałaban's per-scale
contraction appears only after the RG **field rescaling** and the
**ℓ²(lattice) operator assembly with multiplicity** (brick S2); S1 is
the certified Cauchy–Schwarz input to that, not the contraction itself.
Proof:
collapse the block double sum to a sum over `blockOf ×ˢ range L`
(`Finset.sum_product`), bound the smul-norm by the ℓ¹ sum
(`norm_smul`, `norm_sum_le`), square (`pow_le_pow_left₀`), and apply
Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) with
`#(blockOf ×ˢ range L) = L^d·L` (`Finset.card_product`, `blockOf_card`).

This is the **first brick of U1** (`docs/UV-SINGLE-SCALE-PLAN.md`), the
small-field half of the per-scale RG-stability bound `|R_k| ≤ M·rᵏ`.
Honest scope: S1 is the deterministic Cauchy–Schwarz seed; the genuine
analytic core (**S2**, the Gaussian/propagator covariance contraction,
Bałaban CMP 95–96) remains a months-scale campaign requiring the
renormalized Gaussian measure (not in Mathlib).  Source CMP 95; strategy
**Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track; Clay
distance ~0% (<0.1%), unchanged.

## Addendum 43 (2026-06-12, **gauge-RG UV-U1 brick S1′ — the ℓ²(lattice)
operator contraction of `Q`** `YangMills.RG.linAvg_l2_le`; core 8247)

**Build:** green (8247 jobs).  Oracle (verbatim):

```
'YangMills.RG.linAvg_l2_le'  [propext, Classical.choice, Quot.sound]
'YangMills.RG.sum_blockOf'   [propext, Classical.choice, Quot.sound]
```

`∑_{y',μ} ‖linAvg A ⟨y',μ,+⟩‖² ≤ (L^d)⁻¹·L² · ∑_{z,μ} ‖A⟨z,μ,+⟩‖²`, i.e.
`∑_bonds ‖Q A‖² ≤ L^{2-d}·∑_bonds ‖A‖²`.  **This corrects and completes
the S1 audit (Add. 42):** while the *per-bond* Cauchy–Schwarz bound is
not a contraction (the line sum grows by `L`), the *ℓ²-summed* bound IS
— the factor is `L^{2-d}`, which is `< 1` for `d ≥ 3` (the physical
`d = 4` gives `L^{-2}`).  The bare averaging operator is a genuine
**ℓ²-contraction**, the deterministic backbone of Bałaban's small-field
RG step.

Mechanism (and why the exponent is `2-d` not `1-d`): summing the
per-bond bound (Add. 42, factor `L^{1-d}`) over all bonds, each fine
bond `⟨z,μ,+⟩` is hit by **exactly `L`** of the block/line triples — the
blocks tile the lattice (`sum_blockOf`, the fibers of `blockSite`) and
for each line offset `k` the shift `(shift μ)^[k]` is a bijection
(`shift_bijective`/`iterShift_bijective`, two-sided inverse
`shiftBack`).  So the multiplicity is `L`, giving `L^{1-d}·L = L^{2-d}`.
Proof: `Finset.sum_fiberwise_of_maps_to` (partition),
`Function.Bijective.sum_comp` (reindex per `k`), `Finset.sum_const`
(the `L` copies).

This is the genuine, certified deterministic contraction of brick S1′;
the remaining **S2** (the rescaled version against the renormalized
Gaussian covariance, Bałaban CMP 95–96) is the months-scale analytic
core.  Source CMP 95; strategy **Lluis Eriksson** (ai.viXra:2602.0088).
Continuum (M4) track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 44 (2026-06-12, **gauge-RG UV-U1 — explicit ℓ²-contraction
ratio of `Q`** `YangMills.RG.linAvg_l2_contraction`; core 8247)

**Build:** green (8247 jobs).  Oracle:
`'YangMills.RG.linAvg_l2_contraction' [propext, Classical.choice, Quot.sound]`.

For `d ≥ 3` (the physical `d = 4`):
`∑_bonds ‖Q A‖² ≤ L⁻¹ · ∑_bonds ‖A‖²`.  The bare averaging operator
contracts the bond ℓ²-norm by a factor of at least `1/L` (`< 1` for
`L ≥ 2`) — the explicit geometric-contraction ratio the per-scale RG
decay (`Paper.uv_geometric_summation`, UV plan U3) consumes.  From
`linAvg_l2_le` (Add. 43) and `L^{2-d} ≤ L^{-1}` (i.e. `L³ ≤ L^d`,
`gcongr` on the inverse-power) with `(L^3)⁻¹·L² = L⁻¹` (`field_simp`).
Source CMP 95; strategy **Lluis Eriksson** (ai.viXra:2602.0088).
Continuum (M4) track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 45 (2026-06-12, **gauge-RG UV-S2 brick G1 — the averaging
operator as a continuous linear map** `YangMills.RG.linAvgCLM`; core 8247)

**Build:** green (8247 jobs).  Oracle:
`'YangMills.RG.linAvgCLM' [propext, Classical.choice, Quot.sound]`.

`linAvgCLM L N' : (ConcreteEdge d (L*N') → V) →L[ℝ] (ConcreteEdge d N' → V)`
(for `[FiniteDimensional ℝ V]`): the linear averaging operator `Q`
bundled as a **continuous linear map** (`LinearMap.toContinuousLinearMap`
on finite-dimensional fibres; linearity from `linAvg_add`/`linAvg_smul`),
with `linAvgCLM_apply : linAvgCLM L N' A = linAvg L N' A`.

**Why this is on the critical path (not scaffolding).**  A verified
Mathlib finding (2026-06-12): `ProbabilityTheory.isGaussian_map
(L : E →L[ℝ] F) : IsGaussian (μ.map L)` is an *instance* — the
pushforward of a Gaussian under a CLM is Gaussian.  So `linAvgCLM` is
exactly the object whose Gaussian pushforward is the **free
renormalization-group step** (`docs/UV-S2-GAUSSIAN-PLAN.md`, opening the
S2 campaign): the coarse free field is automatically Gaussian, and its
covariance is controlled by the proven operator contraction
`linAvg_l2_le`/`linAvg_l2_contraction` (Add. 43–44).  S2's free-field
core (G1–G4) is therefore reachable on existing Mathlib infrastructure;
the interacting correction (G5, the gauge fluctuation integral) remains
the months-scale wall and is the subject of a precise source request
(UV-S2 plan §"Precise source request": Bałaban CMP 95 §2–3 covariance
bound, CMP 96 transformation law, CMP 122-II Thm 1).  Source CMP 95;
strategy **Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track;
Clay distance ~0% (<0.1%), unchanged.

## Addendum 46 (2026-06-12, **gauge-RG UV-S2 brick G3 — covariance
transformation law of the free RG step** `YangMills.RG.covarianceBilinDual_map_clm`;
core 8248)

**Build:** green (**8248 jobs** — incremented, new module
`RG/GaussianStep.lean`).  Oracle:
`'YangMills.RG.covarianceBilinDual_map_clm' [propext, Classical.choice, Quot.sound]`.

For a Gaussian measure `μ` on `E`, a continuous linear map `Q : E →L[ℝ] F`,
and a dual functional `L`:
`covarianceBilinDual (μ.map Q) L L = covarianceBilinDual μ (L∘Q) (L∘Q)`.
Pushing a Gaussian forward under `Q` transforms its covariance bilinear
form by precomposition with `Q` on the dual — the free
renormalization-group step on the covariance, `C ↦ Q C Qᵀ`.  Proved on
Mathlib's `ProbabilityTheory.IsGaussian` framework: the diagonal of the
covariance form is the variance (`covarianceBilinDual_self_eq_variance`,
using `IsGaussian.memLp_two_id` — valid for `μ.map Q` too, Gaussian via
the `isGaussian_map` instance), and variance pushes back under the map
(`variance_map`).

**Significance.** Together with `isGaussian_map` (coarse field is
Gaussian) and the proven operator contraction `linAvg_l2_le`/
`linAvg_l2_contraction` (Add. 43–44), this is the **free fixed-point**
half of S2 (`docs/UV-S2-GAUSSIAN-PLAN.md`, G3): the free RG step maps a
Gaussian to a Gaussian whose covariance is `Q C Qᵀ`, with ℓ²-scale
contracting by `≤ L⁻¹` in `d = 4`.  Stated abstractly for any CLM, so it
is reusable and instantiates at `linAvgCLM`.  The interacting correction
(G5, the gauge fluctuation integral) remains the months-scale wall
(precise source request: UV-S2 plan).  Source standard / CMP 95–96;
strategy **Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track;
Clay distance ~0% (<0.1%), unchanged.

## Addendum 47 (2026-06-12, **gauge-RG UV-S2 brick G4 — free covariance
contraction + Bałaban source-bound audit**
`YangMills.RG.covarianceBilinDual_map_le`; core 8248)

**Build:** green (8248 jobs).  Oracle:
`'YangMills.RG.covarianceBilinDual_map_le' [propext, Classical.choice, Quot.sound]`.

`covarianceBilinDual (μ.map Q) L L ≤ B·‖Q‖²·‖L‖²` given a covariance
bound `∀ M, covarianceBilinDual μ M M ≤ B·‖M‖²` (`0 ≤ B`).  The
operator-norm form of the free RG step `C ↦ Q C Qᵀ`: the pushed-forward
covariance contracts by `‖Q‖²`.  Hypothesis `B` is exactly the Bałaban
fluctuation-covariance bound `‖C_k‖ ≤ c·L²` (CMP 95 Prop 1.1/1.2); with
the deterministic `‖Q‖² ≤ L^{2-d}` (`linAvg_l2_le`, Add. 43) at
`Q = linAvgCLM` this is the per-scale **free** covariance contraction
(S2 brick G4).  Proof: transformation law (`covarianceBilinDual_map_clm`,
Add. 46) + `‖L∘Q‖ ≤ ‖L‖‖Q‖`.  Stated with the covariance bound as an
explicit hypothesis (not `‖covarianceBilinDual μ‖`, whose bilinear
opNorm instance did not synthesise), which is also the faithful CMP 95
input shape.

**Source audit (this addendum's second half).**  The user supplied the
requested Bałaban/Dimock material; faithful transcriptions are recorded
in **`docs/BALABAN-SOURCE-BOUNDS.md`** with citations: CMP 95 covariance
bound (`‖∇^r C_k ∇^{*s}‖ ≤ c L^{2-r-s}`, eqs 1.89/1.114); CMP 122-II
Theorem 1 polymer bounds (2.31[III] `g_j^{κ₀}e^{−κd}`, 1.100
`e^{−p₀(g_k)}e^{−κd}`); Dimock II fluctuation-integral architecture.
**Honesty correction:** Bałaban does NOT state `|R_k| ≤ M·rᵏ` — that is a
simplified surrogate valid only under an extra coupling-flow assumption
(`g_k^{κ₀} ≤ C·rᵏ`).  `docs/UV-SINGLE-SCALE-PLAN.md` §3 now records this
caveat; the existing U0 theorems remain honest implications from their
stated (surrogate) hypothesis, but the true §6.3 obligation is the
polymer bound + coupling-flow assumption.  Source CMP 95/122-II, Dimock
arXiv:1212.5562; strategy **Lluis Eriksson** (ai.viXra:2602.0088).
Continuum (M4) track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 48 (2026-06-12, **gauge-RG UV audit-gap closer — the
coupling-flow bridge** `YangMills.RG.coupling_flow_bridge`; core 8249)

**Build:** green (**8249 jobs** — new module `RG/CouplingFlowBridge.lean`).
Oracle:
`'YangMills.RG.coupling_flow_bridge' [propext, Classical.choice, Quot.sound]`.

Closes the audit gap exposed in Add. 47.  For `0 < r ≤ 1`, `1 ≤ κ₀`,
`0 ≤ A`, `0 ≤ C`, running coupling `g_k ≥ 0`:
`(∀k, g_k ≤ C·rᵏ)` (coupling-flow decay) and `(∀k, |R_k| ≤ A·g_k^{κ₀})`
(Bałaban's faithful polymer bound, CMP 122-II / [III] §2 2.31[III]/1.100)
together give `∀k, |R_k| ≤ (A·C^{κ₀})·rᵏ` — the surrogate consumed by
`Paper.uv_geometric_summation`.  Proof: `g_k^{κ₀} ≤ (C·rᵏ)^{κ₀} =
C^{κ₀}·(rᵏ)^{κ₀} ≤ C^{κ₀}·rᵏ` (the last via `Real.rpow_le_rpow_of_exponent_ge`,
`(rᵏ)^{κ₀} ≤ (rᵏ)^1` for `0 < rᵏ ≤ 1`, `κ₀ ≥ 1`), then `Real.rpow_le_rpow`/
`Real.mul_rpow`.

**Why this is the honest closer, not a shortcut.**  It encodes ONLY the
logical transfer; the two analytically-hard facts are the explicit
hypotheses `hg` (coupling-flow decay — the RG stability of the coupling)
and `hpoly` (the polymer/cluster bound — the Dimock fluctuation integral
+ cluster-expansion-with-holes).  Neither is claimed proved.  The
`sorry`-containing `cluster_expansion_with_holes` sketch from the
supplied research was **deliberately not imported** (iron rule: no
`sorry`).  So the assembly can now depend on the surrogate `|R_k| ≤ M·rᵏ`
via a faithful, oracle-clean implication from Bałaban's true bound +
coupling decay, with the open content sharply isolated.  Sources
(BALABAN-SOURCE-BOUNDS.md): CMP 122-II Thm 1; Dimock arXiv:1212.5562
§§3.8/3.13–3.14.  Strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 49 (2026-06-12, **gauge-RG UV `hg` discharge — geometric
coupling decay from the irrelevant logistic recursion**
`YangMills.RG.logistic_geometric_decay` / `remainder_geometric_of_logistic`;
core 8250)

**Build:** green (**8250 jobs** — new module `RG/CouplingFlow.lean`).
Oracle (verbatim):

```
'YangMills.RG.logistic_geometric_decay'        [propext, Classical.choice, Quot.sound]
'YangMills.RG.remainder_geometric_of_logistic' [propext, Classical.choice, Quot.sound]
```

Discharges the coupling-flow hypothesis `hg : g_k ≤ C·rᵏ` of
`coupling_flow_bridge` (Add. 48) from the explicit RG recursion, **for the
canonically-irrelevant mechanism**:

* `geometric_decay_of_contraction`: `0 ≤ a`, `a_{k+1} ≤ r·a_k` ⟹
  `a_k ≤ rᵏ·a_0` (induction).
* `logistic_step_le`: `r·x·(1−β·x) ≤ r·x` for `0 ≤ βx ≤ 1` (small field).
* `logistic_geometric_decay`: the irrelevant logistic recursion
  `g_{k+1} ≤ r·g_k·(1−β·g_k)` ⟹ `g_k ≤ rᵏ·g_0`.
* `remainder_geometric_of_logistic`: composing with the bridge,
  (irrelevant coupling recursion) + (polymer bound `|R_k| ≤ A·g_k^{κ₀}`)
  ⟹ `|R_k| ≤ (A·g_0^{κ₀})·rᵏ`.

Source: Faria da Veiga–O'Carroll, Physica Scripta 99 (2024) 095262
(irrelevant logistic case); Goswami AHP 2019 (`V^{irr}_k ≤ C·rᵏ`,
`r=L^{−2}`).

**HONESTY CAVEAT (critical, recorded in the module header and
`docs/BALABAN-SOURCE-BOUNDS.md` §4).**  This geometric decay is the
**irrelevant-operator** mechanism (`r < 1` = canonical scaling of an
irrelevant operator, e.g. `L^{−2}`).  The **4D marginal gauge coupling**
decays only **logarithmically** (`λ_n ∼ 1/(βn)`, asymptotic freedom — the
`α=1` telescoping of the same reference), so `g_k ≤ C·rᵏ` is FALSE for the
4D marginal coupling.  In 4D YM the geometric remainder contraction comes
from the irrelevant operators' scaling; the recursion `hrec` here models
those, `r` is their factor.  No inflation of 4D applicability.

This discharges one of the bridge's two hypotheses (`hg`) for the
relevant mechanism; the other (`hpoly`, the cluster expansion / Dimock
fluctuation integral) remains the months-scale analytic core (sources
now transcribed: Dimock II Appendix F, §4–5 of BALABAN-SOURCE-BOUNDS).
Strategy/framing **Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4)
track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 50 (2026-06-12, **gauge-RG UV `hpoly` summation step + full
assembled conditional** `YangMills.RG.polymer_remainder_bound` /
`geometric_remainder_assembled`; core 8251)

**Build:** green (**8251 jobs** — new module `RG/PolymerRemainder.lean`).
Oracle (verbatim):

```
'YangMills.RG.polymer_remainder_bound'      [propext, Classical.choice, Quot.sound]
'YangMills.RG.geometric_remainder_assembled' [propext, Classical.choice, Quot.sound]
```

* `polymer_remainder_bound`: if `R_k = ∑_Y H_k(Y)` (absolutely summable),
  each activity `|H_k(Y)| ≤ A·g_k^{κ₀}·w(Y)`, and `∑_Y w(Y) ≤ K₀`, then
  `|R_k| ≤ (A·K₀)·g_k^{κ₀}` — the `hpoly` input of `coupling_flow_bridge`.
  Proof: `norm_tsum_le_tsum_norm` + `Summable.tsum_le_tsum` +
  `tsum_mul_left`.  The two hypotheses `hact` (activity decay) and `hwK`
  (geometric summability) are **exactly Dimock's two cluster-expansion-
  with-holes estimates**, carried explicitly; this proves the *summation*
  that consumes them.
* `geometric_remainder_assembled`: composing with Add. 49, the full UV
  chain — (cluster-expansion estimates `hact`/`hwK`) + (irrelevant
  coupling recursion `hrec`/`hb`) ⟹ `|R_k| ≤ (A·K₀·g_0^{κ₀})·r^k`, the
  geometric remainder consumed by `Paper.uv_geometric_summation`.

**Honest status (the fork, resolved per iron rules).**  Three external
analyses (ChatGPT, Opus, Gemini) framed the choice: *state* `hpoly` as
interface+axiom (forbidden: no `sorry`/axiom) vs *prove* the full cluster
expansion (months-scale, Mathlib-empty).  Taken: the **third path** —
prove the genuine *summation step* abstractly, with Dimock's two
estimates as explicit carried hypotheses (NOT axioms) and the
cluster-expansion constants (`κ`, `κ₀`, `3κ₀+3`) kept as **parameters**
(per Opus's miscalibration warning; verbatim values, Dimock II Appendix F
vs Dimock III arXiv:1304.0705, must be read off the page).  This shrinks
the frontier by the summation step and isolates the remaining content
precisely: the carried `hact`/`hwK` (the cluster expansion itself) and
`hrec` (the coupling recursion) are the genuinely-unproved analytic
inputs — the months-scale core, NOT done here, NOT claimed.

Source Dimock I/II/III; strategy **Lluis Eriksson** (ai.viXra:2602.0088).
Continuum (M4) track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 51 (2026-06-12, **gauge-RG UV — geometric summability core**
`YangMills.RG.geometric_size_summability`; core 8251)

**Build:** green (8251 jobs).  Oracle:
`'YangMills.RG.geometric_size_summability' [propext, Classical.choice, Quot.sound]`.

`∑_n c_n·qⁿ ≤ (1 − C·q)⁻¹` for `0 ≤ c_n ≤ Cⁿ`, `0 ≤ q`, `0 ≤ C`,
`C·q < 1`.  The Kotecký–Preiss / Appendix-F convergence criterion in its
analytic core: per-size polymer count `c_n` bounded by the animal bound
`Cⁿ`, per-size decay `q = e^{−κ₀}`, smallness `C·q < 1` ⟹ geometric
summability with `K₀ = (1−Cq)⁻¹`.  This **reduces the cluster-expansion
summability `hwK`** (consumed by `polymer_remainder_bound`, Add. 50) to
the **polymer animal-counting bound `c_n ≤ Cⁿ`** — pure lattice
combinatorics, the one remaining elementary input on the summability
branch.  Proof: termwise comparison `c_n qⁿ ≤ (Cq)ⁿ` + `tsum_geometric_of_lt_one`.

Status: the cluster-expansion-with-holes (`hact`/`hwK`) now decomposes
into (i) the activity-decay bound `hact` (the renormalized polymer
activity estimate, Dimock II/III — still the months-scale core) and
(ii) the summability `hwK`, whose analytic convergence is now reduced
(this addendum) to the combinatorial animal count.  Source Dimock I/II/III,
Kotecký–Preiss; strategy **Lluis Eriksson** (ai.viXra:2602.0088).
Continuum (M4) track; Clay distance ~0% (<0.1%), unchanged.

## Addendum 52 (2026-06-12, **gauge-RG — end-to-end UV conditional:
cluster bound + coupling decay ⟹ lattice mass gap**
`YangMills.RG.lattice_mass_gap_of_cluster_and_coupling`; core 8252)

**Build:** green (**8252 jobs** — new module `RG/UVMassGap.lean`).
Oracle:
`'YangMills.RG.lattice_mass_gap_of_cluster_and_coupling' [propext, Classical.choice, Quot.sound]`.

Closes the loop end-to-end.  From
* `hRpoly`: the RG remainder activity bound `|R_{t,k}| ≤ A·e^{−c₀t}·g_k^{κ₀}`
  (spatial decay × coupling power — the Dimock cluster-expansion output),
* `hg`: the coupling-flow decay `g_k ≤ C·rᵏ`,
* `hIRbound`: the theorem-fed IR clustering bound,
* `hcovUV`: `covUV t = ∑_{k<nsc t} R_{t,k}` (covariance as scale-sum),

it derives the **lattice mass gap**
`∃ gap > 0, ∀ t, |covIR t + covUV t| ≤ (C₁ + A·C^{κ₀}·(1−r)⁻¹)·e^{−gap·t}`.
Proof: for each distance `t`, `coupling_flow_bridge` (Add. 48) with
amplitude `A·e^{−c₀t}` turns `hRpoly`/`hg` into the per-scale bound
`|R_{t,k}| ≤ (A·C^{κ₀}·e^{−c₀t})·rᵏ` = the `hRsc` hypothesis of the banked
`lattice_mass_gap_of_per_scale_uv` (Add. 19), which then yields the gap.

**Significance.**  The entire §6.3 UV branch is now a SINGLE oracle-clean
conditional theorem whose only unproved inputs are the two faithful
Bałaban analytic facts — the cluster-expansion activity bound `hRpoly`
and the coupling-flow decay `hg`.  Everything from those to the lattice
mass gap (the bridge, the geometric summation, the assembly) is verified.
The §6.3 obligation is thus reduced, end to end, to `hRpoly` + `hg`.
Honest caveats unchanged: `hg`'s geometric form is the irrelevant
mechanism (4D marginal coupling is logarithmic, Add. 49); discharging
`hRpoly` is the months-scale cluster-expansion-with-holes core; and even
a full discharge gives only the *lattice* gap (M4/M5 untouched, Clay
distance ~0% (<0.1%)).  Source CMP 122-II / Dimock; strategy **Lluis
Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track.

## Addendum 53 (2026-06-12, **gauge-RG UV — summability `hwK` reduced to
the polymer animal-count** `YangMills.RG.polymer_weight_summability`;
core 8252)

**Build:** green (8252 jobs).  Oracle:
`'YangMills.RG.polymer_weight_summability' [propext, Classical.choice, Quot.sound]`.

For polymers `Y` graded by `size : ι → ℕ` with finite per-size fibers,
animal-count bound `#{size = n} ≤ Cⁿ`, per-size decay `q` with `C·q < 1`
(and the weights summable):
`∑_Y q^{size Y} ≤ (1 − C·q)⁻¹`.  This **reduces the cluster-expansion
summability `hwK`** (the `∑_{X⊇□} e^{−κ₀ d} ≤ K₀` substrate, with
`q = e^{−κ₀}`, `K₀ = (1−Cq)⁻¹`) to the **polymer animal-counting bound
`c_n ≤ Cⁿ`** — pure lattice combinatorics.  So the summability branch of
`hRpoly` no longer needs a carried *analytic* hypothesis; it needs only a
combinatorial count.  Proof: fiber decomposition by `size`
(`Equiv.sigmaFiberEquiv`, `Summable.tsum_sigma`, per-fiber
`tsum_fintype`/`Finset.sum_const`), landing on `geometric_size_summability`
(Add. 51).

The cluster-expansion-with-holes now decomposes as: (i) the
activity-*decay* bound `|H_k(Y)| ≤ amp·q^{size Y}` (the Dimock fluctuation
integral + holes localization — the months-scale analytic core, carried);
(ii) the summability, now reduced (this addendum) to the animal count.
Source Dimock I/II/III, Kotecký–Preiss; the existing `KP` layer's
`kp_per_size_bound` is the matching abstract framework
(`docs/BALABAN-SOURCE-BOUNDS.md` §6).  Strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 54 (2026-06-12, **gauge-RG — asymptotic freedom: the 4D
marginal coupling decays only logarithmically**
`YangMills.RG.inv_coupling_linear_growth`; core 8252)

**Build:** green (8252 jobs).  Oracle:
`'YangMills.RG.inv_coupling_linear_growth' [propext, Classical.choice, Quot.sound]`.

For the marginal recursion `g_{k+1} = g_k·(1 − β·g_k)` (`α = 1`, the 4D
case) with `0 < g_k`, `β·g_k < 1`, `0 ≤ β`: **the inverse coupling grows
at least linearly**, `1/g_0 + β·n ≤ 1/g_n`.  Hence `g_n ≤ (1/g_0 + βn)⁻¹
→ 0` like `1/(βn)` — **logarithmic, not geometric**.  Proof: reciprocal
telescoping, `1/g_{k+1} = (1/g_k)·(1−x)⁻¹ ≥ (1/g_k)(1+x) = 1/g_k + β`
(`x = β g_k`, `(1−x)(1+x) = 1−x² ≤ 1`), then induction.

This is the **honest counterpart** to the geometric (irrelevant) decay
`logistic_geometric_decay` (Add. 49): it *proves* that `g_k ≤ C·rᵏ` is
FALSE for the 4D marginal gauge coupling (asymptotic freedom), confirming
in Lean the honesty caveat carried throughout — the geometric remainder
contraction in 4D comes from the *irrelevant operators'* scaling, not the
marginal coupling.  Source: Faria da Veiga–O'Carroll 2024 (marginal
case); the inverse-square form is Bałaban CMP 109 / 1988 eq (2.24)
(`docs/BALABAN-SOURCE-BOUNDS.md` §4).  Strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 55 (2026-06-12, **gauge-RG — end-to-end UV conditional with
the coupling discharged from the RG recursion**
`YangMills.RG.lattice_mass_gap_of_cluster_and_logistic_coupling`; core 8252)

**Build:** green (8252 jobs).  Oracle:
`'…lattice_mass_gap_of_cluster_and_logistic_coupling' [propext, Classical.choice, Quot.sound]`.

Tighter form of `lattice_mass_gap_of_cluster_and_coupling` (Add. 52): the
coupling-flow *decay* hypothesis `hg : g_k ≤ C·rᵏ` is **replaced by the
fundamental logistic RG recursion** `g_{k+1} ≤ r·g_k·(1−β·g_k)`
(`0 ≤ β·g_k ≤ 1`).  The decay is derived internally
(`logistic_geometric_decay`, Add. 49), so the coupling input is now the
β-function recursion itself, not an assumed bound.  Conclusion unchanged:
(cluster activity bound `hRpoly` + coupling recursion `hrec` + IR bound +
covariance scale-sum) ⟹ the lattice mass gap.

So the UV conditional's coupling input is now the **RG recursion**, and
the only remaining genuinely-analytic carried input is the
cluster-expansion activity-decay bound `hRpoly` (the Dimock fluctuation
integral with holes — months-scale).  Source CMP 122-II / Dimock /
Faria da Veiga–O'Carroll; strategy **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance ~0% (<0.1%),
unchanged.

## Addendum 56 (2026-06-12, **gauge-RG — non-vacuity of the end-to-end UV
conditional** `YangMills.RG.lattice_mass_gap_uv_conditional_nonvacuous`;
core 8252)

**Build:** green (8252 jobs).  Oracle:
`'…lattice_mass_gap_uv_conditional_nonvacuous' [propext, Classical.choice, Quot.sound]`.

A FOUNDATIONS-style **non-vacuity audit** of
`lattice_mass_gap_of_cluster_and_logistic_coupling` (Add. 55): its entire
hypothesis bundle is exhibited as **jointly satisfiable with non-degenerate
data** — an explicit witness `g_k = (1/2)ᵏ` (geometric coupling),
`R_{t,k} = e^{−t}·(1/2)ᵏ` (nonzero remainders, certified `R_{0,0}=1≠0`),
IR profile `covIR k = e^{−k}`, `nsc ≡ 1`, constants
`ε=c0=A=κ₀=C1=1, r=1/2, β=0`.  All eleven hypotheses
(positivity/window conditions, the logistic recursion, the IR bound, the
covariance scale-sum, and the cluster activity bound) are proved for this
witness.  So the conditional is **not a vacuously-applicable implication**:
its premise set is inhabited by genuine data.  (`β=0` is the simplest
valid logistic step; β>0 witnesses also exist.)

This closes the audit loop for the UV chain: the end-to-end conditional
is verified AND certified non-vacuous.  Strategy/framing **Lluis
Eriksson** (ai.viXra:2602.0088).  Continuum (M4) track; Clay distance
~0% (<0.1%), unchanged.

## Addendum 57 (2026-06-13, **hRpoly campaign brick P1a — the bounded-degree
walk-count engine** `YangMills.RG.card_walks_length_le_degree_pow`; core 8253)

**Build:** green (**8253 jobs**, +1 over Add. 56's 8252 — module
`YangMills/RG/AnimalCount.lean` added to the core).  Oracle:
`'…card_walks_length_le_degree_pow' [propext, Classical.choice, Quot.sound]`.

First **code** brick of the `hRpoly` campaign (`docs/HRPOLY-CAMPAIGN-PLAN.md`,
opened by the P0 design doc, Add. preceding).  Branch C of `hRpoly` (the
geometric summability `∑_{X⊇□} e^{−κ₀ d_M} ≤ K₀`) was already reduced to the
**lattice animal count** `c_n ≤ Cⁿ` (Add. 53, `polymer_weight_summability`).
The standard route to that geometric count encodes a connected size-`n`
polymer as a bounded-length DFS **walk** on the cube-adjacency graph; this
brick supplies the engine controlling the walk count:

> **`card_walks_length_le_degree_pow`** — for any `SimpleGraph` with
> `∀ w, G.degree w ≤ Δ`, the total number of length-`n` walks from a fixed
> vertex `u` satisfies `∑_v #{p : Walk u v | p.length = n} ≤ Δⁿ`.

Proof: induction on `n` via Mathlib's recursive `finsetWalkLength` description
(`card_finsetWalkLength_succ_le`, itself `Finset.card_biUnion_le` +
`Finset.card_map`), `Finset.sum_comm`, and `card_neighborSet_eq_degree`.
Pure graph combinatorics — no measure theory, no cluster expansion; needs
no Bałaban/Dimock source material (only the degree bound enters the
constant).  **Non-vacuity:** a genuine `≤` on a generally-nonzero count
(at `n = 0` it is exactly `1 ≤ Δ⁰`); the hypothesis `∀ w, G.degree w ≤ Δ`
is satisfiable for every finite graph.  Not a restatement, not vacuous.

**Documented consumer:** the animal-count brick **P1b** (encode a connected
size-`n` polymer into a length-`≤ 2n` walk, then `Fintype.card_le_of_injective`)
→ `RG.polymer_weight_summability`.  Source: standard self-avoiding-walk /
lattice-animal counting (Madras–Slade); strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 58 (2026-06-13, **hRpoly P1b-ii engine — the detour splice**
`YangMills.RG.exists_detour_walk`; core 8253)

**Build:** green (8253 jobs — new *theorem* in the existing
`RG/AnimalCount.lean`, no new module, so the job count is unchanged per
rule 7).  Oracle: `'…exists_detour_walk' [propext, Classical.choice, Quot.sound]`.

The inductive engine of the tree Euler tour (campaign sub-brick P1b-ii,
`docs/HRPOLY-CAMPAIGN-PLAN.md`):

> **`exists_detour_walk`** — for a closed walk `w : G.Walk r r`, a vertex
> `p ∈ w.support`, and a neighbour `u` of `p` (`G.Adj p u`), there is a
> closed walk `w'` with `w'.length = w.length + 2` and
> `w'.support.toFinset = insert u w.support.toFinset`.

Construction: `(w.takeUntil p hp).append (cons hpu (cons hpu.symm (w.dropUntil p hp)))`
— split `w` at `p`, splice the detour `p→u→p`, rejoin.  Length via
`take_spec` + `length_append`/`length_cons`; support via `support_append` +
`mem_support_append_iff` (the duplicate `x = p` disjunct is absorbed because
`p` is the endpoint of `takeUntil`, `end_mem_support`).  Pure Mathlib walk
surgery — no trees, no measure theory, no source material.  **Non-vacuity:**
a constructive existence with exact, non-degenerate length/support equalities
(length strictly grows by 2; support strictly gains `u` when `u ∉ w.support`).

**Role.**  Iterating this over the leaves of a spanning tree (P1b-i) yields a
closed walk of length `2·(#S−1)` whose support is a connected set `S`; that
walk is the injection `animal ↪ walk` consumed against P1a
(`card_walks_length_le_degree_pow`) to give the animal count `c_n ≤ (Δ²)ⁿ`
(P1b-iii → branch C).  Remaining in P1b: the leaf-induction assembly
(P1b-i/ii glue) and the injection/count (P1b-iii).  Source: standard
lattice-animal counting; strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 59 (2026-06-13, **hRpoly P1b/P1c — the lattice animal count**
`YangMills.RG.animal_card_le` + the spanning-tour chain; core 8254)

**Build:** green (**8254 jobs**, +1 over Add. 58 — new module
`YangMills/RG/AnimalTour.lean`).  Oracle (all three):
`[propext, Classical.choice, Quot.sound]`.

Branch C of `hRpoly` (the geometric summability) was reduced to the lattice
animal count `c_n ≤ Cⁿ` (Add. 53).  This addendum **closes that count**:

> **`animal_card_le`** — any family `A` of `S`-connected vertex sets of size
> `n`, each containing the root `r`, on a graph of max degree `≤ Δ`, has
> `A.card ≤ Δ^{2(n−1)}` (i.e. `c_n ≤ Cⁿ` with `C = Δ²`).

Proven via the classical spanning-walk encoding, all in the ambient graph
(no induced-subgraph type surgery), through two reusable lemmas:

* **`exists_peel`** (P1b-i) — the `r`-farthest vertex (max `mlen`, the
  minimal in-`S` walk length, defined by `sInf`) of an `S`-connected set is
  removable: deletion preserves `S`-connectivity and it keeps an inside
  neighbour.  The "max-distance vertex is not a cut vertex" fact, proved by a
  `takeUntil`/`dropUntil` length comparison (`dropUntil` length `0 ⇒ u = z`).
* **`exists_spanning_closed_walk`** (P1b-ii) — induction on `#S`: peel the
  farthest vertex, recurse, splice it back with `exists_detour_walk`
  (Add. 58).  Gives a closed walk from `r` of length `2(n−1)`, support `= S`.
* **`animal_card_le`** (P1c) — the guarded map `animal ↦ spanning closed walk`
  is injective (animal `=` walk support); the length-`2(n−1)` closed walks
  number `≤ Δ^{2(n−1)}` by P1a (`card_walks_length_le_degree_pow`).

Pure graph combinatorics; no measure theory, no cluster expansion, no
Bałaban/Dimock source.  **Non-vacuity:** a genuine cardinality bound on a
satisfiable hypothesis set (e.g. `A = {{r}}`, `n = 1`: `1 ≤ Δ⁰ = 1`); the
spanning walk is produced by construction with the stated support and length.

**Dependency moved.** Branch C of `hRpoly` is now closed *as graph
combinatorics* down to its single remaining interface task — **P2**, the
polymer model: define the cube-adjacency graph (degree `2d`), the polymer
type, and feed `animal_card_le` into `RG.polymer_weight_summability` (whose
`hcount` wants `c_n` as a `Fintype.card`).  The hard analytic cores P3/P4
(cluster expansion with holes; fluctuation integral) still await verbatim
Dimock source.  Source: Madras–Slade; strategy/framing **Lluis Eriksson**
(ai.viXra:2602.0088).  Continuum (M4) track; Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 60 (2026-06-13, **hRpoly branch C closed as graph combinatorics**
`YangMills.RG.rooted_connected_weight_summable`; core 8254)

**Build:** green (8254 jobs — new theorems in `RG/AnimalTour.lean`, no new
module).  Oracle (both): `[propext, Classical.choice, Quot.sound]`.

Two bridge theorems convert the animal count (Add. 59) into the form the
cluster-expansion summability consumes, and then **close the summability
branch**:

* **`rooted_connected_card_le` / `rooted_connected_card_le_pow`** — the
  animal count as an actual cardinal:
  `Nat.card {S : Finset V // r ∈ S ∧ S.card = n ∧ S-connected} ≤ Δ^{2(n−1)}`,
  and (for `Δ ≥ 1`) `≤ (Δ²)ⁿ` — the exact `c_n ≤ Cⁿ` shape of
  `polymer_weight_summability`'s `hcount` (`Fintype.card_subtype` + P1c).
* **`rooted_connected_weight_summable`** — for a bounded-degree graph
  (`Δ ≥ 1`) and `q` with `Δ²q < 1`,
  `∑_Y q^{#Y} ≤ (1 − Δ²q)⁻¹` over all `S`-connected rooted sets `Y`.
  Composes `rooted_connected_card_le_pow` with `polymer_weight_summability`
  (`RG/PolymerRemainder.lean`); the `Summable` premise is free (the polymer
  index type is finite, `Summable.of_finite`).  This **is** Dimock's
  `∑_{X⊇□} e^{−κ₀ d(X)} ≤ K₀` (with `q = e^{−κ₀}`, `K₀ = (1−Δ²q)⁻¹`) —
  now reduced to pure graph combinatorics with explicit constants.

**Dependency moved.**  Branch C of `hRpoly` (the geometric summability
substrate `hwK`) is **closed as graph combinatorics**: from the
bounded-degree hypothesis it is now a *proved theorem*, not a carried input,
on the abstract rooted-connected-set model.  The remaining link is the **P2
instantiation** — identify Dimock's `M`-cube polymers with rooted connected
sets of the cube-adjacency graph (degree `2d`), and set `q = e^{−κ₀}` — at
which point `hwK` is literally discharged in the §6.3 UV conditional.  The
hard analytic cores P3 (cluster expansion with holes) / P4 (fluctuation
integral) still await verbatim Dimock source.  **Non-vacuity:** the
summability bound holds on a satisfiable hypothesis set (`Δ ≥ 1`, `Δ²q < 1`,
e.g. small `q`); the constants are explicit and finite.  Source:
Madras–Slade (animal counting), Kotecký–Preiss (the geometric criterion);
strategy/framing **Lluis Eriksson** (ai.viXra:2602.0088).  Continuum (M4)
track; Clay distance **~0% (<0.1%), unchanged** — this is a lattice
combinatorial estimate, not a continuum or OS-reconstruction result.

## Addendum 61 (2026-06-13, **hRpoly P2 geometry — the `M`-cube adjacency graph
+ concrete lattice summability** `YangMills.RG.cube_polymer_summable`; core 8255)

**Build:** green (**8255 jobs**, +1 — new module `RG/CubeLattice.lean`).
Oracle (both): `[propext, Classical.choice, Quot.sound]`.

With the Dimock II source now in hand (see the source-attribution corrections
below), the `M`-cube polymer geometry is made concrete:

* **`cubeAdj d L`** — the `M`-cube **king-adjacency** `SimpleGraph` on
  `(ZMod L)^d` (differ by `0,±1` in each coordinate; Chebyshev `ℓ^∞`
  distance 1), Dimock II §3.1.2's adjacency, coordination number `3^d − 1`.
* **`cubeAdj_degree_le`** — `degree ≤ 3^d`, via the displacement injection
  `y ↦ (i ↦ y i − x i) ∈ {0,1,−1}^d` (`Fintype.piFinset` + `prod_le_pow_card`).
* **`cube_polymer_summable`** — instantiates `rooted_connected_weight_summable`
  on `cubeAdj`: `∑_Y q^{#Y} ≤ (1 − (3^d)²q)⁻¹` for `(3^d)²q < 1`, the
  geometric summability on the actual lattice geometry with the explicit
  coordination constant `Δ = 3^d`.

The source confirms this is the right object: Dimock II §3.1.2 says a polymer
is a connected union of `M`-cubes, a spanning tree on `n` cubes is explored by
a walk of `≤ 2n` steps, and size-`n` polymers containing a fixed cube number
`≤ cⁿ` with `c ∝ 3^d − 1` — exactly `exists_spanning_closed_walk` /
`animal_card_le`.  **Non-vacuity:** `cubeAdj` is a genuine graph (`L ≥ 1`),
the bound holds for satisfiable `q` (e.g. small `q`), and the rooted-polymer
index type is inhabited by `{r}`.

### Source-attribution corrections (Dimock arXiv:1212.5562, confirmed)
Prior docs had three misattributions, now corrected (see
`docs/BALABAN-SOURCE-BOUNDS.md`, `HRPOLY-CAMPAIGN-PLAN.md` §4):
1. **Appendix F ("cluster expansion with holes") is in Part II**, and its
   convergence is self-contained there (it follows Part I App B), **not** in
   Part III.  Theorem F.1 constants `H₀ ≤ c₀`, `κ ≥ 3κ₀+3`, conclusion
   `O(1)H₀ e^{−(κ−3κ₀−3)d_M(Y, mod Ω^c)}` — confirmed verbatim.
2. The `d_M(X, mod Ω^c)` definition + the summability `∑_{X⊇□} e^{−κ₀ d_M} ≤ K₀`
   are in the **§3 main text (§3.1.2, ~eqs 150–151)**, not Appendix F.
3. The raw activity bound feeding F.1 is in **§3.14** (Lemma 3.18, eq. ~500/506:
   `|H_{k,Π}^+(Y)| ≤ O(1)L³ λ_k^{1/4−10ε} e^{−L(κ−3κ₀−3)d_{LM}(Y, mod Ω^c)}`),
   **not §3.8** (§3.8 is the fluctuation-integral / covariance-localization
   setup).  The coupling is **`λ_k`** (`λ_k = L^{−(N−k)}λ`), not `g_k`;
   `p_k = (−log λ_k)^p`, `α_k = max(λ_k^{1/4}, μ̄_k^{1/2})`; and `H₀ ≍ O(1)L³ λ_k^{1/4−10ε}`.

**CRITICAL model caveat.**  Dimock II/III treats **`φ⁴₃`** (3D scalar UV
problem), so its activity constants (`λ_k^{1/4−10ε}`, the `L³`, the
relevant-coupling `λ_k = L^{−(N−k)}λ`) are **NOT** the 4D Yang–Mills values.
Appendix F is reused as a *general polymer lemma*; the YM activity bounds and
the (logarithmic, marginal) 4D coupling flow come from Bałaban's YM papers,
not from these `φ⁴₃` numbers.  **Clay distance ~0% (<0.1%), unchanged** — this
is lattice combinatorics on a concrete graph; no continuum/OS content.

## Addendum 62 (2026-06-13, **the YM coupling is marginal — summable scale-series
without geometric decay** `YangMills.RG.marginal_coupling_pow_summable`; core 8256)

**Build:** green (**8256 jobs**, +1 — new module `RG/MarginalCoupling.lean`).
Oracle (both headlines): `[propext, Classical.choice, Quot.sound]`.

The Bałaban Yang–Mills source review (now done; map below) confirms the
load-bearing correction: **the 4D YM coupling `g_k` is marginal /
asymptotically free — it runs logarithmically, NOT geometrically.**  A
geometric bound `g_k ≤ C·rᵏ` (`r < 1`) is **false** for the marginal coupling
(it holds only for *irrelevant* couplings, as in Dimock's superrenormalizable
φ⁴₃).  This addendum supplies the *honest* YM coupling side:

* **`marginal_coupling_pow_summable`** — from the asymptotic-freedom lower
  bound `1/g₀ + β·n ≤ 1/gₙ` (the conclusion of `inv_coupling_linear_growth`,
  Add. ~46), `β > 0`, `κ₀ > 1`: the series `∑ₙ gₙ^{κ₀}` **converges**.  So
  although the marginal coupling does not decay geometrically, the
  renormalization-remainder series over scales is still summable for activity
  power `κ₀ > 1`.  Proof: `gₙ ≤ 1/(c(n+1))` then comparison with the `p`-series
  `∑ n^{−κ₀}` (`Real.summable_nat_rpow_inv`).
* **`marginal_coupling_tendsto_zero`** — asymptotic freedom: `gₙ → 0`.
* **`marginal_coupling_pow_summable_of_recursion`** — the same, directly from
  the marginal recursion `g_{k+1} = g_k(1 − β g_k)`.

**Dependency moved.**  The UV `hg` side of `lattice_mass_gap_of_cluster_and_coupling`
used a geometric `g_k ≤ C·rᵏ` — *model-incorrect for YM*.  This brick gives the
correct marginal-coupling summability `∑ g_k^{κ₀} < ∞` (`κ₀ > 1`), the honest
object on which a YM remainder assembly should rest.  It does **not** supply
the YM activity-decay bound (carried; see source map).  **Non-vacuity:** the
hypotheses are satisfiable (e.g. `g_n = g_0/(1+β g_0 n)`-type flows); the
series bound is a genuine convergence, not vacuous.

### Bałaban Yang–Mills source map (lattice SU(N) RG series, all CMP)
For the genuine YM `hRpoly` activity input (NOT Dimock φ⁴₃):
* **CMP 116 (1988), "RG approach to LGT II: Cluster expansions", Lemma 3 /
  eq. (2.38):** the single-scale YM activity bound
  `|H(Z)| ≤ C₃ ε₁ exp(−(1−8δ)^{1/2} L κ d_{k+1}(Z))`; eq. (2.41) exponentiates
  to the effective-action bound `|E^{(k+1)}(X)| ≤ O(1)C₃ε₁ e^{−(1−10δ)^{1/2}Lκ d(X)}`,
  giving the inductive `(I.1.18)`.  **This is the closest source-faithful
  `hRpoly`.**
* **CMP 122-I/II (1989), "Large field renormalization":** the `R`-operation and
  the complete-model remainder bound `|R^{(k)}(X)| ≤ e^{−p₀(g_k)} e^{−κ d_k(X)}`
  (the large-field/holes part); 122-II Theorem 1 = UV stability.
* **CMP 119 (1988), "Convergent renormalization expansions":** the complete
  effective density `A_k = A + E_k + R_k + B_k`, large-field domains.
* **CMP 109 (1987), "RG approach to LGT I":** small-field effective actions and
  the **recursive (marginal) coupling renormalization** — the source for the
  marginal/logarithmic flow this addendum formalizes.
* **CMP 99 (1985), background-field propagators:** the source of the decay
  constant `κ`.
* **Critical:** Bałaban's series proves **UV stability**, *not* a mass gap.
  There is **no Bałaban mass-gap theorem**; any `R_k → mass gap` step is an
  open conjecture, carried as a hypothesis, never a cited lemma.  Clay distance
  **~0% (<0.1%), unchanged.**

## Addendum 63 (2026-06-13, **the marginal-coupling remainder scale-sum bound**
`YangMills.RG.marginal_coupling_remainder_tsum_le`; core 8256)

**Build:** green (8256 jobs — theorem added to `RG/MarginalCoupling.lean`, no
new module).  Oracle: `[propext, Classical.choice, Quot.sound]`.

The honest YM analogue of the geometric coupling bridge, consuming Add. 62's
marginal-coupling summability: given the carried Bałaban YM activity bound
`|R_{t,k}| ≤ A·e^{−c₀t}·g_k^{κ₀}` and `Summable (g_·^{κ₀})` (the marginal
coupling, NOT geometric), the scale-summed remainder satisfies
`∑ₖ |R_{t,k}| ≤ A·e^{−c₀t}·(∑ₖ g_k^{κ₀})`.  So the UV remainder retains the
spatial gap factor `e^{−c₀t}`, with the scale series contributing only a
bounded constant — the coupling side discharged for the marginal YM flow with
no false geometric-decay assumption.  `tsum_le_tsum` + `tsum_mul_left`, the
summand summability by comparison.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 64 (2026-06-13, **the marginal-coupling UV mass-gap conditional**
`YangMills.RG.lattice_mass_gap_of_cluster_and_marginal_coupling`; core 8257)

**Build:** green (**8257 jobs**, +1 — new module `RG/MarginalUVMassGap.lean`).
Oracle (both headlines): `[propext, Classical.choice, Quot.sound]`.

Generalizes the geometric-profile UV assembly to the marginal (YM) coupling,
the honest 4D replacement for `lattice_mass_gap_of_cluster_and_coupling`:

* **`uv_summable_summation`** — finite partial sums of `|R k| ≤ amp·w_k` are
  `≤ amp·S` for `w ≥ 0` summable with `∑' w ≤ S` (`Summable.sum_le_tsum`).
* **`lattice_mass_gap_of_per_scale_uv_summable`** — the banked geometric-profile
  assembly (`lattice_mass_gap_of_per_scale_uv`, Add. 19) generalized from `rᵏ`
  to ANY nonnegative summable `w_k`: from `|R_{t,k}| ≤ (C₂·e^{−c₀t})·w_k` (+ the
  theorem-fed IR bound + the covariance scale-sum), the lattice mass gap with
  constant `C₁ + C₂·S`.  Feeds `lattice_mass_gap_of_exp_clustering_uniform`.
* **`lattice_mass_gap_of_cluster_and_marginal_coupling`** — the headline: the
  coupling flows by the marginal recursion `g_{k+1} = g_k(1 − β g_k)`
  (asymptotically free, NOT geometric), the carried Bałaban YM activity bound
  is `|R_{t,k}| ≤ (C₂·e^{−c₀t})·g_k^{κ₀}` (`κ₀ > 1`), and the lattice mass gap
  follows with the **finite** constant `C₁ + C₂·∑_k g_k^{κ₀}` — the scale-sum
  convergent by `marginal_coupling_pow_summable_of_recursion` (Add. 62) even
  though `g_k` does not decay geometrically.

**Dependency moved.**  The §6.3 UV obligation now has an end-to-end conditional
with the **correct (marginal) YM coupling flow** — no false `g_k ≤ C·rᵏ`.  The
sole carried analytic input is `hRpoly` (the Bałaban YM single-scale activity
bound, CMP 116 Lemma 3 / Large Field II — months-scale gauge construction, NOT
formalized).  The IR side is theorem-fed; the `R_{t,k}`-as-covariance-remainder
reading is carried framing (Bałaban proves UV *stability*, not a mass gap).
**Non-vacuity:** the general `_summable` assembly is non-vacuous for any
geometric `w` (e.g. `(1/2)ᵏ`); the marginal recursion is satisfiable by the
logistic flow `g_0 = 1/2, β = 1` (stays in `(0,1/2]`).  Clay distance **~0%
(<0.1%), unchanged** — a lattice conditional, no continuum/OS content.

## Addendum 65 (2026-06-13, **non-vacuity of the marginal conditional**
`YangMills.RG.exists_marginal_coupling_flow`; core 8257)

**Build:** green (8257 jobs — theorem added to `RG/MarginalUVMassGap.lean`, no
new module).  Oracle: `[propext, Classical.choice, Quot.sound]`.

FOUNDATIONS-discipline non-vacuity certificate for Add. 64's marginal
conditional (matching the geometric `lattice_mass_gap_uv_conditional_nonvacuous`,
Add. 56): the logistic flow `g_{k+1} = g_k(1 − β g_k)` with `β = 1`, `g_0 = 1/2`
satisfies all the coupling hypotheses of
`lattice_mass_gap_of_cluster_and_marginal_coupling` — positivity, smallness
`β·g_k < 1`, and the recursion — so the marginal conditional's coupling premise
is inhabited by genuine data and is NOT vacuously applicable.  Proof: the flow
stays in `(0, 1/2]` by induction (`nlinarith` + `sq_nonneg (g_n − 1/2)`); the
recursion holds definitionally (`Nat.rec`).  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 66 (2026-06-13, **the exponential-decay kernel calculus — Combes–
Thomas / Neumann engine** `YangMills.RG.expDecay_comp`; core 8258)

**Build:** green (**8258 jobs**, +1 — new module `RG/KernelDecay.lean`).
Oracle (`expDecay_comp`, `expDecay_add`): `[propext, Classical.choice, Quot.sound]`.

The first analytic substrate toward the YM activity decay `hRpoly`.  Every
Bałaban multiscale propagator/activity bound rests on the fact that
exponentially-decaying operator kernels form a **calculus**; this file builds
it abstractly and source-independently for real kernels on a metric `(V, d)`:

* **`ExpDecay d a κ K`** := `∀ x y, |K x y| ≤ a·e^{−κ·d x y}`.
* **`expDecay_comp`** (the crux) — composition preserves decay: `A`, `B` at
  rate `κ` give `(x,y) ↦ ∑_z A x z·B z y` at rate `κ − σ`, amplitude `a·b·S`,
  using the uniform exponential summability `∑_z e^{−σ d(x,z)} ≤ S`
  (`0 ≤ σ ≤ κ`).  Triangle inequality extracts `e^{−(κ−σ)d(x,y)}`; the
  summability absorbs `e^{−σ d(x,z)}`.  This is the Combes–Thomas /
  Neumann-series engine (the resolvent/propagator of a bounded-range operator
  decays exponentially; the YM decay constant `κ` of CMP 116 Lemma 3 is
  inherited from CMP 95/99 via exactly this mechanism).
* **`expDecay_add` / `expDecay_smul` / `ExpDecay.mono`** — closure under sums,
  nonnegative scalars, amplitude/rate weakening.

**Dependency moved.**  The summability hypothesis `∑_z e^{−σ d(x,z)} ≤ S` is
exactly what `RG/AnimalTour.lean` / `RG/CubeLattice.lean` supply on the
`M`-cube graph — so this calculus is *connected* to the closed combinatorial
substrate, not free-floating.  **It does NOT prove the YM activity bound**
(the carried `hRpoly`, needing the full gauge fluctuation construction); it is
the analytic toolkit that bound's proof must consume.  **Non-vacuity:** the
composition is a genuine quantitative inequality; the hypotheses are jointly
satisfiable (any bounded-degree lattice with `d` the graph distance gives the
summability via the animal count, e.g. `cubeAdj`).  Source: Combes–Thomas,
Bałaban CMP 95/99; strategy/framing **Lluis Eriksson** (ai.viXra:2602.0088).
Continuum (M4) track; Clay distance **~0% (<0.1%), unchanged**.

## Addendum 67 (2026-06-13, **fixed-rate iterated kernel composition — the
Neumann engine** `YangMills.RG.expDecay_pow`; core 8258)

**Build:** green (8258 jobs — theorems added to `RG/KernelDecay.lean`, no new
module).  Oracle (`expDecay_comp_asym`, `expDecay_pow`):
`[propext, Classical.choice, Quot.sound]`.

Extends the kernel-decay calculus (Add. 66) to the iteration needed for a
resolvent/propagator decay:

* **`expDecay_comp_asym`** — asymmetric composition: `A` at the higher rate
  `β + σ` composed with `B` at rate `β` gives `A∘B` at the **unreduced** rate
  `β` (amplitude `a·b·S`).  The extra `σ` of `A` pays for the intermediate
  summation, so the output keeps `B`'s rate — the form that iterates at a
  fixed rate.
* **`Kpow`** — the `n`-fold compositional power of a kernel.
* **`expDecay_pow`** — the Neumann engine: a kernel `K` at rate `κ` has all
  powers `Kⁿ` decaying at the **fixed** rate `κ − σ` with geometric amplitude
  `a·(a·S)ⁿ`.  Induction on `n` via `expDecay_comp_asym` (`K` at rate
  `κ = (κ−σ)+σ` ∘ `Kⁿ` at rate `κ−σ` stays at `κ−σ`).  This is the per-power
  input to `∑ₙ Kⁿ` (the resolvent `(1−K)⁻¹`): with `a·S < 1` the amplitudes
  `a·(a·S)ⁿ` are geometrically summable, giving a fixed-rate exponentially-
  decaying resolvent — the Combes–Thomas conclusion (Bałaban CMP 95/99), the
  source of the YM activity decay constant `κ`.

**Dependency moved.**  The analytic substrate now reaches the iterated/resolvent
level.  Still source-independent and still NOT the YM activity bound (carried
`hRpoly`).  **Non-vacuity:** genuine quantitative bounds; hypotheses jointly
satisfiable on any bounded-degree lattice (`cubeAdj`) via the animal-count
summability.  Continuum (M4) track; Clay distance **~0% (<0.1%), unchanged**.

## Addendum 68 (2026-06-13, **resolvent / Neumann decay — the Combes–Thomas
conclusion** `YangMills.RG.expDecay_resolvent`; core 8258)

**Build:** green (8258 jobs — theorem added to `RG/KernelDecay.lean`, no new
module).  Oracle: `[propext, Classical.choice, Quot.sound]`.

The capstone of the exponential-decay kernel calculus (Add. 66–67):

* **`expDecay_resolvent`** — if `K` decays at rate `κ` (amplitude `a`), the
  lattice has exponential summability `∑_z e^{−σ d(x,z)} ≤ S`, and the
  **smallness `a·S < 1`** holds, then the Neumann series
  `(1 − K)⁻¹ = ∑ₙ Kⁿ` converges to a kernel decaying at the **fixed** rate
  `κ − σ` with amplitude `a/(1 − a·S)`.  Sums `expDecay_pow` over the geometric
  amplitudes `a·(a·S)ⁿ` (`summable_geometric_of_lt_one`,
  `tsum_geometric_of_lt_one`).

This is the operator-theoretic heart of every Bałaban propagator bound — a
bounded-range, weakly-coupled operator has an **exponentially-decaying
resolvent**; the YM activity-decay constant `κ` (CMP 116 Lemma 3) is inherited
from precisely this resolvent decay of the background-field propagator
(CMP 95/99).  The kernel-decay calculus is now complete through the resolvent
level: `ExpDecay`, sum/scalar/`mono`, composition (`expDecay_comp` /
`_comp_asym`), powers (`expDecay_pow`), and resolvent (`expDecay_resolvent`) —
a coherent, source-independent analytic toolkit the YM activity bound's proof
must consume.

**Dependency moved.**  The full source-independent analytic substrate toward
`hRpoly` is now built (combinatorial summability + marginal coupling +
kernel-decay/resolvent calculus).  The remaining gap is exactly the **carried
YM activity bound** `hRpoly` itself, which requires the concrete gauge
construction (the lattice gauge-covariant Laplacian / background-field operator
as a specific `ExpDecay` instance — the months-scale CMP 95/99/109/116 work),
not further abstract substrate.  **Non-vacuity:** genuine quantitative bound;
hypotheses jointly satisfiable on `cubeAdj` with small `a`.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 69 (2026-06-13, **Schur boundedness of decaying kernels — the
covariance face** `YangMills.RG.expDecay_quadratic_form_le`; core 8259)

**Build:** green (**8259 jobs**, +1 — new module `RG/KernelSchur.lean`).
Oracle (both): `[propext, Classical.choice, Quot.sound]`.

The boundedness companion to the kernel-decay calculus (Add. 66–68), on a
finite lattice:

* **`expDecay_finset_row_le`** — the ℓ¹ row-sum bound `∑_y |K x y| ≤ a·S`.
* **`expDecay_quadratic_form_le`** — the finite-dimensional **Schur test**:
  an exponentially-decaying kernel (symmetric metric) gives a quadratic form
  `|∑_{x,y} u x · K x y · u y| ≤ (a·S)·∑_x (u x)²`.  Proof: `|bilinear| ≤
  ∑∑|u_x||K_xy||u_y|`, then the Schur AM–GM `2|u_x||u_y| ≤ u_x²+u_y²` and
  row/column summability (`Finset.sum_comm`).

This is exactly the shape of a **covariance bound** `Cov ≤ a·S`: a background-
field propagator with an `ExpDecay` kernel induces a covariance form controlled
by `a·S` (cf. `RG/GaussianStep.lean`, Bałaban CMP 95–96).  Source-independent,
finite-dimensional, and **volume-free** (the bound `a·S` is volume-uniform).

**Dependency moved.**  The source-independent operator/kernel/covariance
substrate toward `hRpoly` is now complete: spatial **decay** (kernel calculus +
resolvent, Add. 66–68) and **boundedness** (Schur row-sum + quadratic form,
this addendum).  Together they are the full analytic toolkit Bałaban's gauge
construction consumes to produce the YM activity bound `|H_k(X)| ≤ H₀ e^{−κ d}`.
The remaining gap is the **carried `hRpoly`** — instantiating this toolkit on
the concrete lattice gauge-covariant operator (CMP 95/99/102/109/116, months-
scale), not further abstract substrate.  **Non-vacuity:** genuine quadratic
bound; hypotheses satisfiable on any finite bounded-degree lattice (`cubeAdj`).
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 70 (2026-06-13, **operator-norm Schur bound — the full ℓ² Schur
test** `YangMills.RG.expDecay_op_bilinear_le`; core 8259)

**Build:** green (8259 jobs — theorem added to `RG/KernelSchur.lean`, no new
module).  Oracle: `[propext, Classical.choice, Quot.sound]`.

The sharp operator-norm form of the Schur test (strengthening the
covariance/quadratic bound of Add. 69):

* **`expDecay_op_bilinear_le`** — an exponentially-decaying kernel `K`
  (symmetric metric, summability `S`) is bounded as a bilinear form by
  `a·S·‖u‖·‖v‖`: `|∑_{x,y} u x · K x y · v y| ≤ a·S·√(∑ u²)·√(∑ v²)`, i.e.
  `‖K‖_{op} ≤ a·S`.  Proof: bound by `∑∑|u_x||K_xy||v_y|`, write it as
  `∑_{(x,y)} (√|K_xy| |u_x|)(√|K_xy| |v_y|)`, apply Cauchy–Schwarz over the
  product index (`Finset.sum_mul_sq_le_sq_mul_sq`), bound the two factors by
  row/column summability (`a·S·‖u‖²`, `a·S·‖v‖²`), and take square roots.  The
  `u = v` case recovers `expDecay_quadratic_form_le`.

**Dependency moved.**  This completes the source-independent
operator/kernel/covariance substrate toward `hRpoly`: decay (`ExpDecay`,
composition, resolvent — Add. 66–68) **and** boundedness (row-sum, quadratic
form, and now the sharp operator norm — Add. 69–70).  This is the full analytic
toolkit Bałaban's gauge construction consumes; the remaining gap is the carried
`hRpoly`, i.e. exhibiting the concrete lattice gauge-covariant operator as an
`ExpDecay` instance (CMP 95/99/102/109/116, months-scale).  **Non-vacuity:**
genuine operator bound; hypotheses satisfiable on `cubeAdj`.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 71 (2026-06-13, **PSD covariance-kernel interface** —
`YangMills.RG.psd_cauchy_schwarz` + diagonal bounds; core 8260)

**Build:** green (**8260 jobs**, +1 — new module `RG/CovarianceKernel.lean`).
Oracle (`psd_diag_nonneg`, `psd_cauchy_schwarz`): `[propext, Classical.choice, Quot.sound]`.

The covariance layer of the `hRpoly` analytic substrate, connecting the
exponential-decay/Schur calculus to a Gaussian field's covariance:

* **`expDecay_diag_abs_le`** — the diagonal (field variance at coincident
  points) of an `ExpDecay` kernel is `≤ a` (when `d x x = 0`).
* **`IsPSDKernel K`** := `∀ u, 0 ≤ ∑_{x,y} u x K x y u y` (the covariance
  property).
* **`psd_diag_nonneg`** — a PSD kernel has nonnegative diagonal (variance ≥ 0),
  via the indicator test vector.
* **`psd_cauchy_schwarz`** — the **covariance Cauchy–Schwarz**
  `(∑ u K v)² ≤ (∑ u K u)(∑ v K v)` for a symmetric PSD kernel, via the
  discriminant of the nonnegative quadratic `t ↦ ∑ (u+t v) K (u+t v) ≥ 0`
  (`discrim_le_zero`).

**Dependency moved.**  Combined with the Schur operator-norm bound
(`expDecay_op_bilinear_le`, Add. 70), a background-field propagator that is a
symmetric PSD `ExpDecay` kernel now has: covariance form `≤ a·S`, variances
`≤ a`, the covariance Cauchy–Schwarz, and exponentially-decaying powers/
resolvent — the **complete finite-lattice covariance/operator toolkit** a
Gaussian fluctuation bound consumes.  This closes the source-independent
analytic substrate toward `hRpoly`; the remaining gap is exhibiting the
concrete lattice gauge-covariant operator as such a kernel (CMP 95/99/102/
109/116, months-scale).  **Non-vacuity:** genuine PSD-form inequalities; the
zero kernel and any Gram kernel `K x y = ⟨e_x, e_y⟩` are PSD instances.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 72 (2026-06-13, **Gaussian field-size / MGF bound from a covariance
bound** `YangMills.RG.gaussian_exp_integral_le`; core 8261)

**Build:** green (**8261 jobs**, +1 — new module `RG/GaussianMGF.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

First brick of the **Gaussian-from-covariance layer** (new campaign): the
fluctuation-integral input that a Gaussian field with bounded covariance has
uniformly bounded exponential moments.

* **`gaussian_exp_integral_le`** — if the 1-D marginal of a centered measure
  `μ` under the linear observable `L` is `gaussianReal 0 v` (the defining
  centered-marginal property of a Gaussian field), and the variance `v ≤ B`
  (with `B = a·S·‖L‖²` the value `expDecay_quadratic_form_le` / `psd_cauchy_schwarz`
  supply), then `∫ exp(L φ) dμ ≤ exp(B/2)`.  Built directly on Mathlib's
  `mgf_gaussianReal` (the 1-D Gaussian MGF) via `mgf L μ 1 = ∫ exp(L φ)`.

**Dependency moved.**  The covariance/operator substrate (Add. 66–71) now feeds
a genuine Gaussian fluctuation bound: bounded covariance ⇒ bounded exponential
field moments, the small-field integral input.  **Honest scope:** the
hypothesis `μ.map L = gaussianReal 0 v` is the genuine centered-1-D-marginal
property (true for every Gaussian measure), a faithful carried hypothesis, NOT
a fabricated constructor.  Deriving it from an abstract `[IsGaussian μ]`
(centered, via `isGaussian_map` + the charFun characterization + the
`IsGaussian`-on-ℝ = `gaussianReal` identity) is the natural next brick.  Does
NOT prove `hRpoly`.  **Non-vacuity:** `gaussianReal 0 v` itself (with `μ = `
pushforward, `L = id`) satisfies the hypothesis.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 73 (2026-06-13, **self-contained Gaussian MGF bound for an abstract
centered Gaussian** `YangMills.RG.gaussian_exp_integral_le_isGaussian`; core 8261)

**Build:** green (8261 jobs — theorem added to `RG/GaussianMGF.lean`, no new
module).  Oracle: `[propext, Classical.choice, Quot.sound]`.

Completes the prompt's target objective: the Gaussian field-size bound with
**no carried marginal hypothesis**, reduced fully to abstract Gaussianity +
centering + the variance bound.

* **`gaussian_exp_integral_le_isGaussian`** — for any `[IsGaussian μ]` on a
  separable Banach space, a centered linear observable `L` (`μ[L] = 0`) with
  bounded variance (`Var[L; μ] ≤ B`, the value `expDecay_quadratic_form_le` /
  `psd_cauchy_schwarz` supply, `B = a·S·‖L‖²`) satisfies
  `∫ exp(L φ) dμ ≤ exp(B/2)`.  Derives the 1-D marginal
  `μ.map L = gaussianReal 0 (Var[L;μ])` from Mathlib's
  `IsGaussian.map_eq_gaussianReal`, then applies `gaussian_exp_integral_le`
  (Add. 72).

**Dependency moved.**  The Gaussian-from-covariance layer is now closed at the
abstract level: *centered Gaussian + covariance bound `a·S` ⇒ exponential
field-size bound* `exp(½ a·S ‖L‖²)` — exactly the small-field fluctuation
integral input, with the covariance bound supplied by the kernel/Schur/PSD
substrate (Add. 66–71).  The full source-independent analytic toolkit toward
`hRpoly` — combinatorial summability, marginal coupling, kernel decay/resolvent,
Schur/operator boundedness, PSD covariance, and now the Gaussian MGF bound — is
in place and oracle-clean.  The remaining gap is the carried `hRpoly`:
constructing the concrete lattice gauge `IsGaussian` fluctuation measure with
its covariance the gauge-covariant propagator (an `ExpDecay`+PSD kernel) — the
months-scale CMP 95/99/102/109/116 gauge construction.  **Non-vacuity:** any
centered `gaussianReal`-type measure satisfies the hypotheses.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 74 (2026-06-13, **the concrete multivariate Gaussian as an
`IsGaussian` measure** `YangMills.RG.isGaussian_pi` + `isGaussian_pi_map_clm`;
core 8262)

**Build:** green (**8262 jobs** — incremented from 8261 by the new module
`RG/GaussianPi.lean`).  Oracle: both `[propext, Classical.choice, Quot.sound]`.

This closes the gap flagged at the end of Add. 73 — "no constructive Gaussian
measure."  Add. 72/73 bounded the field-size integral for *any abstract*
`[IsGaussian μ]`; the open question was whether a concrete finite-dimensional
Gaussian measure exists in Mathlib as an `IsGaussian` instance.  It does not
ship one (Mathlib has 1-D `gaussianReal` and the abstract predicate, but no
multivariate Gaussian).  This module supplies the missing primitive.

* **`isGaussian_pi`** — `Measure.pi (fun i => gaussianReal (m i) (v i))` on
  `ι → ℝ` (`[Fintype ι]`), the standard multivariate Gaussian with mean `m` and
  diagonal covariance `diag v`, **is** an `IsGaussian` measure.  Proof: the
  coordinate projections are independent (`iIndepFun_pi`) and each has 1-D
  Gaussian law (`Measure.pi_map_eval` + `isGaussian_gaussianReal`), hence
  *jointly* Gaussian (Mathlib's `iIndepFun.hasGaussianLaw`); the joint law of the
  coordinates is the identity pushforward, i.e. the measure itself.

* **`isGaussian_pi_map_clm`** — pushing the standard multivariate Gaussian
  forward through **any continuous linear map** `A : (ι → ℝ) →L[ℝ] F` yields an
  `IsGaussian` measure on `F` (via `isGaussian_map_of_measurable`).  Taking `A`
  a square-root / Cholesky factor of a target PSD covariance realizes a centered
  Gaussian field with covariance bilinear form `A ∘ Aᵀ` — the constructive
  Gaussian-from-covariance object the small-field fluctuation integral integrates
  against.

**Dependency moved.**  `gaussian_exp_integral_le_isGaussian` (Add. 73) now has
concrete, non-abstract `IsGaussian` measures to consume — the field-size bound is
instantiable on a genuine constructed measure, not only on a hypothesis.  The
remaining `hRpoly` gap is now purely: (i) match `A ∘ Aᵀ` to the specific
gauge-covariant background-field propagator (`ExpDecay`+PSD kernel; Cholesky /
spectral factor + the CMP 99 propagator bound), and (ii) the full single-scale
raw-activity bound (CMP 116) — both carried as honest hypotheses, never axioms.
**Non-vacuity:** `ι := Fin n`, `m := 0`, `v := 1` gives the standard `n`-dim
Gaussian; `A := id` recovers it.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 75 (2026-06-13, **the standard multivariate Gaussian is centered +
the fully concrete field-size bound** `YangMills.RG.pi_gaussian_centered` +
`pi_gaussian_exp_integral_le`; core 8262)

**Build:** green (8262 jobs — theorems added to `RG/GaussianPi.lean`, no new
module).  Oracle: both `[propext, Classical.choice, Quot.sound]`.

This ties Add. 74 (`isGaussian_pi`) to Add. 73 (the abstract field-size bound),
turning the latter from hypothesis-fed into instantiated-on-an-explicit-measure.

* **`pi_gaussian_centered`** — for `μ = Measure.pi (fun i => gaussianReal 0 vᵢ)`
  and any dual `L`, `μ[L] = 0`.  Proof by symmetry: each `gaussianReal 0 vᵢ` is
  `x ↦ -x`-invariant (`gaussianReal_map_neg` + `neg_zero`), so the product
  measure is (`Measure.pi_map_pi`); hence `μ[L] = μ[L∘(-·)] = -μ[L]`
  (`L` linear; `IsGaussian.integrable_dual` for integrability), so `μ[L] = 0`.

* **`pi_gaussian_exp_integral_le`** — the capstone: for the centered standard
  multivariate Gaussian and any dual `L` with `Var[L;μ] ≤ B`,
  `∫ exp(L φ) dμ ≤ exp(B/2)`.  This is `gaussian_exp_integral_le_isGaussian`
  (Add. 73) instantiated via `isGaussian_pi` + `pi_gaussian_centered` — a fully
  concrete, non-vacuous fluctuation-integral bound on a genuine constructed
  measure (no abstract `IsGaussian` hypothesis, no carried centering).

The abstract Gaussian-from-covariance layer is now end-to-end concrete: construct
`μ` (`isGaussian_pi`), it is centered (`pi_gaussian_centered`), and bounded
covariance gives the field-size bound (`pi_gaussian_exp_integral_le`); the
kernel/Schur/PSD substrate (Add. 66–71) supplies `Var[L;μ] ≤ a·S·‖L‖²`.  The
remaining `hRpoly` gap is unchanged: the concrete gauge-covariant propagator
(CMP 99) realizing the covariance, and the CMP 116 single-scale raw-activity
bound — both carried as honest hypotheses.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 76 (2026-06-13, **the variance bridge: covariance form of the
product Gaussian computed + the Schur→variance→MGF connection**
`YangMills.RG.pi_gaussian_variance` + `_of_covariance_sum` +
`_of_uniform_variance`; core 8262)

**Build:** green (8262 jobs — theorems added to `RG/GaussianPi.lean`, no new
module).  Oracle: all three `[propext, Classical.choice, Quot.sound]`.

Closes the bridge flagged at the end of Add. 75: the covariance form of the
constructed Gaussian is now *computed*, not abstract, and wired to the
field-size bound — realizing the chain *(uniform) covariance bound → variance
bound → field-size/MGF bound* on a genuine constructed measure.

* **`pi_gaussian_variance`** — for `μ = Measure.pi (fun i => gaussianReal 0 vᵢ)`
  and any dual `L`, `Var[L; μ] = ∑ᵢ (L eᵢ)²·vᵢ` (`eᵢ = Pi.single i 1`).  Proof:
  `L = ∑ᵢ (L eᵢ)·(·ᵢ)` (`Finset.univ_sum_single` + linearity); coordinates are
  independent (`iIndepFun_pi`) and `L²`-integrable (`IsGaussian.memLp_dual`), so
  `Var` of the sum splits (`IndepFun.variance_sum`); each term is
  `(L eᵢ)²·Var[(·ᵢ)] = (L eᵢ)²·vᵢ` (`variance_const_mul` +
  `variance_id_gaussianReal` via the coordinate marginal `Measure.pi_map_eval`).

* **`pi_gaussian_exp_integral_le_of_covariance_sum`** — `∑ᵢ (L eᵢ)²·vᵢ ≤ B ⟹
  ∫ exp(L φ) dμ ≤ exp(B/2)` (substitute the computed variance into Add. 75's
  bound): the "variance bound ⟹ MGF" link with the variance *computed*.

* **`pi_gaussian_exp_integral_le_of_uniform_variance`** — `vᵢ ≤ a` (uniform
  covariance bound) `⟹ ∫ exp(L φ) dμ ≤ exp(a·(∑ᵢ (L eᵢ)²)/2)`.  The small-field
  fluctuation-integral input in canonical shape `exp(½ a·‖·‖²)`; the `a·S` of the
  Schur bound (`expDecay_quadratic_form_le` / `psd_cauchy_schwarz`, Add. 69–71)
  plugs directly into `a`.

The diagonal product-Gaussian covariance is now end-to-end concrete and connected
to the kernel/Schur substrate.  The off-diagonal (general PSD) covariance remains
via the `A`-pushforward (`isGaussian_pi_map_clm`, Add. 74) with `A∘Aᵀ = C` — the
Cholesky/spectral-factor step, still ahead.  The `hRpoly` gap is unchanged: the
concrete CMP-99 gauge-covariant propagator realizing `C`, and the CMP-116
single-scale raw-activity bound — carried as honest hypotheses, never axioms.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 77 (2026-06-13, **general / off-diagonal covariance via the
A-pushforward** `YangMills.RG.pi_gaussian_map_variance` +
`pi_gaussian_map_exp_integral_le`; core 8262)

**Build:** green (8262 jobs — theorems added to `RG/GaussianPi.lean`, no new
module).  Oracle: both `[propext, Classical.choice, Quot.sound]`.

Lifts Add. 76 from the diagonal product Gaussian to an *arbitrary* constructed
Gaussian covariance `A∘Aᵀ` — the realistic shape of the Bałaban fluctuation
propagator (off-diagonal in general).

* **`pi_gaussian_map_variance`** — for `A : (ι → ℝ) →L[ℝ] F` and a dual `L` on
  `F`, `Var[L; μ.map A] = ∑ᵢ (L (A eᵢ))²·vᵢ`.  Proof: `variance_map` reduces to
  `Var[L∘A; μ]`, then `pi_gaussian_variance` on the composite dual `L∘L A`.

* **`pi_gaussian_map_exp_integral_le`** — for the field `μ.map A` and any dual
  `L` with `∑ᵢ (L (A eᵢ))²·vᵢ ≤ B`, `∫ exp(L φ) d(μ.map A) ≤ exp(B/2)`.  Centering
  transported through `A` (`pi_gaussian_centered` on `L∘L A`), variance the
  explicit form above — the small-field bound for an arbitrary (off-diagonal)
  constructed Gaussian covariance.

The Gaussian-from-covariance layer is now complete at the constructed level:
build the standard Gaussian (`isGaussian_pi`), push through any factor `A`
(`isGaussian_pi_map_clm`), it is centered (`pi_gaussian_centered` transported),
its covariance form is explicit (`pi_gaussian_map_variance`), and a bound on that
form gives the field-size bound (`pi_gaussian_map_exp_integral_le`).  The only
remaining step to a fully-realized fluctuation field is matching `A∘Aᵀ` to the
concrete CMP-99 gauge-covariant propagator (the Cholesky / spectral-factor +
propagator-bound step) and the CMP-116 single-scale raw-activity bound — both
carried as honest hypotheses, never axioms.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 78 (2026-06-13, **the faithful closure: ExpDecay covariance kernel ⟹
Gaussian field-size bound** `YangMills.RG.pi_gaussian_map_variance_quadratic` +
`pi_gaussian_map_exp_integral_le_of_expDecay`; core 8262)

**Build:** green (8262 jobs — theorems added to `RG/GaussianPi.lean`; the module
now also imports `RG/KernelSchur.lean`).  Oracle: both
`[propext, Classical.choice, Quot.sound]`.

This is the end-to-end join of the two independent substrates built this session:
the kernel decay / Schur test (`RG/KernelDecay.lean`, `RG/KernelSchur.lean`,
Add. 53–71) and the constructed Gaussian field (`RG/GaussianPi.lean`,
Add. 74–77).  *An exponentially-decaying covariance kernel now provably yields the
small-field fluctuation bound on a genuine constructed Gaussian.*

* **`pi_gaussian_map_variance_quadratic`** — the covariance of the transformed
  field is the Gram quadratic form of its kernel:
  `Var[L; μ.map A] = ∑ₓ∑ᵧ cₓ·Kₓᵧ·cᵧ` with `Kₓᵧ = ∑ᵢ vᵢ·(A eᵢ)ₓ·(A eᵢ)ᵧ`,
  `cₓ = L eₓ`.  Proof: expand `L(A eᵢ) = ∑ₓ (A eᵢ)ₓ·cₓ`, square via
  `Finset.sum_mul_sum`, reorganize the triple sum (`Finset.sum_comm`).  Puts the
  covariance into the exact shape `expDecay_quadratic_form_le` consumes.

* **`pi_gaussian_map_exp_integral_le_of_expDecay`** — the closure: if the Gram
  covariance kernel `K` is `ExpDecay d a κ K` (symmetric metric, row-sum `≤ S`),
  then `∫ exp(L z) d(μ.map A) ≤ exp(a·S·(∑ₓ (L eₓ)²)/2)`.  Variance = kernel
  quadratic form (above) `≤ a·S·∑cₓ²` by the finite-dimensional Schur test
  (`expDecay_quadratic_form_le`, Add. 69), feeding the field-size bound
  (`pi_gaussian_map_exp_integral_le`, Add. 77).  The decay constants `(a, κ, S)`
  are exactly those a Combes–Thomas / gauge-propagator analysis supplies.

The Gaussian-fluctuation toolkit is now complete and self-joined: *ExpDecay
covariance kernel ⟹ Schur quadratic-form bound ⟹ variance bound ⟹ field-size /
MGF bound*, all on an explicitly constructed Gaussian measure, zero axioms.  The
sole remaining input to instantiate it on the real Bałaban fluctuation field is
the concrete CMP-99 gauge-covariant propagator (showing its kernel is `ExpDecay`
with the right `κ`) and the CMP-116 single-scale raw-activity bound — carried as
honest hypotheses, never axioms.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 79 (2026-06-13, **the constructed Gram covariance kernel is PSD**
`YangMills.RG.gram_kernel_isPSDKernel`; core 8262)

**Build:** green (8262 jobs — theorem added to `RG/GaussianPi.lean`; module now
also imports `RG/CovarianceKernel.lean`).  Oracle:
`[propext, Classical.choice, Quot.sound]`.

Coherence / non-vacuity capstone of the Gaussian layer: the Gram covariance
kernel `Kₓᵧ = ∑ᵢ vᵢ·(A eᵢ)ₓ·(A eᵢ)ᵧ` of the transformed field `μ.map A` is a
genuine `IsPSDKernel` (`RG/CovarianceKernel.lean`, Add. 71) — every quadratic
form `∑ₓ∑ᵧ uₓ·Kₓᵧ·uᵧ ≥ 0`.  This certifies the Gram construction always realizes
a *valid* covariance, tying the constructed Gaussian to the PSD-kernel interface
(`psd_diag_nonneg`, `psd_cauchy_schwarz`).  Slick proof: any coefficient vector
`u` is realized by the dual `L = ∑ₓ uₓ·projₓ` (so `L eₓ = uₓ`), whence the
quadratic form equals `Var[L; μ.map A] ≥ 0`
(`pi_gaussian_map_variance_quadratic` + `variance_nonneg`).

The Gaussian-from-covariance layer (`RG/GaussianPi.lean`) is now a closed,
self-consistent toolkit: construct (`isGaussian_pi`), transform
(`isGaussian_pi_map_clm`), centered (`pi_gaussian_centered`), covariance is a
valid PSD kernel (`gram_kernel_isPSDKernel`) computed as a quadratic form
(`pi_gaussian_map_variance_quadratic`), and an ExpDecay covariance kernel gives
the field-size bound (`pi_gaussian_map_exp_integral_le_of_expDecay`).  The only
remaining input is the concrete CMP-99 gauge propagator (its kernel `ExpDecay`)
and the CMP-116 raw-activity bound — carried hypotheses, never axioms.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 80 (2026-06-13, **finite-range ⟹ ExpDecay: the operator-level
Combes–Thomas input** `YangMills.RG.finiteRange_isExpDecay`; core 8262)

**Build:** green (8262 jobs — theorem added to `RG/KernelDecay.lean`, no new
module).  Oracle: `[propext, Classical.choice, Quot.sound]`.

Opens the concrete-propagator track.  Until now the `ExpDecay` calculus
(composition, powers, resolvent — Add. 53–56) and the field-size bound
(Add. 78) consumed `ExpDecay` kernels *hypothetically*.  This supplies the first
concrete source of them.

* **`finiteRange_isExpDecay`** — a kernel `K` of finite range `R`
  (`K x y = 0` whenever `d x y > R`) and bounded by `M` is `ExpDecay d (M·e^{κR}) κ K`
  for *any* rate `κ ≥ 0`.  On the support `e^{-κ d} ≥ e^{-κR}` absorbs the
  constant; off it `K = 0`.  Hence every finite-range lattice operator — the
  nearest-neighbour Laplacian, the Wilson hopping term, the background-field
  covariant difference operator — is `ExpDecay`, and by `expDecay_comp` /
  `expDecay_pow` / `expDecay_resolvent` its resolvent (the lattice propagator) is
  too.  Composed with `gram_kernel_isPSDKernel` +
  `pi_gaussian_map_exp_integral_le_of_expDecay` (Add. 78–79), this is the
  concrete origin of the exponentially-decaying Gaussian covariance the
  fluctuation integral needs.

This reduces the gauge-propagator obstruction to two faithful, source-grounded
facts: (i) the concrete Bałaban background-field covariant operator is
finite-range (immediate from its definition) so its inverse on the small-field
region is `ExpDecay` via the resolvent series, and (ii) the CMP-116 single-scale
raw-activity bound — both carried as honest hypotheses, never axioms.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 81 (2026-06-13, **the resolvent of a small finite-range operator
decays exponentially — concrete Combes–Thomas**
`YangMills.RG.finiteRange_resolvent_isExpDecay`; core 8262)

**Build:** green (8262 jobs — theorem added to `RG/KernelDecay.lean`).  Oracle:
`[propext, Classical.choice, Quot.sound]`.

The single composite that turns the abstract resolvent calculus into the literal
mechanism of the Bałaban propagator bound.

* **`finiteRange_resolvent_isExpDecay`** — a finite-range kernel `K` (range `R`,
  bound `M`), small enough that `M·e^{κR}·S < 1` for some rate `κ > σ` (with
  `∑_z e^{−σ d(x,z)} ≤ S`), has Neumann-series resolvent
  `(1 − K)⁻¹ = ∑ₙ Kⁿ` that is `ExpDecay` at the *positive* rate `κ − σ`, with
  amplitude `M·e^{κR}/(1 − M·e^{κR}·S)`.  Pure composition of
  `finiteRange_isExpDecay` (Add. 80: range ⇒ decay at any rate) with
  `expDecay_resolvent` (Add. 56: decay + smallness ⇒ resolvent decay).

This is exactly how the YM activity-decay constant `κ` (CMP 116 Lemma 3) arises:
the background-field covariant difference operator is finite-range, and its
inverse — the propagator (CMP 95/99) — inherits exponential decay from this
resolvent estimate.  The chain is now concrete end-to-end at the *operator* level:
**finite-range operator ⇒ resolvent ExpDecay ⇒ (Gram) covariance ExpDecay ⇒ Schur
quadratic-form bound ⇒ Gaussian field-size bound**.  The remaining inputs are the
two faithful source facts — the concrete operator's finite range / small-field
smallness (CMP 95/99) and the CMP-116 raw-activity bound — carried as honest
hypotheses, never axioms.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 82 (2026-06-13, **volume-uniform lattice exponential summability from
a shell-growth bound** `YangMills.RG.lattice_exp_sum_le_of_shell`; core 8262)

**Build:** green (8262 jobs — theorem added to `RG/KernelDecay.lean`).  Oracle:
`[propext, Classical.choice, Quot.sound]`.

Discharges the *recurring* geometric hypothesis of the entire decay stack — the
summability `∑_z e^{−σ d(x,z)} ≤ S` consumed (as `hsum`/`hS`/`hrow`) by
`expDecay_comp`, `expDecay_resolvent`, `finiteRange_resolvent_isExpDecay`, and
`expDecay_quadratic_form_le`.

* **`lattice_exp_sum_le_of_shell`** — if the shell cardinalities
  `#{z : ℓ z = k}` (with `ℓ` the graph distance from a fixed point) are bounded by
  `N k`, and `∑ₖ N k · e^{−σk}` is summable, then
  `∑_z e^{−σ·ℓ z} ≤ ∑'ₖ N k · e^{−σk}` — a bound **independent of the lattice
  size**.  On `ℤ^d` the shells grow polynomially (`N k = C·(k+1)^{d−1}`), so the
  dominating series is polynomial × geometric, finite for every `σ > 0`: this is
  the geometric origin of the uniform summability constant `S` in the
  Combes–Thomas / Bałaban propagator estimates.  Proof: group into shells
  (`Finset.sum_fiberwise_of_maps_to`), bound each shell by `N k`, compare the
  finite shell-sum to the full series (`Summable.sum_le_tsum`).

With this, the decay-and-fluctuation substrate is geometrically self-contained:
the lattice geometry supplies `S`, finite-range operators are `ExpDecay`
(Add. 80), their resolvents decay (Add. 81), the resulting Gram covariance is PSD
(Add. 79) and its quadratic form is Schur-bounded (Add. 69), giving the Gaussian
field-size bound (Add. 78).  The remaining inputs are the two faithful source
facts — the concrete Bałaban operator's finite range / smallness (CMP 95/99) and
the CMP-116 raw-activity bound — carried as honest hypotheses, never axioms.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 83 (2026-06-14, **explicit geometric shell constant**
`YangMills.RG.lattice_exp_sum_le_geometric`; core 8262)

**Build:** green (theorem added to `RG/KernelDecay.lean`).  Oracle:
`[propext, Classical.choice, Quot.sound]`.

Specializes Addendum 82 to the bounded-degree / geometric-shell form most
directly consumed by the Combes–Thomas constants.

* **`lattice_exp_sum_le_geometric`** — if
  `#{z : ℓ z = k} ≤ C·r^k` and the exponential rate beats the shell growth,
  `r·exp(-σ) < 1`, then

      ∑_z exp(-σ·ℓ z) ≤ C · (1 - r·exp(-σ))⁻¹.

This packages the uniform summability constant `S` in closed form, rather than
leaving it as an abstract `∑'_k N k·exp(-σk)`.  It is the exact bounded-degree
lattice version used by the finite-range resolvent and Schur bounds: shell
growth supplies `r`; decay supplies `exp(-σ)`; the smallness condition is the
ordinary geometric-series condition.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 84 (2026-06-14, **repository coherence hardening**; current-state
docs + RG axiom-scan coverage; core 8262)

No new theorem was added in this checkpoint.  The improvement is
certification/reproducibility:

* added `CURRENT-STATE.md` as the short live entry point;
* updated README / frontier / roadmap / handoff docs from the stale
  `hRpoly`+`hg` frontier to the current `hRpoly` frontier, with the
  marginal-coupling and summability scaffolding recorded as theorem-fed;
* updated live build-count references to **8262 jobs**;
* corrected `YangMillsCore.lean` comments so the modern clean `YangMills/RG/**`
  layer is not confused with the excluded legacy Balaban-RG packet;
* extended `scripts/check_consistency.py` so verified-core axiom scanning now
  includes `YangMills/RG`.

Verification rerun:

```text
python scripts/check_consistency.py
✅ Zero sorry in Lean source; zero axioms in the verified-core tree

lake env lean oracle_check.lean
every headline line ends [propext, Classical.choice, Quot.sound]

lake build YangMillsCore
Build completed successfully (8262 jobs).
```

## Addendum 85 (2026-06-18, **off-diagonal matrix-coefficient vanishing
repaired back into the verified core**
`YangMills.ClayCore.sunHaarProb_entry_offdiag`; core 8263)

**Build:** green (the bit-rotted `ClayCore/SchurEntryOffDiag.lean`, excluded
since the 2026-05 cleanup, repaired and re-imported by `YangMillsCore`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

The module states the Schur off-diagonal entry-orthogonality
**L2.6 step 1b-ii**:

* **`sunHaarProb_entry_offdiag`** — for `i ≠ k`,

      ∫ U, U.val i j * star (U.val k l) ∂(sunHaarProb N) = 0.

  This generalizes the on-diagonal / off-diagonal entry vanishing already in
  the core (`SchurEntryOrthogonality`, `SchurEntryNAlitySelection`) to
  *arbitrary* column indices `j, l`: any matrix-coefficient pair with distinct
  **row** indices has zero Haar mean. This is the row-index half of the
  Schur-orthogonality structure (node F4 in `HORIZON.md`): together with the
  N-ality selection rules it is the algebraic engine of the area law's kill
  mechanism, and a stepping stone toward the full `∫ U_{ij} conj(U_{kl}) =
  (1/N) δ_{ik} δ_{jl}`.

**What bit-rotted and how it was repaired.** Three Mathlib-v4.29 elaboration
seams had broken the file:

1. `rw [star_mul]` was ambiguous on `ℂ` (both the `StarMul` reverse-order law
   `star_mul` and its commutative variant `star_mul'` apply). Repaired by
   computing the conjugation through the explicit ring endomorphism,
   `show (starRingEnd ℂ) (a*b) = _` then `(starRingEnd ℂ).map_mul` + `mul_comm`,
   following the idiom already used in `SchurDiagPhase` (`star_I_mul_ofReal`).
2. `Filter.EventuallyEq.of_forall` is no longer a public name. Repaired by
   carrying the invariance through `MeasureTheory.integral_mul_left_eq_self`
   + `funext` instead of `integral_congr_ae` + `EventuallyEq.of_forall`,
   following the idiom of `SchurZeroMean.sunHaarProb_trace_complex_integral_zero`.
3. `sunHaarProb N` requires `[NeZero N]`; the original left it implicit.
   Repaired by adding `[NeZero N]` to the headline theorem (the auxiliary
   lemmas need only `Fin N`).

The mathematics is unchanged (left-invariance of Haar against `piAntiSymSU i k`,
whose phase factor is `exp(I·π) = -1`, forces `I₀ = -I₀`, hence `I₀ = 0`); only
the proof scripts were hardened against the rename/ambiguity. The module is
re-imported by `YangMillsCore` (the `NOTE: bit-rotted` guard is removed), the
build job count incremented **8262 → 8263**, and the headline is wired into
`oracle_check.lean`.

**Honest scope.** This is lattice-side SU(N) Haar algebra, one step of the
character-orthogonality programme toward F4 (which itself is downstream of
Peter–Weyl, still not in Mathlib). It discharges *no* `hRpoly`/§6.3/continuum
obligation; Clay distance **~0% (<0.1%), unchanged**.

## Addendum 86 (2026-06-18, **polymer modified metric combinatorial core**
`YangMills.RG.walk_crosses_frontier` and `YangMills.RG.absorbedHole_touches_skeleton_single`; core 8264)

**Build:** green (the new module `YangMills/RG/ModifiedMetric.lean` added and imported by `YangMillsCore`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum closes the combinatorial core of the polymer-with-holes campaign brick **P2b-i**:

* **`walk_crosses_frontier`** — a walk staying inside `A ∪ B` that starts in `A \ B` and ends in `B \ A` must contain an edge crossing from `A` to `B`.
* **`absorbedHole_touches_skeleton_single`** — for a walk-connected polymer `Y ∪ H₀` composed of skeleton `Y` and a single disjoint absorbed hole `H₀`, the hole `H₀` must touch the skeleton `Y` via a `cubeAdj`-edge.

**How compilation was resolved.** The initial implementation relied on a nonexistent `SimpleGraph.Walk.exists_cons_of_not_nil` decomposition lemma, which caused compilation errors under Mathlib v4.29. This was replaced with a direct induction proof using a strong induction recursor on the walk length (`n`) combined with `match p with` and the explicit recursor constructor pattern `@Walk.cons`. The induction variables were generalized, and the `omega` linter was assisted by rewriting the definition of `Walk.length_cons` explicitly to resolve inequality proofs.

**Honest scope.** This is purely combinatorial lattice geometry, providing the walk-based topological lemma for single-hole absorption (Dimock II (arXiv:1212.5562) Section 5, Lemma \label{summit}). It does not resolve any multi-hole configurations or the analytic Gaussian suppressions of the holes. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 87 (2026-06-18, **multi-hole skeleton touching and multiplicity bounds**
`YangMills.RG.absorbedHole_touches_skeleton_multi` and `YangMills.RG.touchingHoles_card_le`; core 8264)

**Build:** green (multiplicity bounds and associated theorems added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum closes the multi-hole combinatorial bounds of the polymer-with-holes campaign brick **P2b-ii-a**:

* **`absorbedHole_touches_skeleton_multi`** — in a connected polymer with multiple disjoint holes having no adjacency edges between them, every absorbed hole must share a boundary edge with the skeleton.
* **`touchingHoles_card_le`** — the number of absorbed holes touching the skeleton $Y$ is at most $\Delta \cdot |Y|$, where $\Delta$ is the maximum degree of the adjacency graph.

**How compilation was resolved.**
1. To ensure all typeclass resolutions remain clean and constructive, we annotated the type parameter `(H₀ : Finset V)` explicitly inside the `touchingHoles` filter predicate. This allowed Lean to constructively synthesize decidability of the bounded existential properties without relying on noncomputable axioms.
2. In the `card_neighborPairs` proof, the `subst` tactic was bypassed by obtaining elementwise projections from the tuple equality `(x, a) = (x1, x2)` and showing `x = y` through a chain of rewrites (`hx1, h1, ← hy1`), avoiding complex unification issues.
3. In `touchingHoles_card_le`, we resolved the `Nat.cast` type coercion issue in the sum-majorant inequality by explicitly adding `Nat.cast_id` to the `simp only` list, simplifying the cast term `↑(#Y) * Δ` directly to `#Y * Δ`.
4. In the empty-vertex case, the contradiction was solved by simplifying the membership predicate to `False` and using `(hV ⟨x⟩).elim` under `¬ Nonempty V`.

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


## Addendum 88 (2026-06-18, **active-edge cardinality bound for connected sets**
`YangMills.RG.card_le_activeEdges_add_one`; core 8264)

**Build:** green (active-edge cardinality bound added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum completes the active-edge cardinality bound for connected sets:

* **`card_le_activeEdges_add_one`** — For any connected vertex set `S` in a graph `G`, its cardinality is bounded by the number of active edges in `S` plus 1: $|S| \leq |E(G[S])| + 1$.

**How compilation was resolved.**
1. We resolved a walk support type mismatch in `walkConnected_of_walk_from_root` by using `List.mem_reverse` for the reversed walk support and implementing a self-contained helper `mem_of_mem_tail` to convert membership in `List.tail` to list membership.
2. We fixed the `Sym2.mk` constructor arity mismatch where `Sym2.mk` expects two arguments (`Sym2.mk p u` via notation `s(p, u)`) instead of a pair tuple `Sym2.mk (p, u)`.
3. We assisted the `omega` solver by explicitly adding `h_card_erase : S'.card = S.card - 1` using `card_erase_of_mem huS` to the context, which allowed `omega` to linearly solve the cardinality induction step without encountering non-linear subtraction issues.
4. We cleaned up the unused variable warning for `hr` in `walkConnected_of_walk_from_root` and updated the calling code.

**Honest scope.** This is purely combinatorial lattice geometry, providing a cardinality bound for connected sets. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 89 (2026-06-18, **polymer modified metric definition and properties**
`YangMills.RG.discreteModifiedMetric`, `YangMills.RG.skeleton_card_le_discreteModifiedMetric_add_one`, and `YangMills.RG.discreteModifiedMetric_empty_holes`; core 8264)

**Build:** green (modified metric and associated theorems added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the polymer modified metric definition and its basic combinatorial properties, marking progress on **P2b-ii-b-1**:

* **`discreteModifiedMetric`** — The discrete modified metric $d_M(X, \bmod H)$ defined as the Steiner tree length of the skeleton. To ensure classical decidability of the existential properties, we used a `by classical` block in its definition.
* **`skeleton_card_le_discreteModifiedMetric_add_one`** — Proves that the cardinality of the skeleton is bounded by the modified metric plus 1: $|\text{skeleton } H\ X| \leq d_M(X, \bmod H) + 1$.
* **`discreteModifiedMetric_empty_holes`** — Proves that when the hole family $H$ has no holes, the modified metric simplifies to the standard bulk tree metric: $d_M(X, \bmod \emptyset) = |X| - 1$.

**How compilation was resolved.**
We used `Nat.sInf_mem` to extract the minimal connected vertex set $S$ spanning the skeleton, and verified that its card is related to the modified metric. For `discreteModifiedMetric_empty_holes`, we showed that when holes are empty, the set of connected sets containing the skeleton and contained in $X$ is the singleton $\{X\}$. We then proved that the `sInf` of a singleton $\{x\}$ equals $x$ by utilizing `Nat.sInf_mem` and `Set.mem_singleton_iff`.

**Honest scope.** This is purely combinatorial lattice geometry, defining the modified metric and its skeleton cardinality bound. It does not resolve the analytic Gaussian suppressions of the holes required for full summability. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 90 (2026-06-18, **multi-hole polymer fillings multiplicity bounds**
`YangMills.RG.fillings_card_le_two_pow` and `YangMills.RG.cube_fillings_card_le_two_pow`; core 8264)

**Build:** green (fillings bounds added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum completes the multi-hole polymer multiplicity bounds, marking progress on **P2b-ii-b-2**:

* **`admissibleFillings`** — Defines the set of connected, hole-respecting polymers with a fixed skeleton Y.
* **`fillings_card_le_two_pow`** — Proves that the number of admissible fillings is bounded by $2^{\Delta \cdot |Y|}$.
* **`cube_fillings_card_le_two_pow`** — Proves the corresponding $2^{3^d \cdot |Y|}$ bound on the d-dimensional cube lattice.

**How compilation was resolved.**
We defined the injection from admissible fillings to subsets of touching holes using `absorbedHoles`. By proving injectivity of this mapping (`admissibleFillings_inj`) and leveraging the cardinality of the powerset, we bounded the number of fillings by $2^{|\text{touching holes}|}$ and combined it with the touching holes cardinality bound `touchingHoles_card_le` to yield $2^{\Delta \cdot |Y|}$.

**Honest scope.** This is purely combinatorial lattice geometry, bounding the number of polymers corresponding to a skeleton. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 91 (2026-06-18, **discrete modified metric comparison bounds**
`YangMills.RG.discreteModifiedMetric_le_bulkTreeLength`, `YangMills.RG.discreteModifiedMetric_mono_skeleton`, and `YangMills.RG.discreteModifiedMetric_mono_holes`; core 8264)

**Build:** green (metric comparison theorems added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the source-faithful comparison bounds for the discrete modified metric, marking progress on **P2b-ii-b-3**:

* **`discreteModifiedMetric_le_bulkTreeLength`** — Proves that the discrete modified metric is bounded above by the standard bulk tree metric: $d_M(X, \bmod H) \leq |X| - 1$ for connected $X$.
* **`discreteModifiedMetric_mono_skeleton`** — Proves that a larger skeleton $Y_1 \subseteq Y_2$ (for a fixed polymer $X$) yields a larger metric: $d_M(X, \bmod H_1) \leq d_M(X, \bmod H_2)$ when $\text{skeleton } H_1\ X \subseteq \text{skeleton } H_2\ X$.
* **`discreteModifiedMetric_mono_holes`** — Proves that more holes $H_1.holes \subseteq H_2.holes$ (which reduces the skeleton size) yields a smaller metric: $d_M(X, \bmod H_2) \leq d_M(X, \bmod H_1)$.

**How compilation was resolved.**
We proved that $X$ itself is a valid candidate for the Steiner tree spanning the skeleton, which immediately bounds the `sInf` of Steiner tree lengths by $|X| - 1$. For the monotonicity theorems, we showed that if $Y_1 \subseteq Y_2 \subseteq X$, any valid connected set $S$ spanning $Y_2$ also spans $Y_1$. Thus, the set of spanning tree lengths of $Y_2$ is a subset of the set of spanning tree lengths of $Y_1$. We then leveraged `Nat.sInf_le` and `Nat.sInf_mem` to prove the inequalities, avoiding typeclass synthesis or constructive decidability errors by working with classical decidability locally inside the proofs.

**Honest scope.** This is purely combinatorial lattice geometry, establishing discrete comparison bounds for the modified metric. It does not construct the continuum tree-length metric from first principles. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 92 (2026-06-18, **skeleton-fillings multiplicity bound**
`YangMills.RG.skeleton_fillings_weight_summable`; core 8264)

**Build:** green (preliminary bound added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the preliminary combinatorial estimate for fillings multiplicity over skeletons (progress on **P2b-ii-c**):

* **`skeleton_fillings_weight_summable`** — Proves that the polymer sum over all connected skeletons $Y$ containing a fixed root $r$ of the fillings card multiplied by the exponential metric weight $q^{|Y|}$ converges and is bounded by a volume-independent constant:
  $$\sum'_{Y \ni r} |admissibleFillings(Y)| \cdot q^{|Y|} \leq (1 - 3^{2d} \cdot q \cdot 2^{3^d})^{-1}$$
  under the coordination entropy-suppression condition.

**How compilation was resolved.**
We bounded the filling multiplicity term using `cube_fillings_card_le_two_pow` (yielding $2^{3^d \cdot |Y|}$) and combined it with the metric factor $q^{|Y|}$ into a single unified base $q' = q \cdot 2^{3^d}$. The resulting sum was then majorized by the standard lattice polymer sum using `Summable.tsum_le_tsum` and bounded using `cube_polymer_summable`. Finiteness of the index type was used to discharge the summability premise via `Summable.of_finite`.

**Honest scope.** This is purely combinatorial lattice geometry, proving that the skeleton-growth series converges under sufficient exponential suppression. It is a preliminary combinatorial estimate, not the modified-metric summability itself. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 93 (2026-06-18, **discrete modified-metric summability**
`YangMills.RG.discreteModifiedMetric_weight_summable`; core 8264)

**Build:** green (the genuine modified-metric summability theorem added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum proves the genuine discrete modified-metric summability on the cube lattice, closing **P2b-ii-d**:

* **`discreteModifiedMetric_weight_summable`** — Proves that the polymer sum over all connected, hole-respecting polymers $X$ containing a fixed root $r$ in their skeleton, weighted by the exponential metric decay $q^{d_M(X, \bmod H) + 1}$, converges and is bounded by a volume-independent constant:
  $$\sum'_{X : r \in \text{skel } X} q^{d_M(X, \bmod H) + 1} \leq (1 - 3^{2d} \cdot q \cdot 2^{3^d + 1})^{-1}$$
  under the coordination entropy-suppression condition.

**How compilation was resolved.**
We grouped the polymer sum fiberwise over their connected minimal spanning sets $S$ using `exists_minimal_spanning_set` to associate each polymer $X$ with a spanning set $S$ of cardinality $d_M(X, \bmod H) + 1$. By partitioning the sum via `Finset.sum_fiberwise_of_maps_to`, the multiplicity of polymers matching a given spanning set $S$ was bounded by the powerset of $S$ times the maximum fillings of each subset, yielding $2^{(3^d + 1)|S|}$. The resulting sum was then majorized by the standard lattice polymer sum with base $q' = q \cdot 2^{3^d + 1}$ and bounded using `cube_polymer_summable`. All summability premises were discharged via `Summable.of_finite` over the finite torus.

**Honest scope.** This is purely combinatorial lattice geometry, establishing the discrete modified-metric summability on the cube lattice. It does not resolve the analytic Gaussian suppressions of the holes or the continuum limit. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 94 (2026-06-18, **holes-respected polymer system instantiation**
`YangMills.RG.holePolymerSystem`; core 8265)

**Build:** green (instantiation added to `HolePolymerSystem.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum instantiates the abstract `KP.PolymerSystem` for the holes-respected polymer family on the cube lattice, marking progress toward **P3**:

* **`holePolymerSystem`** — Defines the polymer system with nonempty, connected finsets of cubes respecting the hole family $H$, with overlap as the incompatibility relation.
* **`Fintype` instance** — Synthesized classically to establish that the polymer type is finite on the torus, allowing full compatibility with the existing KP expansion and convergence theorems.

**How compilation was resolved.**
We proved self-incompatibility via `Finset.disjoint_left.mp` on a nonempty witness, and established the Fintype instance by introducing `attribute [local instance] Classical.propDecidable` and carrying the torus positivity constraint `[NeZero L]`. The instance and constructor were marked as `noncomputable` due to the classical choice axiom dependency.

**Honest scope.** This is a structural instantiation of the polymer system framework on the lattice. It does not prove the analytical Gaussian activity bounds for the renormalization group or the continuum limit. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 95 (2026-06-18, **discrete modified metric degenerate cases regression testing**
`YangMills.RG.discreteModifiedMetric_d_zero` and `YangMills.RG.discreteModifiedMetric_L_one`; core 8265)

**Build:** green (regression lemmas added to `ModifiedMetric.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum completes the boundary-case testing of the discrete modified metric:

* **`discreteModifiedMetric_d_zero`** — Proves that when $d = 0$, the metric is always 0.
* **`discreteModifiedMetric_L_one`** — Proves that when $L = 1$, the metric is always 0.

**How compilation was resolved.**
Since $d = 0$ or $L = 1$, the underlying type of cubes is a subsingleton (proven using `funext` and Lean's built-in `nomatch` construct for empty type elimination, or `Subsingleton.elim`). Thus, any spanning set $S$ has cardinality at most 1, so the Steiner tree length $S.card - 1$ is always 0.

**Honest scope.** This is purely combinatorial testing on degenerate lattice dimensions and sizes. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 96 (2026-06-18, **holes-respected rooted activity sum bound**
`YangMills.RG.rootedHolePolymerSum` and `YangMills.RG.rootedHolePolymerSum_bound`; core 8265)

**Build:** green (rooted sum and bounds added to `HolePolymerSystem.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the rooted polymer activity sum and its volume-independent upper bound:

* **`rootedHolePolymerSum`** — Defines the total activity sum of connected, hole-respecting polymers whose skeleton contains a fixed root $r$.
* **`rootedHolePolymerSum_bound`** — Proves a volume-uniform bound on the norm of the activity sum under the coordination entropy-suppression condition.

**How compilation was resolved.**
We bounded the norm of the activity sum by the sum of the norms using `norm_tsum_le_tsum_norm` (discharged via the finite-sum summability proof). We then mapped the sum over the subtype of polymers to a sum over all connected, hole-respecting finsets using `Fintype.sum_equiv` with a bijection `f1`, and majorized it via the discrete modified-metric summability theorem.

**Honest scope.** This provides the convergent activity sum bound required by the cluster expansion consumer. It does not prove the analytical Gaussian activity bounds for the renormalization group or the continuum limit. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 97 (2026-06-18, **holes-respected polymer system KP convergence and bounds**
`YangMills.RG.holePolymerSystem_KPCriterion`, `YangMills.RG.holePolymerSystem_converges`, and `YangMills.RG.holePolymerSystem_norm_clusterSum_le`; core 8265)

**Build:** green (convergence theorems added to `HolePolymerSystem.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum connects the holes-respected polymer system to the abstract Kotecký–Preiss convergence machinery, advancing **P3** (proving structural convergence under bare KP, while the analytical modified-metric decay bound on clusters remains open):

* **`holePolymerSystem_KPCriterion`** — Proves that under the modified-metric bound, a constant weight function $a(X) = 1$ satisfies the KP criterion for sufficiently small $q$.
* **`holePolymerSystem_converges`** — Proves that the Mayer cluster series for the holes-respected polymer system converges absolutely under the bare KP criterion.
* **`holePolymerSystem_norm_clusterSum_le`** — Establishes a quantitative bound on the norm of the cluster sum.

**How compilation was resolved.**
We verified that $q \leq 1$ holds since the polymer system has cardinality at least 1 (nonempty hypothesis), and used a `calc` block with `gcongr` to show that $q^{d_M + 1} \leq q$ for $0 \leq q \leq 1$ without external lemmas. We then instantiated `KP.kp_convergence_sharp` and `KP.kp_norm_clusterSum_le_sharp` directly.

**Honest scope.** This completes the combinatorial and structural convergence substrate of the cluster expansion with holes. It does not prove the analytical Gaussian activity bounds for the renormalization group or the continuum limit, nor does it establish the modified-metric decay bound on the cluster activities themselves. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 98 (2026-06-18, **translation-invariance of the modified metric and polymer system**
`YangMills.RG.translatePolymer`, `YangMills.RG.holePolymerSystem_incomp_translate`, and `YangMills.RG.rootedHolePolymerSum_translate`; core 8265)

**Build:** green (translation theorems added to `Translation.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the translation-invariance of the discrete modified metric, the holes-respected polymer system, and its rooted activity sum:

* **`translatePolymer`** — Defines the translation operator on polymers.
* **`holePolymerSystem_incomp_translate`** — Proves that translation preserves the incompatibility relation (overlap or touching) on the lattice.
* **`rootedHolePolymerSum_translate`** — Proves that the rooted polymer activity sum is translation-invariant on the torus under translated activity.

**How compilation was resolved.**
We constructed the bijection `g` between the root-centered polymer subtype and the translated root-centered subtype. We proved injectivity and surjectivity of `g` using the injection/surjection lemmas for polymer translation. Fintype sum equivalence was utilized to reduce the translated sum to the original sum, and `translateActivity_apply` resolved the activity identity.

**Honest scope.** This completes the translation-invariance substrate for the holes-respected polymer gas. It does not prove the analytical Gaussian activity bounds or the continuum limit. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 99 (2026-06-18, **volume-uniform Kotecky-Preiss criterion and convergence under local summability**
`YangMills.RG.closedNeigh`, `closedNeigh_card_le`, `incomp_imp_intersect`, `holePolymerSystem_KPCriterion_volumeUniform`, `holePolymerSystem_converges_volumeUniform`, and `holePolymerSystem_norm_clusterSum_le_volumeUniform`; core 8267)

**Build:** green (volume-uniform theorems added to `LocalKP.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the volume-uniform Kotecký–Preiss criterion and absolute convergence of the holes-respected polymer system under a local volume-independent activity summability condition:

* **`closedNeigh`** — Defines the closed neighborhood of a set of cubes on the lattice.
* **`closedNeigh_card_le`** — Bounds the cardinality of the closed neighborhood of a set $X$ of cubes by $(3^d + 1) |X|$.
* **`incomp_imp_intersect`** — Proves that if two polymers $X, Y$ are incompatible, then $Y$ must intersect the closed neighborhood of $X$.
* **`holePolymerSystem_KPCriterion_volumeUniform`** — Establishes that the polymer system satisfies the KP criterion with weight function $a(X) = |X|$ under local volume-independent summability.
* **`holePolymerSystem_converges_volumeUniform`** — Proves the absolute convergence of the cluster series volume-uniformly.
* **`holePolymerSystem_norm_clusterSum_le_volumeUniform`** — Bounds the norm of the cluster sum volume-uniformly.

**How compilation was resolved.**
We bounded the cardinality of the closed neighborhood by first showing it is a subset of the big union of the single-element inserts and neighbor sets, and then majorized each neighbor set cardinality by $3^d$ (using the graph degree bound `cubeAdj_degree_le`). We established that incompatibility implies intersection with `closedNeigh` via a disjunction on overlap versus adjacency. The KP criterion was proved by bounding the sum over incompatible polymers by a big union over cubes in `closedNeigh X`, majorizing this by the local summability bound, and cancelling the $(3^d + 1)$ factors using `mul_inv_cancel₀` for `ℝ`.

**Honest scope.** This completes the volume-uniform convergence substrate of the cluster expansion for the holes-respected polymer gas under local summability. It does not prove the analytical Gaussian bounds on the activities. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 100 (2026-06-18, **cluster modified metric, decay weight base cases, and walk connectedness of unions**
`YangMills.RG.clusterUnion`, `clusterModifiedMetric`, `clusterUnion_skeleton`, `clusterUnion_fin_one`, `clusterModifiedMetric_fin_one`, `clusterDecayWeight`, `clusterDecayWeight_fin_one`, and `walkConnected_union`; core 8268)

**Build:** green (cluster definitions and theorems added to `ClusterDecay.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the union and modified metric of polymer clusters, defines the cluster decay weight function under the modified metric, and establishes walk-connectedness for the union of two connected set-polymers that overlap or touch:

* **`clusterUnion`** — Defines the union of all polymers in a cluster.
* **`clusterModifiedMetric`** — Defines the modified metric of a cluster.
* **`clusterUnion_skeleton`** — Proves that the skeleton of a cluster union equals the big union of the individual polymer skeletons.
* **`clusterUnion_fin_one`** — Proves that for a single-polymer cluster ($n=1$), the cluster union reduces exactly to that polymer.
* **`clusterModifiedMetric_fin_one`** — Proves that for $n=1$, the cluster metric equals the individual polymer's modified metric.
* **`clusterDecayWeight`** — Defines the decay weight $q^{d_M(Union X) + 1}$ of a cluster.
* **`clusterDecayWeight_fin_one`** — Proves that for $n=1$, the cluster decay weight reduces to the single polymer's decay weight.
* **`walkConnected_union`** — Proves that the union of two connected sets that touch or overlap remains connected.

**How compilation was resolved.**
We defined `clusterUnion` as a big union over `Finset.univ` of the polymer values. We proved the skeleton union lemma `skeleton_biUnion` showing skeleton distributes over big unions, which resolved `clusterUnion_skeleton`. The single-polymer base case lemmas were proved using a subsingleton elimination on `Fin 1` to reduce the index of `Fin 1` to `0`. We proved `walkConnected_union` by performing a case analysis on the location of endpoints and constructing the concatenated path using `SimpleGraph.Walk.append` and `Walk.support_append` properties from Mathlib.

**Honest scope.** This completes the first mathematical targets of the polymer cluster remainder convergence substrate. It does not prove the analytical Gaussian activity bounds on clusters. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 101 (2026-06-19, **cluster remainder convergence substrate and metric monotonicity base case**
`YangMills.RG.walk_union_connected`, `YangMills.RG.cluster_closedNeigh_union_connected`, `YangMills.RG.clusterRemainderSum_summable`, and `YangMills.RG.discreteModifiedMetric_le_clusterModifiedMetric`; core 8268)

**Build:** green (the remaining Phase 8 targets added to `ClusterDecay.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the Phase 8 substrate targets that were actually
proved:

* **`walk_union_connected`** — Proves that if we have a path in the incompatibility graph of a polymer cluster, we can connect the endpoints of the path in the big union of their closed neighborhoods.
* **`cluster_closedNeigh_union_connected`** — Proves that if `IsCluster` holds, then the union of the closed neighborhoods of all polymers in the cluster is connected.
* **`clusterRemainderSum_summable`** — Proves the absolute volume-uniform convergence of the cluster activity remainder sum under the local Kotecký–Preiss criterion.
* **`discreteModifiedMetric_le_clusterModifiedMetric`** — Establishes only the
  base case $n=1$, where the cluster union is exactly the single polymer.

**How compilation was resolved.**
We defined the connectivity of the union of closed neighborhoods using a path induction on the incompatibility graph. The remainder sum absolute convergence was bounded by introducing a parameter $t > 0$ and scaling the polymer activities, then applying the Kotecký–Preiss criterion to the scaled system to achieve a volume-uniform bound. The metric comparison was resolved only for the base case $n=1$ by using subsingleton elimination on the single polymer cluster index.

**Honest scope correction.** This does **not** prove an arbitrary-cluster
comparison `discreteModifiedMetric H (X i).val ≤ clusterModifiedMetric H z X`.
Subset inclusion of a polymer into the union is insufficient because
`discreteModifiedMetric` is a Steiner minimum constrained to lie inside its
ambient finset; enlarging the ambient set can introduce shortcuts.  The source
shape remains `d_M` of the cluster object/union, but downstream work must not
treat the `Fin 1` theorem as a general monotonicity lemma. Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 102 (2026-06-19, **coarse gauge-renormalization operator Ū and its gauge covariance**
`YangMills.RG.UbarDeviation`, `coarseTransform`, `UbarDeviation_gaugeAct`, `rep_UbarDeviation_gaugeAct`, `Ubar`, and `Ubar_gaugeAct`; core 8269)

**Build:** green (the B4-Ū targets added to `Ubar.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the coarse gauge-renormalization operator `Ū` on the lattice and proves its gauge covariance under a matrix representation of the gauge group:

* **`UbarDeviation`** — Defines the orientation-consistent path cancellation deviation term for a coarse edge $C$ at a fine site $x$.
* **`coarseTransform`** — Restricts a fine gauge transform to coarse lattice basepoints.
* **`UbarDeviation_gaugeAct`** — Proves that the deviation term conjugates by the source basepoint under gauge transformations.
* **`rep_UbarDeviation_gaugeAct`** — Transports the deviation gauge act theorem to the matrix algebra unit group representation.
* **`Ubar`** — Defines the coarse gauge-renormalization operator `Ū` using the matrix exponential, block average weights, and `nearLog`.
* **`Ubar_gaugeAct`** — Proves that `Ū` behaves like a coarse gauge configuration under gauge transformations (transforming by conjugation at the coarse edge endpoints).

**How compilation was resolved.**
We replaced implicit algebra coercions with explicit `.val` projections for `Units 𝔸` throughout the proof steps of `Ubar_gaugeAct` to avoid typeclass synthesis failures for `Inv 𝔸`. We resolved a stuck typeclass instance problem by supplying `(𝔸 := 𝔸)` explicitly to `rep_UbarDeviation_gaugeAct`. Finally, we proved the sum conjugation identity by constructing a sum-rewriting lemma `h_rw` and finished the main proof using precise right-associative rewriting (`← mul_assoc`, `Units.inv_mul`, `one_mul`).

**Honest scope.** This completes the target B4-Ū (full) from the gauge-RG campaign plan. It does not prove the analytical Gaussian activity bounds or the continuum limit. Clay distance **~0% (<0.1%), unchanged**.


## Addendum 103 (2026-06-19, **locality of the coarse gauge-renormalization operator Ū**
`YangMills.RG.wilsonLine_congr`, `YangMills.RG.UbarDeviation_congr`, and `YangMills.RG.Ubar_locality`; core 8269)

**Build:** green (locality theorems added to `Ubar.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the locality of the coarse gauge-renormalization operator `Ū` on the lattice (Target B5-full):

* **`wilsonLine_congr`** — Proves that two gauge configurations that agree on all edges of a path produce the same Wilson line.
* **`UbarDeviation_congr`** — Proves that the deviation term `UbarDeviation` is local, depending only on the coarse edge value and the fine gauge configuration on the adjacent paths.
* **`Ubar_locality`** — Proves that `Ū` at a coarse edge $C$ depends only on the fine configuration on the paths within the blocks adjacent to the endpoints of $C$, and the coarse configuration at $C$.

**How compilation was resolved.**
We resolved a type mismatch in `wilsonLine_congr` by passing the prepended edge explicitly as `e` to `List.mem_cons_of_mem e he'` instead of omitting it. We resolved a let-binder definition mismatch in rewriting the sum inside `Ubar_locality` by defining the sum-equivalence lemma `h_sum` directly in terms of `blockOf L N' (FiniteLatticeGeometry.src C)` and applying `dsimp [Ubar]` prior to rewriting, which substituted local let bindings and allowed the rewrite to match exactly.

**Honest scope.** This completes the locality proof for the coarse averaging operator on the lattice. It does not prove the analytical Gaussian bounds on the activities or the continuum limit. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 104 (2026-06-19, **UV scale dictionary and concrete covUV target**
`YangMills.RG.scaleSpacing`, `YangMills.RG.covUV_concrete`, `YangMills.RG.covUV_polymer`, `YangMills.RG.covUV_polymer_eq`, `YangMills.RG.hUV_of_per_scale`, `YangMills.RG.lattice_mass_gap_of_cluster_and_coupling`, `YangMills.RG.lattice_mass_gap_of_cluster_and_logistic_coupling`, `YangMills.RG.lattice_mass_gap_uv_conditional_nonvacuous`, `YangMills.RG.lattice_mass_gap_of_per_scale_uv_summable`, and `YangMills.RG.lattice_mass_gap_of_cluster_and_marginal_coupling`; core 8269)

**Build:** green (the U0/U3 targets and mass gap refactoring added to `UVMassGap.lean` and `MarginalUVMassGap.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the concrete representation of the ultraviolet covariance `covUV` and the scale-to-spacing dictionary, refactoring the mass gap conditionals to discharge the carried abstract covariance parameter:

* **`scaleSpacing`** — Defines the scale-to-spacing dictionary $a_k = a_* / L^{k_* - k}$.
* **`covUV_concrete`** — Defines the UV covariance as the concrete finite sum of scale remainders $\sum_{k < n(t)} R_{t,k}$.
* **`covUV_polymer`** — Defines the UV covariance in terms of underlying polymer activities.
* **`covUV_polymer_eq`** — Proves the equivalence of the polymer and remainder representation of the UV covariance.
* **`hUV_of_per_scale`** — Collapses the per-scale remainder geometric decay to the covariance-level UV decay.
* **Refactored mass gap theorems** — Refactors `lattice_mass_gap_of_cluster_and_coupling`, `lattice_mass_gap_of_cluster_and_logistic_coupling`, `lattice_mass_gap_uv_conditional_nonvacuous`, `lattice_mass_gap_of_per_scale_uv_summable`, and `lattice_mass_gap_of_cluster_and_marginal_coupling` to use `covUV_concrete` directly, eliminating the carried `covUV` parameter and `hcovUV` hypothesis.

**How compilation was resolved.**
We added the `noncomputable` keyword to `scaleSpacing`, `covUV_concrete`, and `covUV_polymer` to resolve Lean compiler errors regarding noncomputable division (`ℝ`) and `tsum`. We removed the unused `hc0` parameter from `hUV_of_per_scale` to clean up linter warnings, and eliminated `nsc` from the existential list in `lattice_mass_gap_uv_conditional_nonvacuous` to match the discharged `hcovUV` hypothesis. We added the missing `import YangMills.RG.UVMassGap` to `MarginalUVMassGap.lean` to make `covUV_concrete` visible.

**Honest scope.** This completes the UV scale dictionary and concrete target formulation (Target U0/U3). It does not prove the analytical Gaussian bounds on the activities or the continuum limit. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 105 (2026-06-19, **sharp second moment of the fundamental character**
`YangMills.ClayCore.signedSwapMat`, `YangMills.ClayCore.signedSwapSU`, `YangMills.ClayCore.instIsHaarMeasureSUN`, `YangMills.ClayCore.instIsMulRightInvariantSUN`, `YangMills.ClayCore.sunHaarProb_entry_normSq_eq`, `YangMills.ClayCore.sunHaarProb_entry_normSq_eq_inv_Nc`, and `YangMills.ClayCore.sunHaarProb_trace_normSq_integral_eq_one`; core 8270)

**Build:** green (the F1 target added to `SchurNormOne.lean`).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum formalises the sharp second moment of the fundamental character trace norm-squared:
\[ \int_{\text{SU}(N_c)} \|\text{tr } U\|^2 d\text{Haar} = 1 \]
for $N_c \ge 2$, closing the target F1 from the Schur-orthogonality program:

* **`signedSwapMat` & `signedSwapSU`** — Defines the signed swap matrix and shows it is a member of the special unitary group $\text{SU}(N)$.
* **Haar uniqueness on compact non-commutative groups** — Instantiates the compact Haar probability measure `sunHaarProb` and registers `IsHaarMeasure` and `IsMulRightInvariant` instances, bypassing the lack of generic Mathlib instances.
* **`sunHaarProb_entry_normSq_eq`** — Proves column-level entry norm-squared integral equality $\int |U_{mi}|^2 d\text{Haar} = \int |U_{mj}|^2 d\text{Haar}$ for any $i \neq j$ via right invariance under `signedSwapSU`.
* **`sunHaarProb_entry_normSq_eq_inv_Nc`** — Shows that each entry has integral $1/N_c$.
* **`sunHaarProb_trace_normSq_integral_eq_one`** — Proves the final Target F1 of the fundamental character trace norm-squared.

**How compilation was resolved.**
We solved compilation issues by ensuring all inequality symmetry relations (e.g., passing `hij.symm`, `Ne.symm hbi`, `Ne.symm hbj`, `Ne.symm hab`) were provided to `simp` to discharge sub-goals in matrix entry evaluations. We simplified the disjointness proof in `prod_decomp_two` to a direct contradiction, avoiding Let-binder and case-split variable renaming clashes. We removed duplicate and unused variables (`[NeZero N]` and `hN`) from the signatures of `sunHaarProb_entry_normSq_eq` and `sunHaarProb_trace_normSq_integral_eq_one` to address linter warnings.

**Honest scope.** This completes the sharp second moment of the fundamental character (Target F1). It does not prove the mass gap of the 4D Yang-Mills theory in the continuum limit. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 106 (2026-06-19, **exact Schur orthogonality for the fundamental SU(N) representation**
`YangMills.ClayCore.sunHaarProb_fundamental_entry_orthogonality` and
`YangMills.ClayCore.inner_fundamentalMatrixCoeffL2`; core 8271)

**Build:** green (`SchurFundamentalOrthogonality.lean` added to the verified core).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum closes the defining-representation case of the matrix-coefficient
Haar `L²` API:

* **`sunHaarProb_entry_offdiag_right`** — distinct columns are orthogonal, by
  right Haar invariance under a traceless diagonal phase. Together with the
  existing row-off-diagonal theorem, this covers every unequal coefficient.
* **`sunHaarProb_entry_normSq_integral_eq_inv_N`** — each fundamental matrix
  coefficient has squared Haar norm `1 / N`.
* **`sunHaarProb_fundamental_entry_orthogonality`** — the full four-index
  identity
  `∫ Uᵢⱼ conj(Uₖₗ) dHaar = if i = k ∧ j = l then 1 / N else 0`.
* **`fundamentalMatrixCoeffL2`** and
  **`inner_fundamentalMatrixCoeffL2`** — package the coefficients as vectors in
  Haar `L²` and restate the same identity as their Hilbert-space inner product.
* **`orthonormal_normalizedFundamentalMatrixCoeffL2`** — after multiplication
  by `√N`, the `Fin N × Fin N` coefficient family is an `Orthonormal ℂ` family
  in Haar `L²`, the interface consumed by the orthonormal half of Peter-Weyl.

**Honest scope.** This is Schur orthogonality for the defining representation
only. It does not prove generic compact-group Peter-Weyl, classify irreducible
SU(N) representations, construct the continuum limit, or prove the Clay mass
gap. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 107 (2026-06-19, **generic continuous-unitary matrix representation API**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep` and
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.character_conj`; core 8272)

**Build:** green (`ContinuousUnitaryRep.lean` added to the verified core).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum adds the reusable analytic half of the F2 representation API:

* **`ContinuousUnitaryMatrixRep G ι`** — a continuous monoid homomorphism from
  a topological group into Mathlib's `Matrix.unitaryGroup ι ℂ`.
* **`matrixCoeff` / `matrixCoeffL2`** — every coefficient is a continuous
  function and, on a compact domain with a finite Borel measure, has a
  canonical vector in `L²`.
* **`character` / `characterL2`** — the trace character has the same
  continuous and `L²` interfaces.
* **`character_conj`** — characters are invariant under group conjugation,
  proved using the unitary inclusion into matrix units and cyclicity of trace.
* **`fundamentalUnitaryRep`** — the defining representation of `SU(N)`
  instantiates the generic API, and its generic coefficients reduce
  definitionally to the entry functions used in Addendum 106.

**Honest scope.** This does not bundle basis-free representations, prove
irreducibility, compare inequivalent representations, or establish
Peter-Weyl density. It is infrastructure directly consumed by those future
statements. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 108 (2026-06-19, **continuous-unitary representations bridged to
Mathlib's algebraic Schur theory**; core 8272)

**Build:** green. Oracle: `[propext, Classical.choice, Quot.sound]`.

`ContinuousUnitaryMatrixRep.toRepresentation` turns the unitary matrix action
into Mathlib's algebraic `Representation ℂ G (ι → ℂ)`, with the action
computing definitionally as matrix-vector multiplication. This makes the
existing representation-theory library directly consumable:

* `intertwiner_bijective_or_eq_zero` states that an intertwiner between
  irreducible continuous unitary matrix representations is either bijective
  or zero.
* `exists_eq_smul_one_of_self_intertwiner` is the scalar form of Schur's
  lemma: every self-intertwiner of an irreducible finite-dimensional complex
  representation is a scalar multiple of the identity.

These are algebraic Schur conclusions, not generic Haar orthogonality. No
irreducibility classification, inter-representation integral formula, or
Peter-Weyl density theorem is claimed. Clay distance **~0% (<0.1%),
unchanged**.


## Addendum 110 (2026-06-19, **Extra High audit correction of the lattice `Ū` logarithm**
`YangMills.RG.UbarDeviationLogArg`, `YangMills.RG.UbarDeviationLogArg_gaugeAct`,
repaired `YangMills.RG.Ubar` / `YangMills.RG.Ubar_gaugeAct` /
`YangMills.RG.Ubar_locality`, `YangMills.RG.clusterUnion_connected`, and the
current `YangMills.ClayCore.GenericSchurOrthogonality` scalar self-average)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

The Extra High audit found a semantic error in Addenda 102–103: `nearLog Y` is the
Mercator series for `log(1 + Y)`, but the lattice `Ū` definition fed it the represented
deviation group element `D` itself.  CMP 109 (0.12) applies `log` to the near-identity
deviation group element
`U(c₋,x)·U(x,x(c))⁻¹·U(x(c),c₊)·U(-c)`.  Therefore the Lean Mercator argument must be
`D - 1`.

Repair:

* `UbarDeviationLogArg` now packages the faithful logarithm variable
  `(MatrixRealization.rep (UbarDeviation ...)).val - 1`.
* `Ubar` averages `nearLog (UbarDeviationLogArg ...)`; the covariance hypothesis is now
  `‖UbarDeviationLogArg ...‖ < 1`, not `‖rep(D).val‖ < 1`.
* `units_conj_sub_one` and `UbarDeviationLogArg_gaugeAct` prove the required subtraction
  covariance
  `u·D·u⁻¹ - 1 = u·(D - 1)·u⁻¹`, so `nearLog_conj` applies to the faithful variable.
* `represented_group_element_norm_lt_one_impossible_of_norm_eq_one` records the physical
  calibration: in a unitary realization where `‖D‖ = 1`, the old strict premise
  `‖D‖ < 1` is impossible.
* `UbarDeviationLogArg_small_of_deviation_eq_one` records non-vacuity of the corrected
  small-field premise at exact identity deviation.

The audit also checked the latest
`sunHaarProb_trace_normSq_integral_eq_one` and the concrete/marginal UV assembly for
scope overclaim: the Haar theorem is an exact SU(N) Haar character-norm statement, while
the UV mass-gap assembly continues to carry the analytic RG activity and IR inputs as
explicit hypotheses.  No repair was needed there.

The second Extra High escalation, `clusterModifiedMetric`, was also audited against the
Dimock source notes.  The definition as `discreteModifiedMetric` of the cluster union is
the source-shaped `d_M(Y, mod Ωᶜ)` for the cluster object.  However, the requested
arbitrary constituent comparison is not a formal monotonicity fact and should not be
claimed: the metric is a constrained Steiner minimum, so enlarging the ambient finset can
add shortcuts.  The code already proved only the valid `Fin 1` comparison; this audit
repairs the documentation and the Phase 8 ledger wording so downstream work cannot treat
that base case as a general theorem.

As the next source-grounded RG-activity substrate step, the audit adds
`clusterUnion_connected`: a genuine hole-polymer cluster has connected raw union because
the incompatibility graph chains constituent polymers by overlap or one-step cube
adjacency.  This supports the `d_M`-of-union design without asserting the false
constituent-metric monotonicity.

During full-core verification, the tracked `GenericSchurOrthogonality.lean` changes failed
on a fragile probability-Haar constant-integral rewrite and on the final diagonal
coefficient simplification.  This checkpoint repairs those proofs and verifies
`trace_haarAverageMatrix`, `haarAverageMatrix_eq_trace_div_card_smul_one`, and
`integral_matrixCoeff_mul_star`: for an irreducible finite-dimensional continuous unitary
representation, the self matrix-coefficient integral is
`δᵢₖ δⱼₗ / Fintype.card ι`.  This closes the scalar half that the previous generic-Haar
entry had left open; Peter-Weyl density remains open.

**Honest scope.** This fixes a real source-faithfulness bug in the `Ū` layer and prevents
downstream work from relying on the physically impossible old `‖D‖ < 1` premise.  It does
not prove the Balaban/Dimock activity estimate, the continuum limit, or OS/Wightman
reconstruction. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 111 (2026-06-19, **cluster-level modified-metric skeleton control**
`YangMills.RG.clusterUnion_skeleton_card_le_clusterModifiedMetric_add_one`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum closes the immediate post-audit cluster-metric interface.  The
Extra High audit rejected the tempting but false arbitrary comparison
`discreteModifiedMetric H (X i).val ≤ clusterModifiedMetric H z X`: the modified
metric is a constrained Steiner minimum, so enlarging the ambient set can create
shortcuts and is not monotone in that direction.  The source-faithful object is
instead the whole cluster union.

The new theorem states exactly that valid cluster-level fact:
`clusterUnion_skeleton_card_le_clusterModifiedMetric_add_one` proves that if
`X` is a genuine `IsCluster` tuple in the hole-polymer system, then

`(skeleton H (clusterUnion H z X)).card ≤ clusterModifiedMetric H z X + 1`.

The proof is intentionally short: `clusterUnion_connected` supplies connectedness
of the raw cluster union, and the already-proved
`skeleton_card_le_discreteModifiedMetric_add_one` applies to that union.  This
is the interface the later activity-decay proof can consume: metric decay of the
cluster object controls the size of its active skeleton, without asserting any
unsupported constituent-polymer monotonicity.

**Honest scope.** This is an RG-substrate theorem toward the Balaban/Dimock
`hRpoly` activity estimate.  It does not prove the activity decay, the continuum
limit, or OS/Wightman reconstruction. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 112 (2026-06-19, **cluster unions packaged as hole polymers**
`YangMills.RG.polymerWithHoles_biUnion`, `YangMills.RG.clusterUnion_polymerWithHoles`,
`YangMills.RG.clusterUnion_nonempty`, `YangMills.RG.clusterUnionPolymer`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum packages the source-shaped cluster object as an actual polymer of
the holes-respected polymer system whenever the cluster tuple is nonempty.

* `polymerWithHoles_biUnion` proves that a finite union of hole-respecting sets
  is hole-respecting: if a hole is contained in one summand, it is contained in
  the union; otherwise it is disjoint from every summand and hence from the
  union.
* `clusterUnion_polymerWithHoles` specializes that statement to the raw union of
  a tuple of hole polymers.
* `clusterUnion_nonempty` records that a `Fin (n+1)` tuple of nonempty polymers
  has nonempty raw union.
* `clusterUnionPolymer` combines nonemptiness, `clusterUnion_connected`, and
  `clusterUnion_polymerWithHoles` into a single subtype package:
  the raw union of a nonempty genuine cluster is itself a valid
  `(holePolymerSystem H z).Polymer`.

Together with Addendum 111, this gives downstream `hRpoly` work a clean object:
the cluster can be collapsed to its union polymer, and the modified metric of
that union controls its active skeleton.  No unsupported constituent-polymer
metric monotonicity is used.

**Honest scope.** This is still RG substrate for the Balaban/Dimock activity
estimate.  It does not prove the activity decay, continuum limit, or
OS/Wightman reconstruction. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 113 (2026-06-19, **skeleton-pinned cluster remainder summability**
`YangMills.RG.clusterSkeletonRemainderSumTerm`,
`YangMills.RG.clusterSkeletonRemainderSumTerm_le`,
`YangMills.RG.clusterSkeletonRemainderSum_summable`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum adds the source-shaped cluster remainder variant pinned at the
active skeleton of the cluster union, rather than merely at any point of the raw
cluster union.

* `clusterSkeletonRemainderSumTerm` is the skeleton-pinned analogue of
  `clusterRemainderSumTerm`: the filter is
  `IsCluster P X ∧ r ∈ skeleton H (clusterUnion H z X)`.
* `clusterSkeletonRemainderSumTerm_le` proves termwise domination by the
  existing raw-union-pinned term.  The proof uses only the defining inclusion
  `skeleton_subset H (clusterUnion H z X)` and nonnegativity of the Ursell/activity
  norm factor.
* `clusterSkeletonRemainderSum_summable` transfers the existing summability
  theorem to the skeleton-pinned series by `Summable.of_nonneg_of_le`.

This is the correct support shape for the later activity-decay theorem: Dimock's
modified metric weights the active skeleton of the cluster object.  No new
activity estimate, paper constant, or constituent-polymer metric monotonicity is
claimed.

**Honest scope.** This is RG summability substrate toward `hRpoly`; the
Balaban/Dimock activity-decay estimate itself remains open.  It does not prove
the continuum limit or OS/Wightman reconstruction. Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 114 (2026-06-19, **skeleton-pinned terms bounded by pinned cluster weights**
`YangMills.RG.clusterSkeletonRemainderSum_term_le_pinned`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum exposes the termwise bound that Addendum 113 implicitly uses:

`clusterSkeletonRemainderSumTerm H z r n ≤ (n+1) · Σ_{c∋r} pinnedClusterWeight (holePolymerSystem H z) c n`.

The proof is a clean two-lemma chain: skeleton-pinned terms are dominated by
raw-union-pinned terms (`clusterSkeletonRemainderSumTerm_le`), and raw-union
terms are bounded by the already-proved pinned-cluster-weight estimate
(`clusterRemainderSum_term_le`).  This gives future `hRpoly` work a single named
inequality from the source-shaped skeleton support condition to the banked KP
pinned-weight machinery.

**Honest scope.** This is still summability/weight substrate only.  The
Balaban/Dimock activity-decay estimate remains open; no continuum limit or
OS/Wightman reconstruction is claimed. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 115 (2026-06-19, **skeleton-pinned cluster remainder sum bound**
`YangMills.RG.clusterSkeletonRemainderSum_term_le_skeletonPinned`,
`YangMills.RG.clusterSkeletonRemainderSum_term_le_tilt`, and
`YangMills.RG.clusterSkeletonRemainderSum_tsum_le`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum turns the termwise skeleton-pinned bridge into the quantitative
total-series estimate consumed by the next `hRpoly` interface:

* `clusterSkeletonRemainderSum_term_le_skeletonPinned` sharpens the root
  symmetrization: from `r ∈ skeleton H (clusterUnion H z X)`, it pins at a
  constituent polymer whose own active skeleton contains `r`.
* `clusterSkeletonRemainderSum_term_le_tilt` pays the order factor `(n+1)` by
  the standard `scaleActivity (exp t)` tilt, producing a bound by the tilted
  pinned-cluster weights under an explicit `0 < t`.
* `clusterSkeletonRemainderSum_tsum_le` sums over all orders and applies
  `pinned_cluster_summable_sharp` under the explicit tilted KP criterion,
  bounding the skeleton-pinned remainder series by
  `t⁻¹ * Σ_{r∈skeleton(c)} exp(t) * ‖activity c‖ * exp(|c|)`.

This is the source-shaped skeleton analogue of the KP restriction/off-region
tail estimate: the final pinned sum is still keyed by active-skeleton
membership, not merely raw support membership.

**Honest scope.** The theorem still assumes the tilted KP criterion and does
not prove the concrete Yang-Mills activity decay.  The remaining hard input is
the Balaban/Dimock fluctuation-integral estimate for the actual gauge RG
operator.  No continuum limit or OS/Wightman reconstruction is claimed. Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 116 (2026-06-19, **metric activity decay consumed by skeleton remainders**
`YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum closes the next connector after Addendum 115.  The theorem
`clusterSkeletonRemainderSum_tsum_le_metric_bound` proves:

if the tilted, cardinality-weighted hole-polymer activity satisfies the
Dimock-shaped bound

`exp(t) * ‖activity(c)‖ * exp(|c|) ≤ A * q^(discreteModifiedMetric(c)+1)`,

then the total skeleton-pinned cluster remainder is bounded by

`t⁻¹ * A * (1 - (3^d)^2 * (q * 2^(3^d+1)))⁻¹`,

under the already-formalized hole-disjointness / no-cross-edge / nonempty-hole
conditions and the smallness condition on `q`.

The proof composes the skeleton-rooted pinned cluster estimate
(`clusterSkeletonRemainderSum_tsum_le`) with the discrete modified-metric
summability theorem (`discreteModifiedMetric_weight_summable`).  The only
bookkeeping is the subtype/equivalence bridge from
`{c : PolymerType H z // r ∈ skeleton H c.val}` to raw connected
hole-respecting finsets.

**Honest scope.** This proves the exact consumer side of the Balaban-Dimock
activity-decay input.  It still does not prove that activity estimate for the
actual Yang-Mills RG operator; that remains the `hRpoly`/P3-P4 analytic core.
No continuum limit or OS/Wightman reconstruction is claimed. Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 117 (2026-06-19, **tilted local KP criterion and one-shot skeleton metric bound**
`YangMills.RG.holePolymerSystem_KPCriterion_volumeUniform_scaled`,
`YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound_of_local`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum removes a technical carried hypothesis from Addendum 116's
consumer theorem.  The new theorem
`holePolymerSystem_KPCriterion_volumeUniform_scaled` proves the
volume-uniform Kotecký-Preiss criterion for the scalar-tilted hole polymer
system directly from the local tilted activity-sum smallness condition:

`Σ_{Y∋s} ‖ρ · z(Y)‖ · exp(|Y|) ≤ (3^d+1)⁻¹`.

The proof is the same local-neighbourhood argument as the unscaled
`holePolymerSystem_KPCriterion_volumeUniform`: incompatibilities are covered by
the closed neighbourhood, whose cardinality is bounded by `(3^d+1)|X|`.

The follow-up theorem
`clusterSkeletonRemainderSum_tsum_le_metric_bound_of_local` then combines:

* the scaled local KP criterion at `ρ = exp(t)`;
* the skeleton-rooted cluster remainder estimate;
* the modified-metric activity-decay hypothesis;
* the discrete modified-metric summability theorem.

It yields the same volume-uniform skeleton remainder bound as Addendum 116 but
with the KP criterion derived internally from the local summability window.

**Honest scope.** The theorem still assumes the local activity-sum smallness
and the modified-metric activity-decay estimate.  Those are exactly the
Balaban/Dimock `hRpoly`/P3-P4 analytic inputs; they are not proved here.  No
continuum limit or OS/Wightman reconstruction is claimed. Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 118 (2026-06-19, **scaled local KP convergence API**
`YangMills.RG.holePolymerSystem_converges_volumeUniform_scaled`,
`YangMills.RG.holePolymerSystem_norm_clusterSum_le_volumeUniform_scaled`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum rounds off the API opened in Addendum 117.  The scaled local KP
criterion now feeds the same two sharp KP interfaces already available in the
unscaled local theory:

* `holePolymerSystem_converges_volumeUniform_scaled` — absolute convergence of
  the scalar-tilted hole-polymer cluster series;
* `holePolymerSystem_norm_clusterSum_le_volumeUniform_scaled` — the matching
  volume-uniform norm bound for the tilted cluster sum.

Both theorems are direct applications of `KP.kp_convergence_sharp` and
`KP.kp_norm_clusterSum_le_sharp` to the scalar-tilted polymer system, with
`holePolymerSystem_KPCriterion_volumeUniform_scaled` supplying the criterion.

**Honest scope.** These are consumer/API theorems for a scalar activity tilt.
They do not prove the Yang-Mills activity-decay estimate, the cluster expansion
with holes, the continuum limit, or OS/Wightman reconstruction. Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 119 (2026-06-19, **local skeleton-tail interfaces**
`YangMills.RG.clusterSkeletonRemainderSum_summable_of_local`,
`YangMills.RG.clusterSkeletonRemainderSum_tsum_le_of_local`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum removes the explicit tilted KP hypothesis from the two lower
skeleton-tail interfaces:

* `clusterSkeletonRemainderSum_summable_of_local` proves summability of the
  skeleton-pinned cluster remainder series from the local tilted
  activity-sum window;
* `clusterSkeletonRemainderSum_tsum_le_of_local` proves the pre-metric
  quantitative skeleton-pinned bound from the same local window.

Both theorems derive the scalar-tilted KP criterion through
`holePolymerSystem_KPCriterion_volumeUniform_scaled`, exactly as the later
metric-bound theorem does.  The skeleton-tail ladder is now uniformly
source-shaped: local tilted smallness feeds summability, the pinned KP bound,
and the modified-metric consumer theorem without carrying a separate
`KPCriterion` hypothesis at each layer.

**Honest scope.** These are still consumer theorems.  They do not bridge
raw-support local smallness from skeleton-rooted modified-metric summability,
and they do not prove the Balaban/Dimock Yang-Mills activity-decay estimate.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 120 (2026-06-19, **explicit exponential-tilt local KP bridge**
`YangMills.RG.holePolymerSystem_KPCriterion_volumeUniform_exp`,
`YangMills.RG.holePolymerSystem_converges_volumeUniform_exp`,
`YangMills.RG.holePolymerSystem_norm_clusterSum_le_volumeUniform_exp`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum names the exact `ρ = exp(t)` specialization repeatedly consumed
by the RG tail estimates.  The local smallness window is source-shaped as

`Σ_{Y∋s} exp(t) * ‖z(Y)‖ * exp(|Y|) ≤ (3^d+1)⁻¹`,

while the polymer system is the scalar-tilted system
`(holePolymerSystem H z).scaleActivity (Real.exp t)`.  The bridge theorem
`holePolymerSystem_KPCriterion_volumeUniform_exp` converts between these two
presentations once, using positivity of `exp(t)`.  The companion convergence
and norm-bound theorems expose the same specialization at the cluster-series
API level.

The skeleton-tail `_of_local` theorems now call this named bridge instead of
rebuilding the scalar-norm conversion internally.

**Honest scope.** This is an API consolidation for the already-carried local
activity window.  It does not prove local smallness, the Yang-Mills
activity-decay estimate, or any continuum/OS result. Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 121 (2026-06-19, **raw cluster-tail local interface**
`YangMills.RG.clusterRemainderSum_summable_of_local`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum adds the raw-union-pinned companion to the skeleton local-tail
interfaces.  `clusterRemainderSum_summable_of_local` proves summability of the
raw cluster remainder series from the source-shaped tilted local window

`Σ_{Y∋s} exp(t) * ‖z(Y)‖ * exp(|Y|) ≤ (3^d+1)⁻¹`,

deriving the scalar-tilted KP criterion through
`holePolymerSystem_KPCriterion_volumeUniform_exp` rather than carrying an
abstract `KPCriterion` hypothesis.  This keeps the lower tail layer aligned
with the later skeleton-pinned `_of_local` API.

**Honest scope.** This is still a consumer theorem for an explicit local
smallness hypothesis.  It does not prove that local smallness from the
modified-metric activity decay, nor the Balaban/Dimock cluster expansion with
holes. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 122 (2026-06-19, **raw cluster-tail quantitative local bound**
`YangMills.RG.clusterRemainderSum_tsum_le`,
`YangMills.RG.clusterRemainderSum_tsum_le_of_local`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum completes the raw-union-pinned lower tail API.  The theorem
`clusterRemainderSum_tsum_le` bounds the full raw-pinned cluster remainder
series by the pinned KP one-polymer sum after the `exp(t)` tilt pays the order
factor:

`Σ'_n R_raw(r,n) ≤ t⁻¹ Σ_{c∋r} exp(t) * ‖z(c)‖ * exp(|c|)`.

The wrapper `clusterRemainderSum_tsum_le_of_local` derives the required
tilted KP criterion from the source-shaped local smallness window via
`holePolymerSystem_KPCriterion_volumeUniform_exp`.  Together with Addendum
121, the raw tail layer now has both summability and a quantitative local
consumer theorem, matching the shape already available for the skeleton layer.

**Honest scope.** This theorem consumes raw-support local smallness; it does
not derive that smallness from skeleton-rooted modified-metric estimates.  The
Balaban/Dimock activity-decay theorem and the cluster expansion with holes
remain the open analytic inputs. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 123 (2026-06-19, **pinned-weight tilt lemma**
`YangMills.KP.orderFactor_pinnedClusterWeight_le_tilt`,
`YangMills.RG.clusterRemainderSum_term_le_tilt`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum extracts the order-factor tilt algebra as a reusable pinned
cluster-weight lemma.  `orderFactor_pinnedClusterWeight_le_tilt` proves at the
KP layer that `(n+1) * pinnedClusterWeight P c n` is dominated by the
`exp(t)`-tilted pinned weight with a global `t⁻¹` loss, using
`t(n+1) ≤ exp(t(n+1))` and `pinnedClusterWeight_scale`.
`clusterRemainderSum_term_le_tilt` is now the raw-tail specialization, and
the skeleton termwise tilt theorem also consumes the same KP lemma.

**Honest scope.** This is proof infrastructure for the raw tail API.  It does
not add a new physical estimate and does not bridge the unresolved
raw-support/skeleton-rooted local-smallness issue. Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 124 (2026-06-19, **finite-pin pinned-weight exchange**
`YangMills.KP.scaleActivity_exp_norm_activity_mul_exp`,
`YangMills.KP.summable_finset_pinnedClusterWeight`,
`YangMills.KP.tsum_finset_pinnedClusterWeight_le`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum names the scalar-norm and finite-pin `tsum` bookkeeping
repeatedly used by off-region and RG cluster-tail estimates.
`scaleActivity_exp_norm_activity_mul_exp` identifies the weighted norm of the
`exp(t)`-tilted activity with `exp(t) * ‖z(c)‖ * exp(a(c))`.  Under a sharp KP criterion,
`summable_finset_pinnedClusterWeight` proves summability of
`n ↦ Σ_{c∈s} pinnedClusterWeight P c n`, and
`tsum_finset_pinnedClusterWeight_le` proves

`Σ'_n Σ_{c∈s} pinnedClusterWeight P c n ≤ Σ_{c∈s} ‖z(c)‖ e^{a(c)}`.

The proof is the finite exchange `Summable.tsum_finsetSum` followed by the
per-polymer sharp pinned theorem.  The existing off-region, raw-tail, and
skeleton-tail bounds now consume this KP-level helper instead of rebuilding
the exchange locally.

**Honest scope.** This is proof factoring inside the verified KP/RG
summability substrate.  It does not strengthen the physical hypotheses and
does not address the open Balaban/Dimock activity-decay or
raw-support/skeleton-rooted local-smallness bridge. Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 125 (2026-06-19, **generic irreducible character orthogonality**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.integral_character_mul_star_eq_zero_of_not_equiv`
and `YangMills.ClayCore.ContinuousUnitaryMatrixRep.integral_character_mul_star`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum packages the character-level corollaries of the generic
matrix-coefficient Schur orthogonality API.

* `integral_character_mul_star_eq_zero_of_not_equiv` proves that characters of
  inequivalent irreducible continuous unitary matrix representations are
  orthogonal in Haar `L²`.
* `integral_character_mul_star` proves that an irreducible character has Haar
  `L²` norm one.

Both proofs expand characters as finite traces, exchange the finite sums with
the integral, and consume the already-verified coefficient identities
`integral_matrixCoeff_mul_star_eq_zero_of_not_equiv` and
`integral_matrixCoeff_mul_star`.

**Honest scope.** This is the character-level Schur orthogonality corollary for
the repo's matrix-realized irreducible API.  It does not prove Peter-Weyl
completeness, classify SU(N) irreducibles, construct a continuum limit, or
discharge the open `hRpoly` activity-decay estimate. Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 126 (2026-06-19, **character orthogonality in Haar L2**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2_eq_zero_of_not_equiv`
and `YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2`,
plus `YangMills.ClayCore.ContinuousUnitaryMatrixRep.orthonormal_characterL2`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum packages the generic irreducible character orthogonality from
Addendum 125 in Mathlib's Hilbert-space `L²` interface.  The theorem
`inner_characterL2_eq_zero_of_not_equiv` says that the `characterL2` vectors of
inequivalent irreducible continuous unitary matrix representations are
orthogonal, and `inner_characterL2` says that an irreducible character has unit
inner product with itself.  Both wrappers are direct applications of
`ContinuousMap.inner_toLp` followed by the integral character identities.
The theorem `orthonormal_characterL2` then packages any finite family of
pairwise inequivalent irreducible characters as an `Orthonormal` family.

**Honest scope.** This is API packaging for the F2/Peter-Weyl substrate.  It
does not add Peter-Weyl completeness, SU(N) representation classification,
continuum construction, or the open `hRpoly` activity-decay estimate. Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 127 (2026-06-19, **raw-local metric majorant for skeleton tails**
`YangMills.RG.clusterSkeletonRemainderSum_tsum_le_metric_bound_of_raw_local_metric`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum adds the source-facing consumer for the current `hRpoly`
frontier.  If a source proves the pointwise activity decay

`exp(t) * ‖z(c)‖ * exp(|c|) ≤ A * q^(d_M(c)+1)`

and also proves the **raw-support** local smallness of that same majorant,

`Σ_{Y∋s} A * q^(d_M(Y)+1) ≤ (3^d+1)^(-1)`,

then
`clusterSkeletonRemainderSum_tsum_le_metric_bound_of_raw_local_metric`
derives the local KP window and applies the existing skeleton metric
consumer, yielding the usual
`t^(-1) * A * (1 - (3^d)^2 * (q * 2^(3^d+1)))^(-1)` bound.

**Honest scope.** This deliberately does **not** derive raw-support local
smallness from skeleton-rooted modified-metric summability.  That bridge
remains blocked pending a Yang-Mills source giving raw-support activity
control, hole-interior suppression, or a polymer-class restriction.  The
theorem is a verified consumer for such a source input, not a proof of the
Yang-Mills activity estimate. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 128 (2026-06-19, **finite character linear independence**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.linearIndependent_characterL2`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum extracts the classical finite-family consequence of Addendum 126:
pairwise inequivalent irreducible continuous unitary matrix characters are
linearly independent in Haar `L²`.  The proof uses the Hilbert-space route:
`orthonormal_characterL2` followed by Mathlib's
`Orthonormal.linearIndependent`.

**Honest scope.** This is still finite-family F2/Peter-Weyl substrate.  It does
not prove Peter-Weyl completeness, classify SU(N) irreducibles, construct a
continuum theory, or discharge the open `hRpoly` activity-decay estimate. Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 129 (2026-06-19, **finite character coefficient extraction**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2_sum`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum adds the finite Fourier-coefficient identity for the generic
character substrate.  For a finite pairwise-inequivalent family of irreducible
continuous unitary matrix representations, the coefficient `c a` in
`Σ b, c b • characterL2(ρ b)` is recovered as the Haar `L²` inner product with
`characterL2(ρ a)`.  The proof is the existing finite orthonormal family theorem
followed by Mathlib's `Orthonormal.inner_right_sum`.

**Honest scope.** This is a finite-family coefficient API.  It does not prove
Peter-Weyl completeness, convergence of infinite character expansions,
SU(N) irreducible classification, continuum construction, or `hRpoly`. Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 130 (2026-06-19, **finite character expansion uniqueness**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.characterL2_sum_eq_sum_iff`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum packages the consumer form of the coefficient-extraction theorem:
inside a fixed finite pairwise-inequivalent family of irreducible continuous
unitary matrix representations, two finite Haar-`L²` character expansions are
equal if and only if their coefficient functions are equal.  The proof applies
`inner_characterL2_sum` to both sides after taking inner product with each
basis character.

**Honest scope.** This is finite-dimensional/finite-family uniqueness only.
It does not assert Peter-Weyl completeness, infinite expansion convergence,
SU(N) irreducible classification, continuum construction, or the open
`hRpoly` activity-decay estimate. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 131 (2026-06-19, **finite character zero-expansion criterion**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.characterL2_sum_eq_zero_iff`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum records the zero-expansion consumer of Addendum 130: in a fixed
finite pairwise-inequivalent family of irreducible continuous unitary matrix
characters, a finite Haar-`L²` character expansion is zero if and only if every
coefficient is zero.  The proof is the uniqueness theorem specialized to the
zero coefficient function.

**Honest scope.** This is still only a finite-family Hilbert-space fact.  It
does not assert Peter-Weyl completeness, infinite expansion convergence,
SU(N) irreducible classification, continuum construction, or the open
`hRpoly` activity-decay estimate. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 132 (2026-06-19, **finite character Gram formula**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.inner_characterL2_sum_sum`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum adds the finite Plancherel/Gram identity for the same substrate:
for two coefficient functions `c,d` on a fixed finite pairwise-inequivalent
irreducible character family,

`⟪Σ a, c a • χ_a, Σ a, d a • χ_a⟫ = Σ a, star (c a) * d a`.

The proof is Mathlib's `Orthonormal.inner_sum` applied to
`orthonormal_characterL2`.

**Honest scope.** This is a finite-family orthonormal-expansion identity only.
It does not assert Peter-Weyl completeness, infinite expansion convergence,
SU(N) irreducible classification, continuum construction, or the open
`hRpoly` activity-decay estimate. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 133 (2026-06-19, **finite character Parseval formula**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.norm_sq_characterL2_sum`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum records the norm-square consumer of Addendum 132.  For a finite
pairwise-inequivalent irreducible character family,

`‖Σ a, c a • χ_a‖² = Σ a, ‖c a‖²`.

The proof combines the finite Gram formula with
`InnerProductSpace.norm_sq_eq_re_inner` and the elementary complex identity
`star z * z = ‖z‖²`.

**Honest scope.** This is a finite Parseval identity for a fixed finite
orthonormal character family.  It does not assert Peter-Weyl completeness,
infinite expansion convergence, SU(N) irreducible classification, continuum
construction, or the open `hRpoly` activity-decay estimate. Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 134 (2026-06-19, **finite character expansion distance formula**
`YangMills.ClayCore.ContinuousUnitaryMatrixRep.norm_sq_characterL2_sum_sub_sum`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum adds the finite-distance consumer of the Parseval formula.  For
two coefficient functions `c,d` on a fixed finite pairwise-inequivalent
irreducible character family, the Haar-`L²` squared norm of the difference of
the two finite character expansions is exactly

`Σ a, ‖c a - d a‖²`.

The proof rewrites the difference of the two sums as the expansion with
coefficients `c-d`, then applies `norm_sq_characterL2_sum`.

**Honest scope.** This is still finite-family Hilbert-space geometry only.  It
does not assert Peter-Weyl completeness, infinite expansion convergence,
SU(N) irreducible classification, continuum construction, or the open
`hRpoly` activity-decay estimate. Clay distance **~0% (<0.1%), unchanged**.

## Addendum 135 (2026-06-19, **Appendix-F active compatibility interface**
`YangMills.RG.omegaHolePolymerSystem`,
`YangMills.RG.omegaHolePolymerSystem_incomp_iff`,
`YangMills.RG.omegaHolePolymerSystem_incomp_iff_exists`; core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum records a source-audit correction and the corresponding Lean
interface.  Direct extraction of Dimock II Appendix F (arXiv:1212.5562,
PDF pp. 91–92) shows that the with-holes cluster expansion uses
`Ω`-connectedness: two polymers are connected for the cluster relation when
`X₁ ∩ Ω` and `X₂ ∩ Ω` have nonempty intersection, equivalently
`X₁ ∩ X₂ ∩ Ω ≠ ∅`; `Ω`-disjoint need not be disjoint.  This is not the same
relation as the existing touching hard-core `holePolymerSystem`, whose
incompatibility is ordinary full-polymer overlap or one-step cube adjacency.

The new `omegaHolePolymerSystem` keeps the same connected,
hole-respecting finite cube sets, restricts to nonempty active skeletons, and
sets incompatibility to `¬ Disjoint (skeleton H X) (skeleton H Y)`.  The
elementwise theorem
`omegaHolePolymerSystem_incomp_iff_exists` packages the Appendix-F form:
incompatibility iff there exists an active cube contained in both skeletons.

**Honest scope.** This does not prove the cluster expansion with holes, the
Yang-Mills activity-decay estimate, or any continuum theorem.  It prevents a
semantic overclaim: future P3 work must either use the source-facing
`omegaHolePolymerSystem` or prove a comparison theorem before reusing the
already-verified touching-system local-KP consumers. Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 136 (2026-06-19, **Appendix-F active local KP consumer**
`YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum records the source-facing local KP package for the active
Appendix-F relation.  The key inclusion
`omega_filter_incomp_subset_skeleton` proves that every polymer incompatible
with `X` in `omegaHolePolymerSystem` is covered by a root in the active
skeleton of `X`.  Therefore a local window

`Σ_{Y : s ∈ skeleton(Y)} exp(t) · ‖z(Y)‖ · exp(|Y|) ≤ 1`

at every active cube `s` implies the Kotecký-Preiss criterion for
`(omegaHolePolymerSystem H z).scaleActivity (exp t)` with weight `|X|`.
The same package includes unscaled/scaled criteria and the corresponding
Mayer-series convergence and cluster-sum norm bounds.

**Honest scope.** This is the KP consumer for Dimock's literal
`Ω`-connected cluster relation, not the Yang-Mills single-scale activity
decay itself.  The hard analytic bound still has to supply the local active
window.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 137 (2026-06-19, **Appendix-F metric-to-active-KP bridge**
`YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum records the metric bridge for the source-facing active system.
If every active polymer satisfies the Dimock-shaped pointwise majorant

`exp(t) · ‖z(Y)‖ · exp(|Y|) ≤ A · q^(d_M(Y)+1)`

and the P2b discrete modified-metric summability constant obeys
`A · (1 - (3^d)^2 · (q · 2^(3^d+1)))⁻¹ ≤ 1`, then
`omegaHolePolymerSystem` satisfies the exponential-tilted KP criterion with
weight `|X|`.  The proof reindexes the active-skeleton local sum into the
already-proved modified-metric summability theorem; no Appendix-F activity
decay is assumed hiddenly beyond the explicit pointwise majorant.

**Honest scope.** This closes the consumer path
pointwise modified-metric decay + summability ⟹ active KP convergence for the
literal `Ω` relation.  It does not prove the Yang-Mills pointwise activity
decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 138 (2026-06-19, **Appendix-F metric-bound convergence wrappers**
`YangMills.RG.omegaHolePolymerSystem_converges_volumeUniform_skeleton_exp_of_metric_bound`,
`YangMills.RG.omegaHolePolymerSystem_norm_clusterSum_le_volumeUniform_skeleton_exp_of_metric_bound`;
core 8273)

**Build:** green (`lake build YangMillsCore`, 8273 jobs).
Oracle: `[propext, Classical.choice, Quot.sound]`.

This addendum packages Addendum 137 through the standard KP consumers.  Under
the same explicit pointwise modified-metric activity majorant and smallness
hypotheses, the exponential-tilted source-facing `Ω`-active Mayer series is
summable, and its cluster-sum norm is bounded by the usual KP activity norm
sum.  This gives the future activity-decay theorem a direct consumer theorem
instead of requiring it to separately invoke the KP criterion.

**Honest scope.** These are wrappers around the already-verified active KP
criterion and sharp KP convergence theorem.  The Yang-Mills pointwise activity
decay remains the open analytic input.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 139 (2026-06-19, **Appendix-F active cluster-tail consumer**
`YangMills.RG.omegaClusterSkeletonRemainderSumTerm`,
`YangMills.RG.omegaClusterSkeletonRemainderSum_term_le_skeletonPinned`,
`YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le`,
`YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le_metric_bound`;
core 8273)

**Build:** green (`lake env lean YangMills/RG/ClusterDecay.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum extends the source-facing `Ω`-active Appendix-F path from the
global KP criterion/cluster-sum consumer to the skeleton-pinned cluster-tail
consumer used by the RG remainder estimates.  The new term
`omegaClusterSkeletonRemainderSumTerm` sums genuine clusters of
`omegaHolePolymerSystem`, pinned when the root lies in the active skeleton of
the raw cluster union.  The symmetrization lemma
`omegaClusterSkeletonRemainderSum_term_le_skeletonPinned` shows that such a
cluster can be pinned at one constituent polymer whose own active skeleton
contains the root; the `exp(t)` tilt then pays the cluster order exactly as in
the older touching-system proof.  Consequently
`omegaClusterSkeletonRemainderSum_tsum_le_metric_bound` proves the active
cluster-tail estimate

`Σₙ omegaClusterSkeletonRemainderSumTerm ≤
 t⁻¹ · A · (1 - (3^d)^2 · (q · 2^(3^d+1)))⁻¹`

under the same pointwise modified-metric majorant
`exp(t) · ‖z(Y)‖ · exp(|Y|) ≤ A · q^(d_M(Y)+1)` and smallness hypotheses
used by Addenda 137–138.

**Honest scope.** This closes another consumer-side mismatch: future P3/P4
work can feed the literal `Ω`-connected Appendix-F relation all the way to a
skeleton-pinned remainder tail, without detouring through the older touching
hard-core system.  It still does not prove the Yang-Mills activity-decay
majorant, the continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 140 (2026-06-19, **Appendix-F active cluster-tail local-window consumers**
`YangMills.RG.omegaClusterSkeletonRemainderSum_summable_of_local`,
`YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le_of_local`; core 8273)

**Build:** green (`lake env lean YangMills/RG/ClusterDecay.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum adds the intermediate source-facing forms for the literal
`Ω`-active Appendix-F relation.  Addendum 139 consumed either a tilted KP
criterion directly or a pointwise modified-metric majorant.  The new theorems
consume the local active-skeleton window

`Σ_{Y : s ∈ skeleton(Y)} exp(t) · ‖z(Y)‖ · exp(|Y|) ≤ 1`

and derive, respectively, summability of the skeleton-pinned active cluster
tail and the quantitative bound by the root-pinned local activity mass.

**Why this matters.**  The Balaban/Yang-Mills source may present the remaining
activity control as a polymer norm or local KP window rather than as a literal
pointwise `A · q^(d_M+1)` estimate.  These theorems let future P3/P4 work feed
that local-window form directly, without inventing an unnecessary metric
majorant or detouring through the older touching hard-core system.

**Honest scope.** This is still a consumer-side theorem.  It does not prove the
Yang-Mills activity-decay estimate, the continuum limit, or OS/Wightman
reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 141 (2026-06-19, **Appendix-F active cluster-tail uniform local window**
`YangMills.RG.omegaClusterSkeletonRemainderSum_summable_of_uniform_local`,
`YangMills.RG.omegaClusterSkeletonRemainderSum_tsum_le_of_uniform_local`; core 8273)

**Build:** green (`lake env lean YangMills/RG/ClusterDecay.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum packages Addendum 140's local-window consumer in the form most
likely to be read directly from a source theorem: a uniform local
active-skeleton polymer norm bound

`Σ_{Y : s ∈ skeleton(Y)} exp(t) · ‖z(Y)‖ · exp(|Y|) ≤ B ≤ 1`.

The new summability theorem derives the same skeleton-pinned active cluster
tail convergence, and the quantitative theorem gives the compact bound

`Σₙ omegaClusterSkeletonRemainderSumTerm ≤ t⁻¹ · B`.

**Honest scope.** This is a downstream consumer of a local polymer norm bound,
not the missing Yang-Mills activity estimate itself.  It closes a statement
shape mismatch for P3/P4 sources while leaving the activity-decay theorem, the
continuum limit, and OS/Wightman reconstruction open.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 142 (2026-06-19, **collar-separated ExpDecay cross-sum**
`YangMills.RG.expDecay_separated_finset_sum_le`; core 8273)

**Build:** green (`lake env lean YangMills/RG/KernelSchur.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum records the first Lean brick extracted from the collar
factorization idea suggested by Lluis Eriksson's `ai.vixra:2512.0064v1`
outlook and the follow-up audit notes.  The thermodynamic maintenance-power
interpretation is deliberately **not** imported into `YangMillsCore`; the useful
mathematical content is the static covariance-decay step.

The theorem states that if an exponentially-decaying kernel satisfies
`|K i j| ≤ a exp(-κ d(i,j))`, and finite regions `A` and `B` are separated by a
collar `ε`, then for nonnegative derivative weights `L_i`, `M_j`,

`Σ_{i∈A,j∈B} |K i j| L_i M_j ≤
 a exp(-κ ε) (Σ_{i∈A} L_i)(Σ_{j∈B} M_j)`.

This is the deterministic finite-sum core that a future Gaussian interpolation
or integration-by-parts factorization theorem will consume.  It turns covariance
`ExpDecay` plus collar separation into the exact exponential price paid by a
cross-region influence term.

**Honest scope.** This is a source-independent algebraic substrate theorem.  It
does not prove the Gaussian integration-by-parts formula, the gauge-fixed
fluctuation covariance decay, the Yang-Mills activity estimate, the continuum
limit, or OS/Wightman reconstruction.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 143 (2026-06-19, **nearLog two-sided cutoff dictionary**
`YangMills.RG.norm_self_le_norm_nearLog_add_tail`,
`YangMills.RG.norm_self_le_two_norm_nearLog_of_norm_le_third`,
`YangMills.RG.norm_nearLog_le_two_norm_self_of_norm_le_half`,
`YangMills.RG.norm_nearLog_two_sided_of_norm_le_third`; core 8273)

**Build:** green (`lake env lean YangMills/RG/NearLog.lean`).  Full-core and
oracle verification are recorded with the commit carrying this addendum.

This addendum records the green part of the block-1 paper audit around large
fields and near-identity charts.  The source-facing claim is the local
dictionary between a near-identity group deviation and its logarithmic
coordinate: Bałaban's analytic logarithm is applied to the deviation from the
identity, so the Lean variable is `Y = D - 1`, not the represented group
element `D` itself.

The raw comparison theorem is

`‖Y‖ ≤ ‖nearLog Y‖ + ‖Y‖²/(1 - ‖Y‖)`.

Under the small-ball hypothesis `‖Y‖ ≤ 1/3`, the tail is absorbed and yields the
coarse but robust two-sided dictionary

`‖Y‖ ≤ 2‖nearLog Y‖ ∧ ‖nearLog Y‖ ≤ 2‖Y‖`.

This matches the formal need behind the large-field cutoff translation
highlighted in Lluis Eriksson's `ai.vixra:2602.0056` (Lemma 2.1 shape:
Hilbert-Schmidt deviation versus principal logarithm), but in the repository it
is proved at the existing Banach-algebra `nearLog` level and consumed only as a
local analytic comparison.  It also reinforces the semantic correction already
made in `Ubar.lean`: `Ubar` averages `nearLog (rep(D).val - 1)`.

**Honest scope.** This does **not** prove the matrix principal-log theorem for
`SU(N)` with Hilbert-Schmidt constants, and it does **not** prove the interface
identifying a conditional fast-field measure with Bałaban's `T`-operation.  It
only closes the local cutoff-conversion brick already available from the
Mercator calculus.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 144 (2026-06-19, **Hilbert-space averaging adjoint mass**
`YangMills.RG.scaledLinAvgCLM`, `YangMills.RG.qMassCLM`,
`YangMills.RG.inner_qMassCLM_self`, `YangMills.RG.qMassCLM_psd`,
`YangMills.RG.qMassCLM_opNorm_le`; core 8274)

**Build:** green (`lake env lean YangMills/RG/AveragingAdjoint.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum records the first theorem-fed brick of the direct covariance
route suggested by the latest Eriksson-paper audit.  The useful mathematical
step is not the broad interpretive thermodynamic language, but the concrete
Hilbert-space operator that a Gaussian block kernel consumes:

`qMassCLM = (sQ)†(sQ)`.

The implementation deliberately does **not** reuse the older `linAvgCLM`
directly, because the plain function space carries Mathlib's sup norm and does
not expose the Hilbert adjoint wanted here.  Instead the new module
`YangMills/RG/AveragingAdjoint.lean` defines fine and coarse bond fields on the
finite-dimensional `ℓ²`/`PiLp 2` Hilbert spaces, keeps the scalar rescaling
`s : ℝ` explicit, and proves:

* `inner_qMassCLM_self`:
  `⟪A, Q†Q A⟫ = ‖Q A‖²`;
* `qMassCLM_psd`: the adjoint mass is positive semidefinite;
* `qMassCLM_opNorm_le`: `‖Q†Q‖ ≤ ‖Q‖²`.

This is the deterministic mass/coercivity algebra behind a future
`GaussianBlockKernel` or finite-range `Q†Q` kernel theorem.

**Honest scope.** This does **not** prove the gauge-fixed Hessian is coercive,
does **not** identify the full Yang-Mills fluctuation covariance, does **not**
prove finite-range kernel decay, and does **not** discharge the activity-decay
input `hRpoly`.  It is a local Hilbert-space substrate theorem only.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 145 (2026-06-19, **abstract Ward-cancellation and activity-limit
bridges** `YangMills.SUSY.ApproxWardComplex`,
`YangMills.SUSY.expect_decomposition_bound`,
`YangMills.SUSY.expect_decomposition_profile_bound`,
`YangMills.SUSY.expect_profile_bound_of_exact_ward`,
`YangMills.RG.activity_profile_bound_of_tendsto`; core 8276)

**Build:** green (`lake env lean YangMills/SUSY/WardComplex.lean`,
`lake env lean YangMills/RG/ActivityLimit.lean`).  Full-core and oracle
verification are recorded with the commit carrying this addendum.

This addendum records the green, low-risk part of the supersymmetry audit.  It
does **not** add a supersymmetric Yang-Mills theory to the verified core.
Instead it formalizes the algebraic cancellation pattern that could later feed
the existing `hRpoly` consumers:

`H_X = Q B_X + R_X`, then integrate/cancel before taking norms.

`ApproxWardComplex` carries a continuous linear operator `Q`, an expectation
functional, and a quantitative Ward-defect estimate

`‖expect (Q F)‖ ≤ defect * ‖F‖`.

The exact theorem `expect_Q_eq_zero_of_defect_eq_zero` proves true Ward
cancellation when `defect = 0`.  The main approximate theorem
`expect_decomposition_bound` proves

`‖expect H‖ ≤ defect * ‖B‖ + ‖expect R‖`

from `H = Q B + R`.  The profile theorem
`expect_decomposition_profile_bound` lifts this pointwise to indexed activity
families: if `B` and `expect R` obey the same profile `w X`, then the integrated
activity obeys that profile with amplitude `defect * Bamp + Ramp`.

`ActivityLimit.lean` adds the corresponding regulator/decoupling consumer:
if complex activities are uniformly bounded by a profile and converge
pointwise, the limit obeys the same profile bound.

**Honest scope.** This is only an abstract algebraic/topological substrate.  It
does **not** construct Grassmann variables, Berezin integration, Pfaffians,
heavy-gluino decoupling, a Nicolai map, the Yang-Mills fluctuation activity
bound, the continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 146 (2026-06-19, **single-scale UV decay producer/consumer split**
`YangMills.RG.SingleScaleUVDecay`,
`YangMills.RG.RawYMActivityDecay`,
`YangMills.RG.RenormalizedHoleActivityDecay`,
`YangMills.RG.singleScaleUVDecay_of_renormalizedHoleActivities`,
`YangMills.RG.lattice_mass_gap_of_singleScaleUVDecay_geometric`; core 8277)

**Build:** green (`lake env lean YangMills/RG/SingleScaleUVDecay.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum records the architectural split suggested by the kinetic-sweep
audit.  The mass-gap assembly consumes a scalar terminal estimate, while the
with-holes polymer construction is only one possible producer of that estimate.
The new module `YangMills/RG/SingleScaleUVDecay.lean` names the three layers:

* `RawYMActivityDecay` — the pre-renormalized fluctuation-integral activity
  profile;
* `RenormalizedHoleActivityDecay` — the Appendix-F output profile for
  renormalized with-holes activities;
* `SingleScaleUVDecay` — the scalar per-scale estimate actually consumed by
  `UVMassGap`.

The theorem `singleScaleUVDecay_of_renormalizedHoleActivities` proves the real
summation bridge: if `Rsc t k = ∑' Y, Hsharp t k Y`, the activities are
absolutely summable, each `Hsharp` obeys the renormalized with-holes profile,
and `∑' Y, w Y ≤ K₀`, then the scalar `SingleScaleUVDecay` holds with amplitude
`A * K₀`.  The proof consumes the already-verified `polymer_remainder_bound`,
so it is not merely a definitional wrapper.

The theorem `lattice_mass_gap_of_singleScaleUVDecay_geometric` restates the
geometric-coupling assembly through the named scalar predicate, so future
producers can feed the existing mass-gap theorem without being forced through a
specific activity representation.

**Honest scope.** This does **not** prove raw Yang-Mills activity decay,
Appendix F, direct covariance identities, Hessian coercivity, continuum limit,
or OS/Wightman reconstruction.  It is an interface and verified summation
bridge only.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 147 (2026-06-20, **type-local functional/activity substrate**
`YangMills.RG.RestrictedField`,
`YangMills.RG.LocalFunctional`,
`YangMills.RG.LocalActivity`,
`YangMills.RG.LocalFunctional.globalEval_eq_of_agreeOn`,
`YangMills.RG.LocalFunctional.globalEval_finsetProd`,
`YangMills.RG.LocalActivity.globalEval_eq_of_agreeOn`,
`YangMills.RG.LocalActivity.globalEval_finsetProd`; core 8278)

**Build:** green (`lake env lean YangMills/RG/LocalFunctional.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum closes the first constructive F.1 substrate recommended by the
kinetic-sweep audit: represent locality in the types, not as a late global
`DependsOnlyOn` proposition.  The new module
`YangMills/RG/LocalFunctional.lean` defines:

* `RestrictedField S V := ∀ x : {x // x ∈ S}, V x.1`;
* `LocalFunctional Site V α`, whose `eval` can only inspect a field restricted
  to its finite `support`;
* `LocalActivity Site Ψ Φ α`, with separate spectator and fluctuation supports;
* global adapters back to full fields;
* finite sums/products via support unions, including a finite-product
  constructor over a subtype-indexed cover.

The locality bridges are theorem-fed.  `globalEval_eq_of_agreeOn` for both
`LocalFunctional` and `LocalActivity` proves that changing global fields outside
the declared support cannot change the value.  The product theorems
`globalEval_finsetProd` prove that the typed finite product evaluates as the
product of global evaluations while carrying the union of supports.

**Honest scope.** This is the algebraic locality substrate for a future
constructive Dimock-F.1 compiler.  It does **not** define `rawMayer`,
`omegaConnectedCoverActivity`, ultralocal product integration,
`dimockEffectiveActivity`, Appendix F, the Yang-Mills raw activity bound,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 148 (2026-06-20, **raw Mayer transform on type-local supports**
`YangMills.RG.LocalFunctional.rawMayer`,
`YangMills.RG.LocalFunctional.rawMayer_globalEval_eq_of_agreeOn`,
`YangMills.RG.LocalFunctional.norm_globalEval_rawMayer_le_two`,
`YangMills.RG.LocalActivity.rawMayer`,
`YangMills.RG.LocalActivity.rawMayer_globalEval_eq_of_agreeOn`,
`YangMills.RG.LocalActivity.norm_globalEval_rawMayer_le_two`; core 8279)

**Build:** green (`lake env lean YangMills/RG/RawMayerWithHoles.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum closes the next local F.1 substrate after Addendum 147.  The new
module `YangMills/RG/RawMayerWithHoles.lean` defines the raw Mayer transform
`H ↦ exp H - 1` on both:

* scalar complex `LocalFunctional` values;
* scalar complex two-field `LocalActivity` values.

Because the transform is implemented by `map`, the finite supports are
preserved by construction.  The theorems
`rawMayer_globalEval_eq_of_agreeOn` for both substrates prove that the Mayer
activity remains insensitive to off-support changes in the relevant global
fields.  The theorems `norm_globalEval_rawMayer_le_two` import the elementary
Mathlib estimate `‖exp z - 1‖ ≤ 2‖z‖` under the smallness hypothesis
`‖z‖ ≤ 1`, providing the first local analytic bound for future activity
decay.

**Honest scope.** This is the local `H_X ↦ m_X` step of a future constructive
Dimock-F.1 compiler.  It does **not** define Ω-connected covers, ultralocal
integration, the renormalized effective activity, Appendix F, the Yang-Mills
raw activity-decay bound, continuum limit, or OS/Wightman reconstruction.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 149 (2026-06-20, **Ω-connected Mayer-cover substrate**
`YangMills.RG.omegaOverlapGraph`,
`YangMills.RG.omegaConnectedIndex`,
`YangMills.RG.OmegaConnectedCover`,
`YangMills.RG.LocalActivity.mayerCoverActivity`,
`YangMills.RG.LocalActivity.globalEval_mayerCoverActivity`,
`YangMills.RG.LocalActivity.mayerCoverActivity_globalEval_eq_of_agreeOn`,
`YangMills.RG.OmegaConnectedCover.mayerActivity`,
`YangMills.RG.OmegaConnectedCover.globalEval_mayerActivity`,
`YangMills.RG.OmegaConnectedCover.mayerActivity_globalEval_eq_of_agreeOn`;
core 8280)

**Build:** green (`lake env lean YangMills/RG/OmegaConnectedCover.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum closes the next algebraic step in the constructive F.1 ladder.
The new module `YangMills/RG/OmegaConnectedCover.lean` defines:

* `omegaOverlapGraph Ω activeSupport`, the graph on cover indices whose edges
  mean that two active supports intersect inside Ω;
* `omegaConnectedIndex`, a walk-connectedness predicate in that graph;
* `OmegaConnectedCover`, a source-shaped package carrying the finite index set,
  Ω, active supports, and the connectedness certificate;
* `LocalActivity.mayerCoverActivity I H`, the finite product of raw Mayer
  activities `∏ᵢ (exp Hᵢ - 1)`;
* `OmegaConnectedCover.mayerActivity`, the same product attached to a
  connected cover package.

The cover product is theorem-fed: its spectator and fluctuation supports are
the corresponding support unions, `globalEval_mayerCoverActivity` and
`globalEval_mayerActivity` evaluate it as the product of the raw Mayer factors,
and the off-support invariance theorems prove that changing either field
outside those unions cannot change the value.

**Honest scope.** The Ω-connectedness condition is recorded but no quantitative
Appendix-F estimate is claimed.  This does **not** prove ultralocal
integration, the renormalized effective activity, the polymer loss
`κ → κ - 3κ₀ - 3`, the Yang-Mills raw activity-decay bound, continuum limit, or
OS/Wightman reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 150 (2026-06-20, **Ward-cancelled polymer activities**
`YangMills.SUSY.norm_finset_sum_expect_Q_le`,
`YangMills.SUSY.wardActivity`,
`YangMills.SUSY.wardActivity_metric_bound_of_decomposition`,
`YangMills.SUSY.wardActivity_metric_bound_of_exact`,
`YangMills.SUSY.omegaClusterSkeletonRemainderSum_tsum_le_of_ward`,
`YangMills.SUSY.omegaClusterSkeletonRemainderSum_tsum_le_of_exact_ward`;
core 8281)

**Build:** green (`lake env lean YangMills/SUSY/WardPolymer.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum records the verified salvage of the SUSY/Ward acceleration idea.
The external delivery package supplied for audit was not applied as a patch:
its unified patch was empty, it contained no Lean source files, and its own
build log reported a no-toolchain/no-repository failure.  The useful idea was
therefore reconstructed directly in the repo as a compiled Lean module.

The new module `YangMills/SUSY/WardPolymer.lean` connects the abstract
`ApproxWardComplex` layer to the literal `Ω`-active skeleton-tail consumer.  It
proves the finite Ward-defect summation estimate, packages the integrated
activity `wardActivity W Hraw = fun X => W.expect (Hraw X)`, derives the
pointwise modified-metric bound from approximate and exact Ward decompositions,
and feeds both forms directly into
`omegaClusterSkeletonRemainderSum_tsum_le_metric_bound`.

**Honest scope.** This does not construct supersymmetric Yang--Mills,
Grassmann/Berezin integration, a regulator, a concrete decomposition
`H_X = Q B_X + R_X` for the Yang--Mills fluctuation integral, the
cohomological-remainder bound, `hRpoly`, continuum limit, or OS/Wightman
reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 151 (2026-06-20, **telescopic regulator activity-limit bridge**
`YangMills.RG.activity_profile_bound_of_finite_telescope`,
`YangMills.RG.activity_profile_bound_of_tendsto_telescope`; core 8281)

**Build:** green (`lake env lean YangMills/RG/ActivityLimit.lean`).  Full-core
and oracle verification are recorded with the commit carrying this addendum.

This addendum closes the telescopic variant requested by the SUSY/Ward
acceleration plan.  The finite theorem proves that if
`‖z 0 X‖ ≤ amp * profile X` and each increment satisfies
`‖z (n+1) X - z n X‖ ≤ B n * profile X`, then

`‖z N X‖ ≤ (amp + ∑_{n<N} B n) * profile X`.

The limit theorem adds nonnegativity of the profile and `B`, summability of
`B`, the bound `∑' n, B n ≤ S`, and pointwise convergence `z n X → zLim X`,
and concludes

`‖zLim X‖ ≤ (amp + S) * profile X`.

This is the regulator-removal consumer needed by future Ward/decoupling
arguments: profile-bounded approximation error budgets add to the final
amplitude rather than requiring a fresh cluster-expansion proof.

**Honest scope.** This is an abstract topological/metric bridge.  It does not
construct the regulator, prove any Yang-Mills fluctuation-integral estimate,
prove `hRpoly`, continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 152 (2026-06-20, **ultralocal product-measure factorization**
`YangMills.RG.LocalFunctional.integral_mul_of_disjoint_support`,
`YangMills.RG.LocalActivity.integral_mul_of_disjoint_fluctuationSupport`;
core 8282)

**Build:** green (`lake env lean YangMills/RG/UltralocalFactorization.lean`).
Full-core and oracle verification are recorded with the commit carrying this
addendum.

This addendum adds the finite ultralocal independence step for the type-local
F.1 substrate.  The new module `YangMills/RG/UltralocalFactorization.lean`
reuses the existing product-measure factorization theorem from
`YangMills/L1_GibbsMeasure/EdgeFactorization.lean` and packages it for:

* two `LocalFunctional`s with disjoint finite supports; and
* two `LocalActivity`s with disjoint fluctuation supports, with the spectator
  field held fixed.

Both theorems factorize the integral of a product under an explicit finite
`Measure.pi` probability measure.  This gives future fluctuation-integral and
polymer compilers a theorem-fed ultralocal independence brick instead of
requiring them to restate support-dependence by hand.

**Honest scope.** This is finite product-measure independence only.  It does
not construct the Yang-Mills Gaussian fluctuation measure, prove covariance
decay, prove Dimock Appendix F, establish the renormalized activity bound
`hRpoly`, continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 153 (2026-06-20, **Mayer-cover ultralocal factorization**
`YangMills.RG.LocalActivity.fluctuationSupport_biUnion_disjoint_of_pairwise`,
`YangMills.RG.LocalActivity.mayerCoverActivity_integral_mul_of_disjoint_fluctuationSupport`,
`YangMills.RG.LocalActivity.mayerCoverActivity_integral_mul_of_pairwise_disjoint_fluctuationSupport`,
`YangMills.RG.OmegaConnectedCover.mayerActivity_integral_mul_of_disjoint_fluctuationSupport`,
`YangMills.RG.OmegaConnectedCover.mayerActivity_integral_mul_of_pairwise_disjoint_fluctuationSupport`;
core 8283)

This addendum connects the type-local Mayer-cover product to the ultralocal
product-measure independence theorem.  The new module
`YangMills/RG/MayerCoverFactorization.lean` proves that two finite products of
raw Mayer activities factorize under an explicit `Measure.pi` fluctuation
measure when their fluctuation-support unions are disjoint.  The pairwise
version derives that union disjointness from pairwise disjoint factor supports,
which is the natural output shape for a disconnected-cover compiler.

The same bridge is packaged for `OmegaConnectedCover.mayerActivity`: the
Ω-connectedness certificates remain part of the cover objects, while the
factorization hypothesis is exactly disjointness of the actual fluctuation
dependencies.

**Honest scope.** This is finite ultralocal independence for disconnected
Mayer-cover components.  It does not prove Dimock Appendix F, the
renormalized activity estimate, the Yang-Mills fluctuation integral,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 154 (2026-06-20, **finite disjoint-union Mayer-cover split**
`YangMills.RG.LocalActivity.globalEval_mayerCoverActivity_union`,
`YangMills.RG.LocalActivity.mayerCoverActivity_union_integral_of_pairwise_disjoint_fluctuationSupport`;
core 8283)

This addendum adds the next finite compiler step on top of Addendum 153.  The
new evaluation theorem proves that a raw Mayer-cover product over a disjoint
union of index sets splits pointwise into the product of the two subcover
products.  The integration theorem combines that split with the ultralocal
factorization bridge: if the two index blocks are disjoint and every
fluctuation support in the first block is disjoint from every fluctuation
support in the second block, then the integral of the product over the union
equals the product of the two subcover integrals.

This is the finite "disconnected cover" reduction that future Appendix-F work
can consume before imposing the source-specific Ω-connectedness and
quantitative polymer-loss estimates.

**Honest scope.** This is still finite algebra plus product-measure
independence.  It does not prove the Appendix-F convergence theorem, the
renormalized activity estimate, the Yang-Mills fluctuation integral,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 155 (2026-06-20, **fluctuation-overlap no-cross-edge split**
`YangMills.RG.LocalActivity.fluctuationOverlapGraph_adj_iff`,
`YangMills.RG.LocalActivity.pairwise_disjoint_fluctuationSupport_of_no_cross_adj`,
`YangMills.RG.LocalActivity.mayerCoverActivity_union_integral_of_no_cross_fluctuationAdj`;
core 8283)

This addendum adds the finite graph criterion for disconnected Mayer-cover
components.  The new `fluctuationOverlapGraph` has an edge exactly when two
type-local activities have overlapping fluctuation supports.  If two disjoint
index blocks have no cross-edge in this graph, then
`pairwise_disjoint_fluctuationSupport_of_no_cross_adj` supplies the pairwise
cross-support disjointness hypothesis consumed by Addendum 154.  The
integrated theorem
`mayerCoverActivity_union_integral_of_no_cross_fluctuationAdj` packages the
result as a graph-theoretic disconnected-cover split.

This is the finite connected-component extraction precursor for future F.1 /
Appendix-F work: a source-specific compiler may identify disconnected blocks
in the fluctuation-overlap graph and feed them directly to the existing
ultralocal factorization theorem.

**Honest scope.** This is still finite graph algebra plus product-measure
independence.  It does not construct the Yang-Mills Gaussian fluctuation
measure, prove covariance decay, prove Dimock Appendix F, establish `hRpoly`,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 156 (2026-06-20, **confined-component Mayer-cover split**
`YangMills.RG.no_adj_confinedComponent_compl`,
`YangMills.RG.LocalActivity.mayerCoverActivity_integral_split_confinedComponent`;
core 8283)

This addendum adds the component-extraction producer for Addendum 155.  The
generic finite definitions `confinedReachable` and `confinedComponent` describe
the component of a root `r` inside a finite index set `K`, using only walks
whose support stays in `K`.  The graph lemma
`no_adj_confinedComponent_compl` proves that no edge can run from this
component to a vertex of `K` outside it: otherwise appending that edge to the
confined walk would put the outside vertex back in the component.

For the fluctuation-overlap graph of a family of local activities, the theorem
`mayerCoverActivity_integral_split_confinedComponent` uses this lemma to split
the Mayer-cover integral over `K` into the integral over the root component
times the integral over the complement `K \ I`.  Thus the finite disconnected
component compiler no longer needs an externally supplied no-cross-edge
hypothesis for a root component; it derives it from confined reachability.

**Honest scope.** This is finite graph/component algebra plus the already
proved product-measure independence.  It does not identify the actual
Appendix-F polymers of Yang-Mills, prove any quantitative polymer loss,
construct the fluctuation measure, establish `hRpoly`, continuum limit, or
OS/Wightman reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 157 (2026-06-20, **finite confined-component decomposition**
`YangMills.RG.biUnion_confinedComponents_eq`,
`YangMills.RG.confinedComponents_eq_of_nonempty_inter`,
`YangMills.RG.disjoint_of_mem_confinedComponents_ne`;
core 8283)

This addendum upgrades the root-component split of Addendum 156 into a finite
all-components decomposition.  The new reachability lemmas
`confinedReachable_refl`, `confinedReachable_symm`, and
`confinedReachable_trans` make the confined-walk relation usable as an
equivalence relation on a finite cover set `K`.  The new finite set
`confinedComponents G K` collects all confined components generated by roots
in `K`.

The theorem `biUnion_confinedComponents_eq` proves that these components cover
exactly `K`.  The theorem `confinedComponents_eq_of_nonempty_inter` proves
that two such components with a common vertex are equal, and
`disjoint_of_mem_confinedComponents_ne` packages the contrapositive as
disjointness of distinct components.  This is the finite partition substrate
needed before an n-ary Mayer-cover integral factorization over connected
components can replace repeated binary splitting.

**Honest scope.** This is finite graph algebra for the F.1 compiler
substrate.  At this checkpoint it did not prove the n-ary integral
factorization yet, did not
identify Dimock Appendix-F polymers, does not prove activity decay or
`hRpoly`, and does not move the continuum / OS reconstruction frontier.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 158 (2026-06-20, **n-ary confined-component Mayer-cover
factorization**
`YangMills.RG.no_adj_of_mem_confinedComponents_ne`,
`YangMills.RG.LocalActivity.mayerCoverActivity_biUnion_integral_of_no_cross_components`,
`YangMills.RG.LocalActivity.mayerCoverActivity_integral_factor_confinedComponents`;
core 8283)

This addendum consumes the finite partition substrate of Addendum 157.  The
new graph lemma `no_adj_of_mem_confinedComponents_ne` proves that two distinct
confined components of a finite cover set have no edge between them.  For the
fluctuation-overlap graph, this supplies exactly the no-cross-edge hypothesis
needed by the product-measure factorization theorem.

The generic theorem
`mayerCoverActivity_biUnion_integral_of_no_cross_components` proves the n-ary
finite disconnected-cover formula: for any finite family of pairwise disjoint
index blocks with no fluctuation-overlap graph edge between distinct blocks,
the Mayer-cover integral over the union of all blocks is the product of the
block integrals.  The proof is by finite induction, using the existing binary
no-cross-edge split at each step.

The consumer
`mayerCoverActivity_integral_factor_confinedComponents` instantiates that
generic theorem for the confined-component partition
`confinedComponents (fluctuationOverlapGraph H) K`.  Thus a finite Mayer cover
now factorizes directly over all its fluctuation-overlap connected components,
instead of requiring an external hand iteration of the binary root/complement
split.

**Honest scope.** This closes another finite algebra/product-measure compiler
step for the future Dimock-F.1 formalization.  It does not identify the actual
Appendix-F polymers, prove the quantitative activity loss, construct the
Yang-Mills fluctuation measure, establish `hRpoly`, continuum limit, or
OS/Wightman reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 159 (2026-06-20, **confined components as Ω-connected covers**
`YangMills.RG.confinedComponent_walkConnected`,
`YangMills.RG.OmegaConnectedCover.confinedComponentCover`,
`YangMills.RG.OmegaConnectedCover.exists_confinedComponentCover_of_mem_confinedComponents`;
core 8283)

This addendum closes the finite handoff from the disconnected-component
compiler back into the source-shaped Ω-cover API.  The support lemma
`mem_confinedComponent_of_mem_confinedWalk_support` shows that every vertex
appearing on a confined walk remains in the same confined component.  The
theorem `confinedComponent_walkConnected` then proves that each confined
component is walk-connected in the ambient graph.

For the Ω-overlap graph, `OmegaConnectedCover.confinedComponentCover` packages
the confined component of a root as an `OmegaConnectedCover` with the same
Ω-region and active-support map.  The theorem
`exists_confinedComponentCover_of_mem_confinedComponents` lifts every member of
`confinedComponents (omegaOverlapGraph Ω activeSupport) K` to such a cover,
so the finite all-components decomposition from Addendum 158 can hand its
blocks directly to the Ω-connected Mayer-product layer.

**Honest scope.** This is finite graph/component packaging for the future
Dimock-F.1 compiler.  It does not prove Appendix-F activity decay, construct
the Yang-Mills fluctuation measure, establish `hRpoly`, continuum limit, or
OS/Wightman reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 160 (2026-06-20, **Ω-active disjointness across confined
components**
`YangMills.RG.OmegaConnectedCover.omegaActiveSupport_disjoint_of_mem_confinedComponents_ne`,
`YangMills.RG.OmegaConnectedCover.pairwise_omegaActiveSupport_disjoint_of_mem_confinedComponents_ne`;
core 8283)

This addendum records the source-facing separation fact associated to
Addendum 159.  If two finite confined components of the Ω-overlap graph are
distinct, then any index in one component and any index in the other have
disjoint active supports inside Ω:
`Disjoint (Ω ∩ activeSupport i) (Ω ∩ activeSupport j)`.  The proof combines the
existing no-edge theorem for distinct confined components with the defining
adjacency criterion of `omegaOverlapGraph`.

The pairwise wrapper packages this as the hypothesis shape expected by later
finite compiler or factorization steps.  It is the finite graph-to-source
translation layer: separated Ω-components give separated Ω-active supports.

**Honest scope.** This is finite Ω-overlap graph algebra only.  It does not
prove Appendix-F activity decay, the Yang-Mills fluctuation measure,
`hRpoly`, continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 161 (2026-06-20, **canonical confined-component cover family**
`YangMills.RG.OmegaConnectedCover.confinedComponentCoverOfComponent`,
`YangMills.RG.OmegaConnectedCover.confinedComponentCoverFamily`,
`YangMills.RG.OmegaConnectedCover.biUnion_confinedComponentCoverFamily_index_eq`,
`YangMills.RG.OmegaConnectedCover.pairwise_omegaActiveSupport_disjoint_confinedComponentCoverFamily`;
core 8283)

This addendum packages Addenda 159–160 as a reusable finite family interface.
For any known member `C` of
`confinedComponents (omegaOverlapGraph Ω activeSupport) K`, the noncomputable
choice `confinedComponentCoverOfComponent` selects an `OmegaConnectedCover`
whose index is exactly `C`, whose Ω-region is `Ω`, and whose active-support map
is the original `activeSupport`.  The theorem
`mayerActivity_confinedComponentCoverOfComponent` rewrites its Mayer activity
back to `LocalActivity.mayerCoverActivity C H`.

The family wrapper `confinedComponentCoverFamily` indexes these covers by the
finite subtype of confined Ω-overlap components.  The theorem
`biUnion_confinedComponentCoverFamily_index_eq` proves that the union of the
family's cover indices is exactly the original finite cover set `K`, and
`pairwise_omegaActiveSupport_disjoint_confinedComponentCoverFamily` gives the
pairwise Ω-active support disjointness across distinct family entries.

**Honest scope.** This is finite compiler packaging for the future
Dimock-F.1/with-holes layer.  It does not prove Appendix-F activity decay,
construct the Yang-Mills fluctuation measure, establish `hRpoly`, continuum
limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 162 (2026-06-20, **canonical confined-component cover partition**
`YangMills.RG.OmegaConnectedCover.disjoint_confinedComponentCoverFamily_index_of_ne`,
`YangMills.RG.OmegaConnectedCover.pairwise_disjoint_confinedComponentCoverFamily_index`;
core 8283)

This addendum completes the finite partition interface for the canonical
confined-component cover family from Addendum 161.  The theorem
`disjoint_confinedComponentCoverFamily_index_of_ne` proves that distinct
entries of `confinedComponentCoverFamily Ω activeSupport K` have disjoint
index sets.  The pairwise wrapper packages the same fact in the family-indexed
form expected by later n-ary factorization and cover-product consumers.

Together with `biUnion_confinedComponentCoverFamily_index_eq`, the family now
has the exact compiler shape needed downstream: it covers all of `K` and its
component indices are pairwise disjoint.

**Honest scope.** This is finite Ω-overlap component packaging only.  It does
not prove Appendix-F activity decay, construct the Yang-Mills fluctuation
measure, establish `hRpoly`, continuum limit, or OS/Wightman reconstruction.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 163 (2026-06-20, **Ω-component support bridge to ultralocal
factorization**
`YangMills.RG.LocalActivity.mayerCoverActivity_integral_factor_confinedOmegaComponents_of_fluctuationSupport_subset`;
core 8283)

This addendum records the finite bridge from source-shaped Ω-components to the
measure-theoretic disconnected-cover factorization.  The theorem
`mayerCoverActivity_integral_factor_confinedOmegaComponents_of_fluctuationSupport_subset`
assumes the explicit containment
`(H i).fluctuationSupport ⊆ Ω ∩ activeSupport i` for each `i ∈ K`.  Under that
hypothesis, distinct confined components of the Ω-overlap graph have disjoint
fluctuation supports, so the ultralocal product probability measure factorizes
the Mayer-cover integral over `K` into the product over those Ω-components.

This is the exact finite adapter a later Appendix-F source compiler needs:
prove that the analytic/local construction declares active supports large
enough to contain the fluctuation dependencies, then the already-verified
component machinery supplies independence.

**Honest scope.** This is finite support algebra plus product-measure
factorization.  It does not prove the support containment for Yang-Mills,
Appendix-F activity decay, the Yang-Mills fluctuation measure, `hRpoly`,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 164 (2026-06-20, **canonical Ω-cover-family factorization
wrapper**
`YangMills.RG.OmegaConnectedCover.mayerActivity_integral_factor_confinedComponentCoverFamily_of_fluctuationSupport_subset`;
core 8283)

This addendum gives the finite F.1 compiler a source-shaped consumer for
Addendum 163.  The theorem
`mayerActivity_integral_factor_confinedComponentCoverFamily_of_fluctuationSupport_subset`
starts from the same explicit containment hypothesis
`(H i).fluctuationSupport ⊆ Ω ∩ activeSupport i` for all `i ∈ K`, but states
the resulting ultralocal Mayer-cover integral factorization directly as a
product over the canonical `confinedComponentCoverFamily`.

The proof reuses the Ω-component support bridge from Addendum 163, converts the
raw component product through `Finset.prod_attach`, and rewrites each selected
component using `mayerActivity_confinedComponentCoverOfComponent`.  This avoids
forcing later source compilers to unfold the chosen root/component witnesses by
hand.

**Honest scope.** This is finite cover-family packaging for the future
Appendix-F compiler.  It does not prove the support-containment hypothesis for
Yang-Mills, the Appendix-F activity decay, the fluctuation measure, `hRpoly`,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 165 (2026-06-20, **support-containment edge adapter**
`YangMills.RG.LocalActivity.fluctuationOverlapGraph_adj_imp_omegaOverlapGraph_adj_of_fluctuationSupport_subset`;
core 8283)

This addendum extracts the graph-level adapter used by the Ω-component
support bridge.  The theorem
`fluctuationOverlapGraph_adj_imp_omegaOverlapGraph_adj_of_fluctuationSupport_subset`
assumes the same local containment hypotheses
`(H i).fluctuationSupport ⊆ Ω ∩ activeSupport i` and
`(H j).fluctuationSupport ⊆ Ω ∩ activeSupport j`.  Under those hypotheses, an
actual fluctuation-overlap edge between `i` and `j` implies an Ω-overlap edge
for the declared active supports.  The proof is the finite contrapositive:
if the declared Ω-active supports are disjoint, the contained fluctuation
supports are disjoint, contradicting the fluctuation edge.

This separates the source-side obligation from the measure-theoretic
factorization: a future Yang-Mills source compiler only has to prove the
support-containment statement for its local activities, and this adapter turns
actual dependencies into the Ω-cover graph relation consumed by the existing
finite F.1 machinery.

**Honest scope.** This is finite support/graph algebra.  It does not prove the
support-containment hypothesis for Yang-Mills, the Appendix-F activity decay,
the fluctuation measure, `hRpoly`, continuum limit, or OS/Wightman
reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 166 (2026-06-20, **Mayer-cover support-containment lifting**
`YangMills.RG.LocalActivity.mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport`,
`YangMills.RG.OmegaConnectedCover.mayerActivity_fluctuationSupport_subset_omega_biUnion_activeSupport`;
core 8283)

This addendum records the finite support-lifting step for the source-facing
Mayer-cover compiler.  The local theorem
`mayerCoverActivity_fluctuationSupport_subset_omega_biUnion_activeSupport`
assumes that each factor in a finite cover has fluctuation support contained
in its declared active support inside `Ω`,
`(H i).fluctuationSupport ⊆ Ω ∩ activeSupport i`.  It proves that the whole
raw-Mayer product over the cover has fluctuation support contained in
`Ω ∩ I.biUnion activeSupport`.  The `OmegaConnectedCover` theorem packages the
same statement for the cover object used by the F.1-facing APIs.

This is the local support analogue of Addendum 165: once a future
Yang-Mills source compiler proves factorwise support containment, the verified
finite layer now propagates that containment to the product activity and to
the Ω-overlap/factorization graph without redoing `biUnion` algebra.

**Honest scope.** This is finite support algebra for already-declared
supports.  It does not prove the support-containment hypothesis for
Yang-Mills, the Appendix-F activity decay, the fluctuation measure, `hRpoly`,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 167 (2026-06-20, **Mayer-cover pointwise product norm bound**
`YangMills.RG.LocalActivity.norm_globalEval_mayerCoverActivity_le_prod_two_of_norm_le`,
`YangMills.RG.OmegaConnectedCover.norm_globalEval_mayerActivity_le_prod_two_of_norm_le`;
core 8283)

This addendum records the finite quantitative companion to Addendum 166.
The local theorem
`norm_globalEval_mayerCoverActivity_le_prod_two_of_norm_le` assumes a
factorwise pointwise raw-activity majorant over a finite cover,
`‖(H i).globalEval ψ φ‖ ≤ A i`, together with the smallness window
`A i ≤ 1` for each `i ∈ I`.  It proves the raw Mayer-cover estimate

`‖(mayerCoverActivity I H).globalEval ψ φ‖ ≤ ∏ i : {i // i ∈ I}, 2 * A i.1`.

The proof is purely finite: rewrite the cover activity as
`∏ᵢ (exp (Hᵢ) - 1)`, use `norm_prod`, apply the already-verified one-factor
Mayer estimate `‖exp z - 1‖ ≤ 2‖z‖`, and multiply the factorwise bounds.
The `OmegaConnectedCover` theorem packages the same estimate for the
source-shaped cover object.

This gives future Appendix-F/Yang-Mills source compilers a direct quantitative
handoff: once the primary source supplies factorwise raw estimates, the
verified layer converts them into the finite product majorant without redoing
complex-norm product algebra.

**Honest scope.** This is finite complex norm algebra plus the elementary
one-factor Mayer estimate.  It does not prove the Yang-Mills raw activity
bound, the source smallness window, Appendix-F activity decay, `hRpoly`,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 168 (2026-06-20, **uniform Mayer-cover size profile**
`YangMills.RG.LocalActivity.norm_globalEval_mayerCoverActivity_le_two_mul_pow_card_of_norm_le`,
`YangMills.RG.OmegaConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_card_of_norm_le`;
core 8283)

This addendum specializes the Addendum 167 product bound to the common
source-facing case where every member of a finite cover has the same small
raw-activity amplitude `A`.  The local theorem
`norm_globalEval_mayerCoverActivity_le_two_mul_pow_card_of_norm_le` assumes
`‖(H i).globalEval ψ φ‖ ≤ A` for all `i ∈ I` and `A ≤ 1`, and proves

`‖(mayerCoverActivity I H).globalEval ψ φ‖ ≤ (2 * A) ^ I.card`.

The cover-facing theorem packages the same statement for
`OmegaConnectedCover`.  This is the finite cardinality profile a later
source compiler can combine with cover-size or skeleton-size estimates before
feeding the existing local-window/metric-bound KP consumers.

**Honest scope.** This is a corollary of the finite product-norm estimate,
not a Yang-Mills activity estimate.  It does not prove the source amplitude
`A`, the source smallness window, Appendix-F activity decay, `hRpoly`,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 169 (2026-06-20, **Mayer-cover decay from a cardinal lower bound**
`YangMills.RG.LocalActivity.norm_globalEval_mayerCoverActivity_le_two_mul_pow_of_le_card`,
`YangMills.RG.OmegaConnectedCover.norm_globalEval_mayerActivity_le_two_mul_pow_of_le_card`;
core 8283)

This addendum turns the uniform cover-size profile of Addendum 168 into the
decay form needed by future metric/skeleton compilers.  If every factor has
raw-activity amplitude `≤ A`, `0 ≤ A`, `A ≤ 1`, the one-factor Mayer cost
satisfies `2 * A ≤ 1`, and a source-side combinatorial argument proves a
lower bound `n ≤ I.card`, then

`‖(mayerCoverActivity I H).globalEval ψ φ‖ ≤ (2 * A) ^ n`.

The proof is finite real algebra: first use the verified cardinal profile
`≤ (2A)^{|I|}`, then use monotonicity of powers for a base in `[0,1]`.
The cover-facing theorem packages the same result for `OmegaConnectedCover`.

This is the exact non-model-specific bridge between a future source theorem
such as "the cover has at least the active skeleton size / modified metric"
and an exponentially small Mayer-cover product.

**Honest scope.** This is finite power monotonicity plus the Mayer product
bound.  It does not prove the source-side lower bound `n ≤ |I|`, the
Yang-Mills raw amplitude `A`, Appendix-F activity decay, `hRpoly`, continuum
limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 170 (2026-06-20, **finite Berezin top-coefficient substrate**
`YangMills.SUSY.finiteExteriorBasis_empty`,
`YangMills.SUSY.finiteBerezinTop_basis`,
`YangMills.SUSY.finiteBerezinTop_top_basis`,
`YangMills.SUSY.finiteBerezinTop_basis_of_ne_top`,
`YangMills.SUSY.finiteBerezinTop_one_of_pos`;
core 8283)

This addendum records the first concrete finite Grassmann/Berezin algebra
under the abstract Ward layer.  The new file `YangMills/SUSY/FiniteBerezin.lean`
uses Mathlib's exterior algebra over the finite complex vector space
`Fin n → ℂ`.  Its canonical basis is indexed by finite subsets of `Fin n`.

The main definition
`finiteBerezinTop n : ExteriorAlgebra ℂ (Fin n → ℂ) →ₗ[ℂ] ℂ`
is the coefficient functional of the top exterior monomial.  The verified
rules are:

* `finiteExteriorBasis_empty` identifies the empty exterior monomial with the
  unit;
* `finiteBerezinTop_basis` proves that the top-coefficient functional is `1`
  on the top basis monomial and `0` on all other exterior basis monomials;
* `finiteBerezinTop_top_basis` and `finiteBerezinTop_basis_of_ne_top` expose
  those two cases separately;
* `finiteBerezinTop_one_of_pos` proves that constants have zero finite
  Berezin integral when the fermionic dimension is positive.

This gives the Ward/SUSY track a real algebraic object beneath the previously
abstract cancellation interface: future finite super-Gaussian work can now
target an actual top-coefficient Berezin functional instead of a purely
schematic expectation symbol.

**Honest scope.** This is only the algebraic Berezin coefficient functional.
It does not construct a Gaussian Berezin weight, fermionic covariance,
Pfaffian/determinant cancellation, a regulator/decoupling theorem, the
Yang-Mills fluctuation activity bound, `hRpoly`, continuum limit, or
OS/Wightman reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 171 (2026-06-20, **finite Berezin exact-Ward cancellation**
`YangMills.SUSY.finiteBerezinTop_one_zero`,
`YangMills.SUSY.finiteBerezinTop_algebraMap_of_pos`,
`YangMills.SUSY.finiteBerezin_expect_Q_eq_zero`,
`YangMills.SUSY.finiteBerezin_eq_expect_remainder_of_exactWard`;
core 8284)

This addendum extends the finite Berezin substrate with the exact algebraic
Ward rule for the concrete top-coefficient functional.  The file now names
the finite exterior algebra as `FiniteExterior n`, proves the scalar endpoint
rules

* `finiteBerezinTop_one_zero`: in zero fermionic dimension, `∫ 1 = 1`;
* `finiteBerezinTop_algebraMap_of_pos`: in positive fermionic dimension,
  every scalar constant has finite Berezin integral `0`;

and introduces `FiniteBerezinExactWard n`, a linear operator `Q` on
`FiniteExterior n` satisfying the exact finite Ward identity
`finiteBerezinTop n (Q F) = 0`.

The theorem `finiteBerezin_eq_expect_remainder_of_exactWard` proves the
concrete cancellation rule:

`H = Q B + R ⟹ finiteBerezinTop n H = finiteBerezinTop n R`.

This is the finite Berezin analogue of the exact branch of
`ApproxWardComplex`, but deliberately remains algebraic: no artificial
norm/topology is placed on Mathlib's exterior algebra merely to fit a
continuous-linear API.

**Honest scope.** This is exact algebraic Ward cancellation for a finite
top-coefficient functional.  It does not construct the Ward differential from
a physical supersymmetry, prove Gaussian Berezin determinant/Pfaffian
identities, bound any Yang-Mills activity, discharge `hRpoly`, or affect the
continuum Clay obligations.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 172 (2026-06-20, **weighted finite Berezin Ward functional**
`YangMills.SUSY.finiteBerezinWeighted_apply`,
`YangMills.SUSY.finiteBerezinWeighted_one`,
`YangMills.SUSY.finiteBerezinWeighted_expect_Q_eq_zero`,
`YangMills.SUSY.finiteBerezinWeighted_eq_expect_remainder_of_exactWard`;
core 8284)

This addendum adds the algebraic weighted Berezin functional

`finiteBerezinWeighted n weight F = finiteBerezinTop n (weight * F)`.

The theorem `finiteBerezinWeighted_one` proves that unit weight recovers the
unweighted top-coefficient functional.  The new structure
`FiniteBerezinWeightedExactWard n weight` then packages an exact finite Ward
identity for this weighted functional, and
`finiteBerezinWeighted_eq_expect_remainder_of_exactWard` proves the weighted
cancellation rule:

`H = Q B + R ⟹ ∫_weight H = ∫_weight R`.

This is the next finite-dimensional substrate needed before a super-Gaussian
toy model: future work can instantiate `weight` by an exterior-algebra
Gaussian weight and then prove, from primary finite Berezin algebra, the
determinant/Pfaffian cancellation identities.

**Honest scope.** The weight is only an algebraic multiplier.  This checkpoint
does not construct a covariance, prove a Gaussian Berezin determinant/Pfaffian
formula, instantiate a physical supersymmetry, bound any Yang-Mills activity,
discharge `hRpoly`, or affect the continuum Clay obligations.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 173 (2026-06-20, **finite Berezin top-density normalization**
`YangMills.SUSY.finiteBerezinWeighted_top_basis_one`,
`YangMills.SUSY.finiteBerezinTopWeight_zero`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_one_of_pos`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_algebraMap_of_pos`;
core 8284)

This addendum adds the first concrete weighted-density seed for the finite
Berezin substrate:

`finiteBerezinTopWeight n a = 1 + a • finiteExteriorBasis n univ`.

The theorem `finiteBerezinWeighted_top_basis_one` proves that weighting by the
top exterior basis monomial integrates the constant observable `1` to `1`.
The theorem `finiteBerezinTopWeight_zero` records that zero top coefficient is
the unit density.  In positive fermionic dimension,
`finiteBerezinWeighted_topWeight_one_of_pos` proves

`∫_(finiteBerezinTopWeight n a) 1 = a`,

and `finiteBerezinWeighted_topWeight_algebraMap_of_pos` proves the scalar
normalization rule

`∫_(finiteBerezinTopWeight n a) z = a * z`.

This is a small but concrete preparation for finite super-Gaussian work: a
future exterior-algebra Gaussian weight must reduce to explicit top-degree
coefficients before any determinant/Pfaffian cancellation theorem can be
honestly stated.

**Honest scope.** This is top-degree density normalization only.  It does not
construct a Gaussian covariance, determinant/Pfaffian identity, physical
supersymmetry, Yang-Mills activity bound, `hRpoly`, continuum limit, or
OS/Wightman reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 174 (2026-06-20, **finite Berezin generator nilpotence**
`YangMills.SUSY.finiteExteriorBasis_singleton_mul_self`;
core 8284)

This addendum records the first generator-level Grassmann algebra theorem in
the finite Berezin substrate.  For every finite fermionic dimension and every
generator index `i`, the degree-one exterior basis monomial squares to zero:

`e_i * e_i = 0`.

The proof uses Mathlib's exterior-algebra basis multiplication theorem for
non-disjoint exterior basis monomials, avoiding any sign-convention shortcut.
This is a basic input for future finite Gaussian/Pfaffian work: any honest
finite Berezin Gaussian expansion needs the nilpotence of repeated generators
before pairings and top-degree coefficients can be computed.

**Honest scope.** This is only generator nilpotence in the finite exterior
algebra.  It does not prove a Gaussian Berezin integral, determinant/Pfaffian
formula, physical supersymmetry, Yang-Mills activity bound, `hRpoly`,
continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 175 (2026-06-20, **finite exterior basis product rules**
`YangMills.SUSY.finiteExteriorBasis_powersetCard_mul_of_not_disjoint`,
`YangMills.SUSY.finiteExteriorBasis_powersetCard_mul_of_disjoint`,
`YangMills.SUSY.finiteExteriorBasis_mul_of_not_disjoint`,
`YangMills.SUSY.finiteBerezinTop_basis_mul_of_not_disjoint`,
`YangMills.SUSY.finiteBerezinTop_powersetCard_mul_of_disjoint_top`;
core 8284)

This addendum generalizes the previous singleton nilpotence brick into the
finite exterior-basis product API needed for explicit Berezin expansions.

* If two basis monomials have overlapping generator support, their product is
  zero.
* Consequently, the Berezin top coefficient of such a product is zero.
* If two cardinality-indexed basis monomials are disjoint, their product is the
  exterior basis monomial of the disjoint union multiplied by Mathlib's explicit
  permutation sign.
* If that disjoint union is the full generator set, the Berezin top coefficient
  of the product is exactly the same explicit orientation sign acting on
  `(1 : ℂ)`.

The disjoint case intentionally leaves the orientation sign visible.  This
avoids the earlier rejected shortcut through concrete decision-procedure signs
and sets up finite Gaussian/Pfaffian identities so their sign conventions
remain auditable.

**Honest scope.** These are algebraic exterior-basis product rules only.  They
do not prove a Gaussian Berezin integral, determinant/Pfaffian formula,
physical supersymmetry, Yang-Mills activity bound, `hRpoly`, continuum limit,
or OS/Wightman reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 176 (2026-06-20, **top-density basis calculus**
`YangMills.SUSY.finiteExteriorBasis_univ_mul_of_nonempty`,
`YangMills.SUSY.finiteExteriorBasis_mul_univ_of_nonempty`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_empty_of_pos`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_of_nonempty`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_top_basis_of_pos`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_of_nonempty_ne_top`;
core 8284)

This addendum computes the elementary top-density weight

`finiteBerezinTopWeight n a = 1 + a • topBasis`

on exterior basis monomials in positive fermionic dimension.

* The top basis monomial annihilates any nonempty basis monomial on either
  side, by repeated-generator nilpotence.
* The empty basis monomial integrates to the prescribed coefficient `a`.
* The top basis monomial integrates to `1`.
* Every nonempty, non-top basis monomial integrates to `0`.

This makes the toy finite Berezin density genuinely usable as a basis-level
coefficient extractor before any Gaussian/Pfaffian determinant statement is
attempted.

**Honest scope.** This is still only finite exterior-algebra bookkeeping for a
top-degree density seed.  It does not construct a Gaussian Berezin integral,
determinant/Pfaffian formula, physical supersymmetry, Yang-Mills activity
bound, `hRpoly`, continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 177 (2026-06-20, **top-density linear coefficient functional**
`YangMills.SUSY.finiteBerezinEmptyCoeff_basis`,
`YangMills.SUSY.finiteBerezinEmptyCoeff_empty_basis`,
`YangMills.SUSY.finiteBerezinEmptyCoeff_basis_of_nonempty`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_eq_top_add_empty_of_pos`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_apply_eq_top_add_empty_of_pos`;
core 8284)

This addendum promotes the previous basis-by-basis top-density computation into
a global linear identity on the finite exterior algebra.  The new
`finiteBerezinEmptyCoeff` reads the coefficient of the empty exterior monomial,
and in positive fermionic dimension the elementary density

`finiteBerezinTopWeight n a = 1 + a • topBasis`

acts by

`finiteBerezinTop + a • finiteBerezinEmptyCoeff`.

Equivalently, integrating an arbitrary finite exterior element against that
weight extracts its top coefficient and adds `a` times its empty coefficient.
This is a small but useful interface for later finite Gaussian/Pfaffian
expansions, where weights must be reduced to coefficient extraction before any
determinant identity can be stated honestly.

**Honest scope.** This is a finite-dimensional linear coefficient identity for
the toy top-density seed.  It does not construct a Gaussian Berezin integral,
fermionic covariance, determinant/Pfaffian formula, physical supersymmetry,
Yang-Mills activity bound, `hRpoly`, continuum limit, or OS/Wightman
reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 178 (2026-06-20, **top-density product coefficient rules**
`YangMills.SUSY.finiteBerezinWeighted_topWeight_basis_mul_of_not_disjoint`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_powersetCard_mul_of_disjoint_top_of_pos`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_powersetCard_mul_of_disjoint_nonempty_ne_top`;
core 8284)

This addendum evaluates the elementary top-density weight on products of
finite exterior basis monomials.

* If the two supports overlap, repeated-generator nilpotence kills the product,
  so the weighted Berezin integral is zero.
* If the supports are disjoint and their union is the full generator set in
  positive fermionic dimension, the weighted integral is exactly Mathlib's
  explicit exterior orientation sign.
* If the disjoint union is nonempty but not top-degree, the weighted integral
  is zero.

These are deliberately sign-exposed product rules.  They are meant to feed a
future finite Gaussian/Pfaffian expansion without hiding the orientation
convention in an opaque decision procedure.

**Honest scope.** This is finite exterior-algebra coefficient bookkeeping for
the toy top-density seed.  It does not construct a Gaussian Berezin integral,
fermionic covariance, determinant/Pfaffian formula, physical supersymmetry,
Yang-Mills activity bound, `hRpoly`, continuum limit, or OS/Wightman
reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 179 (2026-06-20, **finite Berezin coefficient-sum expansion**
`YangMills.SUSY.finiteBerezinEmptyCoeff_one`,
`YangMills.SUSY.finiteBerezinTop_sum_basis_eq_if_mem`,
`YangMills.SUSY.finiteBerezinEmptyCoeff_sum_basis_eq_if_mem`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_sum_basis_eq_coeffs_of_pos`,
`YangMills.SUSY.finiteBerezinWeighted_sum_basis_mul_sum_basis`;
core 8284)

This addendum lifts the finite Berezin monomial calculus to finite coefficient
expansions.

* `finiteBerezinTop` applied to a finite exterior-basis sum selects the
  coefficient of the top monomial if it is present in the finite index set, and
  gives zero otherwise.
* `finiteBerezinEmptyCoeff` does the same for the empty monomial; the same
  functional also sends the algebra unit to one.
* In positive fermionic dimension, the elementary top-density weight
  `1 + a • topBasis` applied to a finite basis sum is exactly
  `top coefficient + a * empty coefficient`.
* For any algebraic weight, the weighted finite Berezin integral of the product
  of two finite basis sums expands bilinearly as the double sum of the weighted
  monomial-product integrals.

These theorems are intended as the finite-sum bridge between the existing
sign-exposed monomial rules and a later tiny Gaussian/Pfaffian toy expansion.

**Honest scope.** This is still finite exterior-algebra coefficient
bookkeeping.  It does not construct a Gaussian Berezin integral, fermionic
covariance, determinant/Pfaffian formula, physical supersymmetry, Yang-Mills
activity bound, `hRpoly`, continuum limit, or OS/Wightman reconstruction.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 180 (2026-06-20, **disjoint-support filter for finite Berezin sums**
`YangMills.SUSY.finiteBerezinWeighted_basis_mul_of_not_disjoint`,
`YangMills.SUSY.finiteBerezinWeighted_sum_basis_mul_sum_basis_filter_disjoint`,
`YangMills.SUSY.finiteBerezinWeighted_topWeight_sum_basis_mul_sum_basis_filter_disjoint`;
core 8284)

This addendum combines the previous bilinear finite-sum expansion with
Grassmann nilpotence.

* Products of exterior-basis monomials with overlapping generator support
  integrate to zero against any algebraic Berezin weight.
* Therefore the weighted Berezin integral of a product of two finite
  exterior-basis sums can be rewritten as a double sum filtered by
  `Disjoint s t`.
* The same filtered form is exposed for the elementary top-density weight.

This is the next mechanical bridge toward finite Gaussian/Pfaffian toy
expansions: coefficient sums can now discard repeated-generator pairs before
the surviving disjoint monomial terms are handed to the sign/top-degree rules.

**Honest scope.** This is finite exterior-algebra bookkeeping.  It does not
construct a Gaussian Berezin integral, fermionic covariance,
determinant/Pfaffian formula, physical supersymmetry, Yang-Mills activity
bound, `hRpoly`, continuum limit, or OS/Wightman reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 181 (2026-06-20, **single-support Appendix-F target-gas Fubini closure**
`YangMills.RG.appendixFConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq`,
`YangMills.RG.sum_appendixFAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies`,
`YangMills.RG.sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies`,
`YangMills.RG.prod_one_add_eq_appendixFTargetPolymerSystem_partition`,
`YangMills.RG.complex_exp_sum_eq_appendixFTargetPolymerSystem_partition`;
core 8287)

This addendum closes the exact finite target-family Fubini/lumping identity
for the single-support Appendix-F compiler in
`YangMills/RG/AppendixFFiniteCover.lean`.

The new dependent left-inverse theorem proves that erasing a target choice to
its selected connected-cover family and reconstructing the target-choice datum
recovers the original choice, under the explicit active-nonempty hypothesis.
The proof uses the already-verified injectivity of the cover-union map on an
admissible connected-cover family and a small private transport lemma for
membership-indexed finite functions.

The new sum identity
`sum_appendixFAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies`
then reindexes the explicit finite choice domain by admissible connected-cover
families.  Composed with the product-over-fibers expansion, this gives
`sum_admissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies`.
Finally,
`prod_one_add_eq_appendixFTargetPolymerSystem_partition` identifies the
single-support target hard-core gas partition with the raw finite Mayer
product, and
`complex_exp_sum_eq_appendixFTargetPolymerSystem_partition` records the
exponential specialization.

Verification:

```
lake env lean YangMills\RG\AppendixFFiniteCover.lean
lake build YangMillsCore
lake env lean oracle_check.lean
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is the finite first Mayer/Appendix-F target identity
for the case where the same support map controls Ω-connectivity and target
unions.  It does not yet prove the two-support holes adapter
`overlapSupport = skeleton`, `targetSupport = full union`, `activePart =
skeleton`; it does not prove the metric bound (642), define or integrate
`K#`, construct the second Ursell activity `H#`, prove the Yang-Mills raw
activity estimate, discharge `hRpoly`, construct a continuum limit, or affect
OS/Wightman/Clay obligations.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 182 (2026-06-20, **source-faithful Appendix-F hole target geometry**
`YangMills.RG.appendixFHoleCoverUnion_skeleton`,
`YangMills.RG.appendixFHoleFullCoverUnion_nonempty`,
`YangMills.RG.appendixFHoleCoverUnion_cubeConnected`,
`YangMills.RG.appendixFHoleCoverUnion_polymerWithHoles`,
`YangMills.RG.appendixFHoleTargetRegion_cubeConnected`,
`YangMills.RG.appendixFHoleTargetRegion_polymerWithHoles`,
`YangMills.RG.appendixFHoleTargetRegion_skeleton_nonempty`,
`YangMills.RG.appendixFHoleTargetRegion_toOmegaPolymer`,
`YangMills.RG.appendixFHoleCoverUnion_injective_on_admissibleConnectedCoverFamily`,
`YangMills.RG.appendixFHoleCoverUnion_image_card_eq`;
core 8288)

This addendum adds `YangMills/RG/AppendixFHoleTarget.lean`, the first finite
two-support bridge for the concrete `omegaHolePolymerSystem` carrier.

The new module proves that the skeleton of a full connected-cover union is
exactly the connected-cover union of the active skeletons:

```
skeleton HF (appendixFCoverUnion (fun X => X.val) C)
  = appendixFCoverUnion (fun X => skeleton HF X.val) C
```

It also proves that every connected cover has a nonempty full target, that
representable full targets are cube-connected, respect the hole family, and
have nonempty active skeleton, and packages them back as `OmegaPolymerType`.
Most importantly for the forthcoming two-support Fubini theorem, an
admissible family whose disjointness is only active-skeleton disjointness
cannot contain two distinct connected covers with the same full target union.
The map from connected covers to full targets is therefore `Set.InjOn` on the
admissible family, and its image preserves cardinality.

Verification:

```
lake build YangMills.RG.AppendixFHoleTarget
lake env lean YangMillsCore.lean
lake env lean oracle_check.lean
lake build YangMillsCore
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite target geometry for the source-faithful
two-support holes adapter.  It does not yet prove the full two-support
target-choice Fubini/lumping identity, the metric inequality (641), the
activity bound (642), ultralocal integration (643)--(644), the second
Ursell/logarithmic expansion (645)--(646), the Yang-Mills raw activity
estimate, `hRpoly`, a continuum limit, or any Clay/OS/Wightman statement.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 183 (2026-06-20, **source-faithful two-support Appendix-F
target-family Fubini closure**
`YangMills.RG.appendixFHoleTargetChoiceCoverFamily_mem_admissible`,
`YangMills.RG.appendixFHoleConnectedCoverFamilyTargetChoiceSigma_targetChoiceCoverFamily_eq`,
`YangMills.RG.sum_appendixFHoleAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies`,
`YangMills.RG.sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies`,
`YangMills.RG.prod_one_add_eq_sum_appendixFHoleAdmissibleTargetFamilies`,
`YangMills.RG.complex_exp_sum_eq_sum_appendixFHoleAdmissibleTargetFamilies`;
core 8289)

This addendum adds `YangMills/RG/AppendixFHoleTargetFamily.lean`, the exact
finite two-support target-family compiler for `omegaHolePolymerSystem`.

The new module uses active skeletons for the Appendix-F compatibility relation
and full hole-polymer unions for target fibers:

```
overlapSupport X = skeleton HF X.val
targetSupport  X = X.val
activePart     Y = skeleton HF Y
```

It defines the connected Mayer activity by full target `Y`, admissible
full-target families whose active skeletons are pairwise disjoint, and the
dependent target-choice domain.  The main proof shows that erasing a target
choice to its selected connected-cover family and then reconstructing the
canonical full-target choice is a dependent left inverse, relying on the
full-target injectivity theorem from Addendum 182.  Conversely, reconstructing
from an admissible connected-cover family and erasing returns the original
family.

Consequently, the explicit finite choice sum is reindexed by admissible
connected-cover families:

```
sum_appendixFHoleAdmissibleTargetChoices_eq_sum_admissibleConnectedCoverFamilies
```

Composing this with the product-over-fibers expansion gives the two-support
target-family identity
`sum_appendixFHoleAdmissibleTargetFamilies_prod_connectedMayerActivity_eq_sum_admissibleConnectedCoverFamilies`.
Finally, the finite raw Mayer product is recovered as
`prod_one_add_eq_sum_appendixFHoleAdmissibleTargetFamilies`, with the
exponential specialization
`complex_exp_sum_eq_sum_appendixFHoleAdmissibleTargetFamilies`.

Verification:

```
lake env lean YangMills\RG\AppendixFHoleTargetFamily.lean
lake build YangMills.RG.AppendixFHoleTargetFamily
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This closes the finite Appendix-F target-family
Fubini/lumping step for the concrete with-holes carrier.  It still does not
prove the metric inequality (641), the activity bound (642), ultralocal
integration to `K#`, the second Ursell/logarithmic expansion to `H#`, the
Yang-Mills raw activity estimate, `hRpoly`, a continuum limit, or any
Clay/OS/Wightman statement.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 184 (2026-06-20, **finite Appendix-F first-activity metric majorant**
`YangMills.RG.norm_appendixFComponentWeight_expSubOne_le_metricProduct`,
`YangMills.RG.norm_appendixFConnectedActivity_le_metricProductCoverSum`,
`YangMills.RG.appendixF_metricProduct_eq_metricCoverWeight`,
`YangMills.RG.norm_appendixFConnectedActivity_le_metricCoverSum`,
`YangMills.RG.norm_appendixFHoleConnectedMayerActivity_expSubOne_le_metricCoverSum`;
core 8290)

This addendum adds `YangMills/RG/AppendixFQuantitative.lean`, the first finite
quantitative layer above the Appendix-F target-family compiler.

The new theorem
`norm_appendixFComponentWeight_expSubOne_le_metricProduct` proves the one-cover
product estimate: if each raw term satisfies

```
‖h i‖ ≤ H0 * Real.exp (-κ * metric i)
```

with `0 ≤ H0`, `H0 ≤ 1`, and `0 ≤ κ`, then the raw Mayer product
`∏ i ∈ C, (exp (h i) - 1)` is bounded by the product of the factorwise weights
`∏ i ∈ C, 2H0 * exp(-κ metric i)`.  The proof uses the already-verified
small raw-Mayer inequality `‖exp z - 1‖ ≤ 2‖z‖` and no source-specific
constant.

The finite first-activity theorem
`norm_appendixFConnectedActivity_le_metricCoverSum` then applies the triangle
inequality over the target fiber and collapses the product weights to

```
Σ C in appendixFTargetFiber Ω overlapSupport targetSupport Λ Y,
  (2 * H0) ^ C.card * Real.exp (-κ * Σ i ∈ C, metric i).
```

The source-facing specialization
`norm_appendixFHoleConnectedMayerActivity_expSubOne_le_metricCoverSum` applies
the same bound to the with-holes carrier: active skeletons control
Ω-connectivity, while full hole-polymer unions control the target fiber.

Verification:

```
lake env lean YangMills\RG\AppendixFQuantitative.lean
lake build YangMills.RG.AppendixFQuantitative
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This proves a finite triangle/product-norm majorant for the
first connected activity `K(Y)`.  The right-hand side is still the explicit
finite sum over connected covers.  This does not prove Dimock's metric
inequality (641), the activity bound (642), connected-cover entropy, the
ultralocal integration to `K#`, the second Ursell/logarithmic expansion to
`H#`, the Yang-Mills raw activity estimate, `hRpoly`, a continuum limit, or any
Clay/OS/Wightman statement.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 185 (2026-06-20, **finite Appendix-F pinned first-activity localization**
`YangMills.RG.appendixFMetricCoverWeight_nonneg`,
`YangMills.RG.appendixFTargetMetricCoverSum_le_pinnedMetricCoverSum`,
`YangMills.RG.norm_appendixFConnectedActivity_le_pinnedMetricCoverSum`,
`YangMills.RG.appendixFHoleTargetMetricCoverSum_le_pinnedMetricCoverSum`,
`YangMills.RG.norm_appendixFHoleConnectedMayerActivity_expSubOne_le_pinnedMetricCoverSum`;
core 8290)

This addendum extends `YangMills/RG/AppendixFQuantitative.lean` with the finite
localization bridge immediately after Addendum 184's metric-cover majorant.

The new definitions package the repeated right-hand sides:

* `appendixFMetricCoverWeight metric H0 κ C`
* `appendixFTargetMetricCoverSum Ω overlapSupport targetSupport Λ metric Y H0 κ`
* `appendixFPinnedMetricCoverSum Ω overlapSupport targetSupport Λ metric r H0 κ`

The pinned sum ranges over all connected raw covers containing at least one
raw target support through the chosen site `r`.  The finite theorem
`appendixFTargetMetricCoverSum_le_pinnedMetricCoverSum` proves the elementary
but important local-influence step: if `r ∈ Y`, every cover in the target
fiber over `Y` contributes to the pinned cover domain, since its target union
is exactly `Y`.  The proof uses only finite set inclusion plus positivity of
the metric cover weight.

Composing this localization with Addendum 184 gives
`norm_appendixFConnectedActivity_le_pinnedMetricCoverSum`, and the source-facing
with-holes theorem
`norm_appendixFHoleConnectedMayerActivity_expSubOne_le_pinnedMetricCoverSum`.
For `omegaHolePolymerSystem`, this says: active skeletons control
Ω-connectivity, full hole-polymer unions control targets, and any pin `r ∈ Y`
dominates the first activity by a local pinned connected-cover sum through
`r`.

Verification:

```
lake env lean YangMills\RG\AppendixFQuantitative.lean
lake build YangMills.RG.AppendixFQuantitative
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is still finite localization, not Dimock's analytic
estimate.  It does not bound the pinned connected-cover sum by a closed
constant or by `exp(-c d_M(Y))`; it does not prove metric inequality (641),
activity bound (642), connected-cover entropy, `K#`, `H#`, Yang-Mills raw
activity, `hRpoly`, continuum limit, or OS/Wightman reconstruction.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 186 (2026-06-20, **finite Appendix-F with-holes metric stitching**
`YangMills.RG.discreteModifiedMetric_add_one_le_card_of_spanning_set`,
`YangMills.RG.appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum`,
`YangMills.RG.appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum`;
core 8290)

This addendum extends `YangMills/RG/AppendixFQuantitative.lean` with the finite
geometric stitching step for the source-facing Appendix-F with-holes carrier.

The reusable variational lemma
`discreteModifiedMetric_add_one_le_card_of_spanning_set` proves that any finite
connected set `S` spanning the active skeleton of a full polymer `X` bounds the
repository's modified metric:

```
discreteModifiedMetric HF X + 1 ≤ S.card.
```

The main cover theorem
`appendixFHoleCoverUnion_discreteModifiedMetric_add_one_le_sum` applies this
to an active-skeleton connected cover of `OmegaPolymerType` polymers.  For each
raw polymer it chooses a minimal connected skeleton-spanning set, then uses the
already-proved `walk_union_connected` transport along the Appendix-F
Ω-overlap graph to show that the union of those spanning sets is connected.
Together with subadditivity of finite-cardinality under `biUnion`, this gives
the finite shifted metric inequality

```
d_M(⋃ full targets, mod holes) + 1
  ≤ Σ_X (d_M(X, mod holes) + 1).
```

The fiber theorem
`appendixFHoleTargetFiber_discreteModifiedMetric_add_one_le_sum` rewrites the
full target union as the target `Y`, yielding the exact source-facing form

```
d_M(Y, mod holes) + 1
  ≤ Σ_{X in C} (d_M(X, mod holes) + 1)
```

for every `C ∈ appendixFTargetFiber` built from active skeletons and full
hole-polymer targets.

Verification:

```
lake env lean YangMills\RG\AppendixFQuantitative.lean
lake build YangMills.RG.AppendixFQuantitative
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This closes the finite geometric part of Dimock-style
metric stitching for the repository's discrete modified metric and the
active-skeleton/full-target split.  It does not prove connected-cover entropy,
does not sum the target-fiber majorant, does not prove activity bound (642),
does not construct `K#` or `H#`, does not prove the Yang-Mills raw activity
estimate, and does not discharge `hRpoly` or any continuum/Clay/OS/Wightman
statement.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 187 (2026-06-20, **adversarial Dimock-Balaban source-claim
audit**; documentation only; core 8290)

This addendum adds `docs/SOURCE-CLAIM-AUDIT.md` and cross-links it from
`CURRENT-STATE.md`, `docs/BALABAN-SOURCE-BOUNDS.md`,
`HYPOTHESIS_FRONTIER.md`, and `README-FOR-NEXT-MODEL.md`.

The audit records contradicted source attributions, the replacement
Dimock-facing statements, the still-pending Balaban extraction queue, and the
provenance fields required before any source statement may be promoted from
`source-pending` to source-verified input.  It is intentionally adversarial:
source extraction is not a Lean proof, scalar `phi^4_3` constants are not
Yang-Mills constants, and polymer-local Balaban bounds are not a scalar
`hRpoly` theorem until the exact support/activity bridge is built.

No Lean theorem was added, no oracle entry changed, no build-job increase is
claimed, and no source-pending Balaban statement was promoted.  The live P3
frontier is now stated as: theorem-fed finite metric stitching in the source
shape of (641), followed by the open connected-cover summation to (642),
`K#`, `H#`, and the final loss.  P4 remains the concrete Yang-Mills raw
activity estimate for the actual gauge RG operator.

Verification:

```
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The oracle output remains
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is documentation and source discipline only.  It closes
no analytic estimate, does not prove activity bound (642), does not construct
`K#` or `H#`, does not prove `hRpoly`, and does not affect the continuum/Clay
frontier.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 188 (2026-06-20, **finite-stencil locality for the scaled
averaging operator**
`YangMills.RG.fineLineSupport`, `YangMills.RG.linAvgSupport`,
`YangMills.RG.linAvg_congr_of_eqOn_support`,
`YangMills.RG.scaledLinAvgCLM_congr_of_eqOn_support`; core 8290)

This addendum closes the next safe part of the averaging-adjoint frontier.  The
linear RG averaging operator `Q` already had its pointwise locality theorem in
quantified form.  This checkpoint names the finite stencils explicitly:

* `fineLineSupport L N' μ x`, the `L` positively-oriented fine bonds read by a
  line integral from `x` in direction `μ`;
* `linAvgSupport L N' c`, the finite block/line stencil read by `linAvg` at
  coarse bond `c`.

The new theorem `linAvg_congr_of_eqOn_support` packages locality as agreement
on that finite stencil.  `scaledLinAvgCLM_congr_of_eqOn_support` lifts the same
finite-stencil locality to the Hilbert-space operator used to form
`qMassCLM = Q†Q`, keeping the scalar normalization `s` explicit.

Verification:

```
lake env lean YangMills\RG\LinearAveraging.lean
lake build YangMills.RG.AveragingAdjoint
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This proves finite-input locality for `Q` and for the scaled
Hilbert-space averaging map.  It does not yet expose an explicit kernel for the
adjoint, does not prove finite-range support for `Q†Q`, does not prove gauge
Hessian coercivity, and does not discharge `hRpoly` or any continuum/Clay
statement.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 189 (2026-06-20, **finite Gaussian block collar normalization**
`YangMills.RG.gaussianBlockKernel`,
`YangMills.RG.gaussianBlockTransform`,
`YangMills.RG.gaussianBlockKernel_isProbability`,
`YangMills.RG.gaussianBlockTransform_isProbability`; core 8291)

This addendum adds `YangMills/RG/GaussianBlockKernel.lean`, a small
measure-theoretic brick for the Balaban/Appendix-F route.  For a continuous
linear averaging map `Q`, a fluctuation law `γ`, and a coarse field `A`, the
conditional block law is the translate of `γ` by `Q A`.  The full finite block
transform samples `A ∼ μ` and `ξ ∼ γ` independently and pushes the product
measure forward by `(A, ξ) ↦ Q A + ξ`.

The new theorem-fed facts are:

* `gaussianBlockKernel_isProbability`: a translated probability fluctuation law
  is still a probability conditional block kernel;
* `gaussianBlockTransform_isProbability`: the finite product block transform is
  a probability measure when both input laws are probability measures.

Verification:

```
lake env lean YangMills\RG\GaussianBlockKernel.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is normalization infrastructure for a finite Gaussian
collar.  It does not prove Gaussianity of the translated conditional kernel,
does not compute or bound its covariance, does not prove finite-range support
for `Q†Q`, does not instantiate Balaban's fluctuation Hessian, does not prove
Dimock's activity bound (642), and does not affect any continuum/Clay theorem.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 190 (2026-06-20, **finite Gaussian collar Gaussian closure**
`YangMills.RG.gaussianBlockCLM`,
`YangMills.RG.gaussianBlockKernel_isGaussian`,
`YangMills.RG.gaussianBlockTransform_isGaussian`; core 8291)

This addendum strengthens `YangMills/RG/GaussianBlockKernel.lean` without
adding analytic assumptions.  The finite block map
`(coarse field, fluctuation) |-> Q coarse field + fluctuation` is now exposed
as the continuous linear map `gaussianBlockCLM Q`, and the block transform is
defined as the pushforward along this map.

The new theorem-fed facts are:

* `gaussianBlockKernel_isGaussian`: if the fluctuation law is Gaussian, then
  every translated conditional block kernel is Gaussian;
* `gaussianBlockTransform_isGaussian`: if the coarse law and fluctuation law
  are Gaussian, then their independent finite block transform is Gaussian.

The proof uses Mathlib's existing Gaussian closure under translation, product
measures, and continuous linear maps.  No source constants or Yang-Mills
normalizations are introduced.

Verification:

```
lake env lean YangMills\RG\GaussianBlockKernel.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This proves Gaussian closure of the finite collar, not a
covariance formula or decay estimate.  It does not compute covariance, does not
prove a Schur/Combes-Thomas bound, does not expose finite-range support for
`Q†Q`, does not instantiate Balaban's fluctuation Hessian, does not prove
Dimock's activity bound (642), and does not affect any continuum/Clay theorem.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 191 (2026-06-20, **Appendix-F first integrated activity Ksharp**
`YangMills.RG.LocalActivity.finsetSum`,
`YangMills.RG.LocalActivity.integrateFluctuation`,
`YangMills.RG.appendixFHoleConnectedLocalActivity`,
`YangMills.RG.appendixFHoleKsharp`,
`YangMills.RG.norm_appendixFHoleKsharp_globalEval_le`; core 8292)

This addendum follows the latest Appendix-F strategy handoff by introducing the
first defined `K -> K#` layer before attempting the second polymer gas.

The type-local substrate now has:

* `LocalActivity.finsetSum`, a finite sum of local activities whose spectator
  and fluctuation supports are the corresponding finite support unions;
* `LocalActivity.integrateFluctuation`, integrating the fluctuation field
  against the ultralocal product measure to produce a spectator-field
  `LocalFunctional`;
* `LocalActivity.norm_globalEval_integrateFluctuation_le_of_norm_le`, carrying
  an explicit `Integrable` hypothesis and proving that a uniform pointwise
  bound transfers through the probability integral.

The new module `YangMills/RG/AppendixFKsharp.lean` defines
`appendixFHoleConnectedLocalActivity`, the type-local version of the already
proved scalar connected target-fiber activity.  Its evaluation theorem states
that global evaluation is exactly
`appendixFHoleConnectedMayerActivity` with the pointwise raw Mayer factors
`exp (H X) - 1`.  The module then defines
`appendixFHoleKsharp` as the fluctuation integral of this local activity and
proves `norm_appendixFHoleKsharp_globalEval_le`.

Verification:

```
lake build YangMills.RG.AppendixFKsharp
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint defines and verifies the finite first
integrated activity object `K#`.  It does not yet prove the n-ary target-family
integration factorization (Dimock (643)), the second hard-core target gas,
the Ursell-defined `H#`, the connected-cover entropy estimate behind (642), or
any concrete Yang-Mills raw activity decay.  It also does not change the
continuum, OS/Wightman, or Clay obligations.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 192 (2026-06-20, **Appendix-F target-fiber entropy overcount**
`YangMills.RG.skeleton_mono_of_subset`,
`YangMills.RG.appendixFTargetFiber_subset_nonemptyPowerset`,
`YangMills.RG.sum_powerset_erase_empty_prod_le_exp_sub_one`,
`YangMills.RG.appendixFTargetFiber_prod_le_exp_sub_one`; core 8293)

This addendum adds `YangMills/RG/AppendixFFiberEntropy.lean`, the finite
combinatorial entropy step immediately after the Appendix-F connected-activity
majorant and metric stitching.

The new module proves:

* skeleton monotonicity under full-polymer inclusion;
* every target fiber is contained in the nonempty powerset of raw indices whose
  full target support is contained in the target `Y`;
* the elementary nonempty-powerset product bound
  `sum prod <= exp (sum weights) - 1`;
* the target-fiber version
  `appendixFTargetFiber_prod_le_exp_sub_one`.

This is the certified finite form of the "forget connectedness/exact-union
constraints and exponentiate the remaining raw-index sum" step.  It is meant
to feed the later local modified-metric summability estimate for `K(Y)`.

Verification:

```
lake env lean YangMills\RG\AppendixFFiberEntropy.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint is finite combinatorial entropy only.  It
does not prove the closed Dimock (642) activity estimate, the `B0`
modified-metric local summability adapter, ultralocal integration/factorization
for `K#`, the second target gas and Ursell expansion to `H#`, or a concrete
Yang-Mills raw activity bound.  It also does not change the continuum,
OS/Wightman, or Clay obligations.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 193 (2026-06-20, **Residual with-holes cluster bridge to hpoly**
`YangMills.RG.polymerClusterResidualRate_nonneg_of_three_mul_add_le`,
`YangMills.RG.kappa0_le_polymerClusterResidualRate_of_four_mul_add_le`,
`YangMills.RG.polymerClusterWithHoles_abs_tsum_le`,
`YangMills.RG.singleScaleUVDecay_of_clusterWithHolesActivities`; core 8294)

This addendum adds `YangMills/RG/PolymerClusterWithHolesBridge.lean`, the
quantitative bookkeeping bridge from a residual Appendix-F with-holes activity
estimate to the existing scalar `hpoly` / `SingleScaleUVDecay` consumer.

The new module defines the residual rate

```
polymerClusterResidualRate κ κ₀ = κ - 3 * κ₀ - 3
```

and records the important margin distinction:

* `κ ≥ 3κ₀ + 3` proves only nonnegative residual decay;
* reusing a geometric summability estimate at exponent `κ₀` requires
  `κ₀ ≤ κ - 3κ₀ - 3`, for instance the stronger source-side condition
  `κ ≥ 4κ₀ + 3`.

It proves the static aggregate theorem
`polymerClusterWithHoles_abs_tsum_le`: a pointwise residual bound
`|H#(Y)| <= C H₀ exp (-(κ - 3κ₀ - 3) d(Y))`, together with
`Σ exp (-κ₀ d(Y)) <= K₀`, implies `Σ |H#(Y)| <= C H₀ K₀` under the explicit
margin `κ₀ <= κ - 3κ₀ - 3`.  It also proves
`singleScaleUVDecay_of_clusterWithHolesActivities`, feeding the same residual
activity estimate directly into the already verified `SingleScaleUVDecay`
interface.

Verification:

```
lake env lean YangMills\RG\PolymerClusterWithHolesBridge.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint does not prove the with-holes expansion, the
Dimock (642) bound, ultralocal integration to `K#`, the second Ursell
expansion to `H#`, any concrete Yang-Mills fluctuation estimate, or the
continuum/OS reconstruction.  It only exposes the exact residual decay margin
needed to reuse the existing geometric summability substrate.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 194 (2026-06-20, **Concrete rooted residual bridge over the
modified metric** `YangMills.RG.exp_neg_kappa0_nat_eq_exp_neg_pow`,
`YangMills.RG.rooted_exp_discreteModifiedMetric_tsum_le`,
`YangMills.RG.rooted_polymerClusterWithHoles_abs_tsum_le`; core 8294)

This addendum extends `YangMills/RG/PolymerClusterWithHolesBridge.lean` from an
abstract metric bridge to a concrete rooted with-holes polymer bridge over the
already verified modified-metric summability theorem.

The new adapter proves the exact translation

```
exp (-(κ₀ * n)) = exp (-κ₀)^n
```

and applies it to the existing theorem
`discreteModifiedMetric_weight_summable` with `q = exp (-κ₀)`.  The resulting
bound is

```
Σ_{X : r ∈ skeleton X} exp (-κ₀ * (d_M(X)+1))
  ≤ (1 - ((3^d)^2) * (exp(-κ₀) * 2^(3^d+1)))⁻¹
```

under the existing hole-disjointness/no-cross-edge/nonempty-hole hypotheses and
the explicit coordination smallness condition
`((3^d)^2) * (exp(-κ₀) * 2^(3^d+1)) < 1`.

The final theorem
`rooted_polymerClusterWithHoles_abs_tsum_le` combines this concrete
summability with the residual margin bridge.  It is the direct rooted
`hpoly`-style aggregate estimate for activities satisfying the concrete
residual modified-metric pointwise bound.

Verification:

```
lake env lean YangMills\RG\PolymerClusterWithHolesBridge.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is still a rooted summability/aggregation adapter.  It
does not prove the analytic residual pointwise estimate, Dimock (642), the
integrated `K#` estimates, the second Ursell expansion to `H#`, or any
continuum/OS/Clay theorem.  It does, however, connect the residual bridge to
the repo's actual modified-metric polymer summability theorem instead of an
abstract `K₀` hypothesis.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 195 (2026-06-20, **OmegaPolymerType residual bridge**
`YangMills.RG.omegaRootedPolymerEquiv`,
`YangMills.RG.omega_rooted_exp_discreteModifiedMetric_tsum_le`,
`YangMills.RG.omega_rooted_polymerClusterWithHoles_abs_tsum_le`; core 8294)

This addendum extends `YangMills/RG/PolymerClusterWithHolesBridge.lean` one
step closer to the Appendix-F consumer by lifting the rooted modified-metric
bridge from the plain concrete subtype

```
{X : Finset (Cube d L) // r ∈ skeleton H X ∧ cubeConnected X ∧ polymerWithHoles H X}
```

to the source-facing active polymer subtype

```
{P : OmegaPolymerType H z // r ∈ skeleton H P.val}.
```

The reusable equivalence `omegaRootedPolymerEquiv` records that the only extra
field in `OmegaPolymerType` is nonempty skeleton, supplied by the root
membership hypothesis.  The theorem
`omega_rooted_exp_discreteModifiedMetric_tsum_le` transports the concrete
summability bound to the `OmegaPolymerType` index shape, and
`omega_rooted_polymerClusterWithHoles_abs_tsum_le` applies the residual
with-holes bridge directly to rooted active Appendix-F polymers.

Verification:

```
lake env lean YangMills\RG\PolymerClusterWithHolesBridge.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is still a type/index adapter plus summation theorem.
It does not prove the residual pointwise bound, Dimock (642), the integrated
`K#` estimate, the second Ursell expansion to `H#`, any Yang-Mills fluctuation
estimate, or any continuum/OS/Clay theorem.  It removes one local impedance
mismatch between the finite Appendix-F polymer type and the residual `hpoly`
bridge.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 196 (2026-06-20, **omega-rooted scalar UV producer**
`YangMills.RG.singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities_four_mul_margin`;
core 8294)

This addendum finishes the immediate consumer-facing adapter after Addendum
195.  The rooted `OmegaPolymerType` residual bridge now feeds the scalar
`SingleScaleUVDecay` predicate consumed by the UV mass-gap assembly.

The theorem
`singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities` takes a
scale-indexed rooted omega-pinned activity family

```
Hsharp : ℕ → ℕ → {P : OmegaPolymerType H z // r ∈ skeleton H P.val} → ℝ
```

together with the residual Appendix-F decay bound in the concrete modified
metric

```
d_M(P.val.val, holes) + 1
```

and the already-proved rooted geometric summability assumptions.  If

```
Rsc t k = ∑' P, Hsharp t k P,
```

then the scalar consumer receives

```
SingleScaleUVDecay Rsc g
  ((C * H₀) *
    (1 - ((3^d)^2) * (exp(-κ₀) * 2^(3^d+1)))⁻¹)
  c₀ κ₀.
```

The companion
`singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities_four_mul_margin`
packages the sufficient margin `κ ≥ 4κ₀ + 3`, using the previously verified
residual inequality `κ₀ ≤ κ - 3κ₀ - 3`.

Verification:

```
lake env lean YangMills\RG\PolymerClusterWithHolesBridge.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is still an adapter theorem: it does not prove the
residual pointwise `Hsharp` estimate, Dimock (642), the integrated `K#`
bound, the second Ursell expansion to `H#`, or any continuum construction.
It closes the formal route from an already-supplied omega-rooted residual
activity estimate to the scalar UV hypothesis.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 197 (2026-06-20, **Appendix-F local summability adapter**
`YangMills.RG.appendixFHole_rootedFiniteExpWeightSum_le`,
`YangMills.RG.appendixFHole_containedWeightSum_le_metric_mul_of_rooted`;
core 8295)

This addendum follows the dependency-order audit recommending that the first
`K#` estimate be preceded by a local modified-metric summability adapter,
rather than by the final residual `H#` bridge.  A new module
`YangMills/RG/AppendixFLocalSummability.lean` defines

```
appendixFHoleExpWeight HF κ X = exp (-(κ * (d_M(X, holes) + 1)))
appendixFKsharpRate κ κ₀ = κ - κ₀ - 2
```

The theorem `appendixFHole_rootedFiniteExpWeightSum_le` restricts the
existing rooted omega modified-metric summability theorem to any finite raw
family `Λ`.

The theorem `appendixFHole_containedWeightSum_le_metric_mul_of_rooted`
converts rooted control

```
Σ_{X ∈ Λ, r ∈ skeleton X} w(X) ≤ K₀
```

into target-contained control

```
Σ_{X ∈ Λ, X.val ⊆ Y} w(X) ≤ (d_M(Y) + 1) K₀
```

for representable Appendix-F full targets `Y`.  The proof overcounts through
roots in `skeleton HF Y`, uses `sum_biUnion_le`, and closes the root count with
`skeleton_card_le_discreteModifiedMetric_add_one`.  The local nonnegativity
hypothesis remains only on `X ∈ Λ`; internally the proof uses a zero extension
off `Λ` to reuse the existing global nonnegativity summation lemma.

Verification:

```
lake env lean YangMills\RG\AppendixFLocalSummability.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is the first preparatory local-summability brick for
the `K(Y)`/`K#` estimate.  It does not prove the pointwise raw activity decay,
the exact exponential-minus-one `K(Y)` estimate, Dimock (642), the
factorization (643), the second Ursell expansion, or any continuum theorem.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 198 (2026-06-20, **source-shaped exact first K# estimate**
`YangMills.RG.norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne`,
`YangMills.RG.norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay`,
`YangMills.RG.norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted`;
core 8296)

This addendum adds `YangMills/RG/AppendixFKsharpEstimate.lean`, the first
source-shaped `K(Y)`/`K#` estimate after the local summability adapter.

The pointwise theorem
`norm_appendixFHoleConnectedLocalActivity_globalEval_le_expSubOne` combines
the existing finite ingredients:

```
raw metric decay
+ target-fiber entropy
+ with-holes metric stitching
+ target-contained local summability
```

to prove the exact nonlinear first-activity bound

```
‖K(Y, ψ, φ)‖
  ≤ exp(-(κ-κ₀)(d_M(Y)+1))
      * (exp(2 H₀ K₀ (d_M(Y)+1)) - 1).
```

The integrated theorem
`norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay` transfers
the same bound to `K#(Y, ψ)` through the already verified probability-integral
bridge, with the `Integrable` hypothesis still explicit.  The rooted variant
`norm_appendixFHoleKsharp_globalEval_le_expSubOne_of_rawMetricDecay_rooted`
derives the contained-support local estimate from rooted modified-metric
summability.

Verification:

```
lake env lean YangMills\RG\AppendixFKsharpEstimate.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This closes the exact finite nonlinear `K(Y)`/`K#` estimate
but deliberately does not prove the linearized `κ - κ₀ - 2` corollary, Dimock
(643) target-family factorization, the second hard-core target gas, the final
`H#` residual rate `κ - 3κ₀ - 3`, the concrete Yang-Mills raw activity decay,
or any continuum/Clay theorem.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 199 (2026-06-20, **second Appendix-F hard-core gas from evaluated K#**
`YangMills.RG.appendixFHoleSecondGas_activity`,
`YangMills.RG.appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion`,
`YangMills.RG.appendixFHoleSecondGas_KPCriterion_of_majorant`; core 8297)

This addendum adds `YangMills/RG/AppendixFSecondGas.lean`, the structural
second-gas layer after the first integrated activity `K#`.

The new evaluated activity
`appendixFHoleSecondGasActivity HF z Λ Hraw μ ψ Y` is definitionally
`(appendixFHoleKsharp HF z Λ Hraw μ Y).globalEval ψ`, and
`appendixFHoleSecondGas` instantiates that scalar activity through the
source-facing `omegaHolePolymerSystem`.  The theorem
`appendixFHoleSecondGas_activity` exposes this projection on the carrier, and
`appendixFHoleSecondGasActivity_eq_zero_of_not_mem_targetRegion` proves that
nonrepresentable first-stage targets have zero activity.

The KP entry point is intentionally not called Dimock (642):
`AppendixFHoleSecondGasKPMajorant` includes the exact tilt and full-cardinality
factor required by the current `omegaHolePolymerSystem` KP consumer.  The
theorem `appendixFHoleSecondGas_KPCriterion_of_majorant` then applies
`omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`
directly under the explicit geometry, smallness, and pointwise-majorant
hypotheses.

Verification:

```
lake env lean YangMills\RG\AppendixFSecondGas.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This exposes the second hard-core gas object and its
existing KP consumer, but it does not prove the source-to-majorant conversion,
Dimock (642), the ultralocal product factorization (643), the Ursell-defined
`H#`, the residual rate `κ - 3κ₀ - 3`, the concrete Yang-Mills raw activity
decay, or any continuum/Clay theorem.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 200 (2026-06-20, **union-fiber second Ursell object H#**
`YangMills.RG.appendixFHoleHsharpTerm_eq_sum_filter`,
`YangMills.RG.appendixFHoleHsharpTerm_eq_zero_of_no_union`,
`YangMills.RG.sum_appendixFHoleHsharpTerm_eq_clusterSum_term`,
`YangMills.RG.appendixFHoleHsharpOfKsharp_eq`; core 8298)

This addendum adds `YangMills/RG/AppendixFHsharp.lean`, the definition-level
second Ursell layer after the second Appendix-F gas.

The fixed-size term `appendixFHoleHsharpTerm HF zK Y n` is the
`1/(n+1)!` Ursell monomial sum over tuples of second-gas polymers whose full
`omegaClusterUnion` is exactly the target `Y`.  The total object
`appendixFHoleHsharp HF zK Y` is the corresponding totalized `tsum` over
`n`, and `appendixFHoleHsharpOfKsharp` feeds in the evaluated `K#` activity
from `appendixFHoleSecondGasActivity`.

The finite theorem `appendixFHoleHsharpTerm_eq_sum_filter` rewrites the
`if`-guarded term as an explicit fiber sum.  The theorem
`appendixFHoleHsharpTerm_eq_zero_of_no_union` closes empty fibers.  The main
finite bookkeeping identity
`sum_appendixFHoleHsharpTerm_eq_clusterSum_term` proves that summing a fixed
cluster-size term over every target `Y` recovers exactly the matching
fixed-size term in the ordinary KP `clusterSum` for the second gas.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharp.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This defines `H#` and proves finite union-fiber
bookkeeping at each fixed cluster size.  It does not prove convergence of the
outer `tsum`, justify exchanging the target sum with that `tsum`, identify a
second-gas partition logarithm, prove Dimock's residual estimate
`κ - 3κ₀ - 3`, extract a real scalar remainder, prove a concrete Yang-Mills
activity bound, or establish any continuum/Clay theorem.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 201 (2026-06-20, **residual H# adapter to UV decay**
`YangMills.RG.clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le`,
`YangMills.RG.rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_four_mul_margin`;
core 8299)

This addendum adds `YangMills/RG/AppendixFHsharpResidual.lean`, the bridge from
a source-supplied residual estimate on the complex second-Ursell object `H#`
to the existing real scalar UV-decay consumer.

The theorem
`clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharp_le` states that if
`‖appendixFHoleHsharp HF (zK t k) Y‖` satisfies the residual bound with rate
`κ - 3κ₀ - 3`, then any real extraction `toReal` with
`|toReal w| <= ‖w‖` satisfies the real-valued
`ClusterWithHolesActivityDecay` predicate.  The rooted variant matches the
index type used by the omega-rooted modified-metric summability theorem.

The theorem `singleScaleUVDecay_of_omegaRootedAppendixFHsharp` composes that
real extraction with
`singleScaleUVDecay_of_omegaRootedClusterWithHolesActivities`, obtaining
`SingleScaleUVDecay` for scalar remainders of the form
`Rsc t k = ∑' P, toReal (appendixFHoleHsharp HF (zK t k) P)`, under the explicit
residual domination condition `κ₀ <= κ - 3κ₀ - 3`.  The theorem
`singleScaleUVDecay_of_omegaRootedAppendixFHsharp_four_mul_margin` supplies the
source-facing sufficient margin `κ >= 4κ₀ + 3`.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpResidual.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is an adapter only.  It does not prove convergence of
the `H#` `tsum`, Dimock's residual estimate, the analytic KP/Ursell loss
behind `κ - 3κ₀ - 3`, the physical real projection, a concrete Yang-Mills raw
activity estimate, or any continuum/Clay theorem.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 202 (2026-06-20, **real/imaginary H# scalar projections**
`YangMills.RG.complex_re_contracts_norm`,
`YangMills.RG.complex_im_contracts_norm`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_im_four_mul_margin`;
core 8299)

This addendum extends `YangMills/RG/AppendixFHsharpResidual.lean` with concrete
scalar projections for the residual `H#` adapter.

The theorems `complex_re_contracts_norm` and `complex_im_contracts_norm`
record the elementary contractions `|Complex.re w| <= ‖w‖` and
`|Complex.im w| <= ‖w‖`.  The real-part specializations
`singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re` and
`singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin` now feed
`Rsc t k = ∑' P, Complex.re (appendixFHoleHsharp HF (zK t k) P)` directly into
the scalar `SingleScaleUVDecay` consumer.  The corresponding imaginary-part
specializations are also available for auditing complex remainders.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpResidual.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This chooses no new physical semantics.  It proves that the
ordinary real and imaginary coordinate projections are contractive and can
therefore instantiate the already verified residual adapter.  If the final
physical scalar projection is not literally `Complex.re`, it still needs its
own definition and contraction theorem.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 203 (2026-06-20, **finite partial H# truncations**
`YangMills.RG.appendixFHoleHsharpPartial_zero`,
`YangMills.RG.appendixFHoleHsharpPartial_succ`,
`YangMills.RG.sum_appendixFHoleHsharpPartial_eq_sum_clusterSum_terms`,
`YangMills.RG.clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le`,
`YangMills.RG.rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_le`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_four_mul_margin`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_re`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpPartial_re_four_mul_margin`;
core 8300)

This addendum adds `YangMills/RG/AppendixFHsharpPartial.lean`, the finite
cutoff version of the Appendix-F second Ursell layer.

The definition `appendixFHoleHsharpPartial HF zK N Y` is the finite sum of
`appendixFHoleHsharpTerm HF zK Y n` over `n < N`.  The lemmas
`appendixFHoleHsharpPartial_zero` and `appendixFHoleHsharpPartial_succ`
record the cutoff recursion.  The theorem
`sum_appendixFHoleHsharpPartial_eq_sum_clusterSum_terms` proves the finite
target-lumping identity: summing this partial `H#` over all target unions is
exactly the finite sum of the matching fixed-size ordinary KP cluster-sum
terms.

The residual-adapter half mirrors the totalized `H#` bridge.  A source-supplied
complex-norm estimate on the finite partial object feeds
`ClusterWithHolesActivityDecay`, then the omega-rooted
`SingleScaleUVDecay` producer, with the usual explicit residual domination
`κ₀ <= κ - 3κ₀ - 3` or sufficient margin `κ >= 4κ₀ + 3`.  Real-part
specializations are provided for the canonical scalar projection.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpPartial.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite staging only.  It does not prove convergence
of the finite partial activities to the totalized `appendixFHoleHsharp`, does
not justify exchange with an infinite target/cluster-size sum, does not prove
Dimock's residual estimate, and does not establish any continuum/Clay theorem.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 204 (2026-06-20, **finite partial H# convergence interface**
`YangMills.RG.appendixFHoleHsharpPartial_tendsto`,
`YangMills.RG.norm_appendixFHoleHsharp_le_of_partial_bound`,
`YangMills.RG.clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_limit_le`,
`YangMills.RG.rooted_clusterWithHolesActivityDecay_of_norm_appendixFHoleHsharpPartial_limit_le`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_of_partial_bounds_four_mul_margin`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_of_partial_bounds`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_of_partial_bounds_four_mul_margin`;
core 8301)

This addendum adds `YangMills/RG/AppendixFHsharpConvergence.lean`, the
contract layer between finite `H#` truncations and the totalized second Ursell
activity.

The theorem `appendixFHoleHsharpPartial_tendsto` proves that, for a fixed
target `Y`, summability of
`n ↦ appendixFHoleHsharpTerm HF zK Y n` implies convergence of the finite
partial activities to `appendixFHoleHsharp HF zK Y`.  The theorem
`norm_appendixFHoleHsharp_le_of_partial_bound` then passes any residual
complex-norm estimate uniform in the finite cutoff `N` to the totalized `H#`
by `le_of_tendsto'`.

The remaining theorems package that limit passage into the existing residual
adapters: totalized `ClusterWithHolesActivityDecay`, the rooted version, the
omega-rooted `SingleScaleUVDecay` producer, the sufficient source margin
`κ >= 4κ₀ + 3`, and the real-part specialization.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpConvergence.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is not Dimock (642) and not a convergence proof from
source estimates.  It only states the exact consumer contract: once fixed-target
summability and uniform finite-partial residual estimates are supplied, the
previous totalized `H#` residual adapter is theorem-fed.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 205 (2026-06-20, **finite partial H# tail error interface**
`YangMills.RG.appendixFHoleHsharp_eq_partial_add_tail`,
`YangMills.RG.appendixFHoleHsharp_sub_partial_tendsto_zero`,
`YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_tail_norm_tsum`,
`YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_of_tail_norm_bound`;
core 8301)

This addendum extends `YangMills/RG/AppendixFHsharpConvergence.lean` with the
tail/Cauchy form of the finite-to-total `H#` interface.

The theorem `appendixFHoleHsharp_eq_partial_add_tail` proves the exact
decomposition

```
appendixFHoleHsharp HF zK Y
  = appendixFHoleHsharpPartial HF zK N Y
    + ∑' i, appendixFHoleHsharpTerm HF zK Y (i + N).
```

The theorem `appendixFHoleHsharp_sub_partial_tendsto_zero` records that the
finite truncation error tends to zero under the fixed-target summability
hypothesis.  The quantitative theorem
`norm_appendixFHoleHsharp_sub_partial_le_tail_norm_tsum` bounds the truncation
error by the shifted norm-tail sum, and
`norm_appendixFHoleHsharp_sub_partial_le_of_tail_norm_bound` packages the same
statement when the source analysis has already supplied an explicit scalar
tail bound.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpConvergence.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This does not prove the source-side fixed-target
summability or any quantitative decay of the second-Ursell tail.  It names the
exact tail object and the norm inequality that future KP/Ursell estimates must
feed before one can claim a source proof of the residual bound.  Dimock (642),
the `κ - 3κ₀ - 3` analytic loss, concrete Yang-Mills raw activity decay,
continuum construction, and Clay remain open.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 206 (2026-06-20, **pointwise H# limit transfer**
`YangMills.RG.tendsto_appendixFHoleHsharpPartial_of_summable`,
`YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_partial_limit`,
`YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_summable_terms`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_partial_limit`;
core 8302)

This addendum adds `YangMills/RG/AppendixFHsharpLimit.lean`, the pointwise
limit-transfer API for finite second-Ursell `H#` truncations.

The theorem `tendsto_appendixFHoleHsharpPartial_of_summable` records the
fixed-target convergence consequence of an explicit
`Summable (fun n => appendixFHoleHsharpTerm HF zK Y n)` hypothesis.  The
theorem `norm_appendixFHoleHsharp_le_residual_of_partial_limit` keeps the
analytic convergence premise even more explicit: if the finite partials
converge pointwise to the repository's totalized `appendixFHoleHsharp`, and if
the finite partials satisfy a residual norm estimate uniformly in the cutoff,
then the same residual estimate holds for total `H#`.  The proof is the
minimal order-theoretic limit transfer by `le_of_tendsto'`.

The summability version
`norm_appendixFHoleHsharp_le_residual_of_summable_terms` feeds the fixed-target
summability theorem into that pointwise limit transfer.  The UV theorem
`singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_partial_limit`
then applies the existing total `H#` real-part residual consumer after the
pointwise bound is obtained.  No limit is passed through the outer rooted
polymer `tsum`, so the future dominated-convergence/majorant obligation remains
localized to the second-Ursell source proof.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpLimit.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is still a contract interface, not the analytic source
estimate.  In the Dimock II numbering, the final `H#` destination is the
Theorem F.1 estimate recorded as (636), while (642) is the preceding `K/K#`
estimate feeding the second gas.  This module proves neither source estimate,
nor the second-Ursell majorant, nor any continuum/Clay theorem.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 207 (2026-06-20, **termwise H# majorant interface**
`YangMills.RG.summable_appendixFHoleHsharpTerm_of_norm_le_majorant`,
`YangMills.RG.norm_appendixFHoleHsharpPartial_le_majorant_sum`,
`YangMills.RG.appendixFHoleHsharp_tail_norm_tsum_le_majorant_tail`,
`YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_majorant_tail`,
`YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_term_majorant`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_term_majorant`;
core 8303)

This addendum adds `YangMills/RG/AppendixFHsharpMajorant.lean`, the explicit
termwise-majorant contract for the second-Ursell `H#` layer.

The theorem `summable_appendixFHoleHsharpTerm_of_norm_le_majorant` proves that
a summable real majorant of
`‖appendixFHoleHsharpTerm HF zK Y n‖` gives fixed-target summability of the
complex `H#` term sequence.  The theorem
`norm_appendixFHoleHsharpPartial_le_majorant_sum` bounds finite `H#` partials
by the corresponding finite majorant sums.  The theorems
`appendixFHoleHsharp_tail_norm_tsum_le_majorant_tail` and
`norm_appendixFHoleHsharp_sub_partial_le_majorant_tail` package the shifted-tail
obligation: the truncation error is bounded by the shifted tail of the same
majorant.

The theorem `norm_appendixFHoleHsharp_le_residual_of_term_majorant` is the
source-facing bridge: if the termwise majorant is summable and its finite sums
obey the residual profile, then the totalized `appendixFHoleHsharp` satisfies
the pointwise residual estimate.  The real-part theorem
`singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_term_majorant`
feeds that contract into the existing omega-rooted UV consumer.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpMajorant.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This module does not prove the analytic second-Ursell
majorant.  It only identifies the exact Lean shape a source proof must supply
to discharge fixed-target summability, finite-partial residual bounds, and
tail estimates.  The source `H#` estimate (Dimock II Theorem F.1/(636)), the
preceding `K/K#` estimate (642), concrete Yang-Mills raw activity decay,
continuum construction, and Clay remain open.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 208 (2026-06-20, **closed-form geometric H# majorants**
`YangMills.RG.sum_range_le_tsum_of_nonneg`,
`YangMills.RG.summable_geometric_majorant`,
`YangMills.RG.tsum_geometric_majorant`,
`YangMills.RG.sum_range_geometric_majorant_le_closed`,
`YangMills.RG.tsum_geometric_majorant_tail`,
`YangMills.RG.norm_appendixFHoleHsharp_sub_partial_le_geometric_tail`,
`YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_geometric_term_majorant`;
core 8304)

This addendum adds `YangMills/RG/AppendixFHsharpGeometricMajorant.lean`, the
closed-form geometric specialization of the termwise `H#` majorant interface.

The preliminary theorem `sum_range_le_tsum_of_nonneg` records the elementary
order fact that finite partial sums of a nonnegative summable real sequence are
bounded by the total `tsum`.  The theorems `summable_geometric_majorant` and
`tsum_geometric_majorant` package Mathlib's geometric series for the profile
`A * q^n` under `0 <= q < 1`, while
`sum_range_geometric_majorant_le_closed` bounds every finite partial sum by
`A * (1 - q)⁻¹` when `0 <= A`.  The theorem
`tsum_geometric_majorant_tail` gives the shifted-tail identity
`∑' i, A*q^(i+N) = A*q^N*(1-q)⁻¹`.

The `H#` theorem `norm_appendixFHoleHsharp_sub_partial_le_geometric_tail`
turns a termwise bound
`‖appendixFHoleHsharpTerm ... n‖ <= A*q^n` into the closed shifted-tail error
bound.  The theorem
`norm_appendixFHoleHsharp_le_residual_of_geometric_term_majorant` says that if
the closed total `A*(1-q)⁻¹` is below the residual profile, then total
`appendixFHoleHsharp` satisfies the pointwise residual estimate.  The real-part
omega-rooted theorem then feeds that geometric majorant contract into the
existing UV consumer under the sufficient margin `κ >= 4κ₀ + 3`.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpGeometricMajorant.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This module does not prove that Dimock's second-Ursell/KP
analysis supplies an `A,q` geometric majorant.  It only discharges the
geometric-series bookkeeping once such a majorant has been proved externally or
in a later source-facing module.  The source `H#` estimate (Dimock II Theorem
F.1/(636)), the preceding `K/K#` estimate (642), concrete Yang-Mills raw
activity decay, continuum construction, and Clay remain open.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 209 (2026-06-20, **packaged geometric H# majorant profiles**
`YangMills.RG.AppendixFHsharpGeometricMajorantProfile.summable_terms`,
`YangMills.RG.AppendixFHsharpGeometricMajorantProfile.tail_bound`,
`YangMills.RG.AppendixFHsharpGeometricMajorantProfile.residual_bound`,
`YangMills.RG.AppendixFHsharpGeometricMajorantProfile.singleScaleUVDecay_of_profile`;
core 8305)

This addendum adds `YangMills/RG/AppendixFHsharpProfile.lean`, a
source-facing record for the closed-form geometric `H#` majorant contract.

The new structure `AppendixFHsharpGeometricMajorantProfile` packages the data a
future second-Ursell/KP source proof should provide: amplitudes `A`, ratios
`q`, the hypotheses `0 <= A`, `0 <= q < 1`, the termwise estimate
`‖appendixFHoleHsharpTerm ... n‖ <= A*q^n`, and the comparison of the closed
total `A*(1-q)⁻¹` with the residual profile.  The profile theorems expose the
already-verified consequences from one object: fixed-target summability,
closed shifted-tail control for finite truncations, the total pointwise
residual bound, and the omega-rooted real-part `SingleScaleUVDecay` consumer
under the sufficient margin `κ >= 4κ₀ + 3`.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpProfile.lean
lake --rehash build YangMills.RG.UltralocalFactorization
lake build YangMillsCore
lake env lean YangMillsCore.lean
lake --rehash build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The first full build attempt exposed a stale/missing
local `.olean` for `UltralocalFactorization` in this public worker checkout;
refreshing that dependency and then rebuilding the root target fixed the cache
state.  The first oracle attempt timed out at 304s with no Lean error; after
the root target was refreshed, the long oracle run completed and the new
entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is a packaging layer only.  It does not prove the
geometric majorant, the second-Ursell/KP estimate, Dimock II Theorem F.1/(636),
Dimock (642), concrete Yang-Mills raw activity decay, continuum construction,
or Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 210 (2026-06-20, **fixed-target H# summability from sharp KP**
`YangMills.RG.norm_appendixFHoleHsharpTerm_le_clusterWeight`,
`YangMills.RG.summable_appendixFHoleHsharpTerm_of_sizeMajorant`,
`YangMills.RG.summable_appendixFHoleHsharpTerm_of_KPCriterion`,
`YangMills.RG.norm_appendixFHoleHsharpPartial_le_residual_of_sizeMajorant`,
`YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_sizeMajorant`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_sizeMajorant`;
core 8305)

This addendum strengthens `YangMills/RG/AppendixFHsharpMajorant.lean` at the
exact finite interface between the Appendix-F `H#` target fibers and the
already-formalized sharp KP cluster-weight theorem.

The theorem `norm_appendixFHoleHsharpTerm_le_clusterWeight` proves that a
fixed-target exact-union term
`appendixFHoleHsharpTerm HF zK Y n` is bounded by the global absolute
per-size cluster weight `KP.clusterWeight (omegaHolePolymerSystem HF zK) n`.
Consequently, `summable_appendixFHoleHsharpTerm_of_KPCriterion` combines that
finite fiber bound with `KP.kp_clusterWeight_summable_sharp` to obtain
fixed-target summability directly from `KP.KPCriterion`.

The new size-majorant residual consumers accept a target-sensitive scalar
majorant `M t k P n` whose total `tsum` is already bounded by the desired
residual profile.  They then produce finite-partial residual bounds, total
pointwise `H#` residual bounds, and the omega-rooted real-part
`SingleScaleUVDecay` consumer under the sufficient margin
`κ >= 4κ₀ + 3`.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpMajorant.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** The KP consequence is fixed-target summability only: the
global `clusterWeight` has forgotten the target `Y`, so it does not prove the
target-sensitive residual profile needed for Dimock F.1/(636).  The
size-majorant theorems are consumers for a future source proof of that
target-sensitive bound, not the proof itself.  Dimock (642), concrete
Yang-Mills raw activity decay, continuum construction, and Clay remain open.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 211 (2026-06-20, **source-facing absolute H# majorant bridge**
`YangMills.RG.appendixFHoleHsharpAbsTerm`,
`YangMills.RG.norm_appendixFHoleHsharpTerm_le_absTerm`,
`YangMills.RG.AppendixFHsharpSourceMajorant`,
`YangMills.RG.appendixFHsharpSourceMajorant_of_absTerm_geometric`,
`YangMills.RG.appendixFHsharpSourceMajorant_of_factorized_absTerm_geometric`,
`YangMills.RG.AppendixFHsharpSourceMajorant.summable_terms`,
`YangMills.RG.AppendixFHsharpSourceMajorant.tail_bound`,
`YangMills.RG.AppendixFHsharpSourceMajorant.residual_bound`,
`YangMills.RG.norm_appendixFHoleHsharp_le_residual_of_source_majorant`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharp_re_four_mul_margin_of_source_majorant`;
core 8306)

This addendum adds `YangMills/RG/AppendixFHsharpSourceMajorant.lean`, the
source-facing absolute finite-sum bridge for the Appendix-F second-Ursell
`H#` layer.

The definition `appendixFHoleHsharpAbsTerm` is the nonnegative fixed-union
counterpart of `appendixFHoleHsharpTerm`: it keeps the same finite
`1/(n+1)!` Ursell fiber over tuples whose `omegaClusterUnion` is the target
`Y`, but replaces the complex summand by
`|ursell(X)| * prod_i ‖activity(X_i)‖`.  The theorem
`norm_appendixFHoleHsharpTerm_le_absTerm` is pure finite triangle inequality.

The structure `AppendixFHsharpSourceMajorant` packages the exact geometric
contract expected from a later source proof: amplitudes `A`, ratios `q`,
positivity, `q < 1`, a termwise bound
`‖appendixFHoleHsharpTerm ... n‖ <= A*q^n`, and the closed residual comparison.
The constructor `appendixFHsharpSourceMajorant_of_absTerm_geometric` turns an
estimate on the absolute finite term into that contract.  The constructor
`appendixFHsharpSourceMajorant_of_factorized_absTerm_geometric` records the
preferred source shape, with target geometry isolated as
`exp(-r * (d_M(P)+1))` and order decay as `rho(t,k)^n`.  The namespace theorems
`AppendixFHsharpSourceMajorant.summable_terms`,
`AppendixFHsharpSourceMajorant.tail_bound`, and
`AppendixFHsharpSourceMajorant.residual_bound` expose fixed-target summability,
closed shifted-tail control, and the pointwise residual estimate from the
packaged source object.  The final two global theorems feed the same contract
into the existing total residual and omega-rooted real-part `SingleScaleUVDecay`
consumers.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpSourceMajorant.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is still a finite bridge and source-contract package.
It does not prove the absolute fixed-union geometric estimate, the
second-Ursell/tree/KP source theorem, Dimock F.1/(636), Dimock (642),
concrete Yang-Mills raw activity decay, continuum construction, or Clay.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 212 (2026-06-20, **support containment for the first Appendix-F Ksharp layer**
`YangMills.RG.appendixFHoleConnectedLocalActivity_spectatorSupport_subset`,
`YangMills.RG.appendixFHoleConnectedLocalActivity_fluctuationSupport_subset`,
`YangMills.RG.appendixFHoleKsharp_support_subset`; core 8306)

This addendum strengthens `YangMills/RG/AppendixFKsharp.lean`, the finite
`K(Y) -> K#(Y)` object layer.

The two new local-activity theorems prove the finite support bridge that had
previously been an explicit obligation around the Appendix-F factorization
layer: if each raw local activity indexed by `X ∈ Λ` has spectator support
contained in the full source polymer `X.val`, then the connected first
activity over a target union `Y` has spectator support contained in `Y`; and
the analogous statement holds for fluctuation support.  The proof uses only
the target-fiber equality
`appendixFCoverUnion (fun X => X.val) C = Y` and the finite fact that every
index contributing to that fiber lies in `Λ`.

The third theorem transfers the spectator-support statement through
`appendixFHoleKsharp`: after integrating the fluctuation field, the resulting
spectator `LocalFunctional` has support contained in the same target union
`Y`.

Verification:

```
lake env lean YangMills\RG\AppendixFKsharp.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite support bookkeeping for the already-defined
first activity.  It does not prove ultralocal factorization (643) for the full
target-family sum, Dimock (642), the second-Ursell/tree estimate, concrete
Yang-Mills raw activity decay, continuum construction, or Clay.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 213 (2026-06-20, **finite Hsharp second-Ursell tree majorant**
`YangMills.RG.appendixFHoleHsharpTreeTerm`,
`YangMills.RG.appendixFHoleHsharpAbsTerm_le_treeTerm`; core 8307)

This addendum adds `YangMills/RG/AppendixFSecondUrsellSource.lean`, the first
source-independent coefficientwise tree step for the Appendix-F second-Ursell
`H#` layer.

The definition `appendixFHoleHsharpTreeTerm` has exactly the same target fiber
and factorial normalization as `appendixFHoleHsharpAbsTerm`, but replaces the
absolute Ursell coefficient by the finite sum over spanning trees of the tuple
incompatibility graph.  The theorem
`appendixFHoleHsharpAbsTerm_le_treeTerm` is a direct finite application of the
already-verified Penrose tree-graph inequality
`KP.abs_ursell_le_card_spanningTrees`, followed by multiplication by the
nonnegative product of activity norms and summation over the fixed-union fiber.

Verification:

```
lake env lean YangMills\RG\AppendixFSecondUrsellSource.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite Penrose domination only.  It does not prove
the Dimock leaf summation, the shifted `K#` estimate (642)/(644), the source
`H#` estimate F.1/(636), the scalar smallness condition, concrete Yang-Mills
raw activity decay, continuum construction, or Clay.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 214 (2026-06-21, **finite admissible Ksharp product factorization**
`YangMills.RG.LocalFunctional.integral_finsetProd_of_pairwise_disjoint_support`,
`YangMills.RG.LocalActivity.integral_finsetProd_of_pairwise_disjoint_fluctuationSupport`,
`YangMills.RG.integral_prod_appendixFHoleConnectedLocalActivity_eq_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton`,
`YangMills.RG.integral_prod_appendixFHoleKsharp_eq_prod_integral_of_admissibleTargetFamilies`;
core 8307)

This addendum strengthens the finite `K -> K#` layer before the source
second-Ursell estimates.

`YangMills/RG/UltralocalFactorization.lean` now has n-ary product-measure
factorization theorems for finite products of `LocalFunctional`s with
pairwise-disjoint supports and finite products of `LocalActivity`s with
pairwise-disjoint fluctuation supports.  These are finite products over an
explicit ultralocal probability measure, not Gaussian covariance estimates.

`YangMills/RG/AppendixFKsharp.lean` now derives active-skeleton support
containment for first connected target activities from source-local
one-polymer support containment.  It then proves two finite admissible-family
factorization adapters:

* a fluctuation-field factorization turning a finite admissible product of
  connected target activities into the product of their integrated `K#(Y)`
  values, when each raw one-polymer fluctuation support lies inside its active
  skeleton;
* a spectator-field factorization for finite products of `K#(Y)` over
  admissible target families, when each raw one-polymer spectator support lies
  inside its active skeleton.

Verification:

```
lake env lean YangMills\RG\UltralocalFactorization.lean
lake env lean YangMills\RG\AppendixFKsharp.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite support/factorization bookkeeping around
Dimock (643)--(644).  It does not prove ultralocal factorization for the
actual Yang-Mills fluctuation measure, the Dimock (642) activity estimate, the
source `H#` estimate F.1/(636), concrete raw activity decay, continuum
construction, or Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 215 (2026-06-21, **finite Appendix-F Ksharp target-family integration**
`YangMills.RG.integral_sum_appendixFHoleConnectedLocalActivity_eq_sum_prod_Ksharp_of_local_fluctuationSupport_subset_skeleton`,
`YangMills.RG.integral_sum_appendixFHoleKsharp_eq_sum_prod_integral_of_admissibleTargetFamilies`;
core 8307)

This addendum closes the finite target-family sum layer on top of Addendum
214's product factorization.

`YangMills/RG/AppendixFKsharp.lean` now proves that the finite sum over
admissible source-facing target families commutes with the first fluctuation
integration and then factors termwise into the corresponding finite `K#`
target-family gas, assuming only per-target-family integrability and the
source-local active-skeleton fluctuation-support bridge.

It also proves the spectator-side finite target-family identity: integrating
the finite `K#` target-family gas under an ultralocal spectator product
measure equals the sum over admissible target families of products of the
single-target spectator integrals, again with per-summand integrability kept
explicit.  This is the finite algebraic/measure-theoretic substrate behind
Dimock (643)--(644), not a quantitative activity estimate.

Verification:

```
lake env lean YangMills\RG\AppendixFKsharp.lean
lake build YangMills.RG.AppendixFKsharp
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite Fubini plus finite ultralocal product
factorization over admissible target families.  It does not prove the
integrability hypotheses for the actual Yang-Mills RG measure, Dimock (642),
the second-Ursell `H#` estimate, concrete raw activity decay, continuum
construction, or Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 216 (2026-06-21, **spectator-integrated Ksharp scalar normalization**
`YangMills.RG.appendixFHoleIntegratedKsharpActivity_eq_integral`,
`YangMills.RG.appendixFHoleIntegratedKsharpActivity_eq_zero_of_not_mem_targetRegion`,
`YangMills.RG.appendixFHoleIntegratedSecondGas_activity`,
`YangMills.RG.integral_sum_appendixFHoleKsharp_eq_sum_prod_integratedKsharpActivity_of_admissibleTargetFamilies`,
`YangMills.RG.appendixFHoleHsharpOfIntegratedKsharp_eq`;
core 8307)

This addendum connects Addendum 215's finite integrated target-family identity
to the scalar activity family consumed by the second `omegaHolePolymerSystem`
and the later `H#` source-majorant layer.

`YangMills/RG/AppendixFSecondGas.lean` now defines
`appendixFHoleIntegratedKsharpActivity`, the scalar target activity obtained by
integrating the local `K#(Y, psi)` functional over the spectator product
measure.  It packages this scalar activity as
`appendixFHoleIntegratedSecondGas`, proves that it vanishes outside the first
connected-cover target region, and rewrites the spectator integral of the
finite `K#` target-family gas as a finite admissible-family sum using this
scalar `z_K` activity.

`YangMills/RG/AppendixFHsharp.lean` now exposes
`appendixFHoleHsharpOfIntegratedKsharp`, the definitional `H#` specialization
obtained by feeding this spectator-integrated scalar `z_K` into the existing
second-Ursell object.

Verification:

```
lake env lean YangMills\RG\AppendixFSecondGas.lean
lake build YangMills.RG.AppendixFSecondGas YangMills.RG.AppendixFHsharp
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is scalar normalization and finite Fubini bookkeeping.
It does not prove the spectator-integrability hypotheses for the concrete
Yang-Mills RG measure, Dimock (642), the source `H#` estimate F.1/(636), any
KP smallness condition, concrete raw activity decay, continuum construction,
or Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 217 (2026-06-21, **integrated Ksharp source-majorant specialization**
`YangMills.RG.appendixFHoleIntegratedKsharpActivityFamily_eq`,
`YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_absTerm_geometric`,
`YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_absTerm_geometric`,
`YangMills.RG.norm_appendixFHoleHsharpOfIntegratedKsharp_le_residual_of_source_majorant`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedAppendixFHsharpOfIntegratedKsharp_re_four_mul_margin_of_source_majorant`;
core 8307)

This addendum connects Addendum 216's spectator-integrated scalar `K#`
normal form to Addendum 211's source-majorant contract.

`YangMills/RG/AppendixFHsharpSourceMajorant.lean` now names the scale-indexed
family

```
zK(t,k,Y) = appendixFHoleIntegratedKsharpActivity HF (z t k) ... Y
```

as `appendixFHoleIntegratedKsharpActivityFamily`.  It then specializes both
source-majorant constructors to this concrete `zK` family: one constructor
from an arbitrary absolute fixed-union geometric estimate, and one from the
preferred factorized form with a modified-metric exponential and a
target-independent cluster-order ratio.

The same module also rewrites the pointwise residual consumer and the
real-part omega-rooted UV consumer for the named object
`appendixFHoleHsharpOfIntegratedKsharp`.  The source proof still must supply
the termwise absolute/tree estimate, positivity, ratio bound, and closed
residual comparison explicitly.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpSourceMajorant.lean
lake build YangMills.RG.AppendixFHsharpSourceMajorant
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is a specialization/adapter layer.  It does not prove
the absolute fixed-union estimate, the Balaban/Dimock second-Ursell leaf
summation, Dimock F.1/(636), Dimock (642), concrete Yang-Mills raw activity
decay, continuum construction, or Clay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 218 (2026-06-21, **tree-term source-majorant constructors**
`YangMills.RG.appendixFHsharpSourceMajorant_of_treeTerm_geometric`,
`YangMills.RG.appendixFHsharpSourceMajorant_of_factorized_treeTerm_geometric`,
`YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_treeTerm_geometric`,
`YangMills.RG.appendixFHsharpSourceMajorant_of_integratedKsharp_factorized_treeTerm_geometric`;
core 8307)

This addendum connects Addendum 212's finite Penrose tree coefficient to
Addendum 217's integrated-`K#` source-majorant normal form.

`YangMills/RG/AppendixFSecondUrsellSource.lean` now proves four constructor
bridges.  The general constructors turn a geometric estimate on the finite
tree term `appendixFHoleHsharpTreeTerm` into an
`AppendixFHsharpSourceMajorant`, either with arbitrary amplitudes `A,q` or
with the preferred factorized modified-metric shape.  The integrated
constructors specialize the same bridge to
`appendixFHoleIntegratedKsharpActivityFamily`.

The proof is purely finite: compose
`appendixFHoleHsharpAbsTerm_le_treeTerm` with the source-supplied tree-term
estimate, then reuse the already verified source-majorant constructors.

Verification:

```
lake env lean YangMills\RG\AppendixFSecondUrsellSource.lean
lake build YangMills.RG.AppendixFSecondUrsellSource
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This commit does not prove the tree-term estimate itself.
It only exposes that as the next exact source obligation.  Dimock's leaf
summation, Dimock F.1/(636), Dimock (642), concrete Yang-Mills raw activity
decay, continuum construction, and Clay remain open.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 219 (2026-06-21, **weighted finite tree transfer**
`YangMills.RG.appendixFHoleHsharpWeightedTreeTerm`,
`YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_nonneg`,
`YangMills.RG.appendixFHoleHsharpWeightedTreeTerm_zero`,
`YangMills.RG.appendixFHoleHsharpTreeTerm_le_scaled_weightedTreeTerm`,
`YangMills.RG.appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_bound`,
`YangMills.RG.appendixFHoleHsharpTreeTerm_le_factorized_of_weighted_geometric`;
core 8315)

This addendum starts the source-faithful decomposition of the missing finite
second-Ursell leaf estimate.

`YangMills/RG/AppendixFSecondUrsellWeightedTree.lean` defines a weighted
fixed-union tree term with the same target fiber and factorial normalization
as `appendixFHoleHsharpTreeTerm`, replacing each activity norm by a supplied
weight `w`.

The main theorem is finite algebra:

```
appendixFHoleHsharpTreeTerm HF zK Y n <=
  epsilon^(n+1) *
    appendixFHoleHsharpWeightedTreeTerm HF zK w Y n
```

under the explicit pointwise hypothesis
`||zK Q.val|| <= epsilon * w Q`.  The exponent is `n+1`, matching the
repository convention that term index `n` uses tuples of size `n + 1`.

The same module now also packages the exact finite reassociation needed by
the source-facing factorized tree constructors:

```
epsilon^(n+1) * (Croot * decay * Cleaf^n)
  =
(Croot * epsilon * decay) * (Cleaf * epsilon)^n.
```

Thus a source theorem may target the weighted tree estimate
`Croot * residualDecay(P) * Cleaf^n`; the Lean side turns it into the
preferred root/leaf factorization under the first-activity size bound.

Verification:

```
lake env lean YangMills\RG\AppendixFSecondUrsellWeightedTree.lean
lake build YangMills.RG.AppendixFSecondUrsellWeightedTree
lake env lean YangMillsCore.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This commit does not prove the weighted tree geometric
estimate, Dimock's leaf summation, the Ksharp source decay, Dimock F.1/(636),
Dimock (642), concrete Yang-Mills raw activity decay, continuum construction,
or Clay.  It only extracts the scalar activity-size factor from the finite
tree term so that the remaining geometric/source estimate has a sharper
Lean-facing target.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 220 (2026-06-21, **CMP116 weighted-tree profile bridge**
`YangMills.RG.balabanCMP116AppendixFHsharpGeometricMajorantProfile_of_weighted_tree_geometric`,
`YangMills.RG.balabanCMP116AppendixFHsharpCluster3Contract_of_weighted_tree_geometric`,
`YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_weighted_tree_geometric`;
core 8315)

This addendum specializes Addendum 219's weighted finite tree transfer to the
CMP116 integrated `K#` family.

`YangMills/RG/BalabanCMP116HsharpSource.lean` now imports the weighted tree
transfer and exposes three source-facing constructors.  The source theorem may
now supply:

```
appendixFHoleHsharpWeightedTreeTerm HF zK w P.val n <=
  Croot(t,k) *
    exp (-(residualRate * (d_M(P)+1))) *
  Cleaf(t,k)^n
```

together with the pointwise first-activity estimate
`||zK Q.val|| <= epsilon(t,k) * w Q`, nonnegativity of the weights and
constants, `Cleaf(t,k) * epsilon(t,k) < 1`, and the closed comparison

```
(Croot(t,k) * epsilon(t,k)) *
  (1 - Cleaf(t,k) * epsilon(t,k))^-1
<= C * H0 * exp (-c0*t) * g(k)^kappa0.
```

The Lean side turns those hypotheses into the existing CMP116 geometric
profile, the closed `cluster3` contract, or the one-shot omega-rooted UV
consumer.  No analytic leaf estimate is proved; it remains the external
CMP116/Dimock source obligation.

Verification:

```
lake env lean YangMills\RG\BalabanCMP116HsharpSource.lean
lake build YangMills.RG.BalabanCMP116HsharpSource
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This commit does not prove the weighted tree estimate, the
first-activity decay, the closed smallness comparison, Dimock's leaf summation,
Dimock F.1/(636), Dimock (642), concrete Yang-Mills raw activity decay,
continuum construction, or Clay.  It only wires the already verified finite
algebra to the CMP116 source endpoints.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 221 (2026-06-21, **CMP116 weighted Hsharp source map**;
documentation only)

This addendum adds `docs/CMP116-WEIGHTED-HSHARP-SOURCE-MAP.md` and updates the
live state to record the current source boundary for the CMP116 weighted
`H#` bridge.

The source map distinguishes three facts that should not be collapsed:

* CMP116, especially (2.4)-(2.11) and Lemma 3/(2.38), is a source-backed
  candidate for the first localized activity estimate after constants,
  supports, and metrics are translated;
* Dimock I Appendix B Step 4 is the printed no-hole mechanism for the
  tree/Ursell leaf summation;
* Dimock II Appendix F theorem `cluster3` is the hole-aware final theorem, but
  it does not print the repository's exact order-wise weighted tree term.

The immediate fork is therefore explicit: either formalize the with-holes
order-wise leaf summation, or expose a direct consumer for Dimock II `cluster3`.
CMP116 alone should not be used as if it proved the weighted `H#` tree
hypothesis.

Verification:

```
git diff --check
git diff --cached --check
lake build YangMillsCore
lake env lean oracle_check.lean
python scripts\check_consistency.py
```

All completed green.  Since this commit changes documentation only, no new Lean
theorem or oracle entry is introduced.

**Honest scope.** This is provenance/control-plane documentation only.  It does
not prove the first-activity estimate, the weighted tree estimate, the closed
smallness comparison, Dimock's leaf summation, Dimock (642), concrete
Yang-Mills raw activity decay, continuum construction, or Clay.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 222 (2026-06-21, **rooted child-order assignments for marked
Hsharp trees**; core 8320)

This addendum strengthens the finite Appendix-F Route-B spine around
`YangMills/RG/AppendixFSecondUrsellMarkedFugacity.lean`.

`YangMills/KP/RootedChildCount.lean` now names the finite type
`rootedChildOrderAssignments T`: an independent permutation of each rooted BFS
child fiber of a tree edge set `T`.  The theorem
`card_rootedChildOrderAssignments` proves that its cardinality is exactly

```
prod_v (rootedChildCount T v)!
```

the factorial product previously used abstractly in the marked-root
second-Ursell majorant.

`AppendixFSecondUrsellMarkedFugacity.lean` now exposes the corresponding
root-marked sum
`appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum`, proves it is equal
to the earlier factorial-product form
`appendixFHoleHsharpWeightedTreeMarkedRootChildFactorSum`, and gives the
direct priced consumer
`appendixFHoleHsharpWeightedTreeMarkedRootChildOrderSum_le_inv_succ_mul_rawSum`.
This turns the child-factorial loss into an actual finite assignment object
that a future leaf-summation map can target.

Verification:

```
lake env lean YangMills\KP\RootedChildCount.lean
lake env lean YangMills\RG\AppendixFSecondUrsellMarkedFugacity.lean
lake build YangMills.RG.AppendixFSecondUrsellMarkedFugacity
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite child-fiber bookkeeping only.  It does not
prove the leaf-summation map, the weighted tree estimate, Dimock F.1/(636),
Dimock (642), concrete Yang-Mills raw activity decay, continuum construction,
OS reconstruction, or Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 223 (2026-06-22, **CMP116 clipped-active-region support constructors**; core 8328)

This addendum adds two finite support constructors for the CMP116 Appendix-F
source package in `YangMills/RG/BalabanCMP116KsharpAdapter.lean`.

`BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_subset_target_inter_omegaRegion`
turns the source-facing inclusion
`F.activeSupport X ⊆ X.val ∩ F.Omega`, together with
`F.Omega = HF.omegaRegion`, into the existing skeleton-locality package.
`BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_eq_target_inter_omegaRegion`
is the equality-form convenience constructor.

Both use the already-proved finite identity
`skeleton HF X.val = X.val ∩ HF.omegaRegion`; they introduce no new analytic
or physical assumption.

Verification:

```
lake env lean YangMills\RG\BalabanCMP116KsharpAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite support bookkeeping only.  It does not prove
CMP116 localization, measurability, raw activity decay, `hR`, large-field-hole
preservation, `hRpoly`, continuum construction, OS/Wightman reconstruction, or
Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 224 (2026-06-22, **CMP116 hard-core graph to Appendix-F skeleton graph**; core 8328)

This addendum extends the CMP116 clipped-active-region adapter in
`YangMills/RG/BalabanCMP116KsharpAdapter.lean`.

Assuming the source-facing equalities `F.Omega = HF.omegaRegion` and
`F.activeSupport X = X.val ∩ F.Omega` on the polymers in `Λ`,
`BalabanCMP116AppendixFSupportHypotheses.zeta_eq_zero_iff_not_disjoint_skeleton_of_activeSupport_eq_target_inter_omegaRegion`
rewrites the CMP116 hard-core condition `F.zeta X Y = 0` as non-disjointness
of the two active skeletons.  The companion theorem
`BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_iff_skeletonOverlapGraph_adj_of_activeSupport_eq_target_inter_omegaRegion`
identifies the CMP116 Ω-overlap graph with the Appendix-F skeleton-overlap
graph on those polymers.

Verification:

```
lake env lean YangMills\RG\BalabanCMP116KsharpAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite hard-core graph bookkeeping only.  It does not
prove the source equality for the localized CMP116 domain, CMP116 localization,
measurability, raw activity decay, `hR`, large-field-hole preservation,
`hRpoly`, continuum construction, OS/Wightman reconstruction, or Clay.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 225 (2026-06-22, **CMP116 one-way hard-core graph adapter from support inclusion**; core 8328)

This addendum adds the inclusion-form version of the CMP116 hard-core graph
adapter in `YangMills/RG/BalabanCMP116KsharpAdapter.lean`.

`BalabanCMP116AppendixFSupportHypotheses.zeta_eq_zero_imp_not_disjoint_skeleton_of_activeSupport_subset_target_inter_omegaRegion`
shows that, if `F.Omega = HF.omegaRegion` and
`F.activeSupport X ⊆ X.val ∩ F.Omega`, then a CMP116 hard-core overlap
`F.zeta X Y = 0` implies non-disjointness of the Appendix-F active skeletons.
The companion
`BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_activeSupport_subset_target_inter_omegaRegion`
maps CMP116 Ω-overlap graph edges into Appendix-F skeleton-overlap graph edges
under the same inclusion hypotheses.

Verification:

```
lake env lean YangMills\RG\BalabanCMP116KsharpAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

All completed green.  The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is finite graph/support bookkeeping only.  It does not
prove the reverse graph implication, the equality form of the localized CMP116
domain, CMP116 localization, measurability, raw activity decay, `hR`,
large-field-hole preservation, `hRpoly`, continuum construction,
OS/Wightman reconstruction, or Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 226 (2026-06-22, **CMP116 source-map audit for localized support**; docs only)

This addendum updates `docs/CMP116-WEIGHTED-HSHARP-SOURCE-MAP.md` and
`docs/SOURCE-CLAIM-AUDIT.md` after the support and hard-core graph adapters
through commit `9a160b67`.

The source map now records the latest Lean consumers:
`BalabanCMP116AppendixFSupportHypotheses.of_activeSupport_subset_target_inter_omegaRegion`,
`BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_activeSupport_subset_target_inter_omegaRegion`,
and
`singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_sourceMeasurable`.

The audit also records the local OCR verdict around CMP116 (2.5)--(2.11) and
Lemma 3/(2.38): the paper supports the product-Gaussian change of variables,
the localized activity `H(Z)`, component factorization, hard-core `zeta`, and
the Lemma 3 decay estimate, but the printed statement that `H(Z)` is localized
in the interior of `Z` is not yet the exact Lean support theorem
`F.activeSupport X subset X.val inter F.Omega` or
`F.activeSupport X subset skeleton HF X.val`.  The remaining source packet must
identify the enlargement convention, hole/large-field compatibility, and the
map from Balaban's localization domains to `OmegaPolymerType` support fields.

Verification:

```
git diff --check
python scripts\check_consistency.py
lake build YangMillsCore
lake env lean oracle_check.lean
```

**Honest scope.** This is documentation/audit work only.  It corrects the live
source map and prevents the CMP116 phrase "localized in the interior of Z" from
being overread as a formal support theorem.  It does not prove CMP116
localization, measurability, raw activity decay, `hR`, large-field-hole
preservation, `hRpoly`, continuum construction, OS/Wightman reconstruction, or
Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 227 (2026-06-22, **current state checkpoint refresh**; docs only)

This addendum updates `CURRENT-STATE.md` after the public checkpoint
`a9d1ebb2d649f9c96819474d1241f8da562e9b4a`.

The top-level certified checkpoint and core job count now match the latest
verified public main: `lake build YangMillsCore` is green at 8328 jobs.  The
RG substrate summary also records the current source-facing CMP116 endpoint
`singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_canonicalRoot_halfBudget_of_sourceMeasurable`
and repeats the precise source boundary: CMP116 (2.5)--(2.11) and Lemma
3/(2.38) support the product-Gaussian change, localized `H(Z)`, hard-core
`zeta`, and decay estimate, but not yet the exact Lean active-support theorem.

Verification:

```
git diff --check
python scripts\check_consistency.py
lake build YangMillsCore
lake env lean oracle_check.lean
```

**Honest scope.** This is a live-state documentation refresh only.  It does not
prove a new Lean theorem, instantiate the CMP116 support hypotheses, discharge
`hraw`, `hR`, `hRpoly`, continuum construction, OS/Wightman reconstruction, or
Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 228 (2026-06-22, **CMP116 graph adapter from support package**; core 8328)

This addendum adds the support-package form of the CMP116 one-way hard-core
graph adapter in `YangMills/RG/BalabanCMP116KsharpAdapter.lean`.

The theorem
`BalabanCMP116AppendixFSupportHypotheses.zeta_eq_zero_imp_not_disjoint_skeleton_of_supportHypotheses`
shows that, once the source has supplied the single support package
`F.activeSupport X subset skeleton HF X.val`, a CMP116 hard-core overlap
`F.zeta X Y = 0` implies non-disjointness of the Appendix-F active skeletons.
The companion theorem
`BalabanCMP116AppendixFSupportHypotheses.omegaGraph_adj_imp_skeletonOverlapGraph_adj_of_supportHypotheses`
maps CMP116 Ω-overlap graph edges into Appendix-F skeleton-overlap graph edges
using only that support package.

This sharpens the previous inclusion-form graph adapter: a source theorem may
now target active-skeleton locality directly, without separately restating
`F.Omega = HF.omegaRegion` and the clipped-region inclusion for the one-way
graph step.

Verification:

```
lake env lean YangMills\RG\BalabanCMP116KsharpAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is finite graph/support bookkeeping only.  It does not
prove the source support package, CMP116 localization, measurability, raw
activity decay, `hR`, large-field-hole preservation, `hRpoly`, continuum
construction, OS/Wightman reconstruction, or Clay.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 229 (2026-06-22, **CMP116 no-cross-edge adapter from support package**; core 8328)

This addendum adds the factorization-facing no-cross-edge direction for the
CMP116 support package in `YangMills/RG/BalabanCMP116KsharpAdapter.lean`.

The theorem
`BalabanCMP116AppendixFSupportHypotheses.zeta_eq_one_of_disjoint_skeleton_of_supportHypotheses`
shows that if two Appendix-F active skeletons are disjoint and the source
active supports are contained in those skeletons, then the CMP116 hard-core
factor is inactive: `F.zeta X Y = 1`.  The companion theorem
`BalabanCMP116AppendixFSupportHypotheses.not_omegaGraph_adj_of_disjoint_skeleton_of_supportHypotheses`
packages this as absence of a CMP116 Ω-overlap graph edge.

This is the no-cross-edge companion to Addendum 228: Addendum 228 maps CMP116
edges into skeleton edges, while this addendum lets skeleton-disjointness rule
out CMP116 edges.  Both remain conditional on the same source support package.

Verification:

```
lake env lean YangMills\RG\BalabanCMP116KsharpAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is finite graph/support bookkeeping for future
factorization use.  It does not prove the source support package, CMP116
localization, measurability, raw activity decay, `hR`, large-field-hole
preservation, `hRpoly`, continuum construction, OS/Wightman reconstruction, or
Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 230 (2026-06-22, **current state source-frontier refresh**; docs only)

This addendum updates the live source-frontier documentation after public
checkpoint `9c2f42c0fc482d51223915b2eacda142dfef97c8`.

`CURRENT-STATE.md` now names `9c2f42c0fc482d51223915b2eacda142dfef97c8` as
the last certified public checkpoint and records the current finite CMP116
hard-core dictionary: under the single source support package
`F.activeSupport X subset skeleton HF X.val`, CMP116 Ω-overlap edges map to
Appendix-F skeleton-overlap edges, and skeleton-disjoint source polymers have
`F.zeta X Y = 1` with no CMP116 Ω-overlap edge.

`docs/CMP116-WEIGHTED-HSHARP-SOURCE-MAP.md` and
`docs/SOURCE-CLAIM-AUDIT.md` now point their live interface notes at
`9c2f42c` rather than older checkpoints.  The refresh also keeps the boundary
explicit: these graph facts are finite consequences of the support package and
do not prove the CMP116 localization theorem that should instantiate the
package.

Verification:

```
git diff --check
python scripts\check_consistency.py
lake build YangMillsCore
lake env lean oracle_check.lean
```

**Honest scope.** This is documentation/audit work only.  It corrects stale
live-state checkpoint references and keeps completed theorem work auditable.  It
does not prove a new Lean theorem, instantiate the CMP116 support package,
discharge `hraw`, `hR`, `hRpoly`, continuum construction, OS/Wightman
reconstruction, or Clay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 231 (2026-06-22, **checkpoint header correction**; docs only)

This addendum corrects a small stale-checkpoint mismatch left after Addendum
230.

`CURRENT-STATE.md` now names
`a901214da57491603d86756a35768d727ebe012e` as the last certified public
checkpoint.  `docs/CMP116-WEIGHTED-HSHARP-SOURCE-MAP.md` distinguishes the
public documentation checkpoint `a901214` from the latest theorem frontier
`9c2f42c`.

Verification:

```
git diff --check
python scripts\check_consistency.py
lake build YangMillsCore
lake env lean oracle_check.lean
```

**Honest scope.** This is documentation/audit work only.  It corrects stale
checkpoint metadata and does not prove a new Lean theorem or discharge any
CMP116/CMP119/CMP122 source obligation.

## Addendum 232 (2026-06-22, **integrated scalar second-gas KP adapter**
`YangMills.RG.AppendixFHoleIntegratedSecondGasKPMajorant`,
`YangMills.RG.appendixFHoleIntegratedSecondGas_KPCriterion_of_majorant`,
`YangMills.RG.BalabanCMP116AppendixFIntegratedSecondGasKPMajorant`,
`YangMills.RG.balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant`;
core 8328)

This addendum gives the spectator-integrated scalar second gas the same
KP-ready interface already available for the evaluated second gas.

`YangMills/RG/AppendixFSecondGas.lean` now defines
`AppendixFHoleIntegratedSecondGasKPMajorant`, the tilted pointwise majorant
for `appendixFHoleIntegratedSecondGas`, and proves
`appendixFHoleIntegratedSecondGas_KPCriterion_of_majorant` by feeding that
majorant into
`omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound`.

`YangMills/RG/BalabanCMP116SecondGasAdapter.lean` exposes the CMP116
specialization
`BalabanCMP116AppendixFIntegratedSecondGasKPMajorant` and
`balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_majorant`, so the
scalar `z_K` carrier produced after spectator integration can be handed
directly to the with-holes KP criterion once a source majorant is supplied.

Verification:

```
lake env lean YangMills\RG\AppendixFSecondGas.lean
lake build YangMills.RG.AppendixFSecondGas
lake env lean YangMills\RG\BalabanCMP116SecondGasAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is a finite consumer adapter only.  It does not prove
Dimock (642), the integrated scalar majorant, the spectator-field law, CMP116
localization, raw activity decay, `hR`, `hRpoly`, continuum construction,
OS/Wightman reconstruction, or Clay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 233 (2026-06-22, **source-bound route to integrated scalar second-gas KP majorant**
`YangMills.RG.appendixFHoleIntegratedSecondGasKPMajorant_of_norm_bound`,
`YangMills.RG.BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source`;
core 8328)

This addendum separates the remaining integrated scalar KP-majorant obligation
into a finite norm-bound transfer and a scalar profile inequality.

`YangMills/RG/AppendixFSecondGas.lean` now proves
`appendixFHoleIntegratedSecondGasKPMajorant_of_norm_bound`: any pointwise norm
bound `B(Y)` for the spectator-integrated scalar second gas gives the KP-ready
majorant as soon as `B` satisfies the already-tilted profile

```
exp t * B(Y) * exp |Y| <= A * q^(d_M(Y)+1).
```

`YangMills/RG/BalabanCMP116SecondGasAdapter.lean` then proves
`BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source`.
It uses the existing source-measurable rooted raw-metric `K#` estimate inside
the first connected target region and the zero-extension theorem outside that
region.  The theorem leaves exactly the final scalar profile comparison as an
explicit hypothesis; no cardinality/constant conversion is hidden.

Verification:

```
lake env lean YangMills\RG\AppendixFSecondGas.lean
lake build YangMills.RG.AppendixFSecondGas
lake env lean YangMills\RG\BalabanCMP116SecondGasAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is a finite proof-assembly adapter for a future source
estimate.  It does not prove the scalar profile inequality, Dimock (642), the
spectator-field law, CMP116 localization, raw activity decay, `hR`, `hRpoly`,
continuum construction, OS/Wightman reconstruction, or Clay.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 234 (2026-06-22, **full-cardinality profile route to integrated second-gas KP**
`YangMills.RG.appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric`,
`YangMills.RG.BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source_of_card_le_metric`,
`YangMills.RG.balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric`;
core 8328)

This addendum splits the scalar `A,q` profile left by Addendum 233 into a
finite exponential-calculus lemma and a source-facing CMP116 consumer.

`YangMills/RG/AppendixFLocalSummability.lean` now proves
`appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric`: if the full
cardinality of a target satisfies

```
|X| <= theta * (d_M(X)+1),
```

then the KP tilt `exp t * exp |X|` can be absorbed into the shifted
modified-metric weight by choosing

```
q = exp (-(rate - theta))
```

and assuming the scalar amplitude comparison `exp t * C <= A`.

`YangMills/RG/BalabanCMP116SecondGasAdapter.lean` now applies this finite lemma
to the spectator-integrated CMP116 second gas.  The majorant wrapper
`BalabanCMP116AppendixFIntegratedSecondGasKPMajorant_of_rawMetricDecay_rooted_of_source_of_card_le_metric`
and the direct KP consumer
`balabanCMP116AppendixFIntegratedSecondGas_KPCriterion_of_rawMetricDecay_rooted_of_source_of_card_le_metric`
combine the source-measurable rooted raw-metric `K#` estimate with the explicit
full-cardinality budget.

Verification:

```
lake env lean YangMills\RG\AppendixFLocalSummability.lean
lake build YangMills.RG.AppendixFLocalSummability
lake env lean YangMills\RG\BalabanCMP116SecondGasAdapter.lean
lake build YangMills.RG.BalabanCMP116SecondGasAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This does not prove the full-cardinality budget; in fact it
makes that missing geometric/source input more visible.  It also does not prove
Dimock (642), CMP116 localization, raw activity decay, spectator-field law,
`hR`, `hRpoly`, continuum construction, OS/Wightman reconstruction, or Clay.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 235 (2026-06-22, **finite full-target cardinality cover-sum budget**
`YangMills.RG.appendixFCoverUnion_card_le_sum`,
`YangMills.RG.appendixFCoverUnion_card_real_le_sum`,
`YangMills.RG.appendixFHoleCoverUnion_card_le_metricSum_of_source_card_le_metric`,
`YangMills.RG.appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric`;
core 8328)

This addendum records the finite cardinality part left exposed by Addendum
234, without claiming the still-missing direct target-metric budget.

`YangMills/RG/AppendixFFiniteCover.lean` now proves the generic overlap-safe
union bound

```
|(appendixFCoverUnion support C)| <= sum_{i in C} |support i|,
```

together with a real-valued cast form for quantitative consumers.

`YangMills/RG/AppendixFQuantitative.lean` specializes this to active
with-holes Appendix-F covers.  If every source polymer in a selected finite
cover obeys

```
|X| <= theta * (d_M(X)+1),
```

then the represented full target satisfies the cover-sum estimate

```
|Y| <= theta * sum_{X in C} (d_M(X)+1).
```

The target-fiber theorem uses only the exact equation
`appendixFCoverUnion (fun X => X.val) C = Y`.

Verification:

```
lake env lean YangMills\RG\AppendixFFiniteCover.lean
lake build YangMills.RG.AppendixFFiniteCover
lake env lean YangMills\RG\AppendixFQuantitative.lean
lake build YangMills.RG.AppendixFQuantitative
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This does not prove the full KP-profile hypothesis
`|Y| <= theta * (d_M(Y)+1)`.  The new theorem gives only the weaker and
source-faithful cover-sum budget; closing the direct target-metric compression
or reformulating the second-gas KP constants remains a source/geometric
obligation.  It also does not prove Dimock (642), CMP116 localization, raw
activity decay, spectator-field law, `hR`, `hRpoly`, continuum construction,
OS/Wightman reconstruction, or Clay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 236 (2026-06-22, **finite Schur-Catalan coercivity budget**
`YangMills.RG.schurCatalanBudget`,
`YangMills.RG.quadraticBudget_sub_finset_le`,
`YangMills.RG.quadraticBudget_sub_finset_pos`,
`YangMills.RG.schurCatalan_lower_bound_of_finset_budget`,
`YangMills.RG.schurCatalan_coercive_of_finset_budget`;
core 8329)

This addendum records the scalar positivity bookkeeping highlighted by the
P4/Riemann comparison note, without turning it into a physical source claim.

`YangMills/RG/SchurCatalanBudget.lean` introduces the scalar envelope

```
(1 - sqrt (1 - 4 * M^2 * epsilon)) / (2 * M)
```

as `schurCatalanBudget`, and proves the finite coercivity principle:
if a base quadratic form dominates `cBase * q v` and each selected finite
multiscale defect is bounded by its scalar budget times `q v`, then the base
minus defects dominates the remaining budget.  In particular,
`schurCatalan_coercive_of_finset_budget` proves strict positivity whenever

```
sum_i schurCatalanBudget (M i) (epsilon i) < cBase
```

and `0 < q v`.

Verification:

```
lake env lean YangMills\RG\SchurCatalanBudget.lean
lake build YangMills.RG.SchurCatalanBudget
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is a finite scalar closure theorem only.  It does not
prove that the Yang--Mills gauge-fixed Hessian is self-adjoint/coercive, does
not prove a Schur-complement self-energy expansion, does not prove propagator
localization, does not prove the R-operation gain, and does not construct or
bound the concrete raw gauge activity.  Those remain exactly the P4
source/geometric obligations.  It also does not prove or use RH.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 237 (2026-06-22, **gauge precision coercivity bookkeeping**
`YangMills.RG.coercive_add_adjointMass_of_blockPoincare`,
`YangMills.RG.coercive_add_qMassCLM_of_blockPoincare`,
`YangMills.RG.coercive_add_perturbation`;
core 8330)

This addendum records the first source-independent P4 coercivity brick prompted
by the spectral/coercivity diagnosis.  The relevant P3 fixed-tree and
target-sensitive `H#` leaf-summation estimates were already present on current
`main`, so this checkpoint moves to the next safe algebraic layer rather than
duplicating the existing leaf-summation route.

`YangMills/RG/GaugePrecision.lean` proves that an explicit block
Poincare/Hodge estimate

```
||x||^2 <= C_P * (<x, K x> + ||Q x||^2)
```

together with positivity of the background quadratic form implies coercivity
of the precision operator

```
K + a * Q†Q
```

with constant

```
min(1,a) / C_P.
```

The theorem `coercive_add_qMassCLM_of_blockPoincare` specializes the abstract
statement to the existing scaled averaging mass `qMassCLM = Q†Q`; the
perturbative closure `coercive_add_perturbation` records the elementary
stability under a quadratic-form defect bounded below by `-delta * ||x||^2`.

Verification:

```
lake env lean YangMills\RG\GaugePrecision.lean
lake build YangMills.RG.GaugePrecision
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is Hilbert-space coercivity algebra only.  It does not
prove the Yang--Mills block Poincare/Hodge theorem, does not identify the
physical gauge-fixed Hessian as `K`, does not prove propagator/covariance
decay, does not construct the raw RG activity, and does not discharge `hRpoly`.
It is designed to be consumed by a future source-backed Hessian/coercivity
packet.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 238 (2026-06-22, **operator-norm coercive perturbation budgets**
`YangMills.RG.IsCoerciveCLM`,
`YangMills.RG.abs_inner_apply_le_opNorm_mul_norm_sq`,
`YangMills.RG.isCoercive_add_of_opNorm_le`,
`YangMills.RG.isCoercive_sub_of_opNorm_le`,
`YangMills.RG.isCoercive_sub_tsum_of_norm_budget`,
`YangMills.RG.isCoerciveCLM_qMassCLM_zero`,
`YangMills.RG.isCoerciveCLM_add_qMassCLM_of_blockPoincare`;
core 8331)

This addendum records the next source-independent P4 coercivity brick from the
gauge-raw-activity handoff.  Appendix F/H# already has the source-facing
consumer from `hraw`/integrability/`hR` to `SingleScaleUVDecay`; this checkpoint
therefore stays before Appendix F and formalizes only the operator-budget
inequality needed by a future gauge-fixed precision proof.

`YangMills/RG/CoercivePerturbation.lean` introduces the predicate

```
IsCoerciveCLM A c := forall x, c * ||x||^2 <= <x, A x>
```

for continuous linear maps on a real Hilbert space.  The key estimate
`abs_inner_apply_le_opNorm_mul_norm_sq` proves

```
|<x, B x>| <= ||B|| * ||x||^2,
```

and the additive/subtractive perturbation theorems show that a perturbation
with operator norm at most `delta` reduces the coercivity constant by at most
`delta`.  The summable-family theorem
`isCoercive_sub_tsum_of_norm_budget` proves the corresponding result for
`A - sum' i, Sigma i` from a scalar summable budget
`||Sigma i|| <= delta i`.

The qMass sanity hooks repackage the existing adjoint block-average mass:
`qMassCLM` is coercive with semidefinite constant `0`, and the previous
block-Poincare plus `qMassCLM` coercivity theorem is exposed through the new
`IsCoerciveCLM` predicate.

Verification:

```
lake env lean YangMills\RG\CoercivePerturbation.lean
lake build YangMills.RG.CoercivePerturbation
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is still deterministic Hilbert-space algebra only.  It
does not define the Yang--Mills gauge-fixed Hessian, prove the needed
Poincare/Hodge estimate, identify the covariance as an inverse, construct
`C^(1/2)`, localize the whitened fluctuation integrand, construct
`BalabanCMP116LocalizedActivityFamily`, prove `hraw`, prove measurability, or
establish the physical remainder identity `hR`.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 239 (2026-06-22, **rooted leaf-summation half-budget wrapper**
`YangMills.RG.singleScaleUVDecay_of_omegaRootedBalabanCMP116AppendixFHsharp_re_four_mul_margin_of_rawMetricDecay_rooted_leafSummation_of_halfBudget`;
core 8331)

This addendum records a small Appendix-F/H# endpoint simplification requested
by the implementation memo.  The existing raw-metric rooted leaf-summation
endpoint required three separate second-Ursell obligations:

```
hsmall
hρ1
hBclosed
```

The new wrapper keeps the explicit rooted first-cover budget family `K₀` and
its proof `hroot`, but replaces those three obligations by the already-verified
uniform half-budget/profile hypotheses:

```
appendixFSecondUrsellLeafConstant d κ₀ * (2 * A₀ t k * K₀ t k) <= 1 / 2
4 * appendixFSecondUrsellMomentConstant d κ₀ * A₀ t k * K₀ t k <= profile
```

It then calls `appendixFSecondUrsell_sourceObligations_of_halfBudget` once and
projects the resulting conjunction into the existing leaf-summation endpoint.
The stronger canonical-root endpoints already on `main` continue to discharge
`hroot` too; this theorem is the intermediate API for non-canonical rooted
budgets.

Verification:

```
lake env lean YangMills\RG\AppendixFHsharpLeafSource.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is endpoint bookkeeping only.  It does not prove the
CMP116 raw activity estimate `hraw`, does not derive integrability/measurability
from the concrete activity, does not identify the physical remainder `hR`, and
does not construct the Yang--Mills gauge activity.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 240 (2026-06-22, **finite Appendix-F target-card tilt in cover weights**
`YangMills.RG.appendixFHoleMetricCoverWeight_mul_exp_card_le_shifted_of_source_card_le_metric`;
core 8331)

This addendum records the first Route-B cover-level tilt checkpoint.  The new
finite theorem proves that, for a connected target-fiber cover `C` of `Y`, a
source-side full-cardinality budget

```
|X| <= theta * (d_M(X) + 1)   for every X in Lambda
```

absorbs the target factor `exp |Y|` into the cover metric weight by shifting
the raw cover rate from `kappa` to `kappa - theta`:

```
appendixFMetricCoverWeight metric H0 kappa C * exp |Y|
  <= appendixFMetricCoverWeight metric H0 (kappa - theta) C.
```

The proof uses the already verified target-fiber cover-sum cardinality bound,
not a direct target-metric compression estimate.  A companion rate identity
`appendixFKsharpRate_sub_left` records
`appendixFKsharpRate (kappa - theta) kappa0 =
 appendixFKsharpRate kappa kappa0 - theta`, preserving the canonical rate
definition while making later tilted adapters algebraically explicit.

Verification:

```
lake env lean YangMills\RG\AppendixFLocalSummability.lean
lake env lean YangMills\RG\AppendixFKsharpEstimate.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is finite decay bookkeeping only.  It does not prove the
source full-cardinality budget, does not compare the full target cardinality
directly with `d_M(Y)+1`, does not prove Dimock (642), does not construct
`hraw`, and does not advance the physical Yang--Mills Hessian/covariance
construction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 241 (2026-06-22, **gauge-fixed precision coercivity composition**
`YangMills.RG.gaugeFixedPrecision_coerciveWithPositiveConstant`;
core 8332)

This addendum records the first P4 gauge-fixed precision composition layer.
The new module `YangMills/RG/GaugeFixedPrecision.lean` introduces

```
gaugeFixedBasePrecisionCLM K0 Q a = K0 + a Q†Q
gaugeFixedPrecisionCLM K0 Q a Sigma =
  gaugeFixedBasePrecisionCLM K0 Q a - sum' i, Sigma i
```

and proves that the existing block-Poincare adjoint-mass coercivity theorem
survives a summable operator-norm perturbation budget:

```
IsCoerciveCLM (gaugeFixedPrecisionCLM K0 Q a Sigma)
  (min 1 a / CP - sum' i, delta i).
```

The strictly positive wrapper separates the scalar smallness condition
`sum' i, delta i < min 1 a / CP` from the non-strict coercivity predicate.
The same file also specializes the theorem to the concrete `qMassCLM`, and
adds finite Schur-Catalan corollaries when the source provides one-sided
quadratic-form defect estimates rather than operator norms.

Verification:

```
lake build YangMills.RG.GaugeFixedPrecision
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is deterministic Hilbert-space composition only.  It
does not define the physical Yang--Mills Hessian, prove the decomposition
`HYM = Kslice + a Q†Q - Σ`, prove the block Hodge/Poincare estimate, prove
perturbation budgets from Balaban sources, construct the inverse covariance,
or produce the raw CMP116 activity estimate `hraw`.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 242 (2026-06-22, **exact covariance from strict coercivity**
`YangMills.RG.covarianceOfIsCoerciveCLM_comp_precision`;
core 8333)

This addendum records the first P4 covariance construction layer.  The new
module `YangMills/RG/CoerciveCovariance.lean` proves that a strictly coercive
finite-dimensional real precision operator has an exact continuous linear
inverse:

```
covarianceOfIsCoerciveCLM A hc hA : E →L[ℝ] E
```

and establishes both operator inverse identities:

```
covarianceOfIsCoerciveCLM A hc hA ∘ A = id
A ∘ covarianceOfIsCoerciveCLM A hc hA = id.
```

The same brick proves the lower image bound from coercivity, injectivity,
surjectivity in finite dimension, the pointwise estimate
`‖C y‖ <= ‖y‖ / c`, the operator estimate `‖C‖ <= c⁻¹`, and positivity of
the covariance quadratic form.  This separates the deterministic inverse
construction from the later physical tasks of defining the gauge-fixed Hessian
and proving its coercivity.

Verification:

```
lake build YangMills.RG.CoerciveCovariance
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is finite-dimensional deterministic functional analysis
only.  It does not define the physical Yang--Mills Hessian, prove
`flatGaugeHodgePoincare`, construct Combes--Thomas decay, construct a
localized covariance square root, or produce the raw CMP116 activity estimate
`hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 243 (2026-06-22, **abstract gauge-fixed precision covariance**
`YangMills.RG.covarianceOfGaugeFixedPrecisionCLM_comp_precision`;
core 8334)

This addendum records the source-independent assembly of the P4 coercivity and
covariance bricks.  The new module `YangMills/RG/GaugeFixedCovariance.lean`
defines the residual constant

```
gaugeFixedResidualCoercivityConstant δ a CP
  = min 1 a / CP - ∑' i, δ i
```

and constructs the exact inverse covariance for the abstract precision

```
gaugeFixedPrecisionCLM K0 Q a Sigma = K0 + a Q†Q - ∑' i, Sigma i
```

from the already verified block-Poincare/Hodge hypothesis, summable
operator-norm budget, and strict budget inequality
`∑' i, δ i < min 1 a / CP`.  The module proves both operator inverse
identities, the reciprocal operator-norm bound, and PSD of the covariance
quadratic form for this assembled precision.

Verification:

```
lake build YangMills.RG.GaugeFixedCovariance
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is still abstract Hilbert-space algebra.  It does not
define the physical Yang--Mills Hessian, prove the flat Hodge/Poincare
inequality, identify the physical block derivative, construct propagator
decay, or prove the CMP116 raw activity estimate `hraw`.  It only ensures that
once the physical precision is proved to satisfy these explicit hypotheses, no
separate covariance-shaped assumption is needed.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 244 (2026-06-22, **finite physical gauge-operator interface**
`YangMills.RG.flatKslice_nonnegative`; core 8335)

This addendum records the first finite physical-operator interface for the P4
route.  The new module `YangMills/RG/PhysicalGaugeOperator.lean` introduces
independent positive-bond one-cochains

```
PositiveBond d N = FinBox d N × Fin d
```

instead of treating the oriented `ConcreteEdge` type as the physical tangent
space.  It also defines active regions, active site/bond/plaquette subtypes,
Dirichlet zero-extension/restriction maps, full and active flat differential
operators, the flat gauge constraint, and the nonnegative flat slice

```
flatKslice = wilsonQuadCoeff * d1†d1 + ξInv * gauge†gauge.
```

The positive-bond block derivative `blockConstraintCLM` wraps the existing
verified `linAvg` through an explicit orientation adapter, preserving the
distinction between the gauge condition and the RG block derivative `Q`.  The
generic soft-precision shell allows the gauge constraint and block derivative
to land in different Hilbert spaces, so the distinction is enforced in the
type signature rather than only in prose.
The soft full-space precision shell is named

```
gaugeFixedPhysicalPrecision =
  physicalKslice physicalGaugeHessian gaugeConstraintCLM ξInv
    + a Q†Q.
```

The exact defect identity

```
physicalPrecision =
  gaugeFixedBasePrecisionCLM flatSlice Q a
    - physicalPrecisionDefect flatSlice physicalPrecision Q a
```

keeps the small-background perturbation estimate as a source obligation rather
than silently building it into the definition.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeOperator.lean
lake build YangMills.RG.PhysicalGaugeOperator
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is flat finite operator infrastructure and soft
full-space `a Q†Q` bookkeeping.  It does not prove the physical Wilson
Hessian formula, the physical Hodge/Poincare inequality, the perturbation
budget from a small background, a Schur complement hard-constraint theorem,
Green-function decay, a localized covariance square root, or the raw CMP116
activity estimate `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 245 (2026-06-22, **triple-infinity influence closure**
`YangMills.RG.tripleInfluence_le_of_geometric_leaf_scale_budget`; core 8336)

This addendum records a source-independent summation organizer for the
Appendix-F/RG frontier.  The new module
`YangMills/RG/TripleInfinityClosure.lean` formalizes the closure of three
separate infinities:

```
k : scale index
n : cluster/leaf order
Y : rooted target geometry
```

The main theorem consumes a pointwise marked estimate

```
|H k n Y| <= M * eps k * (Lleaf * eps k)^n * w Y
```

together with a uniform leaf budget `Lleaf * eps k <= q < 1`, a rooted target
budget `sum_Y w Y <= Kroot`, and a scale budget
`eps k <= A * exp (-(c0 * t)) * scaleWeight k`,
`sum_k scaleWeight k <= G0`.  It proves the closed iterated influence bound

```
sum_k sum_n sum_Y |H k n Y|
  <= M * A * Kroot * G0 * exp (-(c0 * t)) * (1 - q)^(-1).
```

The proof is split into a fixed-scale order/target theorem
`orderTargetInfluence_le_of_geometric_leaf`, a scale theorem
`scaleInfluence_le_of_scale_budget`, and the combined theorem above.  The
summability hypotheses are explicit; no Tonelli/Fubini or source convergence
is hidden.

Verification:

```
lake env lean YangMills\RG\TripleInfinityClosure.lean
lake build YangMills.RG.TripleInfinityClosure
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
```

**Honest scope.** This is deterministic real summation algebra.  It does not
prove the source activity estimate, Dimock/Balaban leaf summation, rooted
target geometry, scale-coupling summability, the physical Hessian/covariance
construction, or the raw CMP116 activity estimate `hraw`.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 246 (2026-06-22, **full-periodic physical gauge cochains**
`YangMills.RG.PhysicalGaugeCochains`; core 8337)

This addendum records the first P4.1 full-periodic cochain layer above the
finite lattice API.  The new module
`YangMills/RG/PhysicalGaugeCochains.lean` fixes one independent coordinate per
positive physical bond,

```
PhysicalBond d N = FinBox d N × Fin d,
```

keeps the Lie-algebra coordinate model as `SUNLieCoord Nc`, and introduces an
explicit `SUNAdjointModel` carrying the background adjoint action and inner
product invariance.  Reversed concrete edges are evaluated from positive-bond
coordinates by background adjoint transport via `orientedOneValue`, with
`orientedOneValue_reverse` proving the inverse-orientation convention.

The module also defines the background-covariant full-periodic cochain maps
`covariantD0CLM` and `covariantD1CLM`, background flatness,
`covariantDivCLM`, the gauge constraint, the positive gauge-fixing mass
`Q†Q`, the background Hodge operator, the trivial-background specialization,
and a flat block constraint through the already verified `linAvg`.
The new oracle targets include adjoint inverse composition, oriented reversal,
the `D0`/`D1` application equations, nonnegativity of the gauge-fixing mass
and Hodge form, and the block-constraint application equation.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This is full-periodic cochain/operator infrastructure with
an explicit background adjoint interface.  It does not construct the physical
Wilson Hessian, prove gauge-fixed coercivity from a source Hodge/Poincare
theorem, construct the covariance/propagator for a physical precision, prove
localization of `C^(1/2)`, or produce the raw CMP116 activity estimate `hraw`.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 247 (2026-06-22, **right-oriented physical Hodge quadratic forms**
`YangMills.RG.PhysicalGaugeCochains`; core 8337)

This addendum records a small P4.1 compatibility closure inside
`YangMills/RG/PhysicalGaugeCochains.lean`.  The previously verified adjoint
calculations produced the gauge-fixing and Hodge quadratic forms in the
orientation

```
inner (K A) A.
```

The generic coercivity API in `GaugePrecision.lean` and
`GaugeFixedPrecision.lean` consumes the source Hodge/Poincare hypothesis in the
orientation

```
inner A (K A).
```

The module now exposes the matching right-oriented identities and
nonnegativity facts:

```
gaugeFixingMass_inner_right
gaugeFixingMass_nonnegative_right
backgroundGaugeHodgeK0_inner_right
backgroundGaugeHodgeK0_nonnegative_right
flatGaugeHodgeK0_nonnegative_right
```

These are pure real-inner-product symmetry consequences of the already
verified adjoint formulas.  They remove an integration nuisance for the next
source theorem `flatGaugeHodgePoincare`, without adding a new physical
assumption or coercivity wrapper.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This is orientation bookkeeping for the physical Hodge
operator.  It does not prove the uniform Hodge/Poincare theorem, identify the
Wilson Hessian, prove a small-background defect estimate, construct a
propagator, or produce `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 248 (2026-06-22, **flat physical Hodge quadratic identities**
`YangMills.RG.PhysicalGaugeCochains`; core 8337)

This addendum records the direct flat specialization of the physical Hodge
quadratic identity at the trivial background.  The new theorems are

```
flatGaugeHodgeK0_inner
flatGaugeHodgeK0_inner_right
```

They state that the quadratic form of `flatGaugeHodgeK0CLM` is exactly the sum
of the squared norms of the trivial-background `covariantD1CLM` and
`gaugeConstraintQCLM`, in both `inner (K A) A` and `inner A (K A)` orientations.
The proofs are `simpa` specializations of the already verified background
Hodge identities.  This keeps the next source-facing theorem
`flatGaugeHodgePoincare` pinned to the flat operator directly, rather than
requiring downstream code to unfold `flatGaugeHodgeK0CLM`.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This is still deterministic Hodge-form bookkeeping.  It does
not prove the uniform flat Hodge/Poincare inequality, identify the Wilson
Hessian, supply the small-background operator-norm estimate, construct a
propagator, or produce `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 249 (2026-06-22, **physical block-constraint support stencil**
`YangMills.RG.PhysicalGaugeCochains`; core 8337)

This addendum records the locality stencil for the full-periodic flat physical
block constraint.  The new definition

```
flatBlockConstraintSupport L N' b
```

is the image of the existing concrete-edge `linAvgSupport` under
`physicalBondOfEdge`, so it is a finite set of independent positive physical
bonds on the fine lattice.  The theorem

```
flatBlockConstraintQCLM_congr_of_eqOn_support
```

states that the block constraint value at a coarse positive bond `b` depends
only on the input one-cochain values on this physical support.  The proof is a
direct lift of `linAvg_congr_of_eqOn_support`; it does not change the averaging
formula or add a new analytic hypothesis.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This is finite-support/locality bookkeeping for the flat
block derivative `Q`.  It does not prove the Hodge/Poincare estimate, Wilson
Hessian identification, small-background defect bound, covariance decay, or
`hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 250 (2026-06-22, **full-periodic flat Hodge/block-Poincare interface**
`YangMills.RG.PhysicalGaugeHodgePoincare`; core 8338)

This addendum records the first full-periodic P4 Hodge/Poincare target module.
The new predicate

```
FlatGaugeHodgePoincare d L N' Nc ρ CP
```

states the trivial-background physical-cochain estimate on the fine side
length `N = L * N'`:

```
‖A‖² ≤ CP * (inner A (flatGaugeHodgeK0CLM A) + ‖flatBlockConstraintQCLM A‖²).
```

The theorem

```
flatGaugeHodgePoincare
```

does not prove that estimate from scratch.  It repackages a supplied
source-level curl/divergence/block inequality using the already verified flat
quadratic identity `flatGaugeHodgeK0_inner_right`.  This keeps the active
Dirichlet API, background-covariant block derivative, Wilson Hessian
normalization, and small-background comparison out of the theorem statement.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeHodgePoincare.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeHodgePoincare.lean
```

**Honest scope.** This is a target proposition and exact operator-identity
adapter.  The unproved source input remains the volume-uniform
curl/divergence/block estimate for the repository's line-integral `Q`, with
the expected dependence on the RG block size `L`.  It does not identify the
Wilson Hessian, prove small-background stability, construct a covariance, or
produce `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 251 (2026-06-22, **block constraint on constant physical one-cochains**
`YangMills.RG.PhysicalGaugeCochains`; core 8338)

This addendum records the finite-combinatorial constant-sector calculation
needed before a flat harmonic-kernel audit.  The averaging layer now proves

```
fineLineSum_constant
linAvg_constant
```

for direction-wise constant concrete-edge fields `A(e) = v(e.dir)`.  The
length-`L` line integral is `(L : ℝ) • v μ`, and the normalized block average
is `(L : ℝ) • v c.dir`; the `L^d` block cardinality cancels the normalization.

The physical cochain layer now defines

```
constantPhysicalGaugeOneCochain
```

and proves

```
flatBlockConstraintQCLM_constant_apply
flatBlockConstraintQCLM_injective_on_constants
```

so the full-periodic flat block constraint sends a direction-wise constant
physical one-cochain to `L` times the corresponding coarse directional value
and is injective on that constant sector.

Verification:

```
lake env lean YangMills\RG\LinearAveraging.lean
lake build YangMills.RG.LinearAveraging
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\LinearAveraging.lean YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This proves only that the soft block term removes
direction-wise constant candidate harmonic modes at the finite algebraic
level.  It does not classify the full flat harmonic kernel, prove the periodic
curl-div identity, prove a volume-uniform block Poincare theorem, identify the
Wilson Hessian, or produce `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 252 (2026-06-22, **flat harmonic kernel zero-form test**
`YangMills.RG.PhysicalGaugeCochains`; core 8338)

This addendum records the first internal flat harmonic-kernel predicate for the
full-periodic physical cochain layer.  The new definition

```
IsFlatHarmonicOneCochain
```

means simultaneous flat curl and gauge-divergence zero at the trivial
background:

```
D₁ A = 0 ∧ div A = 0.
```

The new theorems

```
isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_right_eq_zero
isFlatHarmonicOneCochain_iff_flatGaugeHodgeK0_inner_eq_zero
```

prove that, for the already-defined flat Hodge operator
`flatGaugeHodgeK0CLM`, vanishing of either inner-product orientation of the
quadratic form is exactly equivalent to `IsFlatHarmonicOneCochain`.  The proof
is finite-dimensional and uses the existing identity
`flatGaugeHodgeK0_inner_right`: a sum of two squared norms is zero iff both
terms vanish.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This is a kernel test, not a kernel classification.  It does
not prove that every flat harmonic one-cochain is direction-wise constant,
does not prove a periodic curl-div identity, does not prove a volume-uniform
block Poincare estimate, and does not identify the Wilson Hessian.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 253 (2026-06-22, **constant-sector flat harmonic inclusion**
`YangMills.RG.PhysicalGaugeCochains`; core 8338)

This addendum records the forward constant-sector half of the flat harmonic
kernel audit requested by the full-periodic P4 instruction packet.  The new
whole-map normalization theorem

```
flatBlockConstraintQCLM_constant
```

states that the current unscaled line-integral block map sends a
direction-wise constant fine field to `L` times the corresponding coarse
direction-wise constant field.

The new flat-harmonic inclusion theorems are

```
covariantD1CLM_trivial_constantPhysicalGaugeOneCochain
inner_constantPhysicalGaugeOneCochain_covariantD0CLM_trivial
gaugeConstraintQCLM_trivial_constantPhysicalGaugeOneCochain
isFlatHarmonicOneCochain_constantPhysicalGaugeOneCochain
```

They prove that every direction-wise constant physical one-cochain is flat
harmonic at the trivial background.  The flat curl proof is a direct plaquette
telescoping calculation.  The divergence proof is finite periodic
summation-by-parts: a constant one-form pairs to zero with every flat
zero-form gradient because `FinBox.shift` is a bijection with inverse
`FinBox.shiftBack`.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This proves only the forward inclusion
direction-wise constants `→` flat harmonics and the exact `Q` normalization on
that sector.  It does not prove the reverse classification of flat harmonics,
does not prove the uniform full-periodic curl/divergence/block Poincare
theorem, does not establish independence of a Poincare constant from `N'`,
`Nc`, or `ρ`, and does not identify the Wilson Hessian.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 254 (2026-06-22, **constant-sector Hodge kernel and block-zero test**
`YangMills.RG.PhysicalGaugeCochains`; core 8338)

This addendum records the operator-level closure of the constant-sector audit.
The new theorem

```
flatGaugeHodgeK0CLM_constantPhysicalGaugeOneCochain
```

proves that every direction-wise constant physical one-cochain is killed by
the flat Hodge operator itself at the trivial background, not merely that its
quadratic form vanishes.  The proof unfolds
`flatGaugeHodgeK0CLM = D₁†D₁ + D₀D₀†` and uses the already verified zero flat
curl and zero flat divergence results.

The new theorem

```
flatBlockConstraintQCLM_constant_eq_zero_iff
```

packages the constant-sector block normalization and injectivity as an exact
zero test: the flat block constraint vanishes on a direction-wise constant
field iff the underlying directional value is zero.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This is still a constant-sector fact.  It does not prove the
reverse flat-harmonic classification, the uniform full-periodic
curl/divergence/block Poincare theorem, Wilson-Hessian identification,
propagator localization, covariance-root localization, or `hraw`.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 255 (2026-06-22, **flat Hodge operator kernel and constant joint-kernel**
`YangMills.RG.PhysicalGaugeCochains`; core 8338)

This addendum records two small kernel-audit closures for the full-periodic
physical cochain layer.  The new theorem

```
flatGaugeHodgeK0CLM_eq_zero_iff_isFlatHarmonicOneCochain
```

upgrades the previous quadratic-form zero test to the operator equation
itself: at the trivial background, `flatGaugeHodgeK0CLM A = 0` iff `A` has
zero flat curl and zero flat gauge divergence.

The new theorem

```
flatConstant_jointKernel_eq_zero_iff
```

packages the constant-sector audit in the exact shape used by the future
Poincare proof: on direction-wise constant one-cochains, the joint kernel of
the flat Hodge operator and the flat block constraint is trivial exactly when
the underlying directional value is zero.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This is still kernel bookkeeping.  It does not prove the
reverse classification that every flat harmonic one-cochain is direction-wise
constant, does not prove the full-periodic Poincare theorem, and does not
identify or perturb the Wilson Hessian.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 256 (2026-06-22, **constant-sector flat block norm control**
`YangMills.RG.PhysicalGaugeFlatPoincare`; core 8339)

This addendum records the first quantitative constant-sector normalization
facts for the full-periodic P4 block map.  The new module

```
YangMills/RG/PhysicalGaugeFlatPoincare.lean
```

proves

```
norm_sq_constantPhysicalGaugeOneCochain
flatBlockConstraintQCLM_constant_norm_sq
flatBlockConstraint_controls_constantSector
```

The first theorem expands the `ℓ²` norm squared of a direction-wise constant
physical one-cochain as

```
(N : ℝ)^d * ∑ i, ‖v i‖^2.
```

The second theorem computes the exact norm squared of the current unscaled
line-integral block constraint on such constants:

```
(L : ℝ)^2 * (N' : ℝ)^d * ∑ i, ‖v i‖^2.
```

The third theorem packages the exact sharp ratio

```
‖const_{L*N'} v‖^2 =
  ((L : ℝ)^d / (L : ℝ)^2) * ‖Q const_{L*N'} v‖^2.
```

This proves the constant/harmonic-sector normalization requested by the P4
instruction packet for the current `linAvg` convention.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFlatPoincare.lean
```

**Honest scope.** This is still only the constant-sector quantitative
normalization.  It does not prove the reverse flat-harmonic classification,
the coordinate Gaffney identity, the finite-volume compactness Poincare
theorem, the volume-uniform Poincare theorem, or any Wilson-Hessian
identification.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 257 (2026-06-22, **explicit flat plaquette curl equation**
`YangMills.RG.PhysicalGaugeCochains`; core 8339)

This addendum records a narrow prerequisite for the reverse flat-harmonic
classification ladder.  The full-periodic cochain layer now proves

```
covariantD1CLM_trivial_apply
isFlatHarmonicOneCochain_curl_apply_eq_zero
```

The first theorem unfolds the trivial-background covariant one-to-two
differential as the usual plaquette curl on positive-bond one-cochains:

```
D₁ A p =
  A (p.site, p.dir1)
  + A (p.site.shift p.dir1, p.dir2)
  - A (p.site.shift p.dir2, p.dir1)
  - A (p.site, p.dir2).
```

The second theorem specializes this formula to flat harmonic one-cochains,
giving the pointwise curl equation needed by any later reverse-classification
proof.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This does not prove the explicit divergence formula, the
reverse flat-harmonic classification, the coordinate Gaffney identity, the
finite-volume compactness Poincare theorem, the volume-uniform Poincare
theorem, or any Wilson-Hessian identification.  It is only the first pointwise
curl equation for the full-periodic P4 route.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 258 (2026-06-22, **harmonic-kernel classification bridge**
`YangMills.RG.PhysicalGaugeFlatPoincare`; core 8339)

This addendum records the conditional bridge requested for the fixed-volume P4
route.  The module

```
YangMills/RG/PhysicalGaugeFlatPoincare.lean
```

now imports the flat Hodge/block-Poincare interface and defines

```
FlatHarmonicKernelClassified
```

as the missing reverse statement: every full-periodic flat harmonic physical
one-cochain is direction-wise constant.  From that named hypothesis, it proves

```
flatHarmonicKernel_eq_constantSector
flatGaugeHodgeKernel_eq_constantSector
flatJointKernel_trivial_of_harmonicClassification
```

The first two theorems identify the flat-harmonic and flat-Hodge kernels with
the constant sector under the carried classification hypothesis.  The third
combines that classification with the already verified constant-sector block
audit `flatConstant_jointKernel_eq_zero_iff`, proving that the joint kernel of
`K₀` and the flat block map is trivial at each fixed volume.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFlatPoincare.lean
```

**Honest scope.** This does not prove the reverse classification hypothesis;
it only packages it as an explicit interface and derives the fixed-volume
joint-kernel consequence.  It does not prove the finite-dimensional
anti-Lipschitz/Poincare theorem, the explicit divergence formula, the
coordinate Gaffney identity, the volume-uniform theorem, or any Wilson-Hessian
identification.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 259 (2026-06-22, **fixed-volume flat Hodge/block Poincare from
joint kernel** `YangMills.RG.PhysicalGaugeFlatPoincare`; core 8339)

This addendum records the non-uniform finite-volume Poincare step following
the classification bridge.  The module

```
YangMills/RG/PhysicalGaugeFlatPoincare.lean
```

now proves the generic finite-dimensional theorem

```
exists_sq_norm_le_sum_three_sq_of_jointKernel_trivial
```

for three continuous linear maps.  It bundles the maps into a product map,
uses trivial joint kernel to prove injectivity, invokes Mathlib's
`LinearMap.exists_antilipschitzWith`, and converts the product max norm into
the squared sum bound.

Specialized to the flat physical cochain layer, it also proves

```
exists_flatGaugeHodgeBlockPoincare_of_jointKernel_trivial
flatGaugeHodgeBlockPoincare_of_harmonicClassification
flatCurlDivBlockPoincare_of_harmonicClassification
```

Thus a fixed finite volume with trivial joint kernel of `K₀` and the block map
has some positive `FlatGaugeHodgePoincare` constant.  Combining this with
`FlatHarmonicKernelClassified` gives both the operator-level and explicit
curl/divergence/block forms.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFlatPoincare.lean
```

**Honest scope.** This is fixed-volume and classification-dependent.  It does
not prove the reverse flat-harmonic classification hypothesis, the explicit
divergence formula, the coordinate Gaffney identity, any volume-uniform
constant, any source-backed Balaban/Dimock estimate, or any Wilson-Hessian
identification.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 260 (2026-06-22, **pointwise flat divergence equation**
`YangMills.RG.PhysicalGaugeCochains`; core 8339)

This addendum records the pointwise flat divergence adapter for the full
periodic physical cochain layer.  The module

```
YangMills/RG/PhysicalGaugeCochains.lean
```

now proves

```
gaugeConstraintQCLM_trivial_apply
isFlatHarmonicOneCochain_divergence_apply_eq_zero
```

The first theorem unfolds the adjoint-defined gauge constraint at the trivial
background into the exact backward-divergence formula
`sum_i (A(x,i) - A(x.shiftBack i,i))`.  The proof is a finite periodic
summation-by-parts calculation.  The second theorem combines that formula with
the flat-harmonic predicate to give the corresponding pointwise zero equation.
Together with the already proved pointwise curl formula, flat harmonicity now
has both explicit local equations available for the reverse-classification
ladder.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCochains.lean
```

**Honest scope.** This does not prove the reverse flat-harmonic classification
hypothesis, a coordinate Gaffney identity, any volume-uniform constant, any
source-backed Balaban/Dimock estimate, or any Wilson-Hessian identification.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 261 (2026-06-22, **one-dimensional flat harmonic classification**
`YangMills.RG.PhysicalGaugeFlatPoincare`; core 8339)

This addendum records a non-wrapper base case for the flat harmonic
classification ladder.  The module

```
YangMills/RG/PhysicalGaugeFlatPoincare.lean
```

now proves

```
finBox_one_eq_iterShift
constant_of_shift_invariant_finBox_one
flatHarmonicKernelClassified_one
flatGaugeHodgeBlockPoincare_one
flatCurlDivBlockPoincare_one
```

The first two theorems are the one-dimensional periodic-shift reachability and
constantness lemmas.  `flatHarmonicKernelClassified_one` uses the new
pointwise flat divergence equation to prove that every one-dimensional flat
harmonic physical one-cochain is direction-wise constant.  The last two
theorems feed that classification into the existing fixed-volume compactness
bridge, giving one-dimensional flat Hodge/block-Poincare statements without an
external classification hypothesis.  The produced Poincare constant is still
fixed-volume and may depend on `L`, `N'`, `Nc`, and the adjoint model.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFlatPoincare.lean
```

**Honest scope.** This is a one-dimensional base case only.  It does not prove
the higher-dimensional reverse flat-harmonic classification, a coordinate
Gaffney identity, a volume-uniform full-periodic Poincare constant, any
source-backed Balaban/Dimock estimate, or any Wilson-Hessian identification.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 262 (2026-06-22, **periodic curl/divergence boundary and adapter**
`YangMills.RG.FiniteTorusCurlDiv`; core 8340)

This addendum records the first source-facing layer of the higher-dimensional
flat harmonic classification route.  The lattice module

```
YangMills/L0_Lattice/FiniteLatticeGeometryInstance.lean
```

now packages reusable periodic shift/reindexing infrastructure:

```
FinBox.shift_bijective
FinBox.shiftBack_bijective
FinBox.sum_shift
FinBox.sum_shiftBack
FinBox.shift_shiftBack_comm
FinBox.iter_shift_apply_self
FinBox.iter_shift_apply_ne
FinBox.eq_default_of_shift_invariant
```

The physical cochain module now exposes the short alias

```
isFlatHarmonicOneCochain_div_apply_eq_zero
```

for the pointwise backward-divergence equation.  The new finite-torus module

```
YangMills/RG/FiniteTorusCurlDiv.lean
```

defines the exact coordinate theorem boundary

```
PeriodicCurlDivKernelClassified
```

and introduces finite-difference primitives, currently including the verified
commutation lemma

```
torusForwardDiff_torusBackwardDiff_comm
```

The physical Poincare bridge now proves

```
flatHarmonicKernelClassified_of_curl_div
exists_flatGaugeHodgePoincare_of_periodicCurlDivClassification
```

so a source/proved periodic curl-divergence classification immediately feeds
the existing fixed-volume flat Hodge/block-Poincare compactness theorem.  The
coordinate classification itself remains an explicit hypothesis; no axiom,
opaque proof, Fourier theorem, or uniform-volume estimate was introduced.

Verification:

```
lake env lean YangMills\L0_Lattice\FiniteLatticeGeometryInstance.lean
lake build YangMills.L0_Lattice.FiniteLatticeGeometryInstance
lake env lean YangMills\RG\PhysicalGaugeCochains.lean
lake build YangMills.RG.PhysicalGaugeCochains
lake env lean YangMills\RG\FiniteTorusCurlDiv.lean
lake build YangMills.RG.FiniteTorusCurlDiv
lake env lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\L0_Lattice\FiniteLatticeGeometryInstance.lean YangMills\RG\PhysicalGaugeCochains.lean YangMills\RG\FiniteTorusCurlDiv.lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
```

**Honest scope.** This isolates and consumes the exact source-facing
curl/divergence classification boundary, but does not prove
`periodicCurlDivKernelClassified`, a quantitative Gaffney/Fourier estimate,
a volume-uniform full-periodic Poincare constant, any Wilson-Hessian
identification, propagator localization, covariance-root localization, or
`hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 263 (2026-06-23, **finite-torus curl/divergence classification**
`YangMills.RG.FiniteTorusCurlDiv`; core 8340)

This addendum discharges the finite-coordinate theorem boundary isolated in
Addendum 262.  The module

```
YangMills/RG/FiniteTorusCurlDiv.lean
```

now proves the direct finite-difference Laplacian route:

```
sum_inner_torusBackwardDiff
sum_inner_torusLaplacian_eq_neg_sum_norm_sq
torusLaplacian_component_eq_forwardDiff_divergence
eq_default_of_torusLaplacian_eq_zero
periodicCurlDivKernelClassified
```

The proof is finite-dimensional and full-periodic.  It turns ordered plaquette
curl into symmetric forward differences, uses backward-divergence zero to make
each component torus Laplacian vanish, applies the energy identity to force
all forward differences to be zero, and then uses
`FinBox.eq_default_of_shift_invariant` to conclude direction-wise constancy.

The physical bridge

```
YangMills/RG/PhysicalGaugeFlatPoincare.lean
```

now uses that theorem to prove

```
flatHarmonicKernelClassified
flatHarmonic_eq_constantPhysicalGaugeOneCochain
exists_flatGaugeHodgePoincare
```

so the fixed-volume flat Hodge/block Poincare theorem no longer carries an
external flat-harmonic classification hypothesis.  The resulting constant is
still obtained by finite-dimensional compactness and may depend on the fixed
volume.

Verification targets:

```
lake env lean YangMills\RG\FiniteTorusCurlDiv.lean
lake build YangMills.RG.FiniteTorusCurlDiv
lake env lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\FiniteTorusCurlDiv.lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
```

**Honest scope.** This proves the finite full-periodic classification and the
non-uniform fixed-volume flat Hodge/block Poincare closure.  It does not prove
a volume-uniform Poincare/Gaffney estimate, an explicit numerical constant,
Wilson-Hessian identification, propagator localization, covariance-root
localization, or `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 264 (2026-06-23, **public Dirichlet-route curl/divergence API**
`YangMills.RG.FiniteTorusCurlDiv`; core 8340)

This addendum stabilizes the public names around the finite-torus
classification proved in Addendum 263.  The module

```
YangMills/RG/FiniteTorusCurlDiv.lean
```

now exposes the ordered curl and Dirichlet-route wrappers:

```
torusCurl_eq_plaquette
torusCurl_self
torusCurl_swap
torusCurl_eq_zero_of_ordered_plaquettes
torusForwardDiff_sum
finiteTorusDirichletIdentity
torusLaplacian_component_eq_zero_of_curl_div_zero
torusForwardDiff_eq_zero_of_laplacian_eq_zero
torusForwardDiff_eq_zero_of_curl_div_zero
periodicCurlDivKernelClassified_of_dirichlet
PeriodicCurlDivKernelClassified.proof
```

These names do not strengthen the physical theorem.  They package the already
proved Laplacian/Dirichlet route in the form requested by the implementation
packet, so later physical gauge-fixed precision work can cite a stable endpoint
instead of depending on the internal proof body of
`periodicCurlDivKernelClassified`.

Verification targets:

```
lake env lean YangMills\RG\FiniteTorusCurlDiv.lean
lake build YangMills.RG.FiniteTorusCurlDiv
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\FiniteTorusCurlDiv.lean
```

**Honest scope.** This is an API-stabilization checkpoint for the qualitative
fixed-volume classification.  It still does not prove a volume-uniform
Poincare/Gaffney estimate, an explicit numerical constant, Wilson-Hessian
identification, propagator localization, covariance-root localization, or
`hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 265 (2026-06-23, **fixed-volume flat physical gauge-fixed
precision adapter** `YangMills.RG.PhysicalGaugeFixedPrecision`; core 8341)

This addendum specializes the generic gauge-fixed precision theorem

```
K0 + a Q†Q - Σ
```

to the finite full-periodic physical positive-bond cochain interface.  The new
module

```
YangMills/RG/PhysicalGaugeFixedPrecision.lean
```

adds the shell

```
flatGaugeFixedPrecisionCLM
```

and proves:

```
flatGaugeFixedPrecision_coerciveWithPositiveConstant_of_flatPoincare
exists_flatGaugeFixedPrecision_coerciveWithPositiveConstant
```

The first theorem consumes an explicit `FlatGaugeHodgePoincare` constant `CP`,
a positive soft block mass `a`, summability of the operator correction family
`Σ`, and the strict small-budget condition
`∑' i, δ i < min 1 a / CP`.  It returns strict coercivity of the physical flat
precision shell with residual constant `min 1 a / CP - ∑' i, δ i`.

The second theorem uses the already-proved fixed-volume
`exists_flatGaugeHodgePoincare` to choose some `CP`, while deliberately keeping
the budget condition explicit for that selected constant.

Verification:

```
lake env lean YangMills\RG\PhysicalGaugeFixedPrecision.lean
lake build YangMills.RG.PhysicalGaugeFixedPrecision
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFixedPrecision.lean
```

**Honest scope.** This is a fixed-volume adapter from the proved flat
Hodge/block Poincare endpoint into the generic perturbative precision API.  It
does not prove volume-uniform Poincare/Gaffney constants, Wilson-Hessian
identification, propagator localization, covariance-root localization, or
`hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 266 (2026-06-23, **fixed-volume flat physical covariance
adapter** `YangMills.RG.PhysicalGaugeFixedPrecision`; core 8341)

This addendum extends the fixed-volume flat physical precision adapter from
Addendum 265 by specializing the exact finite-dimensional covariance API to
the same operator

```
flatGaugeFixedPrecisionCLM = K0 + a Q†Q - Σ
```

where `K0` is the trivial-background flat Hodge operator and `Q` is the flat
block constraint on finite periodic positive-bond physical one-cochains.

The module now adds:

```
flatGaugeFixedCovarianceCLM
flatGaugeFixedCovarianceCLM_comp_precision
precision_comp_flatGaugeFixedCovarianceCLM
norm_flatGaugeFixedCovarianceCLM_le
flatGaugeFixedCovarianceCLM_psd
```

These theorems consume the same explicit fixed-volume
`FlatGaugeHodgePoincare`, positive soft mass, summable perturbation budget, and
strict residual-budget hypotheses as the coercivity theorem.  They prove both
operator inverse identities, the operator bound by the inverse residual
coercivity constant, and positivity of the covariance quadratic form.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeFixedPrecision.lean
lake build YangMills.RG.PhysicalGaugeFixedPrecision
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFixedPrecision.lean
```

**Honest scope.** This is still finite-dimensional fixed-volume inverse
bookkeeping.  It does not prove decay/locality of the covariance, construct or
localize a covariance square root, identify the precision with a Wilson
Hessian, prove volume-uniform Poincare/Gaffney constants, or construct `hraw`.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 267 (2026-06-23, **source-facing physical covariance localization
API** `YangMills.RG.PhysicalGaugeCovarianceLocalization`; core 8342)

This addendum records a small P4 interface layer between the exact
fixed-volume flat physical covariance and the future analytic localization
theorem.  The new module

```
YangMills/RG/PhysicalGaugeCovarianceLocalization.lean
```

adds the coordinate source probe

```
singlePhysicalBondCochain
```

and source-facing predicates

```
PhysicalCovarianceKernelBound
PhysicalCovarianceFiniteRange
PhysicalCovarianceExponentialKernelBound
```

together with the conversion

```
physicalCovarianceKernelBound_of_exponential
```

and the certificate

```
PhysicalLocalizedCovarianceCertificate
flatGaugeFixedLocalizedCovarianceCertificate_of_kernelBound
```

The final theorem instantiates the certificate with
`flatGaugeFixedPrecisionCLM` and `flatGaugeFixedCovarianceCLM`, bundling the
already-proved inverse identities, operator norm bound, and PSD quadratic form
with a supplied kernel bound.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCovarianceLocalization.lean
lake build YangMills.RG.PhysicalGaugeCovarianceLocalization
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCovarianceLocalization.lean
```

**Honest scope.** This addendum does not prove covariance decay, finite range,
locality of a covariance square root, Wilson-Hessian identification,
volume-uniform constants, or `hraw`.  The actual analytic work remains the
source theorem that supplies `PhysicalCovarianceKernelBound` for the physical
covariance in a volume-uniform, gauge-fixed setting.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 268 (2026-06-23, **source-facing covariance-root localization
API** `YangMills.RG.PhysicalGaugeCovarianceLocalization`; core 8342)

This addendum extends the P4 source-facing covariance-localization interface
with the next honest endpoint for the Gaussian-coordinate map
`B' = C^{1/2} X`.

The same module now adds:

```
PhysicalLocalizedCovarianceRootCertificate
physicalLocalizedCovarianceRootCertificate_of_source
flatGaugeFixedLocalizedCovarianceRootCertificate_of_source
```

The generic certificate consumes a localized covariance certificate and then
records, as explicit source inputs, the root square identity
`root.comp root = covariance`, an operator-norm bound for `root`, the
self-adjoint quadratic-form orientation, PSD of the root, and a pointwise
kernel bound for `root`.  The flat wrapper specializes this package to
`flatGaugeFixedPrecisionCLM` and `flatGaugeFixedCovarianceCLM` while keeping
all square-root analysis and localization in source hypotheses.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCovarianceLocalization.lean
lake build YangMills.RG.PhysicalGaugeCovarianceLocalization
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCovarianceLocalization.lean
```

**Honest scope.** This addendum does not construct a spectral square root,
prove square-root localization, identify the physical Wilson Hessian, produce
volume-uniform constants, or construct raw Balaban activities.  It only fixes
the Lean target that future source estimates must satisfy before a localized
Gaussian fluctuation activity can be assembled.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 269 (2026-06-23, **source-facing physical gauge fluctuation
activity certificate** `YangMills.RG.PhysicalGaugeFluctuationActivity`; core
8343)

This addendum records the next P4 interface after covariance-root
localization.  The new module

```
YangMills/RG/PhysicalGaugeFluctuationActivity.lean
```

introduces physical gauge coordinate fields and local two-field activities on
positive bonds:

```
PhysicalGaugeField
PhysicalGaugeLocalActivity
PhysicalGaugeRawActivityBound
PhysicalGaugeActivityDecay
PhysicalLocalizedGaussianActivityCertificate
```

and proves the source-packaging/extraction theorems:

```
physicalLocalizedGaussianActivityCertificate_of_source
physicalGaugeRawActivityBound_of_localizedGaussianActivityCertificate
physicalGaugeRawActivityDecay_of_localizedGaussianActivityCertificate
```

The certificate consumes a
`PhysicalLocalizedCovarianceRootCertificate` and packages a local activity
family, active-support containment, nonnegative amplitudes/weights, a raw
pointwise bound, a decay majorant, and an explicit source-construction
proposition tying the activity to the physical Hessian/fluctuation integral.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeFluctuationActivity.lean
lake build YangMills.RG.PhysicalGaugeFluctuationActivity
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFluctuationActivity.lean
```

**Honest scope.** This addendum does not construct the Wilson Hessian, prove
the change of variables, build the Gaussian measure from `C^{1/2}`, prove the
raw Balaban/CMP activity estimate, or discharge `hraw`.  It only fixes the
Lean shape of the source theorem needed before the existing Appendix-F/H#
consumers can receive physical local activities.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 270 (2026-06-23, **Extra High audit: scale-budget sign guard and
flat constant-sector lower bound** `YangMills.RG.TripleInfinityClosure`,
`YangMills.RG.PhysicalGaugeFlatPoincare`; core 8343)

Extra High re-audited the latest public physical RG stack and restored two
semantic guards:

```
scaleInfluence_le_of_scale_budget
tripleInfluence_le_of_geometric_leaf_scale_budget
flatGaugeHodgePoincare_constantSector_lower_bound
```

The triple-infinity closure now requires the scale profile `scaleWeight` to be
pointwise nonnegative, matching the source meaning of a summable scale budget.
This prevents signed summable profiles from being presented as a legitimate
RG budget.  The flat Poincare audit theorem proves that any
`FlatGaugeHodgePoincare d L N' Nc rho CP` constant satisfies
`(L : R)^d / (L : R)^2 <= CP` on a nonzero direction-wise constant sector for
the current unscaled line-integral block map.

Verification targets:

```
lake env lean YangMills\RG\TripleInfinityClosure.lean
lake env lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
lake build YangMills.RG.TripleInfinityClosure
lake build YangMills.RG.PhysicalGaugeFlatPoincare
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\TripleInfinityClosure.lean YangMills\RG\PhysicalGaugeFlatPoincare.lean
```

**Audit findings.** `Ubar` remains faithful and non-vacuous: the Mercator
argument is `rep(D).val - 1`, not `rep(D).val`, and the old unitary
`||D|| < 1` premise is explicitly marked impossible under norm-one physical
realizations.  `sunHaarProb_trace_normSq_integral_eq_one` remains a finite
SU(N) fundamental-character Haar statement only.  The concrete UV assembly and
physical activity layer still carry the analytic Balaban/Dimock source
estimates explicitly; they do not prove covariance/root localization, Wilson
Hessian identification, `hraw`, or a continuum limit.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 271 (2026-06-23, **physical fluctuation-activity certificate
projections** `YangMills.RG.PhysicalGaugeFluctuationActivity`; core 8343)

This addendum keeps the P4 activity layer source-facing and only exposes fields
that were already present in
`PhysicalLocalizedGaussianActivityCertificate`.  The new projection theorems
are:

```
physicalGaugeSpectatorSupport_subset_of_localizedGaussianActivityCertificate
physicalGaugeFluctuationSupport_subset_of_localizedGaussianActivityCertificate
physicalGaugeAmplitude_nonneg_of_localizedGaussianActivityCertificate
physicalGaugeWeight_nonneg_of_localizedGaussianActivityCertificate
physicalGaugeActivityDecay_of_localizedGaussianActivityCertificate
```

Together with the existing raw-bound and combined raw-decay extractions, these
make the certificate usable by later Appendix-F adapter code without peeking
through record fields or asserting any physical-to-CMP116 conversion theorem.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeFluctuationActivity.lean
lake build YangMills.RG.PhysicalGaugeFluctuationActivity
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeFluctuationActivity.lean
```

**Honest scope.** This addendum does not construct the Wilson Hessian, prove
the Gaussian change of variables, localize `C^{1/2}`, identify physical bonds
with CMP116 cubes, convert `SUNLieCoord Nc` into `Fin lieDim -> Real`, or
discharge `hraw`.  A separate source/pro request records those typing and
normalization questions explicitly.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 272 (2026-06-23, **CMP116 active-support dependency wrappers**
`YangMills.RG.BalabanCMP116Localization`; core 8343)

This addendum adds finite support consequences of the existing CMP116
localized-activity fields.  The new theorem names are:

```
BalabanCMP116LocalizedActivityFamily.fluctuationSupport_subset_omega
BalabanCMP116LocalizedActivityFamily.fluctuationSupport_subset_activeSupport
BalabanCMP116LocalizedActivityFamily.activity_globalEval_eq_of_agreeOn_activeSupport
BalabanCMP116LocalizedActivityFamily.mayerCoverActivity_fluctuationSupport_subset_omega
BalabanCMP116LocalizedActivityFamily.mayerCoverActivity_fluctuationSupport_subset_activeUnion
BalabanCMP116LocalizedActivityFamily.mayerCoverActivity_globalEval_eq_of_agreeOn_activeUnion_only
```

They expose that a single localized raw activity, and any finite Mayer product
of such activities, depends only on the declared active support union when a
source theorem states agreement at that coarser level.  The sharper existing
dependency on `Omega ∩ activeSupport` / `Omega ∩ activeUnion` remains available.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116Localization.lean
lake build YangMills.RG.BalabanCMP116Localization
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116Localization.lean
```

**Honest scope.** This is finite support bookkeeping only.  It does not prove
Balaban random-walk localization, construct the physical-to-CMP116 activity
map, prove measurability of a physical source activity, or discharge `hraw`.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 273 (2026-06-23, **CMP116 `K#` support dependency wrappers**
`YangMills.RG.BalabanCMP116KsharpAdapter`; core 8343)

This addendum carries the finite support package through the first-integration
adapter.  The new theorem names are:

```
balabanCMP116AppendixFConnectedLocalActivity_globalEval_eq_of_agreeOn
balabanCMP116AppendixFConnectedLocalActivity_globalEval_eq_of_agreeOn_skeleton
balabanCMP116AppendixFKsharp_globalEval_eq_of_agreeOn
balabanCMP116AppendixFKsharp_globalEval_eq_of_agreeOn_skeleton
```

They say that the CMP116-specialized connected first activity, and the
spectator-integrated `K#`, are unchanged when source fields agree on the full
target `Y` or on the active skeleton `skeleton HF Y`.  The proofs are direct
applications of the existing `LocalActivity` / `LocalFunctional` dependency
lemmas plus the already-recorded CMP116 Appendix-F support inclusions.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116KsharpAdapter.lean
lake build YangMills.RG.BalabanCMP116KsharpAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116KsharpAdapter.lean
```

**Honest scope.** This is finite support bookkeeping after spectator
integration only.  It does not prove the physical gauge-fixed Hessian,
covariance localization, the physical-to-CMP116 activity map, measurability of
that physical source activity, or `hraw`.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 274 (2026-06-23, **CMP116 evaluated second-gas dependency wrappers**
`YangMills.RG.BalabanCMP116SecondGasAdapter`; core 8343)

This addendum propagates the CMP116 `K#` support dependency package to the
evaluated scalar second-gas activity.  The new theorem names are:

```
balabanCMP116AppendixFSecondGasActivity_eq_of_agreeOn
balabanCMP116AppendixFSecondGasActivity_eq_of_agreeOn_skeleton
```

They state that
`balabanCMP116AppendixFSecondGasActivity HF z Lambda F psi Y` is unchanged when
the spectator/source field agrees on either the full target `Y` or the active
skeleton `skeleton HF Y`, assuming the existing
`BalabanCMP116AppendixFSupportHypotheses`.  The proofs are direct applications
of the previously verified `K#` dependency wrappers; no analytic estimate or
new source theorem is introduced.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116SecondGasAdapter.lean
lake build YangMills.RG.BalabanCMP116SecondGasAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116SecondGasAdapter.lean
```

**Honest scope.** This is finite support bookkeeping for the scalar
second-gas interface only.  It does not prove the physical gauge-fixed
Hessian, covariance localization, the physical-to-CMP116 activity map,
measurability of that physical source activity, or `hraw`.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 275 (2026-06-23, **generic Appendix-F `K#` and second-gas
dependency wrappers** `YangMills.RG.AppendixFKsharp`,
`YangMills.RG.AppendixFSecondGas`; core 8343)

This addendum moves the support-dependency interface below the CMP116
specialization.  The new generic theorem names are:

```
appendixFHoleKsharp_globalEval_eq_of_agreeOn
appendixFHoleKsharp_globalEval_eq_of_agreeOn_skeleton
appendixFHoleSecondGasActivity_eq_of_agreeOn
appendixFHoleSecondGasActivity_eq_of_agreeOn_skeleton
```

The `K#` wrappers say that the integrated first activity is unchanged when
spectator/source fields agree on the full target `Y`, respectively on
`skeleton HF Y`, assuming the corresponding one-polymer spectator-support
containment.  The second-gas wrappers propagate the same statements to the
evaluated scalar activity
`appendixFHoleSecondGasActivity HF z Lambda Hraw mu psi Y`.

Verification targets:

```
lake env lean YangMills\RG\AppendixFKsharp.lean
lake build YangMills.RG.AppendixFKsharp
lake env lean YangMills\RG\AppendixFSecondGas.lean
lake build YangMills.RG.AppendixFSecondGas
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\AppendixFKsharp.lean YangMills\RG\AppendixFSecondGas.lean
```

**Honest scope.** This is finite support bookkeeping in the generic Appendix-F
interfaces.  It does not prove Dimock's closed `K#` estimate, the second
Ursell residual bound, the physical gauge-fixed Hessian, covariance
localization, the physical-to-CMP116 activity map, or `hraw`.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 276 (2026-06-23, **cluster-union component containment**
`YangMills.RG.ClusterDecay`; core 8343)

This addendum records the finite geometric containment facts needed before
future local-dependence wrappers for `H#` can reduce component activities to
agreement on a declared target union.  The new theorem names are:

```
clusterUnion_component_subset
clusterUnion_component_subset_of_eq
clusterUnion_component_skeleton_subset
clusterUnion_component_skeleton_subset_of_eq
omegaClusterUnion_component_subset
omegaClusterUnion_component_subset_of_eq
omegaClusterUnion_component_skeleton_subset
omegaClusterUnion_component_skeleton_subset_of_eq
```

The hard-core `clusterUnion` lemmas and the source-facing
`omegaClusterUnion` lemmas both state that each tuple component is contained
in the raw cluster union, and therefore in a declared target `Y` when the
union is equal to `Y`.  The skeleton variants provide the same containment at
the active-skeleton level.

Verification targets:

```
lake env lean YangMills\RG\ClusterDecay.lean
lake build YangMills.RG.ClusterDecay
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\ClusterDecay.lean
```

**Honest scope.** This is finite cluster geometry only.  It does not prove a
local-dependence theorem for `H#`, convergence of the second Ursell series,
Dimock's second-Ursell residual estimate, the physical activity map, or
`hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 277 (2026-06-23, **Hsharp finite local dependence**
`YangMills.RG.AppendixFHsharp`; core 8343)

This addendum records the first local-dependence consumer for the second
Ursell object.  The new theorem names are:

```
omegaHolePolymerSystem_ursell_eq
appendixFHoleHsharpTerm_eq_of_activity_eq_on_union
appendixFHoleHsharpTerm_eq_of_activity_eq_on_skeleton
appendixFHoleHsharp_eq_of_activity_eq_on_union
appendixFHoleHsharp_eq_of_activity_eq_on_skeleton
appendixFHoleHsharpOfKsharp_eq_of_agreeOn
appendixFHoleHsharpOfKsharp_eq_of_agreeOn_skeleton
```

The fixed-size term theorems say that a target fiber contribution is unchanged
when the two scalar second-gas activities agree on every tuple component
polymer contained in the declared full target, respectively whose active
skeleton is contained in the declared target skeleton.  The totalized `H#`
theorems are termwise `tsum_congr` wrappers.  The evaluated `K#`
specializations compose these abstract facts with the existing `K#` support
wrappers, giving full-target and active-skeleton spectator-field agreement
for `appendixFHoleHsharpOfKsharp`.

Verification targets:

```
lake env lean YangMills\RG\AppendixFHsharp.lean
lake build YangMills.RG.AppendixFHsharp
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\AppendixFHsharp.lean
```

**Honest scope.** This is finite support/local-dependence bookkeeping for the
already-defined Appendix-F `H#` object.  It does not prove convergence of the
`H#` series, identify it with a logarithm, prove Dimock's residual estimate,
construct the physical activity map, or discharge `hraw`.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 278 (2026-06-23, **integrated Hsharp finite locality**
`YangMills.RG.AppendixFHsharp`; core 8343)

This addendum completes the four public finite `H#` locality declarations
requested by the Hsharp packet by adding the spectator-integrated scalar
specializations:

```
appendixFHoleHsharpOfIntegratedKsharp_eq_of_agreeOn
appendixFHoleHsharpOfIntegratedKsharp_eq_of_agreeOn_skeleton
```

Since `appendixFHoleHsharpOfIntegratedKsharp` has already integrated both the
spectator and fluctuation fields, these are not new field-agreement theorems.
They are scalar integrated-activity extensionality wrappers: target-level
`H#` is unchanged when the two integrated `z_K` activities agree on every
component polymer contained in the declared full target, respectively whose
active skeleton is contained in the declared target skeleton.  The proof is a
direct application of the existing generic `appendixFHoleHsharp` activity
extensionality theorem; no integral is unfolded.

Verification targets:

```
lake env lean YangMills\RG\AppendixFHsharp.lean
lake build YangMills.RG.AppendixFHsharp
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\AppendixFHsharp.lean
```

**Honest scope.** This is finite support/local-dependence bookkeeping for the
already-defined Appendix-F integrated `H#` object.  It does not prove
measurability, integrability, convergence of the `H#` series, identify it with
a logarithm, prove Dimock's residual estimate, construct the physical activity
map, or discharge `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 279 (2026-06-23, **CMP116 evaluated Hsharp support dependencies**
`YangMills.RG.BalabanCMP116HsharpAdapter`; core 8343)

This addendum adds the CMP116-facing evaluated-`K#` normal form for the
second-Ursell object:

```
balabanCMP116AppendixFHsharpOfKsharp
balabanCMP116AppendixFHsharpOfKsharp_eq_hsharp
balabanCMP116AppendixFHsharpOfKsharp_eq_of_agreeOn
balabanCMP116AppendixFHsharpOfKsharp_eq_of_agreeOn_skeleton
```

The full-target and active-skeleton wrappers compose the existing
`BalabanCMP116AppendixFSupportHypotheses` support package with the generic
Appendix-F `appendixFHoleHsharpOfKsharp` dependency theorems.  No new support
obligation is introduced: the same single source-side active-support inclusion
`F.activeSupport X subset skeleton HF X.val` supplies both the full target and
active-skeleton versions.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116HsharpAdapter.lean
lake build YangMills.RG.BalabanCMP116HsharpAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116HsharpAdapter.lean
```

**Honest scope.** This is a finite support-dependency and naming bridge for
the CMP116 evaluated `H#` layer.  It does not prove CMP116 random-walk
localization, measurability of the physical integrand, Wilson-Hessian
identification, covariance-root decay, convergence of the `H#` series,
Dimock's residual estimate, the physical activity map, or `hraw`.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 280 (2026-06-23, **physical CMP116 activity transport bridge**
`YangMills.RG.PhysicalGaugeCMP116ActivityAdapter`; core 8344)

This addendum adds the structural bridge from the source-facing physical
localized-Gaussian activity certificate to the CMP116/Appendix-F raw activity
interface:

```
PhysicalGaugeCMP116ActivityTransport
physicalGaugeCMP116SupportHypotheses_of_transport
balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport
```

The transport record deliberately carries the source obligations as fields:
the physical activity certificate, the CMP116 localized activity family,
spectator/fluctuation transports into physical positive-bond fields, exact
`globalEval` preservation under those transports, active-support containment
inside `skeleton HF X.val`, and domination of the physical decay weight by
`appendixFHoleExpWeight HF κ X.val`.  The support theorem extracts the existing
`BalabanCMP116AppendixFSupportHypotheses`; the raw theorem chains the physical
certificate's combined raw-decay estimate with the weight domination to produce
the `hraw` shape consumed by Appendix F.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
```

**Honest scope.** This is a source-obligation adapter.  It does not construct
the physical CMP116 localized activity, prove the Wilson Hessian identity,
prove covariance-root localization, prove source measurability, or discharge
the actual `hraw` theorem.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 281 (2026-06-23, **physical-to-CMP116 finite reindexing layer**
`YangMills.RG.PhysicalGaugeCMP116ActivityAdapter`; core 8344)

This addendum implements the lower finite bridge requested by the
physical/CMP116 audit packet.  The new declarations are:

```
PhysicalGaugeRawActivityDecay
LocalActivity.reindex
LocalActivity.globalEval_reindex
PhysicalGaugeCMP116ActivityAdapter
PhysicalGaugeCMP116ActivityAdapter.pullSpectator
PhysicalGaugeCMP116ActivityAdapter.pullFluctuation
PhysicalGaugeCMP116ActivityAdapter.activity
PhysicalGaugeCMP116ActivityAdapter.activeSupport
PhysicalGaugeCMP116ActivityAdapter.globalEval_activity
PhysicalGaugeCMP116ActivityAdapter.spectatorSupport_activity_subset_activeSupport
PhysicalGaugeCMP116ActivityAdapter.fluctuationSupport_activity_subset_activeSupport
```

`LocalActivity.reindex` transports a source local activity along a finite site
map.  Its spectator and fluctuation supports are the finite images of the
source supports, and `globalEval_reindex` rewrites target evaluation exactly to
source evaluation on pulled-back global fields.

`PhysicalGaugeCMP116ActivityAdapter` is the finite physical positive-bond to
cube-site shell: it stores the physical index map, `bondToCube`, spectator and
fluctuation coordinate pulls, and `Omega`.  Its derived `activity` and
`activeSupport` reindex physical local activities and project physical active
supports.  The two support lemmas transport only the certificate's common
physical support containment to the projected cube active support; the Ω half
of CMP116 fluctuation support remains an explicit source obligation.

Verification targets:

```
lake env lean YangMills\RG\LocalFunctional.lean
lake env lean YangMills\RG\PhysicalGaugeFluctuationActivity.lean
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\LocalFunctional.lean YangMills\RG\PhysicalGaugeFluctuationActivity.lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
```

**Honest scope.** This is finite reindexing and support-image bookkeeping.  It
does not construct `BalabanCMP116LocalizedActivityFamily` from the physical
certificate, prove Ω-locality, prove strong measurability, identify the Wilson
fluctuation activity, prove Gaussian pushforward, compare metrics/constants,
or discharge physical `hraw`.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 282 (2026-06-23, **named CMP116 raw metric decay bridge**
`YangMills.RG.PhysicalGaugeCMP116ActivityAdapter`; core 8344)

This addendum names and factors the first-activity raw metric-decay bridge.
The new public declarations are:

```
BalabanCMP116RawMetricDecay
BalabanCMP116LocalizedActivityFamily.of_physicalLocalizedGaussianActivityCertificate
balabanCMP116RawMetricDecay_of_physicalGaugeRawActivityDecay
```

`BalabanCMP116RawMetricDecay` is the universal CMP116 `H(X)` pointwise bound
over an Appendix-F polymer family:

```
∀ ψ φ X, X ∈ Λ →
  ‖(F.activity X).globalEval ψ φ‖ ≤
    H0 * appendixFHoleExpWeight HF κ X.val
```

It is explicitly the first localized activity bound, not the second-Ursell
`H#` residual estimate.  The family constructor is deliberately only a
projection from `PhysicalGaugeCMP116ActivityTransport`; it does not derive the
CMP116 family from the physical certificate or covariance localization alone.
The raw-decay theorem uses only exact `globalEval` preservation, a named
`PhysicalGaugeRawActivityDecay`, the weight domination field, and `0 ≤ H0`.
The existing `balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport` is
now a compatibility specialization of this named predicate.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "\b(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
```

The broad `rg` scan only matches the file-level oracle-target comment in this
module; a declaration-shaped scan has no `sorry`/`admit`/`axiom` hits.

**Honest scope.** This commit names and factors an existing conditional bridge.
It does not prove physical raw decay, construct the CMP116 localized family,
prove Ω-locality, prove strong measurability, prove rooted summability, or
prove the Appendix-F `H#` residual estimate.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 283 (2026-06-23, **exact CMP116 local linear-operator support**
`YangMills.RG.LocalLinearOperator`; core 8345)

This addendum starts the corrected upstream route before any conditional raw
decay bridge.  It adds exact finite support algebra for CMP116 fluctuation
fields:

```
CMP116FluctuationField
cmp116FieldProjection
cmp116FieldProjection_comp
OperatorSupportedBetween
OperatorSupportedBetween.eq_of_agreeOn
OperatorSupportedBetween.apply_eq_zero_outside
OperatorSupportedBetween.add
OperatorSupportedBetween.finsetSum
OperatorSupportedBetween.comp
OperatorSupportedBetween.mono
```

`OperatorSupportedBetween Xin Xout T` means exactly that `T` reads only the
coordinates in `Xin` and has output supported in `Xout`, expressed by equality
against finite coordinate projections.  This is the algebraic support notion
needed before decomposing a nonlocal linear change of variables into local
pieces.

Verification:

```
lake env lean YangMills\RG\LocalLinearOperator.lean
lake build YangMills.RG.LocalLinearOperator
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\LocalLinearOperator.lean
```

**Honest scope.** This commit fixes only exact projection/support algebra for
finite CMP116 coordinate fields.  It does not construct a polymer-local raw
activity, prove a Gaussian change of variables, prove physical raw decay,
localize a physical covariance root, identify a Wilson Hessian, or prove any
Appendix-F cluster estimate.  The Addendum 282 projection remains only a
conditional compatibility bridge, not the constructive route.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 284 (2026-06-23, **physical/CMP116 coordinate dictionary**
`YangMills.RG.PhysicalGaugeCMP116Dictionary`; core 8346)

This addendum adds the first exact finite dictionary between physical
positive-bond degrees of freedom and CMP116 cube coordinates.  The new public
declarations include:

```
CMP116CoordIndex
PhysicalGaugeCoordIndex
PhysicalGaugeCMP116SiteMap
PhysicalGaugeCMP116SiteMap.physicalBondsOver
PhysicalGaugeCMP116Dictionary
PhysicalGaugeCMP116Dictionary.coordEquiv_symm_cell
PhysicalGaugeCMP116Dictionary.pullFluctuationCochain
PhysicalGaugeCMP116Dictionary.pushFluctuation
PhysicalGaugeCMP116Dictionary.pushFluctuation_pullFluctuationCochain
PhysicalGaugeCMP116Dictionary.pullFluctuationCochain_pushFluctuation
PhysicalGaugeCMP116Dictionary.fluctuationFieldLinearEquiv
PhysicalGaugeCMP116Dictionary.pullFluctuationCochain_agreeOn_iff
PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange
```

The structure identifies scalar coordinates
`Cube d L × Fin lieDim` with
`PhysicalBond dPhys N × Fin (Nc^2 - 1)` and carries the cell-compatibility law
that the associated physical bond maps back to the original CMP116 cube.  The
induced pull/push maps between CMP116 coordinate fields and physical
one-cochains are exact inverses, and the support-agreement theorem states that
agreement on a cube set is equivalent to agreement after pulling back on all
physical bonds assigned to that cube set.

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116Dictionary.lean
lake build YangMills.RG.PhysicalGaugeCMP116Dictionary
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116Dictionary.lean
rg -n "PhysicalLocalizedGaussianActivityCertificate|weight_domination|raw_bound|decay_bound|H0|κ|root" YangMills\RG\PhysicalGaugeCMP116Dictionary.lean
```

The final grep is expected to return empty.

**Honest scope.** This commit fixes only finite scalar-coordinate packing and
support-agreement transfer.  It does not construct a polymer-local raw
activity, prove a physical Gaussian change of variables, localize the physical
square-root map, identify a Wilson Hessian, or prove any Appendix-F estimate.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 285 (2026-06-23, **localized physical-root transport to CMP116 operators**
`YangMills.RG.PhysicalGaugeCMP116OperatorTransport`; core 8347)

This addendum adds the finite operator-support layer needed between a supplied
physical covariance root and later CMP116 activity construction.  The new
public declarations include:

```
singleCMP116CubeField
cmp116Field_eq_sum_singleCube
map_cmp116Field_eq_sum_singleCube
CMP116LinearMapKernelBound
CMP116KernelFiniteRange
cmp116FiniteRangeClosure
OperatorSupportedBetween.of_singleBond_kernel_zero
OperatorSupportedBetween.of_kernel_bound_finiteRange
CMP116LocalizedLinearMap
CMP116LocalizedLinearMap.ofProjection
physicalBondProjection
physicalBondsOver
cmp116OperatorOfPhysical
PhysicalRootToCMP116OperatorTransport
PhysicalRootToCMP116OperatorTransport.rootOperator
PhysicalRootToCMP116OperatorTransport.localizedRootOperator
PhysicalRootToCMP116OperatorTransport.rootOperator_kernelBound_of_certificate
PhysicalRootToCMP116OperatorTransport.localizedRootOperator_supportedBetween
PhysicalRootToCMP116OperatorTransport.localizedRootOperator_eq_of_agreeOn
PhysicalRootToCMP116OperatorTransport.localizedRootOperator_apply_eq_zero_outside
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMap
```

Verification targets:

```
lake env lean YangMills\RG\LocalLinearOperator.lean
lake build YangMills.RG.LocalLinearOperator
lake env lean YangMills\RG\PhysicalGaugeCMP116OperatorTransport.lean
lake build YangMills.RG.PhysicalGaugeCMP116OperatorTransport
lake env lean YangMills\RG\PhysicalGaugeFluctuationActivity.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\LocalLinearOperator.lean YangMills\RG\PhysicalGaugeCMP116OperatorTransport.lean
rg -n "PhysicalGaugeRawActivityDecay|BalabanCMP116RawMetricDecay|PhysicalGaugeCMP116ActivityTransport|weight_domination|raw_bound|decay_bound|H0|κ" YangMills\RG\PhysicalGaugeCMP116OperatorTransport.lean
```

The final grep is expected to return empty.

**Honest scope.** This commit transports supplied root/operator data into a
CMP116 exact-support form and proves finite-range support consequences.  It
does not construct the physical covariance root, prove root localization or
truncation, build local Wilson activities, prove Gaussian change of variables,
or prove raw activity decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 286 (2026-06-23, **dictionary-instantiated CMP116 activity adapter**
`YangMills.RG.PhysicalGaugeCMP116ActivityAdapter`; core 8347)

This addendum closes a small finite bridge between the physical/CMP116 scalar
coordinate dictionary and the activity adapter.  The new public declarations
include:

```
PhysicalGaugeCMP116Dictionary.image_bondToCube_subset_iff_physicalBondsOfCells
PhysicalGaugeCMP116Dictionary.pullFluctuationAtBond
PhysicalGaugeCMP116Dictionary.pullFluctuationCochain_apply
PhysicalGaugeCMP116ActivityAdapter.ofDictionary
PhysicalGaugeCMP116ActivityAdapter.pullFluctuation_ofDictionary
PhysicalGaugeCMP116ActivityAdapter.globalEval_activity_ofDictionary
PhysicalGaugeCMP116ActivityAdapter.spectatorSupport_activity_ofDictionary_subset_iff
PhysicalGaugeCMP116ActivityAdapter.fluctuationSupport_activity_ofDictionary_subset_iff
PhysicalGaugeCMP116ActivityAdapter.activeSupport_ofDictionary_subset_iff
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116Dictionary.lean
lake build YangMills.RG.PhysicalGaugeCMP116Dictionary
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116Dictionary.lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
git diff --cached -U0 -- YangMills\RG\PhysicalGaugeCMP116Dictionary.lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean | rg -n "^\+.*(PhysicalGaugeRawActivityDecay|BalabanCMP116RawMetricDecay|PhysicalGaugeCMP116ActivityTransport|weight_domination|raw_bound|decay_bound|H0|κ|GaussianChange|gaussian)"
```

The final staged-source grep is expected to return empty.

**Honest scope.** This checkpoint is finite support and field-transport
bookkeeping.  It makes the adapter consume the existing dictionary directly but
does not construct a localized activity family, prove a Gaussian pushforward,
localize a covariance root, identify a Wilson Hessian, or prove `hraw`.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 287 (2026-06-23, **dictionary-instantiated CMP116 localized family**
`YangMills.RG.PhysicalGaugeCMP116ActivityAdapter`; core 8347)

This addendum closes the next finite theorem gate after the dictionary adapter:
it constructs the concrete `BalabanCMP116LocalizedActivityFamily` obtained from
dictionary-instantiated physical local activities, provided the source side
supplies exactly the remaining finite/local obligations: strong measurability,
physical spectator/fluctuation support containment, and physical active-support
Ω-locality.

The new public declarations are:

```
PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary
PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary_Omega
PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary_activeSupport
PhysicalGaugeCMP116ActivityAdapter.localizedFamilyOfDictionary_activity
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
git diff --cached -U0 -- YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean | rg -n "^\+.*(PhysicalGaugeRawActivityDecay|BalabanCMP116RawMetricDecay|PhysicalGaugeCMP116ActivityTransport|weight_domination|raw_bound|decay_bound|H0|κ|GaussianChange|gaussian|hraw)"
```

The final staged-source grep is expected to return empty.

**Honest scope.** This checkpoint is not a producer theorem for `H(Z)`: it
does not construct the physical local activities, prove Gaussian change of
variables, localize `C^(1/2)`, identify a Wilson Hessian, prove raw decay, or
discharge `hraw`.  It only packages already supplied physical support and
measurability obligations into the concrete CMP116 localized-family interface.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 288 (2026-06-23, **Appendix-F support from dictionary localized family**
`YangMills.RG.PhysicalGaugeCMP116ActivityAdapter`; core 8347)

This addendum closes the finite support bridge from the dictionary-built
CMP116 localized family into the Appendix-F support-hypothesis record.  If the
source side proves that each physical active support, after the CMP116
dictionary projection, lies over the active skeleton of the target polymer, the
existing localized family now supplies `BalabanCMP116AppendixFSupportHypotheses`
directly.

The new public declaration is:

```
PhysicalGaugeCMP116ActivityAdapter.appendixFSupportHypotheses_of_localizedFamilyOfDictionary
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean
git diff --cached -U0 -- YangMills\RG\PhysicalGaugeCMP116ActivityAdapter.lean | rg -n "^\+.*(PhysicalGaugeRawActivityDecay|BalabanCMP116RawMetricDecay|PhysicalGaugeCMP116ActivityTransport|weight_domination|raw_bound|decay_bound|H0|κ|GaussianChange|gaussian|hraw)"
```

The final staged-source grep is expected to return empty.

**Honest scope.** This is a finite support theorem.  It does not construct the
physical local activities, prove Gaussian change of variables, localize
`C^(1/2)`, identify a Wilson Hessian, prove raw decay, or discharge `hraw`.
It only turns an explicit physical preimage-to-skeleton support obligation into
the Appendix-F support package consumed by later CMP116 layers.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 289 (2026-06-23, **dictionary-backed localized Gaussian activity construction**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8348)

This addendum adds a source-facing construction layer that assembles existing
dictionary, covariance-root transport, Gaussian-change, localized-family, and
physical transport records without adding analytic content.  The dictionary now
provides the continuous coordinate equivalence, the projection compatibility
used by CMP116 root transport, the canonical `root ∘ dictionary` Gaussian map,
and constructors for the localized family and transport package.

The new public declarations are:

```
PhysicalGaugeCMP116Dictionary.fluctuationFieldContinuousLinearEquiv
PhysicalGaugeCMP116Dictionary.fluctuationFieldContinuousLinearEquiv_support_projection
PhysicalGaugeCMP116Dictionary.gaussianRootMap
PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.ofDictionaryRoot
PhysicalRootToCMP116OperatorTransport.ofDictionary
PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses
physicalLocalizedGaussianActivityCertificate_of_cmp116Source
BalabanCMP116LocalizedActivityFamily.ofDictionary
PhysicalGaugeCMP116ActivityTransport.ofDictionary
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
```

**Honest scope.** This checkpoint does not prove that the dictionary/root map
preserves a Gaussian law, does not localize the exact covariance root, does not
identify the Wilson Hessian, does not construct physical local activities, does
not prove raw decay, and does not discharge `hraw` or `hRpoly`.  It only removes
arbitrary coordinate/family plumbing by making the dictionary-backed choices
canonical wherever the existing interfaces already support that assembly.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 290 (2026-06-23, **canonical Gaussian pushforward integral consumer**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8348)

This addendum adds the first consumer theorem for the dictionary-backed
Gaussian change of variables.  Given an explicit pushforward identity in the
existing `PhysicalGaugeCMP116GaussianChange` record, complex-valued Bochner
integrals can now be rewritten from the physical Gaussian measure back to the
CMP116 product-coordinate measure.  The canonical specialization applies this
directly to `D.gaussianRootMap root`.

The new public declarations are:

```
PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.integral_gaussianCoordinateMap_eq
PhysicalGaugeCMP116Dictionary.PhysicalGaugeCMP116GaussianChange.integral_ofDictionaryRoot
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean oracle_check.lean
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint still does not prove the Gaussian
pushforward identity, localize the covariance root, identify the Wilson
Hessian, construct physical local activities, prove raw decay, or discharge
`hraw`/`hRpoly`.  It only turns a supplied source pushforward theorem into a
stable integral rewrite consumed by later localized-activity estimates.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 291 (2026-06-23, **source-package Gaussian integral accessor**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8348)

This addendum wires the separated localized-Gaussian source package to the
canonical Gaussian integral consumer from Addendum 290.  The source package now
has a named `gaussianChange` accessor and a direct source-package integral
rewrite, both derived only from the explicit `gaussian_pushforward` field.

The new public declarations are:

```
PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.gaussianChange
PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.integral_gaussianRootMap_eq
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean oracle_check.lean
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint still does not prove the source
`gaussian_pushforward` theorem.  It does not localize the covariance root,
identify the Wilson Hessian, construct physical local activities, prove raw
decay, or discharge `hraw`/`hRpoly`.  It only makes the existing source package
directly consumable by downstream estimates that need the Gaussian integral
rewrite.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 292 (2026-06-23, **physical-activity Gaussian integral consumer**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8348)

This addendum specializes the source-package Gaussian integral rewrite to the
concrete physical local activity evaluator.  Downstream source-faithful
activity estimates can now rewrite the CMP116 product-coordinate integral of
`activity.globalEval` after `D.gaussianRootMap root` directly to the
corresponding physical Gaussian integral.

The new public declaration is:

```
PhysicalGaugeCMP116LocalizedGaussianActivitySourceHypotheses.integral_physicalActivity_gaussianRootMap_eq
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry reports only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint still does not prove the source
`gaussian_pushforward` theorem.  It does not localize the covariance root,
identify the Wilson Hessian, construct physical local activities, prove raw
decay, or discharge `hraw`/`hRpoly`.  It only makes the existing Gaussian
source package directly consumable by physical local activity estimates.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 293 (2026-06-23, **raw-source compatibility adapter**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8348)

This addendum adds the thin compatibility package requested for the current
source path.  The new raw-source structure extends the separated
localized-Gaussian source package with the unfolded physical pointwise raw
estimate, and the two new adapter theorems derive the existing physical raw
decay predicate and localized-Gaussian certificate from that one source
package.

The new public declarations are:

```
PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses
physicalGaugeRawActivityDecay_of_cmp116RawSource
physicalLocalizedGaussianActivityCertificate_of_cmp116RawSource
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries are expected to remain within
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint still does not prove the Gaussian
pushforward, covariance-root localization, Wilson-Hessian identification,
physical local activity construction, or the raw pointwise estimate.  It only
packages that unfolded raw estimate as a source field and removes the separate
`PhysicalGaugeRawActivityDecay` premise from the compatibility certificate
constructor.  It does not discharge `hraw`, `hRpoly`, fluctuation
integrability, or any continuum-facing obligation.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 294 (2026-06-23, **raw-source CMP116 transport consumers**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8348)

This addendum composes the raw-source compatibility package with the existing
dictionary transport and Appendix-F raw-decay adapters.  Given the raw-source
package plus the still-explicit source measurability, support localization, and
weight-domination hypotheses, Lean now constructs the full
`PhysicalGaugeCMP116ActivityTransport`, derives `BalabanCMP116RawMetricDecay`
for the transported family, and exposes the exact pointwise `hraw` shape
consumed by the Appendix-F estimates.

The new public declarations are:

```
physicalGaugeCMP116ActivityTransport_of_cmp116RawSource
balabanCMP116RawMetricDecay_of_cmp116RawSource
balabanCMP116_hraw_of_cmp116RawSource
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries are expected to remain within
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint does not prove source measurability,
Appendix-F support localization, weight domination, the raw activity estimate,
Gaussian pushforward, covariance-root localization, Wilson-Hessian
identification, fluctuation integrability, or `hRpoly`.  It only proves that,
once those source/geometric hypotheses are supplied, the existing transport
stack reaches `BalabanCMP116RawMetricDecay` and the exact Appendix-F `hraw`
premise without another separate raw-decay argument.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 295 (2026-06-23, **raw-source H# scale consumer**
`YangMills.RG.PhysicalGaugeCMP116RawHsharp`; core 8349)

This addendum adds the scale-indexed consumer for the raw-source CMP116 path.
The new module packages the canonically transported raw-source localized
families over RG scales and feeds them into the existing source-measurable H#
UV endpoint.  The theorem discharges the endpoint's `hraw` premise from
`balabanCMP116_hraw_of_cmp116RawSource`; it does not replace the H# remainder,
probability, geometry, smallness, or profile hypotheses.

The new public declarations are:

```
physicalGaugeCMP116RawSourceScaleFamily
singleScaleUVDecay_of_cmp116RawSource_hsharp
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116RawHsharp.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116RawHsharp.lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint is source-independent plumbing.  It still
does not prove source measurability, Appendix-F support localization, weight
domination, integrability, the rooted physical remainder identity, the
probability law, the H# smallness/profile inequalities, Gaussian pushforward,
covariance-root localization, Wilson-Hessian identification, local physical
activity construction, raw pointwise estimates, or `hRpoly`.  It only shows
that once a scale-indexed raw-source package supplies those inputs, the
existing H# theorem consumes the transported family without a separate `hraw`
argument.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 296 (2026-06-23, **namespaced raw-source transport and support**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8349)

This addendum gives the raw-source transport its canonical namespaced
constructor and adds the missing direct Appendix-F support-package projection.
The older global transport constructor remains as a compatibility alias of the
namespaced constructor, and the existing raw-metric and `hraw` wrappers keep
their public names.

The new public declarations are:

```
PhysicalGaugeCMP116ActivityTransport.of_cmp116RawSource
physicalGaugeCMP116SupportHypotheses_of_cmp116RawSource
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint adds no new analytic input and proves no new
Balaban estimate.  It only centralizes the already-verified composition
`raw-source package -> localized Gaussian certificate -> dictionary transport`
under the namespaced constructor and exposes the support package as a named
projection.  Source measurability, support localization, weight domination,
raw pointwise decay, Gaussian pushforward, covariance-root localization,
Wilson-Hessian identification, integrability, H#/K# smallness, `hRpoly`, and
the continuum problem all remain open.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 297 (2026-06-23, **transport-backed K# consumer**
`YangMills.RG.BalabanCMP116SecondGasAdapter`; core 8349)

This addendum adds the transport-level single-scale K# consumer for the CMP116
activity path.  The theorem takes a
`PhysicalGaugeCMP116ActivityTransport`, projects its localized family
`T.family`, derives the Appendix-F raw bound from
`balabanCMP116_hraw_of_physicalGaugeCMP116ActivityTransport`, and feeds both
into the existing spectator-integrated K# estimate.

The new public declaration is:

```
norm_balabanCMP116AppendixFIntegratedKsharpActivity_le_ksharpRate_of_transport
```

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116SecondGasAdapter.lean
lake build YangMills.RG.BalabanCMP116SecondGasAdapter
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116SecondGasAdapter.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry reports only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint adds no new analytic input and proves no new
Balaban estimate beyond reusing the existing K# theorem.  It only removes
independent `F` and `hraw` arguments from this transport-backed K# call site.
Probability, target-region membership, rooted leaf budget, smallness,
rate-margin hypotheses, source measurability, support localization, weight
domination, raw pointwise decay, Gaussian pushforward, covariance-root
localization, Wilson-Hessian identification, H#/K# endpoint smallness,
`hRpoly`, and the continuum problem all remain open.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 298 (2026-06-23, **raw-source H# to marginal M3**
`YangMills.RG.PhysicalGaugeCMP116RawM3`; core 8350)

This addendum routes the raw-source CMP116/H# endpoint into the marginal
lattice M3 assembly.  `YangMills.RG.MarginalUVMassGap` now exposes the named
predicate consumer `lattice_mass_gap_of_singleScaleUVDecay_marginal`; the new
module `YangMills.RG.PhysicalGaugeCMP116RawM3` defines the CMP116 H# UV
amplitude and proves the direct raw-source theorem
`lattice_mass_gap_of_cmp116RawSource_hsharp_marginal`.

The new public declarations are:

```
cmp116RawHsharpUVAmplitude
lattice_mass_gap_of_singleScaleUVDecay_marginal
lattice_mass_gap_of_cmp116RawSource_hsharp_marginal
```

Verification targets:

```
lake env lean YangMills\RG\MarginalUVMassGap.lean
lake build YangMills.RG.MarginalUVMassGap
lake env lean YangMills\RG\PhysicalGaugeCMP116RawM3.lean
lake build YangMills.RG.PhysicalGaugeCMP116RawM3
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\MarginalUVMassGap.lean YangMills\RG\PhysicalGaugeCMP116RawM3.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint adds no new physical/source estimate.  It
only composes the existing raw-source H# `SingleScaleUVDecay` producer with the
already verified marginal-coupling lattice assembly.  The rooted H# remainder
identity, source package, covariance/root localization, Gaussian pushforward,
Wilson-Hessian identification, local activity construction, support and weight
domination, strong measurability/integrability, H# profile and half-budget
inequalities, marginal-flow hypotheses, IR bound, `hRpoly`, and the continuum
problem all remain open.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 299 (2026-06-23, **raw-source H# frontier bundle**
`YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier`; core 8351)

This addendum names the exact raw-source CMP116/H# hypothesis boundary as the
proposition-valued structure `PhysicalGaugeCMP116RawHsharpFrontier`.  The new
module projects that bundle into the existing UV producer and into the
marginal-coupling M3 consumer via
`PhysicalGaugeCMP116RawHsharpFrontier.singleScaleUVDecay` and
`PhysicalGaugeCMP116RawHsharpFrontier.lattice_mass_gap_marginal`.

The new public declarations are:

```
PhysicalGaugeCMP116RawHsharpFrontier
PhysicalGaugeCMP116RawHsharpFrontier.singleScaleUVDecay
PhysicalGaugeCMP116RawHsharpFrontier.lattice_mass_gap_marginal
```

Verification targets:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116RawHsharpFrontier.lean
lake build YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116RawHsharpFrontier.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint proves no new source estimate and discharges
no physical hypothesis.  It only replaces a long endpoint argument surface with
one named, auditable frontier object and reuses the already verified raw-source
H# and marginal M3 consumers.  The Hessian construction, Gaussian pushforward,
covariance-root localization, Wilson-Hessian identification, local activity
construction, rooted H# remainder identity, H# profile and half-budget
estimates, marginal-flow hypotheses, IR bound, `hRpoly`, and the continuum
problem all remain open.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 300 (2026-06-23, **raw-source M3 frontier wrapper**
`YangMills.RG.PhysicalGaugeCMP116RawM3`; core 8351)

This addendum adds the M3-specific frontier bundle
`CMP116RawSourceM3Frontier` and the top-level wrapper
`lattice_mass_gap_of_cmp116RawSourceM3Frontier`.  The wrapper calls the
existing theorem `lattice_mass_gap_of_cmp116RawSource_hsharp_marginal`; it only
replaces the separate raw-source/H# proof arguments, support/geometric facts,
measure facts, Appendix-F profile facts, marginal-flow facts, and IR bound by
one record.  The truncation schedule `nsc` remains a theorem parameter rather
than a record field.

The new public declarations are:

```
CMP116RawSourceM3Frontier
lattice_mass_gap_of_cmp116RawSourceM3Frontier
```

Verification targets:

```
git diff --check
lake env lean YangMills\RG\PhysicalGaugeCMP116RawM3.lean
lake build YangMillsCore
lake env lean oracle_check.lean
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116RawM3.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry reports only
`[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint proves no source theorem and does not
construct a physical frontier witness.  It only provides the current marginal
M3 endpoint with one named record argument instead of many independent proof
arguments.  The concrete covariance/root certificate, Gaussian pushforward,
Wilson-Hessian identification, local activity construction, raw pointwise
decay, Appendix-F support and weight transport, rooted H# remainder identity,
profile/half-budget estimates, marginal flow, IR decay, `hRpoly`, and the
continuum problem all remain open.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 301 (2026-06-23, **executable M3 frontier dependency graph**
`YangMills.RG.M3FrontierDependencies`; core 8352)

This addendum adds an executable audit graph for `CMP116RawSourceM3Frontier`.
`CMP116RawSourceM3FrontierField` has one constructor for each of the 30
frontier fields, `M3FrontierHypothesisKind` classifies them as analytic,
geometric, measure-theoretic, or RG-flow facts, and
`M3FrontierDependencyGraph` records the current derived spine:

```
frontier fields -> rawSourceScaleFamily -> rawSourceHsharpUVDecay
  -> marginalM3Assembly
```

The graph checks are theorem-backed:

```
M3FrontierDependencyGraph.isAcyclic_eq_true
M3FrontierDependencyGraph.allFrontierFieldsCovered_eq_true
M3FrontierDependencyGraph.allFrontierFieldsUsed_eq_true
M3FrontierDependencyGraph.derivedNodesHavePositiveRank_eq_true
```

The companion note is `docs/M3-FRONTIER-DEPENDENCIES.md`.

Verification targets:

```
lake env lean YangMills\RG\M3FrontierDependencies.lean
lake build YangMills.RG.M3FrontierDependencies
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\M3FrontierDependencies.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\M3-FRONTIER-DEPENDENCIES.md
```

The new oracle entries report no project axioms.

**Honest scope.** This checkpoint is an audit layer only.  It proves no
physical source theorem, adds no frontier field, and does not make `hraw`,
H# decay, `SingleScaleUVDecay`, or the M3 conclusion into source assumptions.
The concrete covariance/root certificate, Gaussian pushforward,
Wilson-Hessian identification, local activity construction, raw pointwise
decay, Appendix-F support and weight transport, rooted H# remainder identity,
profile/half-budget estimates, marginal flow, IR decay, `hRpoly`, and the
continuum problem all remain open.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 302 (2026-06-23, **M3 frontier edge-use coverage**
`YangMills.RG.M3FrontierDependencies`; core 8352)

This addendum strengthens the executable audit graph for
`CMP116RawSourceM3Frontier`.  In addition to checking that every frontier field
has a graph node, the graph now checks that every frontier field is consumed by
at least one derived-node input list:

```
M3FrontierDependencyGraph.allInputFields
M3FrontierDependencyGraph.allFrontierFieldsUsed
M3FrontierDependencyGraph.allFrontierFieldsUsed_eq_true
```

The companion note `docs/M3-FRONTIER-DEPENDENCIES.md` records the new invariant.
The new oracle entry reports no axioms.

Verification targets:

```
lake env lean YangMills\RG\M3FrontierDependencies.lean
lake build YangMills.RG.M3FrontierDependencies
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\M3FrontierDependencies.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\M3-FRONTIER-DEPENDENCIES.md
```

**Honest scope.** This remains an audit-only checkpoint.  It does not prove any
physical source theorem or construct a witness for the M3 frontier.  The
concrete covariance/root certificate, Gaussian pushforward,
Wilson-Hessian identification, local activity construction, raw pointwise
decay, Appendix-F support and weight transport, rooted H# remainder identity,
profile/half-budget estimates, marginal flow, IR decay, `hRpoly`, and the
continuum problem all remain open.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 303 (2026-06-23, **Balaban CMP116 source theorem target**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8353)

This addendum states the source-facing target for the raw-source M3 frontier.
The new module adds:

```
PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components
BalabanCMP116SourceAssumptions
BalabanCMP116SourceTheorem
```

`of_components` is pure record packaging.  It reassembles the existing
raw-source compatibility package from its five explicit source components:
Gaussian pushforward, root localization, Wilson-Hessian identification, local
physical activity construction, and raw pointwise decay.

`BalabanCMP116SourceAssumptions` mirrors the current
`CMP116RawSourceM3Frontier` parameter spine while replacing the opaque
`raw_source` field by individually auditable source fields.  The truncation
schedule remains outside the record, matching the frontier.

`BalabanCMP116SourceTheorem` is a proposition:

```
BalabanCMP116SourceAssumptions ... -> CMP116RawSourceM3Frontier ...
```

No theorem named `CMP116RawSourceM3Frontier.of_balabanSource` is introduced in
this checkpoint; that name is reserved for the later proof after the source
facts are actually established.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116SourceTheorem.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

Only `#check` entries are added to `oracle_check.lean` for this checkpoint.

**Honest scope.** This states a checked target interface only.  It does not
prove the covariance/root certificate, Gaussian pushforward, Wilson-Hessian
identification, local activity construction, raw pointwise decay, Appendix-F
support/weight transport, rooted H# remainder identity, profile/half-budget
estimate, marginal flow, IR bound, or any continuum theorem.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 304 (2026-06-23, **Balaban source raw-package projection**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8353)

This addendum adds the reusable source-assumption projection:

```
BalabanCMP116SourceAssumptions.rawSource
```

It takes a `BalabanCMP116SourceAssumptions` value and returns the canonical
scale-indexed
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses` package by
calling `PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_components`
on the five unfolded source fields.  This avoids reconstructing the raw-source
package by hand in later consumers while still not constructing
`CMP116RawSourceM3Frontier`.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMills.RG.BalabanCMP116SourceTheorem
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116SourceTheorem.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

Only a `#check` entry is added to `oracle_check.lean` for this projection.

**Honest scope.** This is projection plumbing only.  It proves no Balaban source
fact, no frontier witness, no mass-gap endpoint, and no continuum theorem.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 305 (2026-06-23, **rooted H# identity raw-source projection bridge**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8353)

This addendum adds the projection-consistency theorem:

```
BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity_rawSource
```

It restates the `BalabanCMP116SourceAssumptions` field
`rooted_hsharp_remainder_identity` using the canonical
`BalabanCMP116SourceAssumptions.rawSource` projection, so later consumers can
refer to one raw-source package instead of duplicating the local
five-component construction.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMills.RG.BalabanCMP116SourceTheorem
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116SourceTheorem.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry is a `#print axioms` for the projection theorem and
reports `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This theorem proves only that the already-assumed rooted H#
identity is definitionally compatible with the canonical raw-source projection.
It does not prove the physical rooted remainder identity, any Balaban source
fact, any frontier witness, or any continuum theorem.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 306 (2026-06-23, **Balaban source assumptions package into M3 frontier**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8353)

This addendum closes the named source-theorem implication by pure record
packaging.  The new declarations are:

```
CMP116RawSourceM3Frontier.of_balabanSourceAssumptions
BalabanCMP116SourceAssumptions.to_m3Frontier
balabanCMP116SourceTheorem_of_assumptions
```

The constructor maps the 29 non-raw source fields directly into the matching
`CMP116RawSourceM3Frontier` fields and maps the five unfolded raw-source fields
through the existing `BalabanCMP116SourceAssumptions.rawSource` projection.  The
rooted H# field is supplied by
`BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity_rawSource`, so
the local raw-source package is definitionally the same one used by the
frontier field.

Verification targets:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMills.RG.BalabanCMP116SourceTheorem
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\BalabanCMP116SourceTheorem.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries are `#print axioms` checks for all three packaging
declarations; each reports `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This proves only the structural implication from the source
assumption record to the existing frontier record.  It does not prove the
covariance/root certificate, Gaussian pushforward, root localization,
Wilson-Hessian identification, local activity construction, raw pointwise
decay, support/weight transport, the physical rooted H# identity, profile or
marginal estimates, IR decay, or any continuum theorem.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 307 (2026-06-23, **resolvent-first local SPD precision substrate**
`YangMills.RG.LocalSPDPrecision`; core 8354)

This addendum adds the first source-independent substrate for the
resolvent-first precision route.  New declarations include:

```
neumannResolventKernel
LocalFiniteRangeResolventData
LocalFiniteRangeResolventData.resolventAmplitude
LocalFiniteRangeResolventData.resolvent_expDecay
InverseSqrtCoefficientMajorant
inverseSqrtCoefficientMajorant_summable
inverseSqrtCoefficientMajorant_tsum_le
inverseSqrtCoefficientMajorant_tail_le
inverseSqrtBinomialCoeff
inverseSqrtBinomialCoeff_majorant
inverseSqrtBinomialCoeff_tsum_le
inverseSqrtBinomialCoeff_tail_le
```

`LocalFiniteRangeResolventData` carries the constants and hypotheses needed by
the existing `finiteRange_resolvent_isExpDecay` theorem.  Its theorem
`resolvent_expDecay` packages those fields into exponential decay of the
Neumann resolvent kernel.  Separately, the scalar inverse-square-root
coefficients `choose(2n,n)/4^n` are proved nonnegative and at most `1`, giving
closed geometric series and shifted-tail bounds for later finite-range
truncations of normalized inverse square roots.

Verification targets:

```
lake env lean YangMills\RG\LocalSPDPrecision.lean
lake build YangMills.RG.LocalSPDPrecision
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\LocalSPDPrecision.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report `[propext, Classical.choice, Quot.sound]` for:

```
LocalFiniteRangeResolventData.resolvent_expDecay
inverseSqrtCoefficientMajorant_summable
inverseSqrtCoefficientMajorant_tail_le
inverseSqrtBinomialCoeff_majorant
inverseSqrtBinomialCoeff_tail_le
```

**Honest scope.** This proves only abstract kernel/scalar estimates.  It does
not identify the Wilson Hessian, prove a spectral sandwich for the physical
precision, prove a physical Combes--Thomas theorem, construct `P^{-1/2}` as a
continuous linear map, produce a covariance-root certificate, or construct any
CMP116 raw activity.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 308 (2026-06-24, **normalized precision inverse-root tail constants**
`YangMills.RG.LocalSPDPrecision`; core 8354)

This addendum extends the resolvent-first local SPD substrate with the scalar
normalization used by a future spectral sandwich.  New declarations include:

```
normalizedPrecisionContraction
normalizedPrecisionContraction_nonneg
normalizedPrecisionContraction_lt_one
one_sub_normalizedPrecisionContraction
inv_one_sub_normalizedPrecisionContraction
inverseSqrtBinomialCoeff_normalized_tail_le
inverseSqrtNormTail
inverseSqrtBinomialCoeff_normalized_scaled_tail_le
```

For abstract constants `0 < m <= M`, the module defines
`q = 1 - m / M`, proves `0 <= q < 1`, records `1 - q = m / M`, and applies the
already proved binomial tail estimate to the normalized inverse-square-root
series.  The scaled theorem includes the prefactor `M^{-1/2}` via
`(Real.sqrt M)⁻¹`, yielding the scalar tail shape expected for finite-range
approximants to a future `P^{-1/2}`.

Verification targets:

```
lake env lean YangMills\RG\LocalSPDPrecision.lean
lake build YangMills.RG.LocalSPDPrecision
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\LocalSPDPrecision.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

New oracle entries report `[propext, Classical.choice, Quot.sound]` for:

```
normalizedPrecisionContraction_nonneg
normalizedPrecisionContraction_lt_one
inv_one_sub_normalizedPrecisionContraction
inverseSqrtBinomialCoeff_normalized_tail_le
inverseSqrtBinomialCoeff_normalized_scaled_tail_le
```

**Honest scope.** This proves only scalar normalization and tail bookkeeping.
It does not prove that the physical Yang--Mills precision has constants `m`
and `M`, does not prove finite propagation, does not construct
`P^{-1/2}` as an operator, and does not produce any covariance-root or CMP116
activity certificate.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 309 (2026-06-24, **physical local-SPD covariance-root frontier**
`YangMills.RG.PhysicalGaugeLocalSPDPrecisionRoot`; core 8355)

This addendum extends the local-SPD route in two stages.

First, `YangMills.RG.LocalSPDPrecision` now exposes the kernel bookkeeping
needed after the indexing audit that `Kpow K 0 = K`.  New declarations include:

```
LocalFiniteRangeResolventData.baseAmplitude
LocalFiniteRangeResolventData.spatialRatio
LocalFiniteRangeResolventData.spatialRatio_nonneg
LocalFiniteRangeResolventData.spatialRatio_lt_one
inverseSqrtKernelRemainder
LocalFiniteRangeResolventData.inverseSqrtKernelRemainder_expDecay
```

The new inverse-square-root kernel remainder is the non-identity tail.  This
keeps diagonal identity contributions outside the tail, matching the current
`Kpow` convention.

Second, the new module
`YangMills.RG.PhysicalGaugeLocalSPDPrecisionRoot` packages normalized
finite-range physical precision data
`precision = scale • (id - normalizedPerturbation)` and derives:

```
PhysicalLocalSPDInverseSqrtData.coercivityConstant
PhysicalLocalSPDInverseSqrtData.spectralUpperConstant
PhysicalLocalSPDInverseSqrtData.coercivityConstant_pos
PhysicalLocalSPDInverseSqrtData.precision_coercive
PhysicalLocalSPDInverseSqrtData.precision_spectral_upper
PhysicalLocalSPDInverseSqrtData.precision_selfAdjoint_form
PhysicalLocalSPDInverseSqrtData.normalizedPerturbation_finiteRange
PhysicalLocalSPDInverseSqrtData.precision_finiteRange_offDiagonal
PhysicalLocalSPDInverseSqrtData.resolvent_expDecay
PhysicalLocalSPDInverseSqrtData.inverseSqrtCoefficient_tail_le
PhysicalLocalSPDInverseSqrtData.inverseSqrtKernelRemainder_expDecay
PhysicalLocalSPDInverseSqrtData.covariance
PhysicalLocalSPDInverseSqrtData.covarianceWeightCandidate
PhysicalLocalSPDInverseSqrtData.rootWeightCandidate
PhysicalLocalSPDPrecisionRootCertificate
PhysicalLocalSPDPrecisionRootCertificate.toLocalizedCovarianceRootCertificate
```

`covariance` is constructed canonically from strict coercivity using
`covarianceOfIsCoerciveCLM`; inverse identities, norm bound, and PSD are then
inherited from the coercive-covariance layer.  The candidate covariance/root
weights explicitly include the missing identity term plus the exponential
tail.

Verification commands run in this checkpoint:

```
lake env lean YangMills\RG\LocalSPDPrecision.lean
lake env lean YangMills\RG\PhysicalGaugeLocalSPDPrecisionRoot.lean
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMills.RG.LocalSPDPrecision
lake build YangMills.RG.PhysicalGaugeLocalSPDPrecisionRoot
lake build YangMillsCore
lake env lean oracle_check.lean
```

`lake build YangMillsCore` completed at **8355 jobs**.  The new oracle entries
report only `[propext, Classical.choice, Quot.sound]` for:

```
LocalFiniteRangeResolventData.inverseSqrtKernelRemainder_expDecay
PhysicalLocalSPDInverseSqrtData.precision_coercive
PhysicalLocalSPDPrecisionRootCertificate.toLocalizedCovarianceRootCertificate
```

**Honest scope.** This is a frontier/package theorem, not a physical source
theorem.  It does not identify the precision with the Wilson Hessian, prove
operator-power domination, identify the canonical covariance with a Neumann
series, construct a continuous-linear-map inverse square root, prove
covariance/root kernel bounds, prove the separate `root_localization` source
field, construct a Gaussian pushforward, build a local physical activity, or
prove raw activity decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 310 (2026-06-24, **single-bond source norm bridge**
`YangMills.RG.PhysicalGaugeCovarianceLocalization`; core 8355)

This addendum exposes the exact norm bookkeeping for physical single-bond
source probes.  New declarations:

```
singlePhysicalBondCochain_eq_toLp_single
norm_singlePhysicalBondCochain
physicalCovarianceKernelBound_const_opNorm
```

The first theorem identifies `singlePhysicalBondCochain source v` with the
standard `PiLp` singleton.  The second gives the exact equality
`‖singlePhysicalBondCochain source v‖ = ‖v‖`.  The third consumes both this
identity and `ContinuousLinearMap.le_opNorm` to give every physical covariance
operator the constant source/target kernel bound with weight `‖C‖`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCovarianceLocalization.lean
lake env lean YangMills\RG\PhysicalGaugeLocalSPDPrecisionRoot.lean
lake build YangMills.RG.PhysicalGaugeCovarianceLocalization
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCovarianceLocalization.lean YangMills\RG\PhysicalGaugeLocalSPDPrecisionRoot.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`
for:

```
singlePhysicalBondCochain_eq_toLp_single
norm_singlePhysicalBondCochain
physicalCovarianceKernelBound_const_opNorm
```

**Honest scope.** This proves only the norm bridge from a single physical bond
source to operator-norm kernel estimates.  It does not prove finite range,
exponential decay, covariance-root localization, Gaussian pushforward,
physical raw activity decay, or any new source theorem.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 311 (2026-06-24, **finite-range support for local-SPD truncations**
`YangMills.RG.KernelDecay` / `YangMills.RG.LocalSPDPrecision`; core 8355)

This addendum adds exact support bookkeeping for finite-range composition
powers and finite inverse-square-root truncations.  New declarations:

```
Kpow_finiteRange
LocalFiniteRangeResolventData.Kpow_finiteRange
inverseSqrtKernelTruncation
LocalFiniteRangeResolventData.inverseSqrtKernelTruncation_finiteRange
PhysicalLocalSPDInverseSqrtData.kernelMajorant_Kpow_finiteRange
PhysicalLocalSPDInverseSqrtData.inverseSqrtKernelTruncation_finiteRange
```

The key convention is still `Kpow K 0 = K`: the `n`th composition power
contains `n + 1` one-step kernels and is supported in range `(n + 1) * R`.
Consequently, the length-`N` non-identity inverse-square-root truncation has
range `N * R`.  The truncation omits the diagonal identity contribution, which
must remain separate in covariance/root weights.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\KernelDecay.lean
lake env lean YangMills\RG\LocalSPDPrecision.lean
lake env lean YangMills\RG\PhysicalGaugeLocalSPDPrecisionRoot.lean
lake build YangMills.RG.KernelDecay
lake build YangMills.RG.LocalSPDPrecision
lake build YangMills.RG.PhysicalGaugeLocalSPDPrecisionRoot
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\KernelDecay.lean YangMills\RG\LocalSPDPrecision.lean YangMills\RG\PhysicalGaugeLocalSPDPrecisionRoot.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`
for:

```
Kpow_finiteRange
LocalFiniteRangeResolventData.Kpow_finiteRange
LocalFiniteRangeResolventData.inverseSqrtKernelTruncation_finiteRange
PhysicalLocalSPDInverseSqrtData.kernelMajorant_Kpow_finiteRange
PhysicalLocalSPDInverseSqrtData.inverseSqrtKernelTruncation_finiteRange
```

**Honest scope.** This is scalar/kernel support bookkeeping.  It does not
identify a physical Wilson Hessian, prove operator-power domination, identify
the canonical covariance with a Neumann series, construct a continuous-linear
map inverse square root, prove covariance/root kernel bounds, construct a
Gaussian pushforward, build a local physical activity, or prove raw activity
decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 312 (2026-06-24, **dictionary/root operator-coordinate identity**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum adds one exact algebra bridge between the canonical physical
Gaussian root map and the same physical root conjugated into CMP116
coordinates:

```
PhysicalGaugeCMP116Dictionary.gaussianRootMap_eq_coordinates_comp_cmp116OperatorOfPhysical
```

The theorem states that `D.gaussianRootMap root` is exactly the
physical-coordinate realization of
`cmp116OperatorOfPhysical D.fluctuationFieldContinuousLinearEquiv root`.  This
prevents future Gaussian-pushforward and activity-transport source theorems
from unfolding both coordinate definitions by hand.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry reports only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is definition-level coordinate algebra.  It does not
prove the Gaussian pushforward theorem, does not establish an isometry or
Jacobian convention for the product Gaussian, does not localize the physical
covariance root, does not identify a Wilson Hessian, does not construct a
local physical activity, and does not prove raw activity decay.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 313 (2026-06-24, **dictionary localized-root support constructor**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum adds the dictionary-specialized localized CMP116 root-map
constructor:

```
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMap_ofDictionary
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMap_ofDictionary_toContinuousLinearMap
```

Given an explicit physical root kernel bound, the dictionary kernel-bound
transport, and a finite-range CMP116 weight, the constructor produces the
exact `CMP116LocalizedLinearMap` from an input cube set `Xin` to the finite
range closure `cmp116FiniteRangeClosure dist R Xin`.  The simp theorem records
that the underlying map is exactly
`(cmp116OperatorOfPhysical D.fluctuationFieldContinuousLinearEquiv root).comp
(cmp116FieldProjection Xin)`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is a transport/support constructor.  It does not prove
the physical root kernel bound, does not prove finite range of the CMP116
weight, does not construct or localize the covariance root, does not identify
a Wilson Hessian, does not prove Gaussian pushforward, and does not construct
or bound a raw activity.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 314 (2026-06-24, **localized-map underlying-map simp API**
`YangMills.RG.LocalLinearOperator`; core 8355)

This addendum adds exact underlying-map identities for the generic CMP116
localized-map constructors:

```
CMP116LocalizedLinearMap.add_toContinuousLinearMap
CMP116LocalizedLinearMap.finsetSum_toContinuousLinearMap
CMP116LocalizedLinearMap.comp_toContinuousLinearMap
CMP116LocalizedLinearMap.ofProjection_toContinuousLinearMap
```

These theorems expose the `toContinuousLinearMap` fields of localized-map
addition, finite sums, composition, and input/output projection.  They are
mechanical API lemmas intended to keep later finite truncation assembly from
unfolding structure definitions manually.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\LocalLinearOperator.lean
lake build YangMills.RG.LocalLinearOperator
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\LocalLinearOperator.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is localized-operator API bookkeeping.  It does not
prove any finite-range estimate, source theorem, covariance-root
construction/localization, Gaussian pushforward, local activity construction,
or raw activity decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 315 (2026-06-24, **dictionary norm-control interface**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum adds generic two-sided norm-control lemmas for the finite
physical/CMP116 dictionary:

```
PhysicalGaugeCMP116Dictionary.norm_pullFluctuationCochain_le
PhysicalGaugeCMP116Dictionary.norm_pushFluctuation_le
PhysicalGaugeCMP116Dictionary.norm_le_inverse_opNorm_mul_norm_pullFluctuationCochain
PhysicalGaugeCMP116Dictionary.norm_le_opNorm_mul_norm_pushFluctuation
```

The forward lemmas bound the dictionary pull/push maps by the operator norm of
the continuous dictionary equivalence and its inverse.  The reverse lemmas
apply the opposite side of the continuous equivalence to give explicit
two-sided norm control.  These are ordinary operator-norm inequalities; no
isometry, Jacobian normalization, product-Gaussian law, or source estimate is
asserted.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is dictionary norm-interface bookkeeping.  It does not
prove the dictionary is isometric, does not identify a determinant/Jacobian
convention, does not prove Gaussian pushforward, does not localize the
covariance root, does not construct local activities, and does not prove raw
activity decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 316 (2026-06-24, **dictionary Gaussian-map norm budget**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum adds norm-budget lemmas for the canonical dictionary/root
Gaussian coordinate map:

```
PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le
PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_apply_le
PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le_of_root_norm_le
PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_apply_le_of_root_norm_le
```

The operator-norm statement is the standard composition estimate for
`root.comp D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap`.
The pointwise statement follows from the operator-norm bound, and the final two
forms consume an explicit source-supplied root-norm bound.  These lemmas carry
the dictionary constant visibly; they do not assert an isometry or a Gaussian
law.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is a continuous-linear-map norm budget for an already
defined coordinate map.  It does not prove Gaussian pushforward, covariance
identity, root localization/truncation, Wilson-Hessian identification, local
activity construction, or raw activity decay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 317 (2026-06-24, **certificate-fed Gaussian-map norm budget**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum adds certificate-fed versions of the dictionary/root Gaussian-map
norm budget:

```
PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_le_of_covarianceRootCertificate
PhysicalGaugeCMP116Dictionary.norm_gaussianRootMap_apply_le_of_covarianceRootCertificate
```

The lemmas consume the existing
`PhysicalLocalizedCovarianceRootCertificate.root_norm_bound` field and route it
through the previously verified dictionary Gaussian-map norm budget.  This lets
downstream estimates use the localized covariance-root certificate directly
without restating `‖root‖ ≤ rootNormBound`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is a certificate-field projection into an operator-norm
budget.  It does not construct the covariance root, prove a covariance identity
beyond the carried certificate fields, establish Gaussian pushforward, prove
root localization/truncation, identify a Wilson Hessian, construct local
activities, or prove raw activity decay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 318 (2026-06-24, **transport-fed Gaussian-map norm budget**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum routes the dictionary/root Gaussian-map norm budget through the
downstream physical/CMP116 activity transport package:

```
PhysicalGaugeCMP116ActivityTransport.norm_gaussianRootMap_le
PhysicalGaugeCMP116ActivityTransport.norm_gaussianRootMap_apply_le
```

The lemmas consume `T.certificate.root_certificate` from an already constructed
`PhysicalGaugeCMP116ActivityTransport` and expose the same explicit dictionary
constant
`‖D.fluctuationFieldContinuousLinearEquiv.toContinuousLinearMap‖`.  This is the
transport-package consumer of Addendum 317's certificate-fed root-norm budget.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is a downstream transport-package consumer of an
already carried covariance-root certificate.  It does not prove the transport
was built from any particular source theorem, construct the covariance root,
prove Gaussian pushforward, prove root localization/truncation, identify a
Wilson Hessian, construct local activities, or prove raw activity decay.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 319 (2026-06-24, **localized-map support consequences**
`YangMills.RG.LocalLinearOperator`; core 8355)

This addendum adds named support consequences for the localized CMP116
linear-map constructors:

```
CMP116LocalizedLinearMap.add_eq_of_agreeOn
CMP116LocalizedLinearMap.add_apply_eq_zero_outside
CMP116LocalizedLinearMap.finsetSum_eq_of_agreeOn
CMP116LocalizedLinearMap.finsetSum_apply_eq_zero_outside
CMP116LocalizedLinearMap.comp_eq_of_agreeOn
CMP116LocalizedLinearMap.comp_apply_eq_zero_outside
CMP116LocalizedLinearMap.ofProjection_eq_of_agreeOn
CMP116LocalizedLinearMap.ofProjection_apply_eq_zero_outside
```

These lemmas turn the already bundled `OperatorSupportedBetween` proof into the
two consequences later finite localized-root assembly uses directly:
agreement on the declared input region, and coordinatewise zero output outside
the declared output region.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\LocalLinearOperator.lean
lake build YangMills.RG.LocalLinearOperator
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\LocalLinearOperator.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is exact projection/support algebra for finite CMP116
coordinate fields.  It does not construct a covariance root, prove finite-range
or exponential-decay estimates, prove Gaussian pushforward, construct local
activities, or prove raw activity decay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 320 (2026-06-24, **varying-support localized finite sums**
`YangMills.RG.LocalLinearOperator`; core 8355)

This addendum adds the finite-family localized-map assembly constructor:

```
CMP116LocalizedLinearMap.finsetSumVarying
CMP116LocalizedLinearMap.finsetSumVarying_toContinuousLinearMap
CMP116LocalizedLinearMap.finsetSumVarying_eq_of_agreeOn
CMP116LocalizedLinearMap.finsetSumVarying_apply_eq_zero_outside
```

Unlike the previous same-support `finsetSum`, `finsetSumVarying` accepts a
finite family whose pieces have input/output supports `Xin i` and `Xout i`.
The resulting map is certified over the finite unions `I.biUnion Xin` and
`I.biUnion Xout`.  The two consumer lemmas expose the direct consequences:
agreement on the union of declared input supports and coordinatewise zero
outside the union of declared output supports.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\LocalLinearOperator.lean
lake build YangMills.RG.LocalLinearOperator
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\LocalLinearOperator.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This is exact finite-union support algebra.  It does not
construct localized root pieces, prove that any analytic root decomposes into
such pieces, prove finite-range or exponential-decay estimates, prove Gaussian
pushforward, construct local activities, or prove raw activity decay.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 321 (2026-06-24, **finite-piece dictionary localized-root sums**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum routes the varying-support localized-map finite-sum API through
the dictionary-backed CMP116 root transport layer:

```
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_toContinuousLinearMap
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_eq_of_agreeOn
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_apply_eq_zero_outside
```

Given a finite family of input cube sets `Xin i`, the constructor sums the
already localized projected dictionary root maps
`localizedRootLinearMap_ofDictionary ... (Xin i) ...`.  The resulting
`CMP116LocalizedLinearMap` is certified from `I.biUnion Xin` to the union of
the corresponding finite-range closures
`I.biUnion fun i => cmp116FiniteRangeClosure dist R (Xin i)`.  The two
consumer lemmas expose the direct consequences: agreement on the union of the
piece input supports and coordinatewise zero outside the union of the
piece output closures.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint proves exact finite-piece support algebra
for a sum of supplied projected root maps.  It does not prove that such pieces
reconstruct the full covariance root, does not construct an analytic root
decomposition, does not prove finite-range or exponential-decay estimates
beyond the explicit finite-range hypothesis already supplied to each piece,
does not prove Gaussian pushforward, does not construct local activities, and
does not prove raw activity decay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 322 (2026-06-24, **physical-coordinate consumers for finite-piece root sums**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum exposes the physical-coordinate consequences of the finite-piece
dictionary localized-root sum:

```
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_pull_eq_of_agreeOn
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_pull_apply_eq_zero_outside
```

The first theorem says that, after pulling the finite-piece CMP116 root-sum
output back to a physical one-cochain through the dictionary, the output is
unchanged when the CMP116 input fields agree on `I.biUnion Xin`.  The second
theorem says that the pulled physical output is zero on every physical bond
whose assigned CMP116 cube lies outside
`I.biUnion fun i => cmp116FiniteRangeClosure dist R (Xin i)`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint is physical-coordinate support bookkeeping
for an already supplied finite sum of projected root maps.  It does not prove
that the finite pieces reconstruct the full covariance root, does not prove a
Gaussian pushforward identity for the finite sum, does not establish any
isometry or Jacobian convention for the dictionary, does not construct local
activities, and does not prove raw activity decay.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 323 (2026-06-24, **activity consumer for finite-piece root sums**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum exposes the first direct physical-activity consumer of the
finite-piece dictionary localized-root sum:

```
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_activity_globalEval_eq_of_agreeOn
```

It says that a `PhysicalGaugeLocalActivity` evaluated on the physical pullback
of the finite-piece CMP116 root-sum output is unchanged when two CMP116 input
fields agree on `I.biUnion Xin`.  The proof is the exact composition of
`LocalActivity.globalEval_eq_of_agreeOn` with the previously verified pulled
physical-output equality.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry reports only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint proves a local-activity dependence consumer
for a supplied finite sum of projected root maps.  It does not prove that the
finite pieces reconstruct the full covariance root, does not prove a Gaussian
pushforward identity for the finite sum, does not construct local activities,
and does not prove raw activity decay.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 324 (2026-06-24, **finite-family activity consumers for root-piece sums**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum lifts the single physical-activity consumer from Addendum 323 to
finite families of physical local activities:

```
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_activityFamily_sum_globalEval_eq_of_agreeOn
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_activityFamily_finsetSum_globalEval_eq_of_agreeOn
```

The first theorem proves equality for an explicit finite sum of activity
evaluations when the CMP116 inputs agree on `I.biUnion Xin`.  The second
packages the same fact through `LocalActivity.finsetSum`, exposing the form
used by later finite local-activity assemblies.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint is a finite-family consumer of the already
verified single-activity dependence theorem.  It does not prove that the
finite root pieces reconstruct the full covariance root, does not prove a
Gaussian pushforward identity, does not construct local activities, and does
not prove raw activity decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 325 (2026-06-24, **Mayer-cover activity consumer for root-piece sums**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum propagates the finite-piece root-sum input-dependence result
through the Appendix-F raw Mayer-cover product:

```
PhysicalRootToCMP116OperatorTransport.localizedRootLinearMapFinsetSum_ofDictionary_mayerCoverActivity_globalEval_eq_of_agreeOn
```

The theorem says that `LocalActivity.mayerCoverActivity J activity`, evaluated
on the physical pullback of a supplied finite-piece CMP116 root-sum output, is
unchanged when the CMP116 inputs agree on `I.biUnion Xin`.  The proof rewrites
the Mayer-cover product to the finite product of raw Mayer factors
`exp((activity X).globalEval ...) - 1` and applies the single-activity
consumer to each factor.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry reports only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint is an exact Mayer-cover consumer of the
already verified single-activity dependence theorem.  It does not prove that
the finite root pieces reconstruct the full covariance root, does not prove a
Gaussian pushforward identity, does not construct local activities, and does
not prove raw activity decay.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 326 (2026-06-24, **activity-local bridge to the dictionary Gaussian root map**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum adds the activity-local bridge from a supplied finite root-piece
sum to the full dictionary Gaussian-root map:

```
PhysicalRootToCMP116OperatorTransport.gaussianRootMap_activity_globalEval_eq_of_agreeOn_of_localizedRootLinearMapFinsetSum
```

The theorem says that if, for each CMP116 input `ζ`, the full physical
dictionary root field `D.gaussianRootMap root ζ` agrees with the pulled
finite-piece root-sum field on `activity.fluctuationSupport`, then
`activity.globalEval` on the full root map is unchanged when CMP116 inputs
agree on `I.biUnion Xin`.  The key premise is deliberately local to the
activity support; the theorem does not require global equality between the
finite sum and the full root operator.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entry reports only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint is an exact `LocalActivity` locality bridge.
It does not prove that the finite root pieces reconstruct the full covariance
root, does not prove a Gaussian pushforward identity, does not construct local
activities, and does not prove raw activity decay.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 327 (2026-06-24, **CMP116 post-Gaussian localization source anchor**
`docs/SOURCE-CLAIM-AUDIT.md`; core 8355)

This documentation/source-audit checkpoint records the primary-source anchor
for the source-side `hrootPieces` obligation consumed by the activity-local
Gaussian-root bridge from Addendum 326.

New audit row:

```
B5b - CMP 116: Post-Gaussian Localization Of The Root Map
```

The row records CMP116 PDF/printed pages 13--14, equations (2.7)--(2.10).  In
that range Balaban localizes the still-global post-(2.6) expression by
introducing `s` parameters and generalized random-walk expansions, expands
`(C^(k))^(1/2)` through a resolvent/series representation, and rewrites the
product-Gaussian integral as localized quantities `H(Z,Z0)` and `H(Z)`.

`docs/BALABAN-SOURCE-BOUNDS.md` now includes the same anchor in the visually
confirmed source list.  The local page renders used for inspection were
generated under `runtime/sources/primary/renders/`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\BALABAN-SOURCE-BOUNDS.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This checkpoint is source localization bookkeeping only.  It
does not prove the `hrootPieces` hypothesis, does not identify Balaban's
domains with Lean's `LocalActivity.fluctuationSupport`/`activeSupport`, and
does not prove finite or infinite root-piece reconstruction.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 328 (2026-06-24, **CMP116 activity-estimate design constraint**
`docs/SOURCE-CLAIM-AUDIT.md`; core 8355)

This documentation/source-audit checkpoint records the result of inspecting
CMP116 PDF/printed pages 15--20, equations (2.14)--(2.38), to decide whether
the post-(2.6) root expansion should be treated as an exact finite root-piece
reconstruction theorem.

New audit row:

```
B5c - CMP 116: Resummed Activity Estimate Versus Root-Piece Reconstruction
```

The row records that Balaban writes a typical term in (2.14), bounds it in
(2.26), then resums over `D`, `P`, `Z0`, and `Z0'` using the geometric and
summability inputs (2.27), (2.29)--(2.32), (2.34), and (2.36).  The result is
Lemma 3 / (2.38), a localized activity estimate for `H(Z)`.

The practical Lean-facing conclusion is negative for exact finite
reconstruction: this source range supports `local_physical_activity_construction`
and `raw_pointwise_decay` more directly than it supports an exact finite
`localizedRootLinearMapFinsetSum` equality with `(C^(k))^(1/2)`.  Finite
root-piece sums should remain truncations or auxiliary approximations unless a
separate exact activity-support equality theorem is found.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\BALABAN-SOURCE-BOUNDS.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This checkpoint is source-audit bookkeeping only.  It does
not prove a Lean theorem, does not discharge `hrootPieces`, and does not prove
activity decay in Lean.  It prevents a materially false implementation choice:
treating CMP116 pages 15--20 as if they supplied exact finite root
reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 329 (2026-06-24, **CMP116 post-Lemma-3 effective-action bridge**
`docs/SOURCE-CLAIM-AUDIT.md`; core 8355)

This documentation/source-audit checkpoint records CMP116 PDF/printed page 21,
equations (2.39)--(2.41), as the bridge from Lemma 3's localized `H(Z)` bound
to the effective-action estimate.

New audit row:

```
B5d - CMP 116: Post-Lemma-3 Effective-Action Bound
```

The row records that (2.39) inserts products of Lemma 3 factors into the
exponentiated polymer series, (2.40) invokes standard polymer-series bounds
for large `kappa` and small `epsilon_1`, and (2.41) yields the effective-action
estimate

```
|E^(k+1)(X)| <= O(1) C_3 epsilon_1
  * exp (-(1 - 10 delta)^(1/2) L kappa d_{k+1}(X)).
```

The following paragraphs fix `(1 - 10 delta)^(1/2) L = 1`, assume
`O(1) C_3 epsilon_1 <= E_0/2`, and handle the extra
`[log Z^(k)(U_{k+1}) - log Z^(k)(1)]` normalization term by a separate
generalized random-walk expansion with `kappa` replaced by `delta_0 M`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\BALABAN-SOURCE-BOUNDS.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This checkpoint is source-audit bookkeeping only.  It does
not prove a Lean theorem, does not prove Lemma 3, and does not formalize the
polymer-series summability referenced through [26].  It identifies the next
consumer after a future `H(Z)` construction/decay theorem.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 330 (2026-06-24, **activity-local root-piece agreement obligation**
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`; core 8355)

This addendum names the source-facing agreement premise consumed by the
dictionary Gaussian-root activity bridge:

```
PhysicalRootToCMP116OperatorTransport.ActivityLocalRootPieceAgreement
```

It also adds two constructor/transport lemmas:

```
PhysicalRootToCMP116OperatorTransport.activityLocalRootPieceAgreement_of_agreeOn_activeSupport
PhysicalRootToCMP116OperatorTransport.gaussianRootMap_agreeOn_activity_fluctuationSupport_of_cmp116_agreeOn
```

The first restricts agreement on a declared physical active support to the
activity's fluctuation support.  The second transports CMP116 agreement on a
finite localization domain `Xloc` through the dictionary, using
`D.pullFluctuationCochain_agreeOn` and
`D.gaussianRootMap_eq_coordinates_comp_cmp116OperatorOfPhysical`, to produce
the exact `ActivityLocalRootPieceAgreement` required by the existing full-root
consumer.

The existing theorem

```
PhysicalRootToCMP116OperatorTransport.gaussianRootMap_activity_globalEval_eq_of_agreeOn_of_localizedRootLinearMapFinsetSum
```

now takes this named proposition instead of an anonymous expanded binder.
This keeps the finite localized-root sum as one sufficient constructor while
leaving room for later finite, locally finite, or convergent root-piece
interfaces.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`.

**Honest scope.** This checkpoint is Lean plumbing for a named local agreement
obligation.  It does not prove CMP116 domain/enlargement translation, any
finite or infinite reconstruction of `(C^(k))^(1/2)`, a Gaussian pushforward
identity, local activity construction, or raw activity decay.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 331 (2026-06-24, **CMP116 Lemma 3 activity estimate bridge**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8355)

This addendum adds an activity-only source lane for the output of CMP116
Lemma 3 / equation (2.38), without mentioning or using `hrootPieces`.

New declarations:

```
balabanCMP116Lemma3DecayRate
balabanCMP116Lemma3Weight
CMP116Lemma3ActivityEstimate
balabanLemma3_rawActivityDecay
balabanCMP116Lemma3Weight_nonneg
balabanCMP116Lemma3Weight_domination
PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate
```

`CMP116Lemma3ActivityEstimate` records the final resummed pointwise estimate
for already-constructed localized physical activities:

```
||(physicalActivity X).globalEval psi phi||
  <= (C3 * epsilon1) *
     balabanCMP116Lemma3Weight blockScale delta kappaSource sourceMetric X
```

The rate keeps `blockScale` separate from the finite lattice modulus `L` in
`Cube d L`.  The metric-domination theorem compares complete exponents and
therefore leaves any scale normalization, distance convention, or metric loss
as an explicit hypothesis.

The thin raw-source adapter
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate`
reuses the already separated Gaussian pushforward, root-localization,
Wilson-Hessian-identification, and local-activity source package, then fills
only the raw pointwise decay field using the Lemma 3 estimate object.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`
or no additional axioms for definitions.

**Honest scope.** This checkpoint states and adapts the output interface for
Lemma 3.  It does not prove Lemma 3 from CMP116's smallness hierarchy, does
not identify Balaban's `H(Z)` with a constructed activity, does not prove the
metric comparison, and does not prove Gaussian pushforward, Wilson-Hessian
identification, covariance-root localization, or any finite/infinite
root-piece reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 332 (2026-06-24, **CMP116 Lemma 3 finite resummation bridge**
`YangMills.RG.BalabanCMP116Lemma3`; core 8355)

This addendum adds a new module for the activity-only Lemma 3 route:

```
YangMills.RG.BalabanCMP116Lemma3
```

New declarations:

```
CMP116Lemma3Parameters
CMP116HResummation
cmp116HIndexFinset
balabanCMP116H
norm_balabanCMP116H_le_lemma3
cmp116Lemma3ActivityEstimate_of_resummation
```

`CMP116HResummation` names the finite source summation families corresponding
to the pre-Lemma sums over `D`, `P`, `Z0`, and `Z0'`.  It carries summands and
term weights, but no field equivalent to `H_decay` or `raw_pointwise_decay`.

The theorem

```
norm_balabanCMP116H_le_lemma3
```

proves the final norm step from:

* termwise bounds for every source summand; and
* a pre-Lemma summed-weight budget for the finite index set,

to the Lemma-3-shaped bound using the source weight introduced in Addendum
331.  The adapter

```
cmp116Lemma3ActivityEstimate_of_resummation
```

then turns an explicit evaluation identity between a physical local activity
and `balabanCMP116H` into `CMP116Lemma3ActivityEstimate`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3.lean
lake build YangMillsCore
lake env lean oracle_check.lean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new oracle entries report only `[propext, Classical.choice, Quot.sound]`
or no additional axioms for definitions.

**Honest scope.** This checkpoint is not the full analytic extraction of
CMP116 Lemma 3.  It does not derive the termwise bound or the summed-weight
budget from equations (2.27), (2.29)--(2.32), (2.34), (2.36), or (2.37), does
not freeze the exact source definition of `C3`, and does not identify
Balaban's `H(Z)` with a constructed physical activity.  It is the finite
resummation/norm bridge that the future exact source-constant extraction must
feed.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 333 (2026-06-24, **CMP116 Lemma 3 real-distance conclusion interface**
`YangMills.RG.BalabanCMP116Lemma3`; core 8355)

This addendum normalizes the Lemma 3 conclusion interface onto the source
metric shape requested for CMP116 equation (2.38):

```
cmp116Lemma3Weight
cmp116Lemma3Weight_nonneg
CMP116Lemma3ActivityEstimate
balabanLemma3_rawActivityDecay
```

`CMP116Lemma3ActivityEstimate` is now the real-distance proposition

```
∀ Z ψ φ,
  ‖(physicalActivity Z).globalEval ψ φ‖ ≤
    (C3 * epsilon1) *
      cmp116Lemma3Weight dNext delta blockScale kappa Z
```

where `dNext : ι → ℝ` represents Balaban's `d_{k+1}`.  The older
natural-valued source metric interface remains as compatibility wrappers
`balabanCMP116Lemma3DecayRate`, `balabanCMP116Lemma3Weight`, and
`balabanCMP116Lemma3Weight_nonneg`, because
`balabanCMP116Lemma3Weight_domination` still compares that native source metric
against the repository's shifted Appendix-F modified metric.

The resummation bridge now targets the real-distance interface directly:
`norm_balabanCMP116H_le_lemma3` takes a real `dNext`, and
`cmp116Lemma3ActivityEstimate_of_resummation` returns the real-distance
`CMP116Lemma3ActivityEstimate`.  The raw-source helper
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate`
also consumes the real-distance estimate and packages it through
`balabanLemma3_rawActivityDecay`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3.lean
lake build YangMills.RG.BalabanCMP116Lemma3
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> runtime\oracle-cmp116-lemma3-real-interface.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This checkpoint still does not prove CMP116 Lemma 3 from
Balaban's source constants, does not construct or identify `H(Z)`, does not
prove the metric comparison from `d_{k+1}` to `discreteModifiedMetric + 1`, and
does not prove Gaussian pushforward, Wilson-Hessian identification,
covariance-root localization, or finite/infinite covariance-root
reconstruction.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 334 (2026-06-24, **CMP116 Lemma 3 activity lane isolated**
`YangMills.RG.BalabanCMP116Lemma3Estimate`,
`YangMills.RG.BalabanCMP116Lemma3RawSourceAdapter`; core 8358)

This checkpoint separates the CMP116 Lemma 3 activity-only interface from both
the finite resummation bridge and the raw-source M3 source theorem.

New low-level module:

```
YangMills.RG.BalabanCMP116Lemma3Estimate
```

It imports only `YangMills.RG.PhysicalGaugeFluctuationActivity` and contains
the canonical Nat-source-metric Lemma 3 conclusion surface:

```
balabanCMP116Lemma3DecayRate
balabanCMP116Lemma3Weight
balabanCMP116Lemma3Weight_nonneg
CMP116Lemma3ActivityEstimate
balabanLemma3_rawActivityDecay
```

`CMP116Lemma3ActivityEstimate` now has the source-metric shape

```
∀ X ψ φ,
  ‖(physicalActivity X).globalEval ψ φ‖ ≤
    (C3 * epsilon1) *
      balabanCMP116Lemma3Weight
        blockScale delta kappaSource sourceMetric X
```

with `sourceMetric : ι → ℕ` and no embedded `amplitude_nonneg` field.  The
older `cmp116Lemma3Weight`/`cmp116Lemma3Weight_nonneg` declarations remain in
the estimate module only as compatibility real-metric aliases.

`YangMills.RG.BalabanCMP116Lemma3` now imports the estimate module and contains
only the finite resummation bridge: `CMP116Lemma3Parameters`,
`CMP116HResummation`, `cmp116HIndexFinset`, `balabanCMP116H`,
`norm_balabanCMP116H_le_lemma3`, and
`cmp116Lemma3ActivityEstimate_of_resummation`.  The bridge now targets the
Nat-source-metric `CMP116Lemma3ActivityEstimate`.

New downstream adapter module:

```
YangMills.RG.BalabanCMP116Lemma3RawSourceAdapter
```

It imports `YangMills.RG.BalabanCMP116Lemma3Estimate` and
`YangMills.RG.PhysicalGaugeCMP116ActivityConstruction`, and contains:

```
balabanCMP116Lemma3Weight_domination
PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimate
```

`BalabanCMP116SourceTheorem` no longer imports `BalabanCMP116Lemma3`; it keeps
only the pure five-component source packaging and depends through
`PhysicalGaugeCMP116RawM3`.  This matches the intended direction

```
PhysicalGaugeFluctuationActivity
  -> BalabanCMP116Lemma3Estimate
      -> BalabanCMP116Lemma3

PhysicalGaugeCMP116ActivityConstruction
  + BalabanCMP116Lemma3Estimate
      -> BalabanCMP116Lemma3RawSourceAdapter

PhysicalGaugeCMP116RawM3
  -> BalabanCMP116SourceTheorem
```

Verification commands run for this checkpoint:

```
lake build YangMills.RG.BalabanCMP116Lemma3Estimate
lake env lean YangMills\RG\BalabanCMP116Lemma3Estimate.lean
lake env lean YangMills\RG\BalabanCMP116Lemma3.lean
lake env lean YangMills\RG\BalabanCMP116Lemma3RawSourceAdapter.lean
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-lemma3-activity-lane-isolation.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3Estimate.lean YangMills\RG\BalabanCMP116Lemma3.lean YangMills\RG\BalabanCMP116Lemma3RawSourceAdapter.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This is an architectural separation and interface correction.
It does not prove CMP116 equations (2.27), (2.29)--(2.32), (2.34), (2.36), or
(2.37), does not construct or identify Balaban's `H(Z)`, and does not prove
the source metric comparison.  The next analytic step remains a source-faithful
formalization of one named CMP116 summability equation, starting with a concrete
candidate such as equation (2.29).  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 335 (2026-06-24, **CMP116 Lemma 3 dependent resummation indices**
`YangMills.RG.BalabanCMP116Lemma3`; core 8358)

This checkpoint tightens the finite pre-Lemma resummation interface without
adding any analytic source assumption.

`CMP116HResummation` now records the source-shaped dependent index chain:

```
DIndex       : σ → Finset ιD
PIndex       : σ → ιD → Finset ιP
Z0Index      : σ → ιD → ιP → Finset ιZ0
Z0PrimeIndex : σ → ιD → ιP → ιZ0 → Finset ιZ0'
```

The flattened index set `cmp116HIndexFinset` is rebuilt as the nested finite
union over those dependent families.  `balabanCMP116H` and
`cmp116Lemma3ActivityEstimate_of_resummation` consume the same flattened index
type as before, but the allowed terms now follow the CMP116 summation order
rather than a Cartesian product of independent finite sets.

The theorem formerly named

```
norm_balabanCMP116H_le_lemma3
```

has been renamed to

```
norm_balabanCMP116H_le_termWeightSum
```

because it proves the finite triangle-inequality step from termwise summand
bounds plus a supplied summed-weight budget.  It does not prove Lemma 3's
analytic resummation or any source equation.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-lemma3-dependent-indices.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This is a structural/source-shape refactor only.  It still
does not derive the termwise bounds or summed-weight budget from CMP116
equations (2.27), (2.29)--(2.32), (2.34), (2.36), or (2.37), does not construct
or identify `H(Z)`, and does not prove the source metric comparison.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 336 (2026-06-24, **CMP116 equation (2.29) D-stage summability consumer**
`YangMills.RG.BalabanCMP116Eq229`; core 8359)

This checkpoint begins the equation-level CMP116 Lemma 3 source extraction with
the first displayed summability input on Balaban CMP116 page 18, equation
(2.29).  The local primary source is
`runtime/sources/primary/balaban-rg-II-cmp116-1104161193.pdf`, SHA256
`EE39523A0F7B83AF958513C7BD6F9C7731934B40355EF5D6B0F7A68EE6D022FC`; the
rendered page used for audit is
`runtime/sources/primary/renders/cmp116-source-18.png`.

The new module records the source weight

```
cmp116Eq229Weight alpha6 delta kappa metric Y
  = alpha6 * exp (-(delta * kappa * metric Y))
```

and the exact equation (2.29) summability shape

```
sum_D prod_{Y in D} alpha6 * exp(-delta * kappa * d_k(Y)) <= 1.
```

The theorem `cmp116_DStage_sum_le_of_eq229` proves the immediate finite
resummation consumer: if every term in the `D`-sum is bounded by a
nonnegative base factor times the (2.29) product, then the entire `D`-sum is
bounded by the base factor.  This gives a typed local source-equation
interface for the first stage of the Lemma 3 resummation, without asserting
the complete `hbudget`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq229.lean
lake build YangMills.RG.BalabanCMP116Eq229
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-eq229.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq229.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This does not prove Balaban's "for `K` sufficiently large
and `alpha_6` sufficiently small" assertion in (2.29), does not prove the
geometric inequality (2.27), the metric comparisons (2.30)/(2.32), the later
summations (2.34)/(2.36)/(2.37), the final Lemma 3 budget, or the
identification of Balaban's `H(Z)` with a Lean physical local activity.  It
only makes the first source summability equation consumable by subsequent
verified finite resummation steps.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 337 (2026-06-24, **CMP116 Lemma 3 dependent scale-family packaging**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8360)

This checkpoint adds the scale-family layer between the single-scale CMP116
Lemma 3 estimate and the existing raw-source/H# frontier consumers.  The new
module packages a dependent two-scale family of Lemma 3 estimates,

```
forall t k,
  CMP116Lemma3ActivityEstimate
    (physicalActivity t k)
    (sourceMetric t k)
    (blockScale t k)
    (C3 t k)
    (epsilon1 t k)
    (delta t k)
    (kappaSource t k),
```

where the index type may depend on `(t, k)`, for example
`OmegaPolymerType HF (z t k)`.

New public declarations include:

```
cmp116Lemma3ScaleWeight
cmp116Lemma3ScaleAmplitude
cmp116Lemma3ScaleWeight_nonneg
CMP116Lemma3ActivityEstimateScaleFamily
rawSource_of_lemma3ActivityEstimate
PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses.of_lemma3ActivityEstimateScaleFamily
cmp116Lemma3ActivityEstimateScaleFamily_of_resummation
```

The raw-source constructor keeps Gaussian pushforward, root localization,
Wilson-Hessian identification, and local physical activity construction as
explicit per-scale inputs.  It only combines those source facts with the
already supplied Lemma 3 estimate through the existing single-scale adapter.
The resummation constructor applies
`cmp116Lemma3ActivityEstimate_of_resummation` at each scale; it still assumes
the termwise estimates and summed-weight budget at each scale.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMills.RG.BalabanCMP116Lemma3ScaleFamily
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-lemma3-scale-family.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This is record/package plumbing.  It does not prove CMP116
Lemma 3 constants, the termwise source estimates, the summed-weight budget,
equations (2.27), (2.29)--(2.32), (2.34), (2.36), or (2.37), the source metric
comparison, the Gaussian pushforward, covariance-root localization,
Wilson-Hessian identification, local activity construction, or the rooted H#
identity.  The full-index scale-family estimate remains a compatibility
hypothesis until admissible source-domain transport or zero-extension is
formalized.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 338 (2026-06-24, **Lemma-3 source assumptions to raw-source M3 frontier**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8360)

This checkpoint adds the parallel source-assumption record requested after the
scale-family packaging.  The new record
`BalabanCMP116Lemma3SourceAssumptions` has the same consumer-side frontier
surface as `BalabanCMP116SourceAssumptions`, but it replaces the arbitrary
`raw_pointwise_decay` field with the canonical scale-family conclusion

```
CMP116Lemma3ActivityEstimateScaleFamily
  physicalActivity sourceMetric blockScale C3 epsilon1 delta kappaSource.
```

Its canonical weight and amplitude are

```
cmp116Lemma3ScaleWeight sourceMetric blockScale delta kappaSource
cmp116Lemma3ScaleAmplitude C3 epsilon1
```

and `weight_nonneg` is no longer a source field: the projection constructor
derives it from `cmp116Lemma3ScaleWeight_nonneg`.

New public declarations include:

```
BalabanCMP116Lemma3SourceAssumptions
BalabanCMP116Lemma3SourceAssumptions.rawSource
BalabanCMP116Lemma3SourceAssumptions.rooted_hsharp_remainder_identity_rawSource
CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions
BalabanCMP116Lemma3SourceAssumptions.to_m3Frontier
```

The constructor is pure packaging.  It builds `raw_source` through
`rawSource_of_lemma3ActivityEstimate`, passes canonical Lemma-3 weight and
amplitude to `CMP116RawSourceM3Frontier`, and carries forward the existing
covariance-root, Gaussian pushforward, root localization, Wilson-Hessian,
local-activity, support, measurability, Appendix-F geometry, H#, marginal-flow,
and IR hypotheses unchanged.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-lemma3-source-record.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This does not prove CMP116 Lemma 3, the source termwise
estimates, the summed-weight budget, metric domination, Gaussian pushforward,
covariance-root localization, Wilson-Hessian identification, local physical
activity construction, rooted H# identity, marginal-flow estimates, or the IR
bound.  It only exposes a smaller source frontier for callers that already
have the Lemma-3 activity estimate scale family.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 339 (2026-06-24, **CMP116 equation 2.29 D-stage budget constructor**
`YangMills.RG.BalabanCMP116Eq229`; core 8360)

This checkpoint adds the first budget-constructor theorem on top of the
existing equation-(2.29) source predicate.  The new finite equality

```
cmp116H_termWeightSum_eq_nested
```

identifies the flattened `cmp116HIndexFinset` term-weight sum with the nested
source-shaped `D -> P -> Z0 -> Z0'` sum.  The new budget constructor

```
cmp116H_termWeightSum_le_of_eq229
```

then applies `cmp116_DStage_sum_le_of_eq229` to discharge only the outer
`D`-sum.  Its residual hypothesis is exactly the complete post-D resummation
over `P`, `Z0`, and `Z0'`, bounded by the final Lemma-3 base factor times the
equation-(2.29) product for the chosen `D`.  Thus the conclusion has the
`hbudget` shape consumed by `cmp116Lemma3ActivityEstimate_of_resummation`,
without introducing a premise named `hbudget`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq229.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-eq229-dstage-budget.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq229.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** Equation (2.29) itself remains a source hypothesis via
`CMP116Eq229Summability`.  This checkpoint does not prove the residual
`P/Z0/Z0'` resummations, equations (2.27), (2.30), (2.32), (2.34), (2.36), or
(2.37), the termwise complex-valued estimate, the analytic constant hierarchy,
the admissible-domain transport, source metric comparison, or CMP116 Lemma 3.
It only proves that the supplied residual post-D bound plus equation (2.29)
gives the exact finite term-weight budget.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 340 (2026-06-24, **Eq. 2.29 post-D consumer for Lemma-3 activity estimate**
`YangMills.RG.BalabanCMP116Eq229`; core 8360)

This checkpoint adds the thin theorem-fed activity-estimate consumer

```
cmp116Lemma3ActivityEstimate_of_eq229_postD
```

on top of Addendum 339.  It combines the existing source identification of
`balabanCMP116H`, the complex-valued termwise estimate, the equation-(2.29)
summability predicate, and the explicit residual post-D `P/Z0/Z0'` bound, then
feeds the derived finite budget into
`cmp116Lemma3ActivityEstimate_of_resummation`.

The theorem removes the need for callers on this route to pass a separate
monolithic `hbudget`; the residual source work remains a named hypothesis
`hpostD` with the full nested `P -> Z0 -> Z0'` sum visible.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq229.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-eq229-postD-consumer.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq229.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is a consumer theorem, not an analytic source proof.
Equation (2.29), the termwise estimate, the activity-identification equality,
and the residual post-D bound all remain explicit hypotheses.  It does not
prove equations (2.27), (2.30), (2.32), (2.34), (2.36), or (2.37), the constant
hierarchy, admissible-domain transport, source metric comparison, or CMP116
Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 341 (2026-06-24, **scale-family Eq. 2.29 post-D Lemma-3 consumer**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8360)

This checkpoint lifts the Addendum 340 consumer pointwise over scale families:

```
cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_postD
```

The theorem applies `cmp116Lemma3ActivityEstimate_of_eq229_postD` at each
`(t, k)`.  It constructs the canonical
`CMP116Lemma3ActivityEstimateScaleFamily` from per-scale source identification,
complex termwise estimates, equation-(2.29) summability predicates, and
explicit residual post-D `P/Z0/Z0'` bounds.

No stage-specific source inequality is introduced.  The residual source
resummation remains the visible `hpostD` family, so this theorem is only a
composition adapter for callers that already have the post-D bounds.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-eq229-scale-family-consumer.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This theorem does not prove Eq. (2.29), termwise estimates,
residual post-D estimates, equations (2.27), (2.30), (2.32), (2.34), (2.36),
or (2.37), the constant hierarchy, admissible-domain transport, source metric
comparison, Gaussian/root/Hessian/activity source facts, or CMP116 Lemma 3.
It only packages the already explicit per-scale assumptions into the existing
scale-family estimate.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 342 (2026-06-24, **CMP116 residual-stage post-D budget constructor**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8361)

This checkpoint adds the source-neutral residual-stage interface requested for
the CMP116 Lemma-3 resummation route:

```
CMP116PResidualSummability
CMP116Z0ResidualSummability
CMP116Z0PrimeResidualSummability
cmp116H_postD_sum_le_of_residualStages
cmp116H_termWeightSum_le_of_eq229_of_residualStages
```

The first theorem proves that normalized `P`, `Z0`, and `Z0'` residual
summability, together with a pointwise factorization of `R.termWeight`, gives
the complete post-`D` residual budget previously passed as `hpostD`.  The
second theorem specializes the base factor to the Eq. (2.29) product-weight
shape and composes the result with `cmp116H_termWeightSum_le_of_eq229`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-residual-stages.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is finite residual-summation algebra plus composition
with the existing Eq. (2.29) consumer.  It does not identify the residual stage
predicates with CMP116 equations (2.27), (2.30), (2.32), (2.34), (2.36), or
(2.37), prove the source constants, termwise complex-valued estimate,
activity-identification equality, source metric comparison, Gaussian/root/
Hessian/activity source facts, or CMP116 Lemma 3.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 343 (2026-06-24, **scale-family CMP116 residual-stage budget consumer**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8361)

This checkpoint adds the pointwise scale-family consumer

```
cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_residualStages
```

The theorem applies the residual-stage constructor at each `(t, k)`, deriving
the post-`D` budget from normalized `P`, `Z0`, and `Z0'` residual summability,
a named `postDBase` equal to the Eq. (2.29) product-weight base, and a pointwise
term-weight factorization.  It then feeds the resulting post-`D` budget into
the existing Eq. (2.29) activity-estimate scale-family consumer.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-residual-stage-scale-family.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

**Honest scope.** This is only scale-family composition over the already
verified residual-stage and Eq. (2.29) finite consumers.  It does not prove or
source-identify the residual stage estimates, pointwise factorization, Eq.
(2.29), termwise complex-valued estimates, activity identification, source
metric comparison, Gaussian/root/Hessian/activity source facts, or CMP116 Lemma
3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 344 (2026-06-24, **CMP116 P-stage post-D budget helper**
`YangMills.RG.BalabanCMP116Eq229`; core 8361)

This checkpoint adds the smallest requested P-stage decomposition helper:

```
CMP116PStageSummability
cmp116H_postDSum_le_of_pStage
```

`CMP116PStageSummability` is budget-valued, so callers can instantiate the
fixed-`D` P-sum budget with the Eq. (2.29) product without introducing a
nonnegativity premise for `alpha6` or for `pWeight`.  The theorem
`cmp116H_postDSum_le_of_pStage` combines that explicit P-stage budget with a
fixed-`P` nested `Z0/Z0'` residual estimate and recovers the old post-`D`
`hpostD` shape consumed by `cmp116H_termWeightSum_le_of_eq229` and the existing
activity consumers.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq229.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-p-stage-budget.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq229.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This proves only finite summation bookkeeping:
`hPStage + hpostP => hpostD`.  It does not prove Eq. (2.30), identify the
P-stage source family, prove the `Z0/Z0'` residual estimates, prove Eq. (2.29),
termwise complex-valued estimates, activity identification, source metric
comparison, Gaussian/root/Hessian/activity source facts, or CMP116 Lemma 3.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 345 (2026-06-24, **CMP116 post-P residual-stage bridge**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8361)

This checkpoint adds the source-order residual bridge after the budget-valued
P-stage helper:

```
cmp116H_postP_sum_le_of_residualStages
cmp116H_postD_sum_le_of_pStageResidualStages
cmp116H_termWeightSum_le_of_eq229_of_pStageResidualStages
cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages
```

The first theorem proves that normalized fixed-`P` `Z0` and `Z0'` residual
summability, plus a pointwise factorization, imply a post-`P` budget.  The
remaining theorems compose that post-`P` bridge with
`CMP116PStageSummability`, Eq. (2.29), and the existing finite Lemma-3
activity-estimate bridge.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-postP-residual-stage-bridge.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is finite residual-summation algebra and composition.
It does not prove or source-identify the P-stage budget, `Z0` residual
estimate, `Z0'` residual estimate, Eq. (2.29), the termwise complex-valued
estimate, activity identification, source metric comparison, Gaussian/root/
Hessian/activity source facts, or CMP116 Lemma 3.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 346 (2026-06-24, **scale-family CMP116 post-P residual bridge**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8361)

This checkpoint adds the pointwise scale-family wrapper for the source-order
pStage/residual-stage route:

```
cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages
```

The theorem applies
`cmp116Lemma3ActivityEstimate_of_eq229_pStageResidualStages` at each `(t, k)`.
It consumes per-scale Eq. (2.29), `CMP116PStageSummability`, normalized
fixed-`P` `Z0` and `Z0'` residual summability, the complex termwise estimate,
activity identification, and pointwise term-weight factorization, then returns
the canonical `CMP116Lemma3ActivityEstimateScaleFamily`.

Verification commands run for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-postP-residual-stage-scale-family.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is only scale-family composition over the verified
single-scale pStage/residual-stage finite consumer.  It does not prove or
source-identify the P-stage budget, `Z0` residual estimate, `Z0'` residual
estimate, Eq. (2.29), termwise complex-valued estimates, activity
identification, source metric comparison, Gaussian/root/Hessian/activity source
facts, or CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 347 (2026-06-24, **CMP116 Lemma 3 resummation-source boundary**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8361)

This checkpoint adds a parallel source-boundary record for the CMP116 Lemma 3
lane:

```
BalabanCMP116Lemma3ResummationSourceAssumptions
BalabanCMP116Lemma3ResummationSourceAssumptions.lemma3_activity_estimate
BalabanCMP116Lemma3ResummationSourceAssumptions.rawSource
BalabanCMP116Lemma3ResummationSourceAssumptions.to_lemma3SourceAssumptions
BalabanCMP116Lemma3ResummationSourceAssumptions.to_m3Frontier
```

The new record replaces the previous monolithic
`CMP116Lemma3ActivityEstimateScaleFamily` source field with the explicit
finite-resummation obligations already named in Lean: Eq. (2.29)
summability, `CMP116PStageSummability`, fixed-`P` `Z0/Z0'` residual
summability, the activity-identification equality, the complex termwise
estimate, nonnegativity, and the pointwise factorization.  The constructors
derive the existing Lemma-3 source-assumption record and the raw-source M3
frontier via
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageResidualStages`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-lemma3-resummation-source-boundary.log
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is source-boundary packaging only.  It does not prove or
source-identify Eq. (2.29), the P-stage budget, the `Z0` residual estimate, the
`Z0'` residual estimate, activity identification, the termwise complex-valued
estimate, source metric comparison, Gaussian/root/Hessian/activity source
facts, the rooted H# identity, or CMP116 Lemma 3.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 348 (2026-06-24, **CMP116 Lemma 3 resummation M3 constructor**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8361)

This checkpoint normalizes the M3-frontier constructor API for the
resummation-source lane:

```
CMP116RawSourceM3Frontier.of_lemma3ResummationSourceAssumptions
```

The constructor is parallel to
`CMP116RawSourceM3Frontier.of_balabanSourceAssumptions` and
`CMP116RawSourceM3Frontier.of_lemma3SourceAssumptions`.  It packages a
`BalabanCMP116Lemma3ResummationSourceAssumptions` record into the existing
raw-source M3 frontier by first deriving the Lemma-3 source-assumption record.
The method-style alias
`BalabanCMP116Lemma3ResummationSourceAssumptions.to_m3Frontier` now routes
through this constructor.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-lemma3-resummation-m3-constructor.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is API packaging only.  It proves no new estimate and
does not source-identify Eq. (2.29), the P-stage budget, `Z0/Z0'` residual
estimates, activity identification, termwise complex estimates, source metric
comparison, Gaussian/root/Hessian/activity source facts, H#, or CMP116 Lemma
3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 349 (2026-06-24, **CMP116 P-stage source-budget adapter**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8361)

This checkpoint names the source-shaped P-stage residual budget and maps it to
the already normalized P residual predicate:

```
CMP116PStageSourceBound
cmp116PResidualSummability_of_pStageSourceBound
```

`CMP116PStageSourceBound` records the fixed-`D` finite `P` sum with the
explicit source scalar

```
2 * (((blockScale : Real) + 2) ^ 4) *
  pEntropyConstant * epsilon2 * Real.exp (5 * kappa)
```

where `pEntropyConstant` is the stage-specific `O(1)` majorant.  The adapter
then proves normalized `CMP116PResidualSummability` by transitivity from this
source-shaped bound and the explicit smallness restriction that the same scalar
is at most `1`.

Local source check:

```
PDF: C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary\balaban-rg-II-cmp116-1104161193.pdf
PDF SHA256: EE39523A0F7B83AF958513C7BD6F9C7731934B40355EF5D6B0F7A68EE6D022FC
OCR: C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary\text\balaban-rg-II-cmp116-1104161193.txt
OCR SHA256: 1F783762D6EC6FFF9362BB993B2539201E0FE705A5E1C7E0545640CA9EAF2066
OCR range checked: lines 671--793; printed page 20 line 767 confirms the
displayed scalar restriction with leading `2`, `(L+2)^4`, `O(1)`, `epsilon2`,
and `exp 5*kappa`.
```

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-pstage-source-budget.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This checkpoint only converts a supplied source-shaped
P-stage finite-sum bound plus its explicit scalar smallness restriction into
the normalized P residual predicate.  It does not construct `pWeight`, prove
the P-stage source estimate, discharge `Z0/Z0'` residual stages, prove
nonnegativity, prove termwise factorization, identify the physical activity,
or prove CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 350 (2026-06-24, **CMP116 P-source residual bridge consumers**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8361)

This checkpoint routes the already named CMP116 P-stage source-bound interface
into the residual-stage consumers:

```
cmp116H_postD_sum_le_of_pStageSourceBound_residualStages
cmp116H_termWeightSum_le_of_eq229_of_pStageSourceBound_residualStages
cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages
```

Each theorem replaces only the source-neutral
`CMP116PResidualSummability` premise by
`CMP116PStageSourceBound` plus the explicit scalar smallness restriction

```
2 * (((blockScale : Real) + 2) ^ 4) *
  pEntropyConstant * epsilon2 * Real.exp (5 * pStageKappa) <= 1
```

The post-D wrapper keeps an arbitrary nonnegative base.  The term-weight and
activity wrappers keep Eq. (2.29), the Eq.-(2.29) product-weight base,
normalized `Z0/Z0'` residual summability, nonnegativity, and pointwise
factorization as explicit hypotheses.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-pstage-source-residual-bridge.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is a consumer-route improvement only.  It does not
construct `pWeight`, prove the P-stage source estimate, source-identify Eq.
(2.29), discharge `Z0/Z0'` residual stages, prove nonnegativity, prove the
pointwise source factorization, identify the physical activity, prove termwise
complex estimates, or prove CMP116 Lemma 3.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 351 (2026-06-24, **CMP116 P-source scale-family bridge**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8361)

This checkpoint lifts the P-source residual bridge to the dependent scale
family:

```
cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStageSourceBound_residualStages
```

The theorem applies
`cmp116Lemma3ActivityEstimate_of_eq229_pStageSourceBound_residualStages`
pointwise in `(t, k)`.  It consumes per-scale Eq. (2.29), per-scale
`CMP116PStageSourceBound`, the per-scale scalar smallness condition

```
2 * (((pStageBlockScale t k : Real) + 2) ^ 4) *
  pEntropyConstant t k * epsilon2 t k *
    Real.exp (5 * pStageKappa t k) <= 1
```

and the existing per-scale `Z0/Z0'` residual-stage, nonnegativity,
factorization, activity-identification, and termwise-estimate obligations.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-pstage-source-scale-family.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is pointwise packaging only.  It does not construct
`pWeight`, prove the P-stage source estimate, source-identify Eq. (2.29),
discharge `Z0/Z0'` residual stages, prove the pointwise source factorization,
identify the physical activity, prove termwise complex estimates, or prove
CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 352 (2026-06-24, **CMP116 Z0-stage source-budget adapter**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8361)

This checkpoint names the source-shaped `Z0`-stage residual budget and maps it
to the already normalized `Z0` residual predicate:

```
CMP116Z0StageSourceBound
cmp116Z0ResidualSummability_of_z0StageSourceBound
```

`CMP116Z0StageSourceBound` records the fixed-`(Z,D,P)` finite `Z0` sum with
the explicit source scalar

```
(((blockScale : Real) + 2) ^ 4) * z0EntropyConstant * epsilon2
```

The adapter proves normalized `CMP116Z0ResidualSummability` by transitivity
from this source-shaped bound and the explicit smallness restriction that the
same scalar is at most `1`.

This scalar intentionally has neither the P-stage leading `2` nor the P-stage
`Real.exp (5 * kappa)` factor.  The constant `z0EntropyConstant` is separate
from `pEntropyConstant`, because the source's different `O(1)` occurrences are
not definitionally identified.

Source anchor: CMP116 printed page 19, the `Z0` resummation around geometric
estimate (2.32), together with the collected printed page 20 smallness
restrictions.  Equation (2.32) is treated as the geometric input controlling
the `Z0` resummation, not as a literal statement of this Lean finite-sum
predicate.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-z0-stage-source-budget.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This checkpoint only converts a supplied source-shaped
`Z0` finite-sum bound plus its explicit scalar smallness restriction into the
normalized `Z0` residual predicate.  It does not construct `Z0Index`, identify
`z0Weight`, prove the `Z0` source estimate, discharge `Z0'`, prove
nonnegativity, prove termwise factorization, identify the physical activity,
or prove CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 353 (2026-06-24, **CMP116 combined post-P residual route**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`,
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8361)

This checkpoint adds a source-safe route for CMP116 Lemma 3 consumers that do
not split the final residual resummations into separate normalized `Z0` and
`Z0'` predicates:

```
CMP116PostPResidualBound
cmp116H_postD_sum_le_of_pStagePostPResidualBound
cmp116H_termWeightSum_le_of_eq229_of_pStagePostPResidualBound
cmp116Lemma3ActivityEstimate_of_eq229_pStagePostPResidualBound
cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound
```

`CMP116PostPResidualBound` records the direct fixed-`(Z,D,P)` nested
`Z0/Z0'` finite-sum estimate:

```
sum_Z0 sum_Z0' termWeight <=
  ((C3 * epsilon1) *
    balabanCMP116Lemma3Weight blockScale delta kappa sourceMetric Z) *
  pWeight Z D P
```

The downstream theorems compose this combined post-`P` bound with an explicit
P-stage budget and Eq. (2.29), then feed the existing resummation theorem for
the activity estimate.  The scale-family wrapper applies the same route
pointwise in `(t, k)`.

This deliberately avoids inventing a separate `Z0'` source scalar.  It is a
consumer interface for a supplied combined post-`P` estimate, useful when the
primary source bounds the last two resummations together or in a summation
order not faithfully represented by the repository's normalized `Z0` then
`Z0'` predicates.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMills.RG.BalabanCMP116Lemma3ScaleFamily
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-postp-combined-residual-final.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This checkpoint proves finite-sum algebraic routing only.  It
does not prove the combined post-`P` estimate, Eq. (2.29), the P-stage budget,
activity identification, termwise estimates, nonnegativity, the `Z0'` source
estimate, any CMP116 constant hierarchy, or CMP116 Lemma 3.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 354 (2026-06-24, **CMP116 split residuals to combined post-P bridge**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8361)

This checkpoint proves that the earlier split normalized residual-stage route
packages into the newer combined post-`P` residual predicate:

```
cmp116PostPResidualBound_of_residualStages
```

The theorem consumes normalized `CMP116Z0ResidualSummability`,
`CMP116Z0PrimeResidualSummability`, the pointwise residual factorization,
nonnegativity of `C3 * epsilon1`, nonnegativity of `pWeight`, and
nonnegativity of the `Z0` weight.  It produces
`CMP116PostPResidualBound` with the same canonical CMP116 Lemma-3 base
factor.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-postp-residual-bridge.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is an interface-unification theorem only.  It does not
prove the split residual estimates, the combined post-`P` estimate, any source
constant, Eq. (2.29), the P-stage budget, activity identification, termwise
estimates, or CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 355 (2026-06-24, **CMP116 post-P scale source package**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8361)

This checkpoint names the post-`P` scale-family source boundary:

```
CMP116Lemma3PostPScaleSourceAssumptions
CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate
```

The record packages exactly the assumptions consumed by
`cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_pStagePostPResidualBound`:
Eq. (2.29), the P-stage budget, the direct combined post-`P` residual bound,
activity identification, and the complex termwise estimate.  It deliberately
does not add a standalone `Z0'` source scalar, a fixed-`Z0` `Z0'` source
summability theorem, or a source identification of
`CMP116Z0PrimeResidualSummability`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-postp-scale-source-package.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is source-boundary packaging only.  It proves no source
estimate, no combined post-`P` bound, no Eq. (2.29), no P-stage budget, no
activity identification, no termwise estimate, no metric comparison, and no
CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 356 (2026-06-24, **CMP116 admissible-domain zero extension**
`YangMills.RG.BalabanCMP116Lemma3AdmissibleAdapter`; core 8362)

This checkpoint adds the source-neutral admissible-domain transport interface:

```
cmp116AdmissibleMetricZeroExtension
cmp116Lemma3ActivityEstimate_of_admissible_zeroExtension
CMP116Lemma3AdmissibleActivityEstimateScaleFamily
cmp116AdmissibleMetricScaleExtension
cmp116Lemma3ActivityEstimateScaleFamily_of_admissible_zeroExtension
balabanCMP116Lemma3Weight_domination_of_admissible_metricComparison
```

The zero-extension theorem turns a native CMP116 Lemma-3 estimate on the
admissible subtype `{X // admissible X}` into an estimate on the full index
type only when an explicit outside-domain zero theorem and amplitude
nonnegativity are supplied.  The metric-domination theorem requires both that
every target-family polymer is admissible and that the complete exponent
comparison to the Appendix-F shifted metric is supplied.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3AdmissibleAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-admissible-adapter.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3AdmissibleAdapter.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is transport bookkeeping only.  It proves no
admissibility theorem, no outside-domain vanishing theorem, no source metric
comparison, no activity construction, no combined post-`P` estimate, no Eq.
(2.29), and no CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 357 (2026-06-24, **CMP116 post-P source decomposition**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8362)

This checkpoint separates the source-side combined post-`P` residual estimate
from the canonical downstream consumer:

```
CMP116PostPResidualSourceBound
cmp116PostPResidualBound_of_sourceBound
```

`CMP116PostPResidualSourceBound` records a supplied fixed-`(Z,D,P)` combined
`Z0/Z0'` finite-sum estimate with a source amplitude and source weight.  The
adapter theorem converts it into `CMP116PostPResidualBound` only when an
explicit majorization by the CMP116 Lemma-3 base factor is supplied and the
P-weight is nonnegative.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-postp-source-decomposition.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is a boundary adapter only.  It does not prove the
combined post-`P` source estimate, identify the printed CMP116 constants,
prove the majorization into the canonical Lemma-3 base factor, prove Eq.
(2.29), prove the P-stage budget, identify the physical activity, prove
termwise estimates, or prove CMP116 Lemma 3.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 358 (2026-06-24, **CMP116 admissible post-P source composition**
`YangMills.RG.BalabanCMP116Lemma3AdmissibleAdapter`; core 8362)

This checkpoint composes the existing post-`P` source-boundary package with
the admissible-domain zero-extension adapter:

```
CMP116Lemma3PostPScaleSourceAssumptions.lemma3_activity_estimate_admissible_zeroExtension
```

The theorem instantiates `CMP116Lemma3PostPScaleSourceAssumptions` on the
native admissible subtype `{X // admissible t k X}`, uses
`source.lemma3_activity_estimate` to obtain the subtype Lemma-3 activity
estimate, then applies
`cmp116Lemma3ActivityEstimateScaleFamily_of_admissible_zeroExtension` with the
same outside-domain zero theorem and `(hp t k).amplitude_nonneg`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3AdmissibleAdapter.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-admissible-postp-source-composition.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3AdmissibleAdapter.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is composition bookkeeping only.  It proves no
admissibility theorem, no outside-domain vanishing theorem, no source metric
comparison, no Eq. (2.29), no P-stage budget, no combined post-`P` residual
bound, no activity identification, no termwise estimate, and no CMP116 Lemma
3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 359 (2026-06-24, **CMP116 post-P source majorization scale family**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint names the per-scale source-side majorization needed by the
combined post-`P` residual adapter and lifts the already verified single-scale
consumer over `(t, k)`:

```
CMP116PostPResidualSourceMajorizationScaleFamily
cmp116PostPResidualBoundScaleFamily_of_sourceBound
```

The predicate compares the source amplitude/source weight product with the
canonical CMP116 Lemma-3 base factor at each scale.  The adapter applies
`cmp116PostPResidualBound_of_sourceBound` pointwise, using a supplied
`CMP116PostPResidualSourceBound`, the scale-family majorization, and explicit
nonnegativity of the `P` weight.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-postp-source-majorization-scale-family.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is scale-family bookkeeping only.  It proves no
combined post-`P` source estimate, no majorization from CMP116 printed
constants, no Eq. (2.29), no P-stage budget, no physical activity
identification, no termwise estimate, no admissibility or outside-domain
vanishing theorem, no source-to-Appendix-F metric comparison, and no CMP116
Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 360 (2026-06-25, **CMP116 Eq. (2.29)-weighted P-stage budget**
`YangMills.RG.BalabanCMP116Eq229`,
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`,
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint names the fixed-`D` Eq. (2.29) product and uses it as the
canonical P-stage budget:

```
cmp116Eq229Product
cmp116Eq229Product_nonneg
cmp116Eq229WeightedPWeight
cmp116Eq229WeightedPWeight_nonneg
cmp116PStageSummability_of_pResidualSummability_weighted
cmp116PStageSummabilityScaleFamily_of_pResidualSummability_weighted
```

The finite-sum theorem says that if the normalized P-residual weights sum to
at most `1`, then the Eq. (2.29)-weighted P-weights sum to at most the Eq.
(2.29) product itself.  This gives the exact budget expected by
`CMP116PStageSummability` without replacing the product by an unrelated scalar
smallness bound.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq229.lean
lake build YangMills.RG.BalabanCMP116Eq229
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMills.RG.BalabanCMP116Lemma3ResidualStages
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-eq229-weighted-pstage-budget.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq229.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is finite-sum budget alignment only.  It proves no Eq.
(2.29), no source construction of the normalized P-residual weight, no P-stage
source estimate, no scalar smallness hierarchy, no combined post-`P` estimate,
no activity identification, no termwise estimate, and no CMP116 Lemma 3.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 361 (2026-06-25, **CMP116 weighted P residual to Lemma-3 scale route**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint composes the Eq. (2.29)-weighted normalized P-residual adapter
with the existing direct post-`P` residual Lemma-3 scale-family route:

```
cmp116Lemma3ActivityEstimateScaleFamily_of_eq229_weightedPResidualPostPResidualBound
```

The theorem removes the explicit `CMP116PStageSummability` premise from this
route when normalized P-residual summability and `alpha6 >= 0` are available.
The post-`P` residual bound is still required for the Eq. (2.29)-weighted
P-weights, so the theorem does not hide the combined post-`P` source work.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-weighted-presidual-postp-route.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is a source-neutral composition theorem.  It proves no
Eq. (2.29), no source construction of normalized P-residual weights, no
standalone `Z0'` source estimate, no combined post-`P` source estimate, no
activity identification, no termwise estimate, and no unconditional CMP116
Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 362 (2026-06-25, **CMP116 weighted post-P source package**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint packages the source-boundary route feeding the Eq.
(2.29)-weighted P-residual/post-`P` Lemma-3 scale-family theorem:

```
CMP116Lemma3WeightedPostPScaleSourceAssumptions
CMP116Lemma3WeightedPostPScaleSourceAssumptions.p_residual_summability
CMP116Lemma3WeightedPostPScaleSourceAssumptions.postP_residual_bound
CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate
```

The record exposes the exact obligations that remain: Eq. (2.29), the
source-shaped P-stage bound, its scalar smallness condition, `alpha6 >= 0`,
pointwise P-residual nonnegativity, the combined post-`P` source estimate,
post-`P` majorization by the Lemma-3 base factor, activity identification, and
termwise estimates.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-weighted-postp-source-package.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is source-boundary packaging only.  It proves no Eq.
(2.29), no source construction of the P family, no scalar smallness theorem, no
post-`P` source estimate, no post-`P` majorization theorem, no activity
identification, no termwise estimate, and no unconditional CMP116 Lemma 3.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 363 (2026-06-25, **CMP116 activity-termwise boundary package**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint factors the shared activity-identification and termwise-estimate
obligations out of the CMP116 Lemma-3 source packages:

```
CMP116Lemma3ActivityTermwiseScaleBoundary
CMP116Lemma3PostPScaleSourceAssumptions.activityTermwiseBoundary
CMP116Lemma3WeightedPostPScaleSourceAssumptions.activityTermwiseBoundary
```

The boundary record contains only the equality between physical activity
evaluation and `balabanCMP116H`, plus the termwise norm bound used by the finite
resummation route.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-activity-termwise-boundary.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is boundary factoring only.  It proves no activity
identification, no termwise estimate, no Eq. (2.29), no source resummation
bound, and no CMP116 Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 364 (2026-06-25, **CMP116 weighted source boundary assembly**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint names the boundary subpackages feeding the weighted post-`P`
CMP116 Lemma-3 source route and adds the record constructor that assembles the
existing package from them:

```
CMP116Lemma3Eq229ScaleBoundary
CMP116Lemma3PStageSourceScaleBoundary
CMP116Lemma3WeightedPostPSourceScaleBoundary
CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_boundaries
```

The split keeps Eq. (2.29), P-stage source/smallness data, weighted post-`P`
source/majorization data, and activity/termwise data as distinct obligations.
The constructor copies fields into `CMP116Lemma3WeightedPostPScaleSourceAssumptions`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-weighted-postp-source-boundaries.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is boundary packaging only.  It proves no Eq. (2.29), no
source construction of normalized P-residual weights, no scalar smallness
theorem, no post-`P` source estimate, no post-`P` majorization theorem, no
activity identification, no termwise estimate, and no unconditional CMP116
Lemma 3.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 365 (2026-06-25, **CMP116 weighted boundary direct consumer**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint adds the direct consumer from the named weighted post-`P`
boundary subpackages to the existing CMP116 Lemma-3 scale-family estimate:

```
CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries
```

It composes `of_boundaries` with `lemma3_activity_estimate`, so downstream code
can depend on Eq. (2.29), P-stage, weighted post-`P`, and activity/termwise
boundaries directly instead of taking the monolithic weighted source package as
one premise.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-weighted-boundary-direct-consumer.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is composition only.  It proves no Eq. (2.29), no
P-stage source estimate, no scalar smallness theorem, no post-`P` source
estimate, no post-`P` majorization theorem, no activity identification, no
termwise estimate, and no unconditional CMP116 Lemma 3.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 366 (2026-06-25, **CMP116 weighted boundary raw-source adapter**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint adds the thin raw-source adapter from the named weighted
post-`P` boundary subpackages plus separated physical source facts:

```
rawSource_of_weightedPostPBoundaries
```

The adapter composes
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries`
with `rawSource_of_lemma3ActivityEstimate`, so the output is the existing
`PhysicalGaugeCMP116LocalizedGaussianRawActivitySourceHypotheses` family with
the canonical CMP116 Lemma-3 weight and amplitude.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-weighted-boundary-raw-source.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

**Honest scope.** This is adapter composition only.  It proves no Eq. (2.29),
no P-stage source estimate, no scalar smallness theorem, no post-`P` source
estimate, no post-`P` majorization theorem, no Gaussian pushforward, no
covariance-root localization, no Wilson-Hessian identification, no local
physical activity construction, no activity identification, no termwise
estimate, and no unconditional CMP116 Lemma 3.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 367 (2026-06-25, **charged Wilson-loop connected selection rule**
`YangMills.L1_GibbsMeasure.GibbsSelectionRule`; core 8362)

This checkpoint adds the interacting centre-charge selection theorem for the
connected two-loop expression:

```
connected_wilsonLoopSU_gibbs_eq_zero
```

For positively oriented Wilson loops `es` and `es'`, if
`n ∤ es.length + es'.length`, then
`∫ W_es W_es' dμ_Gibbs - (∫ W_es dμ_Gibbs) * (∫ W_es' dμ_Gibbs) = 0`.
The proof composes the existing total-charge product selection rule with the
single-loop selection rule: non-divisibility of the total charge prevents both
individual lengths from being divisible by `n`, so at least one one-point
expectation vanishes.

Verification commands for this checkpoint:

```
lake env lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-connected-wilsonloop-selection.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

The new theorem's oracle line is
`[propext, Classical.choice, Quot.sound]`.  Honest scope: this is an exact
finite-volume lattice symmetry consequence for the interacting Gibbs measure.
It proves no continuum construction, no OS/Wightman reconstruction, no
spectral-gap statement, and no CMP116 source estimate.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 368 (2026-06-25, **mixed Wilson-loop charge selection**
`YangMills.L1_GibbsMeasure.GibbsSelectionRule`; core 8362)

This checkpoint adds the mixed charge selection rule for the interacting Gibbs
measure:

```
integral_wilsonLoopSU_mul_star_gibbs_eq_zero
connected_wilsonLoopSU_star_gibbs_eq_zero
```

For positively oriented Wilson loops `es` and `es'`, if
`(n : ℤ) ∤ (es.length : ℤ) - (es'.length : ℤ)`, then
`∫ W_es * conj(W_es') dμ_Gibbs = 0`, and the corresponding connected
covariance
`∫ W_es conj(W_es') dμ_Gibbs - (∫ W_es dμ_Gibbs) * conj(∫ W_es' dμ_Gibbs)`
also vanishes.  The proof composes exact Gibbs centre invariance with
`wilsonLoopSU_centerAct` and the existing mixed root-of-unity primitivity lemma
`rootOfUnity_pow_mul_star_pow_ne_one`.

Verification commands for this checkpoint:

```
lake env lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-mixed-wilsonloop-selection.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Both new theorem oracle lines are
`[propext, Classical.choice, Quot.sound]`.  Honest scope: this is an exact
finite-volume lattice symmetry consequence for the interacting Gibbs measure.
It proves no continuum construction, no OS/Wightman reconstruction, no
spectral-gap statement, and no CMP116 source estimate.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 369 (2026-06-25, **finite-product selection and uniform gap criterion**
`YangMills.L1_GibbsMeasure.GibbsSelectionRule`,
`YangMills.Paper.GapRefinementChallenge`; core 8362)

This checkpoint adds two source-faithful infrastructure pieces.

First, it extends the interacting Gibbs centre-charge selection rule from one
or two Wilson loops to finite products:

```
wilsonLoopSU_listProd_centerAct
integral_wilsonLoopSU_listProd_gibbs_eq_zero
integral_wilsonLoopSU_listProd_star_gibbs_eq_zero
```

The holomorphic product vanishes when the total positive-loop centre charge is
non-trivial, and the mixed holomorphic/conjugate product vanishes when the two
finite loop families have unequal total centre charge modulo `n`.

Second, it sharpens the continuum-limit quantifier infrastructure around
regulator-dependent mass gaps:

```
hasUniformPositiveEnergyGap_hasStagewisePositiveEnergyGap
hasUniformPositiveEnergyGap_iff_exists_stagewise_gaps_boundedBelow
halfScaleExcitation_no_stagewise_gaps_boundedBelow
```

The exact criterion says that stagewise positive gaps promote to a
regulator-uniform positive gap iff one can choose stagewise lower bounds that
are themselves bounded below by a single positive constant independent of the
regulator.  The existing `delta / 2` counterexample is strengthened to show
that no such bounded-below choice exists there.

Verification commands for this checkpoint:

```
lake env lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean
lake env lean YangMills\Paper\GapRefinementChallenge.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-listprod-wilsonloop-selection.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean YangMills\Paper\GapRefinementChallenge.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

All five new theorem oracle lines are `[propext, Classical.choice,
Quot.sound]`.

Honest scope: the selection rules are exact finite-volume lattice symmetry
consequences; the gap criterion is logical continuum-limit infrastructure.
This proves no Yang-Mills Hamiltonian construction, no model-specific
excitation spectrum, no continuum measure, no OS/Wightman reconstruction, no
CMP116 activity estimate, and no Clay mass gap.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 370 (2026-06-25, **connected finite-product charge selection**
`YangMills.L1_GibbsMeasure.GibbsSelectionRule`; core 8362)

This checkpoint adds the connected covariance consumer for the mixed
finite-product Wilson-loop selection rule:

```
connected_wilsonLoopSU_listProd_star_gibbs_eq_zero
```

For finite families of positively oriented Wilson loops `Ls` and `Rs`, if the
total centre charges differ modulo `n`, then

```
∫ (∏ W_L) * conj(∏ W_R) dμ_Gibbs
  - (∫ ∏ W_L dμ_Gibbs) * conj(∫ ∏ W_R dμ_Gibbs) = 0.
```

The proof reuses the already verified mixed finite-product integral selection
rule and the one-sided finite-product vanishing theorem for the two mean terms:
if both total charges were individually divisible by `n`, their integer
difference would be divisible by `n`, contradicting the hypothesis.

Verification commands for this checkpoint:

```
lake env lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-connected-listprod-wilsonloop-selection.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new theorem oracle line is `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is an exact finite-volume lattice symmetry consequence for
the interacting Gibbs measure.  It proves no continuum construction, no
OS/Wightman reconstruction, no spectral-gap statement, and no CMP116 source
estimate.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 371 (2026-06-25, **connected holomorphic finite-product selection**
`YangMills.L1_GibbsMeasure.GibbsSelectionRule`; core 8362)

This checkpoint adds the holomorphic connected covariance consumer for finite
Wilson-loop products:

```
connected_wilsonLoopSU_listProd_gibbs_eq_zero
```

For finite families of positively oriented Wilson loops `Ls` and `Rs`, if the
combined total centre charge is non-trivial modulo `n`, then

```
∫ (∏ W_L) * (∏ W_R) dμ_Gibbs
  - (∫ ∏ W_L dμ_Gibbs) * (∫ ∏ W_R dμ_Gibbs) = 0.
```

The proof applies the finite-product integral selection theorem to the
concatenated list `Ls ++ Rs`, then uses the one-sided finite-product vanishing
theorem to kill one mean factor: if both individual total charges were
divisible by `n`, their sum would be divisible by `n`, contradicting the
hypothesis.

Verification commands for this checkpoint:

```
lake env lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-connected-holomorphic-listprod-selection.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\L1_GibbsMeasure\GibbsSelectionRule.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new theorem oracle line is `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is an exact finite-volume lattice symmetry consequence for
the interacting Gibbs measure.  It proves no continuum construction, no
OS/Wightman reconstruction, no spectral-gap statement, and no CMP116 source
estimate.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 372 (2026-06-25, **stagewise lower-bound obstruction**
`YangMills.Paper.GapRefinementChallenge`; core 8362)

This checkpoint adds the generic bounded-stagewise obstruction:

```
not_exists_stagewise_gaps_boundedBelow_of_refinementsProduceArbitrarilySmallPositiveExcitations
```

If a regulator family produces arbitrarily small positive excitation energies,
then no chosen family of stagewise positive lower bounds can itself be bounded
below by one positive regulator-independent constant.  The proof composes the
previously verified arbitrarily-small-refinement obstruction to a uniform gap
with the exact criterion
`hasUniformPositiveEnergyGap_iff_exists_stagewise_gaps_boundedBelow`.

Verification commands for this checkpoint:

```
lake env lean YangMills\Paper\GapRefinementChallenge.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-stagewise-bound-obstruction.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\Paper\GapRefinementChallenge.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md
```

The new theorem oracle line is `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is logical continuum-limit quantifier infrastructure only.
It proves no Yang-Mills Hamiltonian construction, no model-specific excitation
spectrum, no continuum measure, no OS/Wightman reconstruction, no CMP116
activity estimate, and no Clay mass gap.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 373 (2026-06-25, **uniform-gap failure equivalence**
`YangMills.Paper.GapRefinementChallenge`; core 8362)

This checkpoint closes the logical converse for the regulator-gap quantifier
infrastructure:

```
refinementsProduceArbitrarilySmallPositiveExcitations_of_not_hasUniformPositiveEnergyGap
not_hasUniformPositiveEnergyGap_iff_refinementsProduceArbitrarilySmallPositiveExcitations
```

Under the explicit hypothesis that every declared excitation energy is
positive, failure of a regulator-uniform positive gap is equivalent to the
existence of arbitrarily small positive excitation energies along the
refinement family.  The forward direction unwraps the negation of the uniform
lower-bound existential and uses positivity to build the refinement witness.
The reverse direction is the previously verified obstruction theorem.

Verification commands for this checkpoint:

```
lake env lean YangMills\Paper\GapRefinementChallenge.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-uniform-gap-refinement-iff.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\Paper\GapRefinementChallenge.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Both new theorem oracle lines are `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is logical continuum-limit quantifier infrastructure only.
It proves no Yang-Mills Hamiltonian construction, no model-specific excitation
spectrum, no continuum measure, no OS/Wightman reconstruction, no CMP116
activity estimate, and no Clay mass gap.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 374 (2026-06-25, **CMP116 P-stage pointwise/geometric constructor**
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`; core 8362)

This checkpoint adds the source-neutral constructor for the P-stage source
bound:

```
cmp116PStageSourceBound_of_pointwise_geometric
```

For each fixed `(Z,D)`, a pointwise majorization of the P-residual weight by
the extracted P-smallness factor times a geometric P-weight, together with the
finite geometric P-family summation consequence, proves the existing predicate

```
CMP116PStageSourceBound
```

The theorem is intentionally not a restatement of `CMP116PStageSourceBound`:
its premises split the P argument into a pointwise source-term bound and a
separate finite geometric sum.  It also deliberately does not call the
geometric summation premise equation (2.31) itself; it is the finite-sum
consequence one obtains after extracting the source P-family geometry.
Equation (2.30) is only the surrounding metric/cardinality comparison.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-pstage-pointwise-geometric-full.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

The new theorem oracle line is `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is finite P-stage resummation algebra inside the existing
CMP116 source interface.  It proves no construction of `PIndex`, no source
identification of `pResidualWeight` or `pGeometryWeight`, no scalar smallness
hierarchy, no Eq. (2.29) source summability, no post-`P` estimate, no activity
identification, no termwise complex estimate, and no Clay mass gap.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 375 (2026-06-25, **CMP116 P-stage scale-boundary constructor**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint lifts the P-stage pointwise/geometric constructor to the
existing scale-family boundary record:

```
CMP116Lemma3PStageSourceScaleBoundary.of_pointwise_geometric
```

The constructor fills the `p_stage_source_bound` field using
`cmp116PStageSourceBound_of_pointwise_geometric`, while keeping the scalar
smallness field and pointwise nonnegativity field explicit.  Its hypotheses are
the per-scale P-term majorization, the per-scale finite geometric P-family
summation consequence, `epsilon2 >= 0`, the displayed P-stage smallness
restriction, and nonnegativity of `pResidualWeight`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-pstage-scale-boundary-geometric.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

The new constructor oracle line is `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is scale-family record assembly plus the previously proved
finite P-stage resummation algebra.  It proves no source construction of
`PIndex`, no source identification of `pResidualWeight` or `pGeometryWeight`,
no scalar-smallness hierarchy, no Eq. (2.29), no post-`P` estimate, no activity
identification, no termwise complex estimate, and no Clay mass gap.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 376 (2026-06-25, **P-stage boundary residual-summability consumer**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint exposes the normalized P-residual summability consequence
directly from the P-stage source boundary:

```
CMP116Lemma3PStageSourceScaleBoundary.p_residual_summability
```

The accessor applies `cmp116PResidualSummability_of_pStageSourceBound` at each
scale using only the boundary's `p_stage_source_bound` and
`p_stage_smallness` fields.  This lets downstream finite-sum consumers use the
P-stage boundary without first assembling the larger weighted post-`P` source
package.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-pstage-boundary-residual-summability.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

The new accessor oracle line is `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is a source-neutral consumer of an already supplied P-stage
source boundary and scalar smallness.  It proves no source construction of
`PIndex`, no source identification of `pResidualWeight` or `pGeometryWeight`,
no scalar-smallness hierarchy, no Eq. (2.29), no post-`P` estimate, no activity
identification, no termwise complex estimate, and no Clay mass gap.  Clay
distance **~0% (<0.1%), unchanged**.

## Addendum 377 (2026-06-25, **post-P boundary residual consumer**
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8362)

This checkpoint exposes the canonical post-`P` residual bound directly from
the weighted post-`P` source boundary plus the two nonnegativity-carrying
boundaries:

```
CMP116Lemma3WeightedPostPSourceScaleBoundary.postP_residual_bound
```

The accessor applies `cmp116PostPResidualBoundScaleFamily_of_sourceBound` to
the boundary's `postP_source_bound` and `postP_majorization` fields.  The
nonnegativity of the Eq. (2.29)-weighted P weight is derived explicitly from
`CMP116Lemma3Eq229ScaleBoundary.alpha6_nonneg` and
`CMP116Lemma3PStageSourceScaleBoundary.p_residual_weight_nonneg`.  This lets
downstream consumers use the post-`P` boundary without first assembling the
larger weighted post-`P` scale-source package.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-postp-boundary-residual-consumer.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

The new accessor oracle line is `[propext, Classical.choice, Quot.sound]`.
Honest scope: this is a source-neutral consumer of already supplied Eq. (2.29),
P-stage, and post-`P` source boundaries.  It proves no source construction of
the `D/P/Z0/Z0'` families, no scalar-smallness hierarchy, no Eq. (2.29), no
combined post-`P` source estimate, no activity identification, no termwise
complex estimate, and no Clay mass gap.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 378 (2026-06-25, **CMP116 Eq. (2.31) P-bond entropy boundary**
`YangMills.RG.BalabanCMP116Eq231`; direct P-stage bridge; core 8363)

This checkpoint adds the narrow Eq. (2.31) P-bond boundary and finite subset
entropy theorem, then connects it directly to the existing P-stage
source-bound route:

```
CMP116Eq231PBondBoundary
cmp116Eq231PWeight
cmp116PGeometricFamilySummation_of_eq231
cmp116PStageSourceBound_of_eq231_pointwise
CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise
```

The boundary records only the data needed to overcount current `PIndex`
entries by finite bond subsets: an injective bond-set encoding, containment in
an eligible bond carrier, nonnegative gap mass, and the carrier count
`#carrier <= 4*M^4*gapMass`.  The theorem proves the finite powerset estimate
behind Eq. (2.31), using
`4*M^4*exp(-2*rate) <= rate`, and then weakens the resulting `<= 1` bound to
the existing P-stage constructor target through the explicit hypothesis
`1 <= pEntropyConstant * exp(5*kappa)`.

This also corrects the local attribution in
`BalabanCMP116Lemma3ResidualStages.lean`: Eq. (2.30) is the metric/cardinality
comparison, not the P-family summation.  The direct constructors remove the
intermediate abstract `hgeometric` premise when the Eq. (2.31) bond boundary is
available.  The existing public P-stage API names are unchanged.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-pstage-direct.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq231.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

The new theorem oracle lines are `[propext, Classical.choice, Quot.sound]`.
Honest scope: this proves only the finite Eq. (2.31) bond-subset entropy
estimate under an explicit boundary and its finite composition into the
P-stage source-bound route.  It proves no construction of `PIndex`, no source
identification of `pWeight` or `pGeometryWeight`, no Eq. (2.29), no scalar
hierarchy, no post-`P` estimate, no activity identification, no termwise
complex estimate, and no Clay mass gap.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 379 (2026-06-25, **Eq. (2.31)-specialized weighted post-P
Lemma-3 consumer** `YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8363)

This checkpoint exposes the direct scale-family consumer

```
CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries
```

It composes the Eq. (2.31) P-bond boundary constructor
`CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise` with the existing
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_boundaries`.
The result removes the intermediate `CMP116Lemma3PStageSourceScaleBoundary`
premise when explicit Eq. (2.31) bond data are already available, while keeping
Eq. (2.29), pointwise P residual majorization, Eq. (2.31) rate/target data,
scalar smallness, weighted post-`P` source/majorization, activity
identification, and termwise estimates as explicit inputs.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-weighted-postp-lemma3.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Honest scope: this is source-neutral composition only.  It proves no source
construction of `PIndex`, no source identification of `pResidualWeight` or
`pGeometryWeight`, no Eq. (2.29), no scalar hierarchy, no weighted post-`P`
source estimate, no activity identification, no termwise complex estimate, and
no Clay mass gap.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 380 (2026-06-25, **Eq. (2.31)-specialized weighted post-P raw
source adapter** `YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8363)

This checkpoint exposes the direct raw-source adapter

```
rawSource_of_eq231_weightedPostPBoundaries
```

It composes
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries`
with `rawSource_of_lemma3ActivityEstimate`.  This removes the intermediate
`CMP116Lemma3PStageSourceScaleBoundary` premise from raw-source construction
when explicit Eq. (2.31) bond-boundary data are already available.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-rawsource-weighted-postp.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Honest scope: this is a source-neutral adapter composition only.  It proves no
Gaussian pushforward, covariance-root localization, Wilson-Hessian
identification, local activity construction, Eq. (2.31) source construction,
Eq. (2.29), scalar hierarchy, weighted post-`P` source estimate, activity
identification, termwise estimate, or Clay mass gap.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 381 (2026-06-25, **Eq. (2.31) weighted package raw-source
projection** `YangMills.RG.BalabanCMP116Lemma3ScaleFamily`; core 8363)

This checkpoint exposes two source-neutral package adapters:

```
CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries
CMP116Lemma3WeightedPostPScaleSourceAssumptions.rawSource
```

The first constructs the full weighted post-`P` scale-source package directly
from Eq. (2.29), explicit Eq. (2.31) P-bond data, pointwise/rate/target/
smallness/nonnegativity hypotheses, the weighted post-`P` boundary, and the
activity/termwise boundary.  The second projects any such package to the
physical raw-source records using the existing separated Gaussian/root/Hessian/
activity hypotheses.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-weighted-package-rawsource.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Honest scope: this is package plumbing only.  It proves no construction of the
CMP116 P family, no pointwise residual estimate, no Eq. (2.29), no scalar
hierarchy, no weighted post-`P` source estimate or majorization, no activity
identification, no termwise estimate, no Gaussian pushforward, no covariance-
root localization, no Wilson-Hessian identification, no local activity
construction, and no Clay mass gap.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 382 (2026-06-25, **weighted post-P source frontier package**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8363)

This checkpoint exposes the source-theorem-layer package

```
BalabanCMP116Lemma3WeightedPostPSourceAssumptions
```

plus the projections/constructors

```
BalabanCMP116Lemma3WeightedPostPSourceAssumptions.lemma3_activity_estimate
BalabanCMP116Lemma3WeightedPostPSourceAssumptions.rawSource
BalabanCMP116Lemma3WeightedPostPSourceAssumptions.to_lemma3SourceAssumptions
CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions
BalabanCMP116Lemma3WeightedPostPSourceAssumptions.to_m3Frontier
```

The package keeps the physical/M3 source obligations explicit while replacing
the monolithic Lemma-3 estimate field with a supplied
`CMP116Lemma3WeightedPostPScaleSourceAssumptions` package.  The constructors
then reuse the already checked Lemma-3 source and M3-frontier routes.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-weighted-postp-source-frontier.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Honest scope: this is source-frontier record plumbing only.  It proves no
Eq. (2.29), no Eq. (2.31) source construction, no P-stage source estimate, no
weighted post-`P` source estimate or majorization, no activity identification,
no termwise estimate, no Gaussian pushforward, no covariance-root localization,
no Wilson-Hessian identification, no local activity construction, and no Clay
mass gap.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 383 (2026-06-25, **Eq. (2.31) weighted post-P source-frontier constructor**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8363)

This checkpoint exposes the source-theorem-layer constructor

```
BalabanCMP116Lemma3WeightedPostPSourceAssumptions.of_eq231_boundaries
```

It builds the `weighted_postP_source` field with the already checked
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries`, then
copies the physical/M3 source fields into
`BalabanCMP116Lemma3WeightedPostPSourceAssumptions`.  This removes only a
manual intermediate package-assembly step for callers that already have
Eq. (2.31) P-bond data.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-weighted-postp-source-frontier.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Honest scope: this is record assembly only.  It proves no Eq. (2.29), no
Eq. (2.31) source construction, no pointwise P-residual estimate, no scalar
hierarchy, no weighted post-`P` source estimate or majorization, no activity
identification, no termwise estimate, no Gaussian pushforward, no covariance-
root localization, no Wilson-Hessian identification, no local activity
construction, and no Clay mass gap.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 384 (2026-06-25, **Eq. (2.31) weighted post-P M3-frontier constructor**
`YangMills.RG.BalabanCMP116SourceTheorem`; core 8363)

This checkpoint exposes the direct M3-frontier constructor

```
CMP116RawSourceM3Frontier.of_eq231WeightedPostPSourceBoundaries
```

It composes
`BalabanCMP116Lemma3WeightedPostPSourceAssumptions.of_eq231_boundaries` with
`CMP116RawSourceM3Frontier.of_lemma3WeightedPostPSourceAssumptions`, so a caller
with explicit Eq. (2.31) weighted post-`P` source-boundary data can reach the
existing raw-source M3 frontier without manually assembling the intermediate
source-theorem package.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-weighted-postp-m3-frontier.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\SOURCE-CLAIM-AUDIT.md
```

Honest scope: this is source-neutral composition only.  It proves no
Eq. (2.29), no Eq. (2.31) source construction, no pointwise P-residual
estimate, no scalar hierarchy, no weighted post-`P` source estimate or
majorization, no activity identification, no termwise estimate, no Gaussian
pushforward, no covariance-root localization, no Wilson-Hessian identification,
no local activity construction, no H# identity, no RG-flow bound, no IR bound,
and no Clay mass gap.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 385 (2026-06-25, **structured primary-source citation lookup**
`docs/source-citations` and `scripts/source_citations.py`; core 8363)

This checkpoint adds a repository-native citation catalog for the source
regions that have been repeatedly revisited during the CMP116 Lemma 3 campaign:

```
docs/SOURCE-CITATIONS.md
docs/source-citations/cmp116-lemma3.json
scripts/source_citations.py
```

The catalog records stable keys such as `cmp116.eq231.p-bond-sum`, local
artifact paths under the runtime source cache, status labels
(`visual_confirmed`, `ocr_corrupted`, etc.), Lean-facing targets, permitted
uses, prohibited overclaims, and open extraction questions.  It is intended to
make future source work start from a compact locator rather than broad OCR
searches or repeated rendered-page rediscovery.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py list
python scripts\source_citations.py show cmp116.eq231.p-bond-sum
python scripts\source_citations.py find Eq231
python scripts\source_citations.py lean CMP116Eq231PBondBoundary
python scripts\source_citations.py check-local
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-source-citations.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md README.md docs\SOURCE-CITATIONS.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md scripts\source_citations.py
```

Honest scope: this is navigation and provenance infrastructure only.  It does
not prove any CMP116 estimate, does not improve OCR fidelity, does not add a
new source theorem, and does not discharge Eq. (2.29), Eq. (2.31), post-`P`
resummation, scalar hierarchy, activity identification, Gaussian pushforward,
covariance-root localization, Wilson-Hessian identification, H# identity,
RG-flow bound, IR bound, or Clay mass gap.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 386 (2026-06-25, **CMP116 Eq. (2.31) source-shaped rate reducer**
`YangMills.RG.BalabanCMP116Eq231`,
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`,
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`, and
`YangMills.RG.BalabanCMP116SourceTheorem`)

This checkpoint removes the opaque source-facing Eq. (2.31) rate premise from
the weighted post-`P` route.  The new theorem

```
cmp116Eq231_rate_condition_of_source_smallness
```

proves the elementary implication

```
0 < gk
80*M^4*gk^2 <= gamma2*epsilon1^2
------------------------------------------------------------
4*M^4*exp(-2*(gamma2*epsilon1^2/(20*gk^2)))
  <= gamma2*epsilon1^2/(20*gk^2)
```

The fixed-index constructor
`cmp116PStageSourceBound_of_eq231_pointwise`, the scale-family constructor
`CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise`, the weighted
post-`P` constructors
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries` and
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries`,
and the source-theorem/M3-frontier constructors now consume the source-shaped
rate

```
gamma2 * epsilon1^2 / (20*gk^2)
```

through explicit `hgk` and `hsourceRateSmall` hypotheses instead of accepting
an arbitrary `eq231Rate` plus `hrate`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
python scripts\source_citations.py validate
python scripts\source_citations.py lean cmp116Eq231_rate_condition_of_source_smallness
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-source-rate-smallness.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq231.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md README.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Honest scope: this does not prove that CMP116 states the displayed `80`
smallness condition, does not extract the full source constant hierarchy, and
does not construct the P family, pointwise P-residual estimate, Eq. (2.29),
post-`P` source estimate, activity identification, termwise estimate,
Gaussian pushforward, covariance-root localization, Wilson-Hessian
identification, H# identity, RG-flow bound, IR bound, or Clay mass gap.  It
only discharges the formal exponential-rate condition once the source-shaped
positivity and sufficient smallness condition are available.  Clay distance
**~0% (<0.1%), unchanged**.

## Addendum 387 (2026-06-25, **CMP116 Eq. (2.31) visual extraction**
`docs/source-citations`, `scripts/source_citations.py`, and
`YangMills.RG.BalabanCMP116Eq231`)

This checkpoint records the visually inspected CMP116 Eq. (2.31) display in
the repository citation catalog.  The key
`cmp116.eq231.p-bond-sum` is now `visual_confirmed` and records the exact
source-facing shape:

```
rho = gamma2*epsilon1^2/(20*gk^2)
gapMass = M^-4*|Z0 \ Y0|
summand = exp(-rho*gapMass) * exp(-2*rho*|P|)
bracket = rho - 4*M^4*exp(-2*rho)
```

The citation CLI now prints `extracted claims` for entries that have them, so
future workers can use

```
python scripts\source_citations.py show cmp116.eq231.p-bond-sum
```

without reopening broad OCR windows.  The Lean docstring in
`BalabanCMP116Eq231.lean` was updated to distinguish the visually confirmed
source bracket from the stronger sufficient condition proved by
`cmp116Eq231_rate_condition_of_source_smallness`.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp116.eq231.p-bond-sum
python scripts\source_citations.py find "rho - 4"
python scripts\source_citations.py check-local
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-visual-extraction.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq231.lean CURRENT-STATE.md README.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json scripts\source_citations.py
```

Honest scope: this is source extraction and auditability infrastructure.  It
does not construct the source-to-Lean dictionary for `PIndex`, `pBonds`, or
`bondCarrier`, does not instantiate `CMP116Eq231PBondBoundary`, does not prove
the full scalar hierarchy after Eq. (2.31), and does not discharge Eq. (2.29),
post-`P`, activity, Gaussian/root/Hessian, H#, RG-flow, IR, or Clay mass-gap
inputs.  Clay distance **~0% (<0.1%), unchanged**.

## Addendum 388 (2026-06-25, **CMP116 Eq. (2.31) exact source-bracket interface**
`YangMills.RG.BalabanCMP116Eq231`,
`YangMills.RG.BalabanCMP116Lemma3ResidualStages`,
`YangMills.RG.BalabanCMP116Lemma3ScaleFamily`, and
`YangMills.RG.BalabanCMP116SourceTheorem`)

This checkpoint removes the artificial source-facing use of the sufficient
condition

```
0 < gk
80*M^4*gk^2 <= gamma2*epsilon1^2
```

from the Eq. (2.31)-specialized P-stage and weighted post-`P` routes.  The new
theorem

```
cmp116Eq231_rate_condition_of_source_bracket
```

rewrites the exact source bracket condition recorded for Eq. (2.31),

```
4*M^4*exp(-(gamma2*epsilon1^2/(10*gk^2)))
  <= gamma2*epsilon1^2/(20*gk^2),
```

into the generic finite P-family rate premise

```
4*M^4*exp(-2*(gamma2*epsilon1^2/(20*gk^2)))
  <= gamma2*epsilon1^2/(20*gk^2).
```

The fixed-index constructor
`cmp116PStageSourceBound_of_eq231_pointwise`, the scale-family constructor
`CMP116Lemma3PStageSourceScaleBoundary.of_eq231_pointwise`, the weighted
post-`P` constructors
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_boundaries` and
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_boundaries`,
and the source-theorem/M3-frontier constructors now consume that exact bracket
premise directly.  The older
`cmp116Eq231_rate_condition_of_source_smallness` theorem remains available as
a formal sufficient reducer, but is no longer the active source-facing contract.

Verification commands for this checkpoint:

```
lake build YangMills.RG.BalabanCMP116Eq231
lake build YangMills.RG.BalabanCMP116Lemma3ResidualStages
lake build YangMills.RG.BalabanCMP116Lemma3ScaleFamily
lake env lean YangMills\RG\BalabanCMP116SourceTheorem.lean
python scripts\source_citations.py validate
python scripts\source_citations.py lean cmp116Eq231_rate_condition_of_source_bracket
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-source-bracket.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean YangMills\RG\BalabanCMP116Eq231.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean YangMills\RG\BalabanCMP116SourceTheorem.lean CURRENT-STATE.md README.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Honest scope: this is a weakening and source-alignment of an existing Eq.
(2.31) interface, not a construction of Balaban's finite bond set inside the
repository model.  It does not construct `PIndex`, `pBonds`, or `bondCarrier`,
does not prove the pointwise P-residual estimate, Eq. (2.29), post-`P` source
estimate, activity identification, termwise estimate, Gaussian pushforward,
covariance-root localization, Wilson-Hessian identification, H# identity,
RG-flow bound, IR bound, or Clay mass gap.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 389 (2026-06-25, **CMP116 Eq. (2.29) visual extraction**
`docs/source-citations`, `docs/BALABAN-SOURCE-BOUNDS.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, and `CURRENT-STATE.md`)

This checkpoint records a visual inspection of CMP116 printed/PDF page 18 for
the D-stage summability region.  The citation key
`cmp116.eq229.d-stage-summability` is now `visual_confirmed` and records:

```
Eq. (2.27):
  sum_{Y in D} (d_k(Y) + 5) >= d_k(Y0) + 5

Eq. (2.29):
  sum_D prod_{Y in D} alpha6 * exp(-delta*kappa*d_k(Y)) <= 1

Eq. (2.30):
  (3*2^3)^-1 * M^-4 * |Y| <= d_k(Y) <= M^-4 * |Y| - 1
```

The page also records the extraction of
`alpha6 * exp(-delta*kappa*d_k(Y))` from each factor in the product over
`Y in D`, the product reduction (2.28), and the qualitative source condition:
for `K` sufficiently large and `alpha6` sufficiently small, Eq. (2.29) holds.

No Lean theorem was added in this checkpoint.  The purpose is source
auditability: the exact display is now available through

```
python scripts\source_citations.py show cmp116.eq229.d-stage-summability
```

without reopening the OCR window.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp116.eq229.d-stage-summability
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md README.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Honest scope: this extraction does not prove Eq. (2.29) in Lean, does not
formalize the cited combinatorial proof from [26], does not determine uniform
threshold dependencies for `K` and `alpha6`, and does not identify the
repository's `DIndex`, `DParts`, or `eq229Metric` with Balaban's source
families.  It only removes OCR ambiguity around the displayed D-stage product
summability statement and adjacent metric inequalities.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 390 (2026-06-25, **CMP116 reference [26] source target**
`docs/source-citations`, `docs/BALABAN-SOURCE-BOUNDS.md`,
`docs/SOURCE-CITATIONS.md`, `docs/SOURCE-CLAIM-AUDIT.md`, and
`CURRENT-STATE.md`)

This checkpoint identifies the bibliographic target behind CMP116's statement
that Eq. (2.29)-type inequalities can be proved by a modification of the
argument in `[26]`.  CMP116 uses Part I for its full reference list; CMP109
printed page 299, reference 26, visually identifies the source as:

```
C. Cammarota, Decay of correlations for infinite range interactions in
unbounded spin systems, Commun. Math. Phys. 85, 517-528 (1982).
```

The new citation key is:

```
cmp109.ref26.cammarota-infinite-range-cluster
```

It resolves to the local CMP109 PDF/text artifacts and the rendered page
`renders/cmp109-reference-26-page-51.png` in the persistent source cache.

No Lean theorem was added in this checkpoint.  The purpose is to remove the
repeated OCR/bibliography search and make the next source request precise:
extract the actual Cammarota theorem, constants, hypotheses, and dictionary
needed to theorem-feed `CMP116Lemma3Eq229ScaleBoundary`.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp109.ref26.cammarota-infinite-range-cluster
python scripts\source_citations.py check-local
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md README.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Honest scope: this is bibliographic source-targeting only.  It does not prove
Eq. (2.29), does not formalize Cammarota's cluster/decay theorem, does not
determine threshold dependencies for `K` or `alpha6`, and does not identify
Cammarota's or Balaban's source families with the repository's `DIndex/DParts`.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 391 (2026-06-25, **Cammarota CMP85 source-access ledger**
`docs/source-citations`, `docs/BALABAN-SOURCE-BOUNDS.md`,
`docs/SOURCE-CITATIONS.md`, `docs/SOURCE-CLAIM-AUDIT.md`, `README.md`, and
`CURRENT-STATE.md`)

This checkpoint adds a direct citation/access key for the Cammarota paper
identified in Addendum 390:

```
cammarota.cmp85.polymer-mayer-source-target
```

The entry records DOI `10.1007/BF01403502`, Springer metadata, Project Euclid
HTML/PDF targets, and the author-uploaded ResearchGate OCR mirror.  The
important status is negative and explicit: the automation environment confirmed
the paper-level polymer-model/Mayer-series relevance, but did not obtain a
clean primary PDF or theorem text that can discharge CMP116 Eq. (2.29).  Project
Euclid returned anti-bot HTML to the automation environment; Springer exposes
metadata and a subscription PDF path; ResearchGate exposes author-uploaded OCR
that is too corrupted to set Lean constants or threshold hypotheses.

No Lean theorem was added in this checkpoint.  The purpose is to stop repeated
broad OCR/source searches and make the next source request exact: obtain the
Cammarota theorem/lemma/equation, its constants and smallness hypotheses, and
the dictionary to Balaban's `D` families before trying to theorem-feed
`CMP116Eq229Summability`.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cammarota.cmp85.polymer-mayer-source-target
python scripts\source_citations.py find Cammarota
python scripts\source_citations.py check-local
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cammarota-source-access.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md README.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Honest scope: this is an access ledger and source request, not a proof of Eq.
(2.29).  It does not formalize Cammarota's theorem, does not determine
large-`K`/small-`alpha6` thresholds, and does not identify Cammarota polymers,
Balaban `D` families, or repository `DIndex/DParts`.  Clay distance **~0%
(<0.1%), unchanged**.

## Addendum 392 (2026-06-25, **citation CLI web-target display**
`scripts/source_citations.py`, `docs/SOURCE-CITATIONS.md`, and
`CURRENT-STATE.md`)

This checkpoint makes the citation lookup system more directly usable for
source-pending entries.  `python scripts\source_citations.py show <key>` now
prints direct web targets from both source metadata and citation locators,
deduplicated by URL.  For example:

```
python scripts\source_citations.py show cammarota.cmp85.polymer-mayer-source-target
```

now displays the Springer, Project Euclid, and author-uploaded OCR targets
without requiring a worker to open the JSON catalog or repeat web search.

No Lean theorem was added.  This is repository infrastructure for source
access and auditability, designed to reduce repeated OCR/search work while
keeping `source_pending` entries clearly non-theorem-fed.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cammarota.cmp85.polymer-mayer-source-target
python scripts\source_citations.py find Cammarota -v
python -m py_compile scripts\source_citations.py
python scripts\source_citations.py check-local
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-citation-cli-weburls.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\VERIFICATION-LEDGER.md scripts\source_citations.py
```

Honest scope: this changes only citation CLI output and docs.  It does not
retrieve the Cammarota PDF, extract Cammarota's theorem, prove Eq. (2.29), or
alter any Lean theorem/hypothesis boundary.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 393 (2026-06-25, **CMP116 Eq. (2.31) P-family source target**
`docs/source-citations`, `docs/SOURCE-CITATIONS.md`,
`docs/BALABAN-SOURCE-BOUNDS.md`, `docs/SOURCE-CLAIM-AUDIT.md`, and
`CURRENT-STATE.md`)

This checkpoint records the next non-cosmetic source target for the Eq. (2.31)
P-stage route:

```
cmp116.eq231.p-family-carrier-source-target
```

The current Lean path still accepts arbitrary `CMP116Eq231PBondBoundary` data.
The visually confirmed Eq. (2.31) display supplies the rate, gap factor, and
finite-subset bracket, but it does not yet identify Balaban's finite bond set
`P` with the repository's `PIndex/pBonds`, nor prove the carrier bound
`|Carrier(Z0,Y0)| <= 4*|Z0 \ Y0|`.  This entry makes that blocker explicit and
names the exact source facts needed before a Lean theorem may replace the
arbitrary boundary argument.

No Lean theorem was added in this checkpoint.  This avoids the false-progress
route of adding a source-looking record that merely repackages the same
arbitrary `P` data.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_citations.py find P-family -v
python scripts\source_citations.py check-local
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-pfamily-source-target.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Honest scope: this is a source-request and citation-audit commit only.  It does
not construct `PIndex`, `pBonds`, `bondCarrier`, prove
`pBonds_injective`, prove the pointwise P-residual estimate, discharge Eq.
(2.29), prove any post-`P` source estimate, or alter the Clay-distance status.
Clay distance **~0% (<0.1%), unchanged**.

## Addendum 394 (2026-06-25, **citation blocker view**
`scripts/source_citations.py`, `docs/SOURCE-CITATIONS.md`, and
`CURRENT-STATE.md`)

This checkpoint adds a compact blocker view to the primary-source citation CLI:

```
python scripts\source_citations.py blockers
python scripts\source_citations.py blockers --status source_pending
```

By default, `blockers` lists all `source_pending` and `ocr_corrupted` entries,
including the source, summary, first Lean consumers, and first open question.
The verbose form reuses the full `show` renderer.  This is meant to make the
next source wake start from the existing citation catalog rather than from
broad OCR or web search.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py blockers
python scripts\source_citations.py blockers --status source_pending
python scripts\source_citations.py blockers -v
python -m py_compile scripts\source_citations.py
python scripts\source_citations.py check-local
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-citation-blockers.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\VERIFICATION-LEDGER.md scripts\source_citations.py
```

Honest scope: this is source-work infrastructure only.  It does not extract new
primary-source mathematics, prove Eq. (2.29), construct the Eq. (2.31)
P-family, or change any Lean theorem boundary.  Clay distance **~0% (<0.1%),
unchanged**.

## Addendum 395 (2026-06-25, **CMP116 Eq. (2.37) and C3 visual extraction**)

Files touched:
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`CURRENT-STATE.md`, and `docs/VERIFICATION-LEDGER.md`.

This checkpoint upgrades two CMP116 Lemma-3 citation entries from
`ocr_corrupted` to `visual_confirmed` using the rendered page-20 source image:

- `cmp116.eq237.post-p-resummation` now records the visual Eq. (2.37) bound:
  for fixed `Z0'`, the post-`P` resummation is controlled by the
  `exp(-(kappa1-1)*(LM)^-4*|Z \ Z0'|)` factor, a product over connected
  components `Z_i'` with factors
  `2*(L+2)^4*O(1)*epsilon2*exp(-((1-7*delta)/2)*L*kappa*d_{k+1}(Z_i'))`,
  and the residual `exp(O(1)*alpha5*|Z|)` factor.
- `cmp116.constants.c3-alpha5` now records the visual alpha5 region,
  the boundedness assumptions on `(LM)^4*alpha0`, `(LM)^4*alpha1`,
  `(LM)^4*alpha4`, `(LM)^4*gamma2`, the resulting absolute-constant
  majorization, and the displayed final
  `C3 = 2*(L+2)^4*O(1)*2*E0*C1*alpha4^-1*alpha6^-1*M^q*exp(C2*kappa1)`
  shape feeding Lemma 3 / Eq. (2.38).

The extraction also records the source-design conclusion already reflected in
Lean: Eq. (2.37) plus the following paragraph supports a combined post-`P`
source boundary and a separate majorization into the canonical Lemma-3 base
factor.  It does not by itself justify splitting the post-`P` source statement
into standalone normalized `Z0` and `Z0'` theorems.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp116.eq237.post-p-resummation
python scripts\source_citations.py show cmp116.constants.c3-alpha5
python scripts\source_citations.py blockers
python scripts\source_citations.py check-local
lake build YangMillsCore
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Oracle note: `lake env lean oracle_check.lean` was attempted with 120s, 300s,
and 600s timeouts and did not complete in this wake; timed-out `lake`/`lean`
processes were stopped.  The partial log
`runtime\oracle-eq237-c3-source.log` contained only standard Lean axiom
sets through the entries reached.  No Lean source file was touched by this
checkpoint.

Honest scope: this is source extraction and auditability work.  No Lean theorem
boundary changed, no Eq. (2.29) theorem was proved, no Eq. (2.31) P-family
carrier was constructed, and no post-`P` source dictionary was supplied.
Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 396 (2026-06-25, **CMP116 Eq. (2.31) concrete source bond-set route**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`,
`YangMills/RG/BalabanCMP116Lemma3ResidualStages.lean`,
`YangMills/RG/BalabanCMP116Lemma3ScaleFamily.lean`,
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `CURRENT-STATE.md`, and this ledger.

This checkpoint narrows one Eq. (2.31) source-facing lane by specializing the
`P` index to the finite bond set itself:

- `cmp116Eq231SourcePIndex` presents source `P` families as filtered powersets
  of the four-direction carrier `gapCubes Z D ×ˢ Finset.univ`.
- `CMP116Eq231PBondBoundary.of_sourceBondSets` constructs the generic
  Eq. (2.31) boundary with `pBonds Z D P := P`, so injectivity is definitional;
  the gap mass is `gapCubes.card / localizationScale^4`, and the carrier count
  is the elementary `4 * gapCubes.card` product count.
- `CMP116Eq231PBondBoundary.of_sourceFilteredBondSets` removes even the
  containment argument when the family is supplied as that filtered powerset.
- `cmp116PStageSourceBound_of_eq231_sourceBondSets` and
  `cmp116PStageSourceBound_of_eq231_filteredBondSets` expose the P-stage source
  bound without asking callers for arbitrary `CMP116Eq231PBondBoundary` data.
- `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourceBondSets` is the first
  downstream scale route switched to the concrete finite-bond-set `PIndex`.

The source-pending citation `cmp116.eq231.p-family-carrier-source-target` was
kept open and retargeted to the remaining honest obligation: the exact CMP116
eligible-bond carrier/orientation statement needed to eliminate the live
`hPcarrier` containment hypothesis.  This commit does not claim full Eq.
(2.31) source closure and does not discharge Eq. (2.29), pointwise P residual
majorization, target constant comparison, post-`P`, activity, termwise,
Gaussian/root/Hessian/local-activity, H#, flow, or IR obligations.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake build +YangMills.RG.BalabanCMP116Eq231:olean
lake build +YangMills.RG.BalabanCMP116Lemma3ResidualStages:olean
lake build +YangMills.RG.BalabanCMP116Lemma3ScaleFamily:olean
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_citations.py lean CMP116Eq231PBondBoundary.of_sourceBondSets
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers
python scripts\source_citations.py lean CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourceBondSets
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-source-bondsets.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Eq231.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
```

Results: focused Lean/module builds passed; `lake build YangMillsCore` passed
8363 jobs; `oracle_check.lean` completed and wrote
`runtime\oracle-source-bondsets.log`; `git diff --check`,
`git diff --cached --check`, `check_consistency.py`, citation validation/local
checks, and the no-sorry/no-admit/no-axiom scan passed.  The builds reported
pre-existing lint warnings in unrelated modules.

Honest scope: this is a genuine narrowing of one Eq. (2.31) source-facing
interface, not an analytic-source proof.  Clay distance **~0% (<0.1%)**,
unchanged.

## Addendum 397 (2026-06-25, **CMP116 Eq. (2.37) post-P majorization consumer**)

Files touched:
`YangMills/RG/BalabanCMP116Eq237.lean`, `YangMillsCore.lean`,
`oracle_check.lean`, `docs/source-citations/cmp116-lemma3.json`,
`docs/SOURCE-CITATIONS.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`CURRENT-STATE.md`, and this ledger.

This checkpoint adds the source-shaped Eq. (2.37) majorization boundary for the
post-`P` stage:

- `CMP116Eq237MajorizationBoundary` records the seven-delta source decay, a
  residual-exponent absorption budget, nonnegativity of the post-`P`
  amplitude, and the displayed `C3*epsilon1` amplitude comparison.
- `cmp116Eq237_residualExponent_absorbed` proves that the residual budget
  absorbs the page-20 weight into the canonical Lemma-3
  `(1 - 8*delta)/2` decay.
- `cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237` derives the
  existing `CMP116PostPResidualSourceMajorizationScaleFamily` consumer.
- `CMP116Lemma3WeightedPostPSourceScaleBoundary.of_sourceBound_eq237Majorization`
  builds the weighted post-`P` boundary from the combined post-`P` source
  bound plus the Eq. (2.37) majorization boundary, removing the independent
  caller-supplied `postP_majorization` field on this route.

The citation catalog now links the visually confirmed Eq. (2.37) and C3/alpha5
source entries to these Lean declarations.  The source-boundary audit notes
that this does not prove the combined post-`P` source sum, the `Z0/Z0'`
source-to-Lean dictionary, finite-family reindexing, or numerical/O(1)
constant majorants.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq237.lean
lake build +YangMills.RG.BalabanCMP116Eq237:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean CMP116Eq237MajorizationBoundary
python scripts\source_citations.py show cmp116.eq237.post-p-resummation
python scripts\source_citations.py blockers
python scripts\source_citations.py check-local
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq237-majorization.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Eq237.lean
```

Results: the focused Lean check and module build passed; `lake build
YangMillsCore` passed 8364 jobs; `oracle_check.lean` completed and wrote
`runtime\oracle-eq237-majorization.log`, including the new Eq. (2.37)
declarations.  Citation validation, citation local-artifact checks,
`git diff --check`, `git diff --cached --check`, `check_consistency.py`, and
the no-sorry/no-admit/no-axiom scan passed.  The builds reported pre-existing
lint warnings in unrelated modules.

Honest scope: this is a real removal of one downstream post-`P` majorization
hypothesis when the Eq. (2.37) majorization boundary is supplied.  It is not a
proof of Eq. (2.29), a construction of Eq. (2.31) source families, a proof of
the combined post-`P` source estimate, or a continuum/Clay result.  Clay
distance **~0% (<0.1%)**, unchanged.

## Addendum 398 (2026-06-25, **Eq. (2.31) filtered P-family scale boundary**)

Files touched:
`YangMills/RG/BalabanCMP116Lemma3ScaleFamily.lean`, `oracle_check.lean`,
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `CURRENT-STATE.md`, and this ledger.

This checkpoint exposes the filtered-powerset Eq. (2.31) route at the
scale-family boundary:

- `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets` builds the
  P-stage source boundary when the resummation record's `PIndex` is explicitly
  equal to `cmp116Eq231SourcePIndex gapCubes admissible`.
- In that presentation, the per-`P` carrier-containment premise is removed:
  containment follows from powerset membership via the already checked
  `cmp116PStageSourceBound_of_eq231_filteredBondSets`.
- The route still requires pointwise P-weight control, the source bracket,
  geometry comparison, target comparison, scalar smallness, and nonnegativity
  explicitly.

The citation catalog now records this scale-level consumer under
`cmp116.eq231.p-family-carrier-source-target`.  The source claim audit keeps the
remaining dictionary obligation explicit: this does not prove Balaban's source
`P` family is the filtered Lean family; it only removes `hPcarrier` once that
`PIndex` equality is supplied.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build +YangMills.RG.BalabanCMP116Lemma3ScaleFamily:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean CMP116Lemma3PStageSourceScaleBoundary.of_eq231_filteredBondSets
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-filtered-bondsets.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
```

Results: focused Lean and module builds passed; `lake build YangMillsCore`
passed 8364 jobs; `oracle_check.lean` completed and wrote
`runtime\oracle-eq231-filtered-bondsets.log`, including both the
`of_eq231_sourceBondSets` and `of_eq231_filteredBondSets` scale constructors.
Citation validation/local checks, `git diff --check`,
`git diff --cached --check`, `check_consistency.py`, and the
no-sorry/no-admit/no-axiom scan passed.  The builds reported pre-existing lint
warnings in unrelated modules.

Honest scope: this removes a live carrier-containment premise only for callers
that already present `PIndex` as the filtered powerset carrier.  It is not a
source proof of that presentation, not Eq. (2.29), not the pointwise P residual
estimate, not post-`P`, and not a continuum/Clay result.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 399 (2026-06-25, **Eq. (2.31) filtered P-family downstream consumers**)

Files touched:
`YangMills/RG/BalabanCMP116Lemma3ScaleFamily.lean`, `oracle_check.lean`,
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `CURRENT-STATE.md`, and this ledger.

This checkpoint propagates the already verified filtered-powerset Eq. (2.31)
route from the P-stage scale boundary into the weighted post-`P` source package
and direct Lemma-3 estimate consumers:

- `CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_filteredBondSets`
  composes Eq. (2.29), the filtered Eq. (2.31) P-stage route, the weighted
  post-`P` boundary, and the activity/termwise boundary.
- `CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_filteredBondSets`
  is the direct Lemma-3 scale-family estimate consumer for the same route.
- Both constructors remove the abstract `CMP116Eq231PBondBoundary` input from
  this downstream package when `R.PIndex` is identified with
  `cmp116Eq231SourcePIndex gapCubes admissible`.

Source audit during this checkpoint re-read CMP116 printed pages 18-19.  The
visible material confirms that `P` is a finite bond set and records the lower
bound `|P| >= (1/2)*M^-4*|Z0 \ Y0|`, but it does not yet provide the precise
eligible oriented-bond carrier theorem, orientation convention, or carrier
upper bound needed to prove the full roadmap item A source dictionary.  A
runtime source request records that gap.

Verification commands for this checkpoint:

```
lake build +YangMills.RG.BalabanCMP116Lemma3ScaleFamily:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_filteredBondSets
python scripts\source_citations.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_filteredBondSets
python scripts\source_citations.py blockers
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-filtered-package.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
```

Honest scope: this is a downstream formal-composition improvement.  It does
not prove the source-native filtered `PIndex` dictionary, the pointwise
P-residual estimate, Eq. (2.29), Eq. (2.37), or any continuum/Clay result.
Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 400 (2026-06-25, **Eq. (2.37) weighted package consumer**)

Files touched:
`YangMills/RG/BalabanCMP116Eq237.lean`, `oracle_check.lean`,
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `CURRENT-STATE.md`, and this ledger.

This checkpoint propagates the Eq. (2.37) post-`P` majorization boundary into
the weighted post-`P` package and direct Lemma-3 estimate:

- `CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237Majorization`
  builds the weighted package from Eq. (2.29), a supplied P-stage source
  boundary, the combined `CMP116PostPResidualSourceBound`, an
  `CMP116Eq237MajorizationBoundary`, and the activity/termwise boundary.
- `CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237Majorization`
  is the corresponding direct scale-family Lemma-3 estimate.
- The live independent `postP_majorization` obligation is theorem-generated by
  `cmp116PostPResidualSourceMajorizationScaleFamily_of_eq237`; the combined
  post-`P` source sum remains explicit.

Verification commands for this checkpoint:

```
lake build +YangMills.RG.BalabanCMP116Eq237:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237Majorization
python scripts\source_citations.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237Majorization
python scripts\source_citations.py blockers
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq237-weighted-package.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Eq237.lean
```

Honest scope: this removes only the separate post-`P` majorization premise once
the Eq. (2.37) boundary is supplied.  It does not prove the combined post-`P`
source bound, Eq. (2.29), the P-stage source boundary, the source-to-Lean
`Z0/Z0'` dictionary, activity/termwise estimates, or any continuum/Clay result.
Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 401 (2026-06-25, **Eq. (2.37) combined post-P source bound consumer**)

Files touched:
`YangMills/RG/BalabanCMP116Eq237.lean`, `oracle_check.lean`,
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `CURRENT-STATE.md`, and this ledger.

This checkpoint theorem-generates the combined post-`P` source-bound consumer
from fixed-`Z0'` Eq. (2.37)-shaped premises:

- `cmp116Eq237Z0PrimeIndex` and `cmp116Eq237Z0Fiber` name the finite
  fixed-`Z0'` reindexing of the repository's dependent `Z0 -> Z0'` stage.
- `cmp116Eq237_nested_sum_eq_fiber_sum` proves the finite transposition.
- `cmp116Eq237Amplitude` and `cmp116Eq237FixedZ0PrimeWeight` name the
  source-shaped Eq. (2.37) amplitude and fixed-`Z0'` majorant while keeping
  `C237`, `Calpha5`, source cardinality, gap cardinality, components, and
  component metric explicit.
- `cmp116PostPResidualSourceBound_of_eq237` derives
  `CMP116PostPResidualSourceBound` from the fixed-`Z0'` estimate, inclusion
  into the canonical source `Z0'` family, and the post-(2.37) final summation.
- `CMP116Lemma3WeightedPostPSourceScaleBoundary.of_eq237`,
  `CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237`, and
  `CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237`
  remove the caller-supplied combined post-`P` source-bound field on the
  Eq. (2.37) route.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq237.lean
lake build +YangMills.RG.BalabanCMP116Eq237:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean cmp116PostPResidualSourceBound_of_eq237
python scripts\source_citations.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq237
python scripts\source_citations.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq237
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq237-source-bound.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Eq237.lean
```

Results: focused Lean and module builds passed; `lake build YangMillsCore`
passed 8364 jobs; `oracle_check.lean` completed and wrote
`runtime\oracle-eq237-source-bound.log`, where the new Eq. (2.37) reindexing,
source-bound theorem, and constructors print only the usual
`[propext, Classical.choice, Quot.sound]` envelope.  Citation validation,
target lookup, local artifact checks, `git diff --check`,
`check_consistency.py`, and the no-sorry/no-admit/no-axiom scan passed.  The
blocker report still lists the pre-existing CMP116 termwise-window OCR issue,
Cammarota CMP85 extraction, and Eq. (2.31) P-family carrier dictionary.
Build warnings were pre-existing lints outside this checkpoint.

Honest scope: this is finite algebra plus a quantitative-constant consumer for
already factored fixed-`Z0'` Eq. (2.37) premises.  It does not prove the
fixed-`Z0'` source estimate, the post-(2.37) final source summation, the
source-to-Lean `D/P/Z0/Z0'` dictionaries, Eq. (2.29), the P-stage source
boundary, activity/termwise estimates, any source `O(1)` constant hierarchy, or
any continuum/Clay result.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 402 (2026-06-25, **Eq. (2.31) filtered P-index membership bridge**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`, `oracle_check.lean`,
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `CURRENT-STATE.md`, and this ledger.

This checkpoint adds the finite extensionality bridge requested by the Eq.
(2.31) P-family source audit:

- `cmp116Eq231SourcePIndex_mem_iff` states membership in the Lean filtered
  source family exactly as carrier containment plus the declared admissibility
  predicate.
- `cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff` proves that a
  pointwise membership iff for an arbitrary `PIndex` is enough to identify it
  with `cmp116Eq231SourcePIndex gapCubes admissible`.
- The source-pending citation `cmp116.eq231.p-family-carrier-source-target` is
  retargeted from a generic carrier request to the exact missing membership
  theorem: a primary-source iff for Balaban's `(P)` family, including bond
  orientation, eligible carrier, and admissibility.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean cmp116Eq231SourcePIndex_mem_iff
python scripts\source_citations.py lean cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-pindex-membership.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Eq231.lean
```

Results: focused Lean and module builds passed; `lake build YangMillsCore`
passed 8364 jobs; `oracle_check.lean` completed and wrote
`runtime\oracle-eq231-pindex-membership.log`, where the new filtered-family
membership and extensionality theorems print only the usual
`[propext, Classical.choice, Quot.sound]` envelope.  Citation validation,
target lookup, local artifact checks, blocker reporting, `git diff --check`,
`check_consistency.py`, and the no-sorry/no-admit/no-axiom scan passed.  The
blocker report now lists the Eq. (2.31) P-family membership/carrier dictionary
as the exact source-pending target.  Build warnings were pre-existing lints
outside this checkpoint.

Honest scope: this removes only a finite extensionality burden once a source
membership iff is supplied.  It does not prove Balaban's `(P)` family is the
filtered Lean family, does not prove the eligible-bond carrier/orientation
dictionary, does not prove Eq. (2.29), pointwise P residual majorization,
post-`P`, activity/termwise estimates, or any continuum/Clay result.  Clay
distance **~0% (<0.1%)**, unchanged.

## Addendum 403 (2026-06-25, **citation local-excerpt CLI and Eq. (2.31) P source window**)

Files touched:
`scripts/source_citations.py`, `README.md`, `docs/SOURCE-CITATIONS.md`,
`docs/BALABAN-SOURCE-BOUNDS.md`, `docs/source-citations/cmp116-lemma3.json`,
`docs/SOURCE-CLAIM-AUDIT.md`, `CURRENT-STATE.md`, and this ledger.

This checkpoint reduces repeated OCR/context churn in the source workflow:

- `python scripts\source_citations.py excerpt <key>` prints the line-numbered
  local source text referenced by `locator.local_text`.
- `excerpt` supports multiple local text ranges for one citation key, so one
  source target can show both a definition window and a later estimate window.
- stdout is configured as UTF-8 with replacement, preventing Windows console
  failures on OCR characters outside the active code page.
- `cmp116.eq231.p-family-carrier-source-target` now points to two local windows:
  CMP116 full-text lines 467-475 for the initial `P` decomposition around Eq.
  (2.3), and `cmp116-pages-15-20.txt` lines 194-214 for the Eq. (2.31) use.

The newly recorded OCR candidate says that for fixed `Y0` the source defines a
set of bonds, decomposes `chi_k` by a sum over `P`, takes `Z0` as the smallest
localization domain containing `Y0` and `P`, and requires bonds of `P` to lie in
the interior of `Z0`.  It still does not theorem-feed the exact Lean
membership iff, positive-direction encoding, or four-direction carrier count.

Verification commands for this checkpoint:

```
python -m py_compile scripts\source_citations.py
python scripts\source_citations.py --help
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_citations.py excerpt cmp116.eq231.p-family-carrier-source-target -C 1
python scripts\source_citations.py validate
python scripts\source_citations.py check-local
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-citation-excerpt.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md README.md docs\SOURCE-CITATIONS.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json scripts\source_citations.py
```

Results: Python compilation and citation CLI checks passed; `show` and
`excerpt` resolved the updated multi-window Eq. (2.31) source target; citation
validation and local artifact checks passed; `lake build YangMillsCore` passed
at 8364 jobs; `oracle_check.lean` completed and wrote
`runtime\oracle-citation-excerpt.log`; diff, consistency, and no-forbidden-token
checks passed.

Honest scope: this is source-work tooling and a sharper citation target.  It
does not close the Eq. (2.31) source theorem, Eq. (2.29), post-`P`,
activity/termwise estimates, continuum construction, or Clay mass gap.  Clay
distance **~0% (<0.1%)**, unchanged.

## Addendum 404 (2026-06-26, **CMP109 oriented-bond citation target for Eq. (2.31)**)

Files touched:
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/BALABAN-SOURCE-BOUNDS.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`CURRENT-STATE.md`, and this ledger.

This checkpoint records the reusable CMP109 source windows needed by the
CMP116 Eq. (2.31) P-family carrier task:

- `cmp109.bond-convention.positive-oriented` points to CMP109 local text around
  printed pages 251, 262, and 269.
- The extracted windows say that a continuous-space subset determines
  nearest-neighbor bonds, that a bond is written with endpoints `(b_-, b_+)`,
  and that later formulas restrict the displayed bonds to positive
  orientation.
- The Eq. (2.31) source request is now narrower: prove the bridge from those
  general CMP109 bond conventions to CMP116's fixed-`(Z0,Y0)` eligible
  P-carrier, carrier count, and pointwise membership iff.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp109.bond-convention.positive-oriented
python scripts\source_citations.py excerpt cmp109.bond-convention.positive-oriented -C 1
python scripts\source_citations.py lean cmp116Eq231SourcePIndex_mem_iff
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers --status source_pending
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp109-bond-convention-citation.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Results: citation validation, target lookup, excerpt printing, local artifact
checks, blocker reporting, full Lean build, oracle check, diff checks,
consistency check, and no-forbidden-token scan passed.

Honest scope: this is a source-navigation checkpoint.  It does not prove the
CMP116 Eq. (2.31) source dictionary, does not prove the carrier bound
`|Carrier(Z0,Y0)| <= 4*|Z0 \ Y0|`, and does not discharge Eq. (2.29),
post-`P`, activity/termwise, continuum, or Clay obligations.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 405 (2026-06-26, **CMP116 page-12 P-carrier formula and CMP109 b0(c) corridor**)

Files touched:
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/BALABAN-SOURCE-BOUNDS.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`CURRENT-STATE.md`, and this ledger.

This checkpoint tightens the source-citation system around the remaining
Eq. (2.31) P-family dictionary blocker:

- `cmp116.eq231.p-family-carrier-source-target` now records the visually
  checked page-12 formula: `Y0^{c,*}` is the set of `T(k)` bonds contained in
  `Y0^c` after excluding the special `b0(c)` bonds, and Eq. (2.3) sums over
  `P` subsets of that set.
- `cmp109.b0-corridor-bond` is a new visually confirmed source key for CMP109
  printed page 267 / PDF page 19.  It records the definition of `b0(c)` as the
  `T(k)` bond contained in `c` and lying in the endpoint-block corridor `B(c)`.
- The audit docs now state that the notation/OCR ambiguity is resolved, while
  the fixed-`(Z0,Y0)` eligible carrier, source membership iff, and
  `4*|Z0 \ Y0|` carrier count remain open.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_citations.py excerpt cmp116.eq231.p-family-carrier-source-target -C 1
python scripts\source_citations.py show cmp109.b0-corridor-bond
python scripts\source_citations.py excerpt cmp109.b0-corridor-bond -C 1
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers --status source_pending
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp109-b0-corridor-citation.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Results: citation validation, target lookup, excerpt printing, local artifact
checks, blocker reporting, full Lean build, oracle check, diff checks,
consistency check, and no-forbidden-token scan passed.  The full build reused
the existing cache and reported only pre-existing linter warnings.

Honest scope: this is a citation and source-navigation checkpoint.  It does
not prove the CMP116 Eq. (2.31) source dictionary, does not prove the carrier
bound, and does not discharge Eq. (2.29), post-`P`, activity/termwise,
continuum, or Clay obligations.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 406 (2026-06-26, **CMP116 Eq. (2.37) companion geometry citations**)

Files touched:
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/BALABAN-SOURCE-BOUNDS.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`CURRENT-STATE.md`, and this ledger.

This checkpoint follows the Eq. (2.37) payoff-first recommendation without
claiming a theorem that the source dictionaries do not yet support:

- Added `cmp116.eq232.z0-gap-distance-geometric` for the page-18 geometric
  inequality used before Eq. (2.33) and adapted after Eq. (2.37).
- Added `cmp116.eq234.y0-subset-summation` for the page-19 finite summation
  over `Y0 subset Z0`, whose analogue is cited in the final post-(2.37)
  `Z \ Z0'` summation.
- Added `cmp116.eq236.scale-transfer-geometric` for the page-19
  scale-transfer comparison `2*d_k(Z_i) >= L*d_{k+1}(Z_i')`, used in the
  fixed-`Z0'` component estimate.
- Updated the source docs to state that these entries are anchors for future
  proofs of `heq237_fixed` and `hpost_eq237`, not a discharge of those
  hypotheses.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_citations.py show cmp116.eq232.z0-gap-distance-geometric
python scripts\source_citations.py excerpt cmp116.eq232.z0-gap-distance-geometric -C 1
python scripts\source_citations.py show cmp116.eq234.y0-subset-summation
python scripts\source_citations.py excerpt cmp116.eq234.y0-subset-summation -C 1
python scripts\source_citations.py show cmp116.eq236.scale-transfer-geometric
python scripts\source_citations.py excerpt cmp116.eq236.scale-transfer-geometric -C 1
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers --status source_pending
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-eq237-companion-citations.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json
```

Results: citation validation, target lookup, excerpt printing, local artifact
checks, blocker reporting, full Lean build, oracle check, diff checks,
consistency check, and no-forbidden-token scan passed.  The full build reused
the existing cache and reported only pre-existing linter warnings.

Honest scope: this is a source-citation checkpoint.  It does not prove the
fixed-`Z0'` Eq. (2.37) source estimate, the final post-(2.37) summation, the
`Z0/Z0'` source-to-Lean dictionary, Eq. (2.29), Eq. (2.31), or any
activity/termwise/continuum obligation.  Clay distance **~0% (<0.1%)**,
unchanged.

## Addendum 407 (2026-06-26, **CMP116 Eq. (2.37) repository global `Z0'` index**)

Files touched:
`YangMills/RG/BalabanCMP116Eq237.lean`,
`docs/source-citations/cmp116-lemma3.json`, `docs/SOURCE-CITATIONS.md`,
`docs/BALABAN-SOURCE-BOUNDS.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`CURRENT-STATE.md`, and this ledger.

This checkpoint closes a finite bookkeeping gap on the repository side of the
Eq. (2.37) route:

- Added `cmp116Eq237GlobalZ0PrimeIndex`, the finite fixed-`Z` union of the
  repository's fixed `(D,P)` `Z0'` families.
- Proved `cmp116Eq237Z0PrimeIndex_subset_global`, the inclusion of every fixed
  `(D,P)` family into that global union.
- Added `cmp116PostPResidualSourceBound_of_eq237_globalIndex`, a specialization
  of the combined post-`P` source-bound consumer that removes the finite
  `hindex` argument when the final post-(2.37) sum is stated over the explicit
  repository global union.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq237.lean
lake build +YangMills.RG.BalabanCMP116Eq237:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean cmp116Eq237GlobalZ0PrimeIndex
python scripts\source_citations.py lean cmp116Eq237Z0PrimeIndex_subset_global
python scripts\source_citations.py lean cmp116PostPResidualSourceBound_of_eq237_globalIndex
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-cmp116-eq237-global-index.log
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json YangMills\RG\BalabanCMP116Eq237.lean
```

Results: focused Lean, target build, citation validation, Lean-target citation
lookups, full `YangMillsCore` build, oracle check, diff checks, consistency
check, and no-forbidden-token scan passed.  The Lean builds reported only
pre-existing linter warnings.  The oracle log contains only the permitted
`[propext, Classical.choice, Quot.sound]` dependency reports and exited
successfully.

Honest scope: this is a repository-index theorem and consumer specialization.
It does not prove the fixed-`Z0'` Eq. (2.37) source estimate, the final
post-(2.37) summation, or the source dictionary identifying Balaban's `Z0'`
summation family with the repository global union.  Eq. (2.29), Eq. (2.31),
activity/termwise, continuum, and Clay obligations remain open.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 408 (2026-06-26, **source database overlay and packet manifest**)

Files touched:
`.gitignore`, `AGENT_BUILDER_PROMPT.md`, `SOURCE_DB_INSTALL.md`,
`CURRENT-STATE.md`, `docs/source-db/**`, `scripts/source_db.py`,
`tests/test_source_db.py`, `source-packets/README.md`,
`source-packets/private/.gitkeep`, `source-packets/manifests/source-artifact-manifest.json`,
and this ledger.

This checkpoint installs the source-database overlay prepared outside the repo:

- `scripts/source_db.py` builds and queries a generated SQLite index from the
  existing `docs/source-citations/*.json` catalogs plus the new
  `docs/source-db/catalogs/*.json` source-spine backlog.
- `docs/source-db/` records the schema, templates, query examples, coverage
  queue, and generated `source_index.sqlite`.
- `source-packets/manifests/source-artifact-manifest.json` records local
  artifact availability and SHA-256 hashes; raw PDFs/OCR/renders and packet
  ZIPs stay out of public Git through `.gitignore`.
- The CLI was hardened for Windows by forcing UTF-8/replacement output for
  `stdout`/`stderr` and by giving SQLite builds unique temporary files, avoiding
  the observed `UnicodeEncodeError` and `.tmp` collision during concurrent
  commands.

Verification commands for this checkpoint:

```
Get-FileHash -Algorithm SHA256 C:\Users\lluis\Desktop\Karol\THE-ERIKSSON-source-db-starter-2026-06-26.zip
Get-FileHash -Algorithm SHA256 C:\Users\lluis\Desktop\Karol\THE-ERIKSSON-source-packet-metadata-2026-06-26.zip
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py coverage
python scripts\source_db.py blockers
python scripts\source_db.py search "Eq. (2.31)"
python scripts\source_db.py show cmp116.eq231.p-bond-sum
python scripts\source_db.py lean CMP116Eq231PBondBoundary
python scripts\source_db.py verify --check-local
python -m pytest tests\test_source_db.py -q
python scripts\source_db.py packet --output source-packets\out\source-packet-metadata.zip
python scripts\source_citations.py validate
python scripts\source_citations.py check-local
python scripts\source_citations.py blockers --status source_pending
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs/SOURCE-CITATIONS.md docs/BALABAN-SOURCE-BOUNDS.md docs/SOURCE-CLAIM-AUDIT.md docs/VERIFICATION-LEDGER.md docs/source-citations docs/source-db scripts/source_db.py AGENT_BUILDER_PROMPT.md SOURCE_DB_INSTALL.md source-packets/README.md source-packets/manifests/source-artifact-manifest.json
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-source-db-install.log
```

Results:
- Input ZIP SHA-256 values matched the supplied checksum file:
  `decce94c91f6cd6c4bbb518f127c067205036e5d70c814540f2303c0db29e2f4`
  for the starter ZIP and
  `2c118872b5e59d3b0289e59c2d30a8161a6a0651c0638c6a2383ed4692fb586c`
  for the metadata ZIP.
- `source_db.py verify/build/stats/coverage/blockers/search/show/lean` passed.
  The built database reports 11 sources, 24 citations, 53 claims, 120 Lean
  target links, 60 open questions, 19 artifact records, and 7 coverage records.
- `source_db.py verify --check-local` passed against
  `C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\sources\primary`.
- `python -m pytest tests\test_source_db.py -q` passed: 3 tests.
- `source-packets\out\source-packet-metadata.zip` was generated but remains
  ignored; SHA-256:
  `0984216e41f5efcf63569195613743d47709475e9e1b017a81bc07edafa20e30`.
- Legacy citation validation/check-local/blocker reporting passed.
- `git diff --check`, `python scripts\check_consistency.py`, and the
  forbidden-token scan passed.
- `lake build YangMillsCore` passed, 8364 jobs, with only pre-existing linter
  warnings.
- `oracle_check.lean` passed; the log contains only permitted
  `[propext, Classical.choice, Quot.sound]` dependency reports.

Honest scope: this is source-database infrastructure.  It does not extract a
new theorem, remove a Lean source hypothesis, or advance continuum/Clay
obligations.  It reduces future OCR/source-search cost and makes source
coverage/blockers queryable through a generated SQLite index.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 409 (2026-06-26, **CMP116 Eq. (2.37) source-index membership interface**)

Files touched:
`YangMills/RG/BalabanCMP116Eq237.lean`, `CURRENT-STATE.md`,
`docs/source-citations/cmp116-lemma3.json`,
`docs/source-db/examples/cmp116-current-seed.json`,
`docs/source-db/source_index.sqlite`, and this ledger.

This checkpoint narrows the remaining post-(2.37) dictionary obligation without
asserting any new source semantics:

- `cmp116Eq237GlobalZ0PrimeIndex_mem_iff` characterizes membership in the
  repository's fixed-`Z` global `Z0'` union as membership in one fixed `(D,P)`
  branch.
- `cmp116Eq237SourceZ0PrimeIndex_eq_global_of_mem_iff` turns a future
  pointwise membership characterization of Balaban's final source `Z0'` family
  into equality with the repository global union.
- `cmp116PostPResidualSourceBound_of_eq237_sourceIndexMemIff` derives the
  combined post-`P` source-bound consumer from a source index, a pointwise iff
  with the repository global union, the fixed-`Z0'` Eq. (2.37) estimate, and
  the final post-(2.37) source summation.  The arbitrary finite inclusion
  `hindex` is no longer a separate input in this route.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq237.lean
python scripts\source_db.py verify
python scripts\source_citations.py validate
python scripts\source_db.py build
python scripts\source_db.py lean cmp116Eq237GlobalZ0PrimeIndex_mem_iff
python scripts\source_db.py lean cmp116Eq237SourceZ0PrimeIndex_eq_global_of_mem_iff
python scripts\source_db.py lean cmp116PostPResidualSourceBound_of_eq237_sourceIndexMemIff
lake build +YangMills.RG.BalabanCMP116Eq237:olean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CITATIONS.md docs\BALABAN-SOURCE-BOUNDS.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json docs\source-db YangMills\RG\BalabanCMP116Eq237.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq237-source-index-memiff.log
```

Results: the focused Lean check, source-db/catalog validation, rebuilt SQLite
index, target lookups, focused olean build, diff check, consistency check,
forbidden-token scan, full `YangMillsCore` build, and oracle check passed.  The
rebuilt source database hash is
`667e976a315e496d2fe094aecb395394d224f6fd697d6246bbdf36342af3e211`.  Lean
builds reported only pre-existing linter warnings, and the oracle log contains
only permitted `[propext, Classical.choice, Quot.sound]` dependency reports.

Honest scope: this is a finite index/dictionary interface.  It does not prove
the fixed-`Z0'` Eq. (2.37) estimate, the final post-(2.37) source summation, or
the source theorem that Balaban's `Z0'` family has this membership
characterization.  Eq. (2.29), Eq. (2.31), activity/termwise, continuum, and
Clay obligations remain open.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 410 (2026-06-26, **Dimock RG source-citation Batch 001 ingestion**)

Files touched:
`CURRENT-STATE.md`, `docs/source-db/COVERAGE.md`,
`docs/source-db/EXTRACTION-BATCHES.md`,
`docs/source-db/catalogs/dimock-rg-i-iii-extracted.json`,
`docs/source-db/catalogs/spine-backlog.json`,
`docs/source-db/manifests/batch-001-dimock-rg-i-iii.json`,
`docs/source-db/reports/BATCH-001-CITATION-INDEX.md`,
`docs/source-db/reports/BATCH-001-DIMOCK-RG.md`,
`docs/source-db/reports/NEXT-SCAN-QUEUE.md`,
`docs/source-db/reports/batch-001-citation-index.csv`,
`docs/source-db/source_index.sqlite`,
`source-packets/manifests/batch-001-dimock-rg-i-iii.json`, and this ledger.

This checkpoint ingests
`C:\Users\lluis\Desktop\Karol\THE-ERIKSSON-source-citations-batch-001-2026-06-26.zip`
as public source metadata for Dimock I-III.  The ZIP SHA-256 matched the
provided Batch 001 note:
`14f5d50c799c442509d81bbbd416a633cdad6ae549e51d2fb842d21345f2eefb`.

The install was intentionally selective:

- The package `scripts/source_db.py` was not copied because the repository
  already contains the newer Windows-safe UTF-8 output and unique temporary
  SQLite build-file fixes.
- The package `.gitignore` was not copied because it was older than the
  repository ignore policy.
- The package `docs/source-db/examples/cmp116-current-seed.json` was not copied
  because it predates the Eq. (2.37) source-index membership targets from
  Addendum 409.
- The Dimock catalogs, source-spine enrichment, Batch 001 reports, coverage
  update, manifests, and rebuilt SQLite index were copied/rebuilt.

The rebuilt repository database is cumulative rather than ZIP-local.  It
therefore includes the pre-existing CMP116/CMP109/CMP119/CMP122/Cammarota
catalog material and preserved Eq. (2.37) Lean targets in addition to the new
Batch 001 Dimock records.  The combined post-build stats are:
13 sources, 42 citations, 119 claims/formulas, 178 Lean target links,
85 open questions, 39 artifact records, and 9 coverage records.  Status counts:
`located`: 2, `ocr_corrupted`: 1, `source_extracted`: 18,
`source_pending`: 7, `visual_confirmed`: 14.  The rebuilt
`docs/source-db/source_index.sqlite` SHA-256 is
`dc14c73a258ffa0be81acb6549a2f220f17a67de75ba3196e8f144376f20b67e`.

Verification commands for this checkpoint:

```
Get-FileHash -Algorithm SHA256 C:\Users\lluis\Desktop\Karol\THE-ERIKSSON-source-citations-batch-001-2026-06-26.zip
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py coverage
python scripts\source_db.py search "Appendix F"
python scripts\source_db.py search "boundary removal"
python scripts\source_db.py show dimockii.appendix-f.cluster-with-holes
python scripts\source_db.py show dimockii.lemma3.19.boundary-removal.507-510
python scripts\source_db.py lean PhysicalLocalizedCovarianceRootCertificate
python -m pytest tests\test_source_db.py -q
python scripts\source_citations.py validate
python scripts\source_citations.py check-local
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\VERIFICATION-LEDGER.md docs\source-db source-packets\manifests\batch-001-dimock-rg-i-iii.json
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-source-citations-batch-001.log
```

Results: the ZIP hash check, source database verify/build/stats/coverage,
representative search/show/lean queries, source-db pytest suite, legacy citation
validation and local check, diff check, consistency check, forbidden-token scan,
full `YangMillsCore` build, and oracle check passed.  Lean builds reported only
pre-existing linter warnings, and the oracle log contains only permitted
`[propext, Classical.choice, Quot.sound]` dependency reports.

Honest scope: this is source lookup infrastructure and source metadata
curation.  It does not prove a new Lean theorem, remove a CMP116 source
hypothesis, or advance the continuum/Clay obligations.  It reduces future OCR
and source-search cost by putting Dimock I-III formulas, reports, manifests,
coverage status, and open questions directly in the repository.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 411 (2026-06-26, **CMP116 Eq. (2.31) source-membership consumers**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`,
`YangMills/RG/BalabanCMP116Lemma3ResidualStages.lean`,
`YangMills/RG/BalabanCMP116Lemma3ScaleFamily.lean`,
`CURRENT-STATE.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`docs/source-citations/cmp116-lemma3.json`,
`docs/source-db/examples/cmp116-current-seed.json`,
`docs/source-db/source_index.sqlite`, and this ledger.

This checkpoint adds theorem-facing consumers for the exact CMP116 Eq. (2.31)
source-membership iff:

```lean
P ∈ PIndex Z D ↔
  P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4)) ∧
    admissible Z D P = true
```

New names:

- `CMP116Eq231PBondBoundary.of_sourcePIndexMemIff`
- `cmp116PStageSourceBound_of_eq231_sourcePIndexMemIff`
- `CMP116Lemma3PStageSourceScaleBoundary.of_eq231_sourcePIndexMemIff`
- `CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_sourcePIndexMemIff`
- `CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_sourcePIndexMemIff`

Compared with the previous filtered-family route, downstream callers no longer
need to first provide either a separate carrier-containment theorem or an
auxiliary equality
`R.PIndex = cmp116Eq231SourcePIndex gapCubes admissible`.  The pointwise iff
itself supplies the containment used by the finite bond-subset boundary and is
also the intended exact future source theorem.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake env lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean
lake build +YangMills.RG.BalabanCMP116Lemma3ResidualStages:olean
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py lean CMP116Eq231PBondBoundary.of_sourcePIndexMemIff
python scripts\source_db.py lean cmp116PStageSourceBound_of_eq231_sourcePIndexMemIff
python scripts\source_db.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_sourcePIndexMemIff
python scripts\source_citations.py lean CMP116Eq231PBondBoundary.of_sourcePIndexMemIff
python scripts\source_citations.py lean CMP116Lemma3WeightedPostPScaleSourceAssumptions.of_eq231_sourcePIndexMemIff
lake build +YangMills.RG.BalabanCMP116Lemma3ScaleFamily:olean
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json docs\source-db YangMills\RG\BalabanCMP116Eq231.lean YangMills\RG\BalabanCMP116Lemma3ResidualStages.lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-source-membership-consumers.log
```

Results: the focused Lean checks, focused olean builds, citation validation,
source-db validation/rebuild/stats, new source-db and legacy citation target
lookups, diff check, consistency check, forbidden-token scan, full
`YangMillsCore` build, and oracle check passed.  The rebuilt source database
reports 13 sources, 42 citations, 119 claims/formulas, 189 Lean target links,
85 open questions, 39 artifact records, and 9 coverage records; its SHA-256 is
`5c3d3364bdfc59226a5def4e097bb967840ec3bc84aa99d485266b977b65dedc`.
Lean builds reported only pre-existing linter warnings, and the oracle log
contains only permitted `[propext, Classical.choice, Quot.sound]` dependency
reports.

Honest scope: this is a source-dictionary consumer interface.  It does not
prove the Eq. (2.31) source-membership iff from CMP116/CMP109, identify the
eligible carrier, prove the four-direction carrier count, prove the pointwise
P-residual estimate, prove Eq. (2.29), or discharge post-`P`, activity,
termwise, continuum, or Clay obligations.  Clay distance **~0% (<0.1%)**,
unchanged.

## Addendum 412 (2026-06-26, **CMP116 Eq. (2.31) raw-source membership consumer**)

Files touched:
`YangMills/RG/BalabanCMP116Lemma3ScaleFamily.lean`,
`CURRENT-STATE.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`docs/source-citations/cmp116-lemma3.json`,
`docs/source-db/examples/cmp116-current-seed.json`,
`docs/source-db/source_index.sqlite`, and this ledger.

This checkpoint adds the raw-source adapter
`rawSource_of_eq231_sourcePIndexMemIff`.  It composes the existing separated
Gaussian/root/Hessian/activity source facts with
`CMP116Lemma3WeightedPostPScaleSourceAssumptions.lemma3_activity_estimate_of_eq231_sourcePIndexMemIff`,
so raw-source callers can use the exact future Eq. (2.31) membership theorem

```lean
P ∈ PIndex Z D ↔
  P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4)) ∧
    admissible Z D P = true
```

without first packaging an abstract `CMP116Eq231PBondBoundary`.  The source
catalogs now map this new Lean target to
`cmp116.eq231.p-family-carrier-source-target` with status `source_pending`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build +YangMills.RG.BalabanCMP116Lemma3ScaleFamily:olean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py lean rawSource_of_eq231_sourcePIndexMemIff
python scripts\source_citations.py lean rawSource_of_eq231_sourcePIndexMemIff
python scripts\source_db.py stats
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json docs\source-db YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-rawsource-membership.log
```

Results: focused Lean, focused olean build, citation validation, source-db
validation/rebuild/target lookup/stats, diff check, consistency check,
forbidden-token scan, full `YangMillsCore` build, and oracle check passed.
The rebuilt source database reports 13 sources, 42 citations, 119
claims/formulas, 190 Lean target links, 85 open questions, 39 artifact records,
and 9 coverage records; its SHA-256 is
`398ad0bfb031d4f279c1fda1418410b16e03dd2cf697262ad1bb009c543b3e89`.
Lean builds reported only pre-existing linter warnings, and the oracle log
contains only permitted `[propext, Classical.choice, Quot.sound]` dependency
reports.

Honest scope: this is source-dictionary plumbing at the raw-source adapter
level.  It does not prove the Eq. (2.31) source-membership iff from
CMP116/CMP109, identify the eligible carrier, prove the four-direction carrier
count, prove the pointwise P-residual estimate, prove Eq. (2.29), or discharge
post-`P`, activity, termwise, continuum, or Clay obligations.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 413 (2026-06-26, **CMP116 Eq. (2.31) Balaban P-family source package**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`, `CURRENT-STATE.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `docs/source-citations/cmp116-lemma3.json`,
`docs/source-db/examples/cmp116-current-seed.json`,
`docs/source-db/source_index.sqlite`, and this ledger.

This checkpoint adds the source-side package
`CMP116Eq231BalabanPFamilySourcePackage`.  It is not another downstream
consumer.  The package keeps a transcribed source predicate
`sourceAdmissible` explicit and requires three source facts:

- `mem_iff_source`: Balaban's Eq. (2.31) `P` family is exactly the source
  admissible family.
- `source_subset_gapCarrier`: the CMP116/CMP109 orientation/carrier dictionary
  places source-admissible `P` inside `gapCubes × Fin 4`.
- `admissible_iff_source`: the Lean boolean `admissible` is equivalent to the
  source condition, including the page-12 `Y0^{c,*}`/`b0(c)`, interior,
  boundary-avoidance, and minimal-domain conventions.

The package derives:

- `cmp116Eq231_balabanPFamily_subset_gapCarrier`
- `cmp116Eq231_balabanPFamily_sourcePIndexMemIff`
- `cmp116Eq231_balabanPFamily_eq_sourceFilteredBondSets`

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py lean CMP116Eq231BalabanPFamilySourcePackage
python scripts\source_db.py lean cmp116Eq231_balabanPFamily_sourcePIndexMemIff
python scripts\source_citations.py lean cmp116Eq231_balabanPFamily_sourcePIndexMemIff
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json docs\source-db YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-source-package.log
```

Results: focused Lean, focused olean build, citation validation, source-db
validation/rebuild/stats/target lookup, diff check, consistency check,
forbidden-token scan, and full `YangMillsCore` build passed.  The rebuilt
source database reports 13 sources, 42 citations, 120 claims/formulas, 194
Lean target links, 85 open questions, 39 artifact records, and 9 coverage
records; its SHA-256 is
`ec3ab0c5536f8acbb65d42b725e84fe3d778794242519bb9faf651b8f2fe04b7`.
Lean builds reported only pre-existing linter warnings.  The oracle check
passed and wrote
`runtime\oracle-eq231-source-package.log`, containing only permitted
`[propext, Classical.choice, Quot.sound]` dependency reports.

Honest scope: this packages the source dictionary obligation without filling
it by a vacuous `admissible := true` convention.  It still does not prove the
CMP116/CMP109 source facts themselves, identify the eligible carrier, prove
the four-direction carrier count, prove the pointwise P-residual estimate,
prove Eq. (2.29), or discharge post-`P`, activity, termwise, continuum, or Clay
obligations.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 414 (2026-06-26, **CMP116 Eq. (2.31) repository carrier count named**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`, `CURRENT-STATE.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `docs/source-citations/cmp116-lemma3.json`,
`docs/source-db/examples/cmp116-current-seed.json`,
`docs/source-db/source_index.sqlite`, and this ledger.

This checkpoint separates the repository-side Eq. (2.31) carrier/count
calculation from the concrete `CMP116Eq231PBondBoundary.of_sourceBondSets`
constructor.  It adds:

- `cmp116Eq231GapCarrier`, naming `gapCubes Z D ×ˢ Finset.univ`;
- `cmp116Eq231GapMass`, naming `|gapCubes Z D| / localizationScale^4`;
- `cmp116Eq231GapCarrier_card`;
- `cmp116Eq231GapMass_nonneg`;
- `cmp116Eq231GapCarrier_card_eq_four_scale4_gapMass`;
- `cmp116Eq231GapCarrier_card_le_four_scale4_gapMass`.

The existing source-bond-set constructor now reuses these named facts instead
of carrying the four-direction product count as an internal local calculation.
The source catalogs map the new targets to
`cmp116.eq231.p-family-carrier-source-target` with status `source_pending`.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_citations.py validate
python scripts\source_citations.py lean cmp116Eq231GapCarrier_card_eq_four_scale4_gapMass
python scripts\source_citations.py lean cmp116Eq231GapCarrier_card_le_four_scale4_gapMass
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py lean cmp116Eq231GapCarrier_card_eq_four_scale4_gapMass
python scripts\source_db.py lean cmp116Eq231GapCarrier_card_le_four_scale4_gapMass
python scripts\source_db.py stats
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json docs\source-db YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-gapcarrier-count.log
```

Results: focused Lean, focused olean build, citation validation, source-db
validation/rebuild/stats/target lookup, diff check, consistency check,
forbidden-token scan, full `YangMillsCore` build, and oracle check passed.
The rebuilt source database reports 13 sources, 42 citations, 121
claims/formulas, 200 Lean target links, 85 open questions, 39 artifact records,
and 9 coverage records; its SHA-256 is
`dd0b5f45ff8f00fd2759b6d0834bd31cf9346ee4c0e6fdda4873ffc458b7a972`.
Lean builds reported only pre-existing linter warnings.  The oracle check
passed and wrote
`runtime\oracle-eq231-gapcarrier-count.log`, containing only permitted
`[propext, Classical.choice, Quot.sound]` dependency reports.

Honest scope: this proves the cardinality of the repository carrier once the
source has been represented as `gapCubes × Fin 4`.  It does **not** prove that
Balaban's eligible `P`-bond carrier is this repository carrier, does not prove
the CMP116/CMP109 source membership iff, and does not prove the pointwise
P-residual estimate, Eq. (2.29), Eq. (2.37), activity/termwise estimates,
Gaussian/root/Hessian/locality, continuum, or Clay obligations.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 419 (2026-06-26, **Batch 004 live-field index and v3 idea DB ingest**)

Files touched:
`BATCH_004_README.md`, `CURRENT-STATE.md`,
`docs/source-db/catalogs/eq231-source-package-live-fields.json`,
`docs/source-db/indices/EQ231-*.md`,
`docs/source-db/manifests/batch-004-eq231-source-package-live-fields.json`,
`docs/source-db/reports/BATCH-004-EQ231-SOURCE-PACKAGE-LIVE-FIELDS.md`,
`docs/source-db/source_index.sqlite`,
`source-packets/manifests/batch-004-eq231-source-package-live-fields.json`,
`docs/idea-db/ym-creative-expansion/*`, and this ledger.

This checkpoint installs the safe Batch 004 operational index and updates the
isolated creative idea database to v3.  Batch 004 adds the Eq. (2.31)
source-package live-field key
`proof.eq231.field.bond-fst-mem-gapCubes` and related field-discharge prompts.
The v3 idea packet adds post-integration hypothesis-removal cards, proof
sprints, Lean templates, and a no-new-consumers guard.  It remains under
`docs/idea-db`, outside `docs/source-db` and outside the Lean import graph.

Hashes checked:

```
THE-ERIKSSON-source-citations-batch-004-safe-patch-2026-06-26.zip
  258892cc0b9ce0fde008699c97ebe6272e0e7f0da11ac010655a35d7f9ab20c4
THE-ERIKSSON-source-citations-batch-004-preview-db-2026-06-26.zip
  0ebd2d76d6c26bf7a9273d0859b6d05df9fe569a5f7d52866e0bf72d1fadad1e
ym-creative-expansion-pack-v3-20260626.zip
  fcf052da1c350b5d34b174969bdb3c17724049d78488bd891826f4e9f811e2dd
```

The v3 query helper was locally patched to force UTF-8 stdout/stderr on
Windows; its installed manifest entry was updated accordingly.  Two generated
markdown files were stripped of trailing whitespace and their installed
manifest hashes were updated.  These changes are packaging/validation fixes,
not source evidence.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show proof.eq231.field.bond-fst-mem-gapCubes
python docs\idea-db\ym-creative-expansion\scripts\validate_pack.py
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --queue
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --search bond_fst
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --search gapCubes
python -m pytest tests\test_source_db.py
git diff --check
git diff --cached --check
python scripts\check_consistency.py
lake build +YangMills.RG.BalabanCMP116Eq231:olean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-batch004-v3-live-fields.log
```

Results: source-citation validation passed with 18 citations from 4 sources;
source-db validation/build/stats passed with 6 catalog files and rebuilt
SQLite hash
`a9c5a8faa39751b8eeab90eb23f0ff8e2f8cdc7044e9b3002af6e307e9c93d10`.
The rebuilt source database reports 14 sources, 70 citation/crosswalk/
proof-card records, 257 claim/formula/proof-obligation records, 295 Lean
target links, 164 open questions, 39 artifact records, and 9 coverage records.
The v3 idea pack validation passed with 45 formula cards indexed, and the
UTF-8 query helper now passes on Windows.  `pytest` passed: 3 tests.
Diff checks, consistency check, focused Eq. (2.31) olean build, full
`YangMillsCore` build, and oracle check passed.  The oracle log contains only
the permitted `[propext, Classical.choice, Quot.sound]` dependency reports.

Honest scope: no Eq. (2.31) source theorem was promoted.  Batch 004 explicitly
keeps `bond-fst-mem-gapCubes` as an operational `lean_linked` target with open
questions: whether CMP116 bases eligible bonds in `Z0 \ Y0`, whether CMP109
positive orientation maps tail/base cube to Lean's first coordinate, and which
boundary/interior clause excludes off-gap tails.  Therefore
`source_subset_gapCarrier`, `mem_iff_source`, `admissible_iff_source`,
Eq. (2.31) pointwise P-residual majorization, Eq. (2.29), Eq. (2.37),
activity/termwise estimates, Gaussian/root/Hessian/locality, continuum, and
Clay obligations remain open.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 415 (2026-06-26, **Batch 002 source/LLM indices installed**)

Files touched:
`CURRENT-STATE.md`, `docs/SOURCE-CLAIM-AUDIT.md`,
`docs/source-db/EXTRACTION-BATCHES.md`, `docs/source-db/QUERY_EXAMPLES.md`,
`docs/source-db/catalogs/llm-operational-crosswalk.json`,
`docs/source-db/indices/*`,
`docs/source-db/manifests/batch-002-llm-context-indices.json`,
`docs/source-db/reports/BATCH-002-LLM-CONTEXT-INDICES.md`,
`docs/source-db/source_index.sqlite`,
`docs/idea-db/ym-creative-expansion/*`, and this ledger.

This checkpoint installs the user-provided Batch 002 operational source-index
packet and stages the creative expansion pack as an isolated idea database.
The input artifact hashes were:

- `THE-ERIKSSON-source-citations-batch-002-2026-06-26.zip`:
  `e4ac52795e4b9585f09bd158e913e0f77b8a2304fb39edffc87cf4a0ad4da2aa`;
- `ym-creative-expansion-pack-20260626.zip`:
  `2e734450d5cfc704164836f3f082fd7da798e60cde6dcb771e3bd259be83ab2a`.

Only the Batch 002 overlay files were installed.  Older package copies of
`scripts/source_db.py`, `examples/cmp116-current-seed.json`, and the package
SQLite snapshot were not overwritten.  The source DB was rebuilt from the
current repository catalogs plus `llm-operational-crosswalk.json`.  The
installed Eq. (2.31) crosswalk was updated to the current frontier: the
repository carrier-count lemmas are already named, and the remaining live
source task is the membership iff plus source-carrier identification.

The creative expansion pack is intentionally under
`docs/idea-db/ym-creative-expansion/`, not under `docs/source-db` and not in
the Lean import graph.  Its query helper received a Windows UTF-8 stdout/stderr
guard so Greek symbols in the queue do not fail under a non-UTF-8 console.

Verification commands for this checkpoint:

```
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show crosswalk.eq231.p-family-source-dictionary-route
python scripts\source_db.py search "source carrier identification"
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --list-cards
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --search eq231
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --queue
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\source-db docs\idea-db
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-batch002-source-ingest.log
```

Results: source-db validation, rebuild, stats, crosswalk lookup, search,
creative-pack query commands, diff check, consistency check, forbidden-token
scan, full `YangMillsCore` build, and oracle check passed.  The rebuilt source
database reports 14 sources, 50 citation/crosswalk records, 154 claim/formula
records, 231 Lean target links, 104 open questions, 39 artifact records, and
9 coverage records; its SHA-256 is
`a91355c59aa3f068392261627a0534b7e2308ca549dc496fff4ccc339a52b5dd`.
Lean builds reported only pre-existing linter warnings.  The oracle check
passed and wrote `runtime\oracle-batch002-source-ingest.log`, containing only
permitted `[propext, Classical.choice, Quot.sound]` dependency reports.

Honest scope: this is a citation/operations ingest and auditability commit. It
does **not** add a new primary source theorem, prove the CMP116/CMP109 source
membership iff, identify Balaban's eligible carrier with the repository
carrier, prove Eq. (2.29), Eq. (2.37), activity/termwise estimates,
Gaussian/root/Hessian/locality, continuum, or Clay obligations.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 416 (2026-06-26, **Eq. (2.31) source-package boundary assembly**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`, `CURRENT-STATE.md`,
`docs/SOURCE-CLAIM-AUDIT.md`, `docs/source-citations/cmp116-lemma3.json`,
`docs/source-db/examples/cmp116-current-seed.json`,
`docs/source-db/catalogs/llm-operational-crosswalk.json`,
`docs/source-db/indices/LEAN-SOURCE-CROSSWALK.md`,
`docs/source-db/indices/LLM-FAST-CONTEXT.md`,
`docs/source-db/indices/lean-source-crosswalk.json`,
`docs/source-db/reports/BATCH-002-LLM-CONTEXT-INDICES.md`,
`docs/source-db/source_index.sqlite`, and this ledger.

This checkpoint adds
`CMP116Eq231PBondBoundary.of_balabanPFamilySourcePackage`, a direct
proof-assembly constructor from the existing non-hollow
`CMP116Eq231BalabanPFamilySourcePackage` to the immediate Eq. (2.31)
`CMP116Eq231PBondBoundary`.  It composes the already verified
`cmp116Eq231_balabanPFamily_sourcePIndexMemIff` route with
`CMP116Eq231PBondBoundary.of_sourcePIndexMemIff`, so callers that have the
explicit source package no longer need to manually pass the pointwise
membership iff to the boundary constructor.

The source catalogs and Batch 002 crosswalk were updated to expose the new Lean
target.  The target is still tied to the `source_pending`
`cmp116.eq231.p-family-carrier-source-target` citation and the operational
`crosswalk.eq231.p-family-source-dictionary-route`; it is not marked as source
verified.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py lean CMP116Eq231PBondBoundary.of_balabanPFamilySourcePackage
python scripts\source_citations.py lean CMP116Eq231PBondBoundary.of_balabanPFamilySourcePackage
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations\cmp116-lemma3.json docs\source-db YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-source-package-boundary.log
```

Results: focused Lean, focused olean build, citation validation, source-db
validation/rebuild/stats/target lookup, diff check, consistency check,
forbidden-token scan, full `YangMillsCore` build, and oracle check passed.
The rebuilt source database reports 14 sources, 50 citation/crosswalk records,
155 claim/formula records, 233 Lean target links, 104 open questions,
39 artifact records, and 9 coverage records; its SHA-256 is
`945117566c5fc0a83883afdb6ee469eb2d3936770d93e54b1657206fa18b8fa2`.
Lean builds reported only pre-existing linter warnings.  The oracle check
passed and wrote `runtime\oracle-eq231-source-package-boundary.log`,
containing only permitted `[propext, Classical.choice, Quot.sound]`
dependency reports.

Honest scope: this removes a manual boundary-assembly step once the explicit
source package is available. It does **not** prove the CMP116/CMP109 source
membership iff, does not identify Balaban's eligible carrier with the
repository carrier, does not prove the pointwise P-residual estimate, Eq.
(2.29), Eq. (2.37), activity/termwise estimates, Gaussian/root/Hessian/locality,
continuum, or Clay obligations.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 417 (2026-06-26, **Batch 003/v2 ingest and Eq. (2.31) carrier projection route**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`, `CURRENT-STATE.md`,
`docs/source-db` Batch 003 proof-obligation catalog/indices/report,
`source-packets/manifests/batch-003-proof-obligation-cards.json`,
`docs/idea-db/ym-creative-expansion` v2 packet files, and this ledger.

Installed source/idea artifacts:

- `THE-ERIKSSON-source-citations-batch-003-2026-06-26.zip`:
  `8fdda342ebd80512671a0c68b03440d8a1b6cf5c6b929a6328fc9f4d8f81d99f`;
- `ym-creative-expansion-pack-v2-20260626.zip`:
  `7fd78d2c240caa822621a4b55eb5160def7ee76a1b307d6114abc4d892284760`.

Only the new Batch 003 files declared in its manifest were installed; the
older package copy of `scripts/source_db.py` was not used.  This preserves the
repository's UTF-8 and atomic-SQLite safeguards.  Batch 003 is operational
metadata only: proof-obligation cards, source-key routing, hypothesis-removal
queue, LLM prompts, and agent checklists.  It does not promote any primary
source status.

The v2 creative expansion packet replaces the previous idea packet under
`docs/idea-db/ym-creative-expansion/`, still outside `docs/source-db` and
outside the Lean import graph.  Its query helper was given a Windows UTF-8
stdout/stderr guard; the installed manifest entry for that helper was updated
to SHA-256
`46acd6ae4bb6a2c0c4bd5005428998a54e98cd00769f675c4498ad94760336ca`.

Lean payload:
`cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes` proves the
existing `CMP116Eq231BalabanPFamilySourcePackage.source_subset_gapCarrier`
field from the narrower source-shaped premise that every encoded source bond
has first coordinate in `gapCubes`.  This is a one-way carrier projection
theorem, not a full source carrier equality, not a `PIndex` membership iff, and
not an `admissible` dictionary.

Verification commands for this checkpoint:

```
Get-FileHash -Algorithm SHA256 C:\Users\lluis\Desktop\Karol\THE-ERIKSSON-source-citations-batch-003-2026-06-26.zip
Get-FileHash -Algorithm SHA256 C:\Users\lluis\Desktop\Karol\ym-creative-expansion-pack-v2-20260626.zip
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py lean cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
python scripts\source_db.py show proof.eq231.membership-iff.source-package
python docs\idea-db\ym-creative-expansion\scripts\validate_pack.py
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --list-cards
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --search eq231
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --queue
python -m pytest tests\test_source_db.py
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-batch003-v2-source-carrier.log
```

Results: package hashes matched; focused olean build passed; source-citation
validation passed with 18 citations from 4 sources; source-db
validation/rebuild/stats/target lookup passed; v2 pack validation and queries
passed; source-db pytest passed, 3 tests; diff check, consistency check, and
forbidden-token scan passed; full `YangMillsCore` build passed; oracle check
passed and wrote `runtime\oracle-batch003-v2-source-carrier.log`.  The oracle
log contains only permitted `[propext, Classical.choice, Quot.sound]`
dependency reports.

The rebuilt source database reports 14 sources, 62 citation/crosswalk/proof-card
records, 215 claim/formula/proof-obligation records, 274 Lean target links,
141 open questions, 39 artifact records, and 9 coverage records; its SHA-256 is
`7055a6e59c513cab80c0f9071dc65f71c7b9ec43001a5f4999aec127b000fc44`.

Note: direct `lake env lean YangMills\RG\BalabanCMP116Eq231.lean` attempts
timed out without Lean diagnostics at 120, 300, and 600 seconds.  The focused
Lake target `lake build +YangMills.RG.BalabanCMP116Eq231:olean` completed and
is the recorded focused Lean check for this checkpoint.

Honest scope: this improves source navigation and adds one conditional
carrier-projection theorem. It does **not** prove the CMP116/CMP109 source
membership iff, does not identify Balaban's eligible carrier with the
repository carrier, does not prove `admissible_iff_source`, the Eq. (2.31)
pointwise P-residual estimate, Eq. (2.29), Eq. (2.37), activity/termwise
estimates, Gaussian/root/Hessian/locality, continuum, or Clay obligations.
Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 418 (2026-06-26, **Eq. (2.31) projected-carrier package producer**)

Files touched:
`YangMills/RG/BalabanCMP116Eq231.lean`, `CURRENT-STATE.md`,
`docs/source-db/catalogs/proof-obligation-cards.json`,
`docs/source-db/indices/PROOF-OBLIGATION-CARDS.md`,
`docs/source-db/indices/proof-obligation-cards.{csv,json}`,
`docs/source-db/source_index.sqlite`, and this ledger.

This checkpoint adds
`CMP116Eq231BalabanPFamilySourcePackage.of_bond_fst_mem_gapCubes`, a
source-package producer for CMP116 Eq. (2.31).  It keeps the two hard source
iff fields explicit:

```
mem_iff_source
admissible_iff_source
```

and replaces the raw `source_subset_gapCarrier` package field by the narrower
source-shaped projected-bond premise:

```
∀ Z D P,
  sourceAdmissible Z D P →
    ∀ b : Cube × Fin 4, b ∈ P → b.1 ∈ gapCubes Z D
```

The proof composes the previous helper
`cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes`.  It is not a
downstream Eq. (2.31) consumer and does not promote any primary source claim.

Verification commands for this checkpoint:

```
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py lean CMP116Eq231BalabanPFamilySourcePackage.of_bond_fst_mem_gapCubes
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean *> C:\Users\lluis\Documents\CodexYangMillsAutopilot\runtime\oracle-eq231-source-package-projection.log
```

Results: focused olean build passed; source-citation validation passed with
18 citations from 4 sources; source-db validation/rebuild/stats/target lookup
passed; diff checks, consistency check, forbidden-token scan, full
`YangMillsCore` build, and oracle check passed.  The rebuilt source database
reports 14 sources, 62 citation/crosswalk/proof-card records, 215
claim/formula/proof-obligation records, 275 Lean target links, 141 open
questions, 39 artifact records, and 9 coverage records; its SHA-256 is
`759028b41350474ed4ae5159939b4e1e106a6b56f8bea022921c441e82f567ae`.

Honest scope: this removes only one layer of package-instantiation friction.
It still requires the projected-bond source theorem, the Eq. (2.31)
`PIndex` membership iff, and `admissible_iff_source`; it does **not** identify
Balaban's carrier with the repository carrier, prove the pointwise residual
estimate, Eq. (2.29), Eq. (2.37), activity/termwise estimates,
Gaussian/root/Hessian/locality, continuum, or Clay obligations.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 420 (2026-06-26, **source DB dictionary-link lookup guard**)

Files touched:
`scripts/source_db.py`, `tests/test_source_db.py`, `CURRENT-STATE.md`, and this
ledger.

This checkpoint improves the public citation lookup workflow.  The command
`python scripts\source_db.py show <key>` now prints the citation's
`dictionary_links`, including source symbol, Lean symbol, relation, status,
statement, and blocker.  This makes operational keys such as
`proof.eq231.source-package.live-fields.v2` self-contained for agents and
external advisors without opening the raw JSON catalog.

The source-db tests now also build a temporary SQLite index and check that every
public JSON citation key is present in the `citations` table.  The specific
Batch 004 key `proof.eq231.source-package.live-fields.v2` is covered, and a
separate smoke test verifies that its dictionary links appear in `show` output.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show proof.eq231.source-package.live-fields.v2
python -m pytest tests\test_source_db.py
lake build +YangMills.RG.BalabanCMP116Eq231:olean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db scripts tests
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: source-citation validation passed with 18 citations from 4 sources;
source-db validation/build/stats passed with 6 catalog files and rebuilt SQLite
hash `a9c5a8faa39751b8eeab90eb23f0ff8e2f8cdc7044e9b3002af6e307e9c93d10`.
The rebuilt source database reports 14 sources, 70 citation/crosswalk/
proof-card records, 257 claim/formula/proof-obligation records, 295 Lean target
links, 164 open questions, 39 artifact records, and 9 coverage records.
`source_db.py show proof.eq231.source-package.live-fields.v2` prints the
Batch 004 dictionary links.  The source-db pytest suite passed with 5 tests.
Focused Eq. (2.31) olean build, diff checks, consistency check, forbidden-token
scan, full `YangMillsCore` build, and oracle check passed.  The oracle output
contains only the permitted `[propext, Classical.choice, Quot.sound]`
dependency reports, with a few declarations reporting no axioms.

Honest scope: this is source-lookup infrastructure only.  It does not promote
`bond_fst_mem_gapCubes`, `source_subset_gapCarrier`, `mem_iff_source`,
`admissible_iff_source`, the Eq. (2.31) pointwise P-residual estimate,
Eq. (2.29), Eq. (2.37), activity/termwise estimates,
Gaussian/root/Hessian/locality, continuum, or Clay obligations.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 421 (2026-06-26, **Batch 005 Eq. (2.29) source queue and v4 mission control**)

Files touched:
`CURRENT-STATE.md`, `docs/source-db/catalogs/eq229-cammarota-live-fields.json`,
`docs/source-db/indices/EQ229-*.md`,
`docs/source-db/indices/CAMMAROTA-ACQUISITION-AND-CITATION-LEDGER.md`,
`docs/source-db/indices/LLM-FAST-CONTEXT-UPDATE-BATCH-005.md`,
`docs/source-db/reports/BATCH-005-EQ229-CAMMAROTA-LIVE-FIELDS.md`,
`docs/source-db/source_index.sqlite`,
`source-packets/manifests/batch-005-eq229-cammarota-live-fields.json`,
`docs/idea-db/ym-creative-expansion/*`, and this ledger.

This checkpoint installs the safe Batch 005 operational source index for
CMP116 Eq. (2.29) and Cammarota CMP85.  It adds nine `lean_linked` cards
centered on the live Eq. (2.29) fields: exact Cammarota theorem extraction,
smallness/threshold hypotheses, the Balaban D-family dictionary, and the
translation into `DIndex/DParts` / `CMP116Eq229Summability`.  These are
routing/acquisition records, not theorem evidence.

The checkpoint also updates the isolated creative expansion pack to v4 under
`docs/idea-db/ym-creative-expansion`.  v4 adds mission contracts, mission
prompts, patch-scoring gates, source-promotion state-machine notes,
source-extraction worksheets, and additional experimental Lean templates.  It
remains outside `docs/source-db` and outside the Lean import graph.  The
Windows query helper is locally patched to force UTF-8 stdout/stderr, and its
manifest entry is updated to the local patched hash.  Two generated markdown
files from the v4 pack were stripped of trailing whitespace, with their manifest
hashes updated to the normalized local bytes.

Hashes checked:

```
THE-ERIKSSON-source-citations-batch-005-safe-patch-2026-06-26.zip
  3222e809c9b36c56107bf225ece03addb00ad1fd27d4006c142f653c3363bc64
THE-ERIKSSON-source-citations-batch-005-preview-db-2026-06-26.zip
  419acc5ca5821b5ecbaee57c0f8ace4c20097632e78b5df49a3a1f8aa3da52c6
ym-creative-expansion-pack-v4-20260626.zip
  69b9854627c7122aba0ee55a21e253e27025fe81149bc4a896d0aff4c1fd0a5f
```

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show proof.eq229.live-fields.v2
python scripts\source_db.py show proof.eq229.cammarota.theorem1.extraction-target.v2
python scripts\source_db.py lean CMP116Lemma3Eq229ScaleBoundary
python docs\idea-db\ym-creative-expansion\scripts\validate_pack.py
python docs\idea-db\ym-creative-expansion\scripts\validate_mission_contracts.py
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --list-cards
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --search eq231
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --queue
python docs\idea-db\ym-creative-expansion\scripts\compile_mission_prompt.py OC_001_eq231_source_subset_gapCarrier
python docs\idea-db\ym-creative-expansion\scripts\check_patch_contract.py --contract docs\idea-db\ym-creative-expansion\mission_contracts\OC_001_eq231_source_subset_gapCarrier.json --intake docs\idea-db\ym-creative-expansion\patch_intake\INTAKE_TEMPLATE.json
python -m pytest tests\test_source_db.py
lake build +YangMills.RG.BalabanCMP116Eq229:olean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: source-citation validation passed with 18 citations from 4 sources.
Source-db validation/build/stats passed with 7 catalog files and rebuilt SQLite
hash `71a3c0706c595ba8ac78b0f58a8dc09867dfb9b1be62a27439255855cd17d8e2`.
The rebuilt source database reports 14 sources, 79 citation/crosswalk/
proof-card records, 296 claim/formula/proof-obligation records, 322 Lean target
links, 187 open questions, 39 artifact records, and 9 coverage records.
Batch 005 `show`/`lean` queries expose Eq. (2.29)/Cammarota routing and
blockers.  The v4 idea pack validation passed with 60 formula cards indexed and
9 mission contracts; mission-contract validation passed; query, queue, and
mission prompt compilation passed.  `check_patch_contract.py` correctly
rejected the empty intake template with missing evidence rather than accepting
a no-evidence patch.  The source-db pytest suite passed with 5 tests.  Focused
Eq. (2.29) olean build, diff checks, consistency check, forbidden-token scan,
full `YangMillsCore` build, and oracle check passed.  The oracle output
contains only the permitted `[propext, Classical.choice, Quot.sound]`
dependency reports, with a few declarations reporting no axioms.

Honest scope: no Eq. (2.29), Eq. (2.31), Eq. (2.37), activity/termwise,
Gaussian/root/Hessian/locality, continuum, or Clay theorem was promoted.  The
Cammarota CMP85 theorem text, exact thresholds, and Balaban D-family dictionary
remain source-pending; v4 is an agent-control artifact only.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 422 (2026-06-26, **source DB artifact acquisition lookup**)

Files touched:
`CURRENT-STATE.md`, `docs/source-citations/cmp116-lemma3.json`,
`docs/source-db/QUERY_EXAMPLES.md`, `docs/source-db/README.md`,
`docs/source-db/source_index.sqlite`, `scripts/source_db.py`,
`tests/test_source_db.py`, and this ledger.

This checkpoint adds a direct citation-system route for finding private source
artifacts before redoing OCR or web lookup.  The new command
`python scripts\source_db.py artifacts [source_id]` prints the configured
`YM_SOURCE_ROOT`, registered acquisition URLs, expected private artifact paths,
media types, hashes, byte sizes, and present/missing state.  It is intentionally
metadata-only: raw PDFs, text extractions, and renders remain out of public Git.

The public Cammarota CMP85 source record now names the expected private
acquisition targets for `cammarota_cmp85`: the PDF, a full text extraction, and
candidate rendered pages 517--519.  The command reports those targets as
missing until a valid primary artifact is available under the private source
root.  This does not assert that the needed theorem is on those pages, nor does
it promote any theorem text or threshold constants.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py artifacts cammarota_cmp85
python scripts\source_db.py artifacts
python -m pytest tests\test_source_db.py
lake build +YangMills.RG.BalabanCMP116Eq229:olean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: source-citation validation passed with 18 citations from 4 sources.
Source-db validation/build/stats passed with 7 catalog files and rebuilt SQLite
hash `5e3b7da45f3c231f75fd7d2688cddf92c7de659bc7a6052fea5bfa0d77d657b9`.
The rebuilt source database reports 14 sources, 79 citation/crosswalk/
proof-card records, 296 claim/formula/proof-obligation records, 322 Lean target
links, 187 open questions, 44 artifact records, and 9 coverage records.
`source_db.py artifacts cammarota_cmp85` prints the Project Euclid, Springer,
and ResearchGate acquisition URLs plus missing private paths for the PDF, text,
and candidate page renders.  The full artifact listing prints the same
Cammarota gap and existing Balaban local artifacts with hashes.  The source-db
pytest suite passed with 6 tests.  Focused Eq. (2.29) olean build, diff
checks, consistency check, forbidden-token scan, full `YangMillsCore` build,
and oracle check passed.  The oracle output contains 1274 axiom reports and no
dependencies outside `[propext, Classical.choice, Quot.sound]`.

Honest scope: this is source-acquisition infrastructure only.  The attempted
public Project Euclid PDF retrieval remains blocked by anti-bot HTML, so no
Cammarota artifact was added and no exact theorem statement, threshold,
Eq. (2.29), Eq. (2.31), Eq. (2.37), activity/termwise estimate,
Gaussian/root/Hessian/locality, continuum, or Clay obligation was promoted.
Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 423 (2026-06-26, **source DB show acquisition context**)

Files touched:
`CURRENT-STATE.md`, `docs/source-db/README.md`, `scripts/source_db.py`,
`tests/test_source_db.py`, and this ledger.

This checkpoint makes source-pending primary records more directly actionable.
`python scripts\source_db.py show <key>` now prints a `source acquisition`
section whenever the key's direct source has registered web URLs or private
artifacts.  The section includes the configured `YM_SOURCE_ROOT`, artifact
names, present/missing state, relative paths, media types, and hashes/byte
sizes when present.  The separate `artifacts <source_id>` command remains the
source-level acquisition planner, especially for operational crosswalks that
route through several primary sources.

The immediate payoff is visible on the two active source fronts:
`show cmp116.eq231.p-family-carrier-source-target` now displays the existing
CMP116 PDF/text/render artifacts and hashes, while
`show cammarota.cmp85.polymer-mayer-source-target` displays Project Euclid,
Springer, and ResearchGate acquisition URLs plus the missing private Cammarota
PDF/text/render targets.  No mathematical source claim is promoted by this
lookup change.

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_db.py show cammarota.cmp85.polymer-mayer-source-target
python -m pytest tests\test_source_db.py
lake build +YangMills.RG.BalabanCMP116Eq229:olean
lake build +YangMills.RG.BalabanCMP116Eq231:olean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: source-citation validation passed with 18 citations from 4 sources.
Source-db validation/build/stats passed with 7 catalog files and rebuilt SQLite
hash `5e3b7da45f3c231f75fd7d2688cddf92c7de659bc7a6052fea5bfa0d77d657b9`.
The rebuilt source database reports 14 sources, 79 citation/crosswalk/
proof-card records, 296 claim/formula/proof-obligation records, 322 Lean target
links, 187 open questions, 44 artifact records, and 9 coverage records.  The
source-db pytest suite passed with 7 tests.  Focused Eq. (2.29) and Eq. (2.31)
olean builds, diff checks, consistency check, forbidden-token scan, full
`YangMillsCore` build, and oracle check passed.  The oracle output contains
1274 axiom reports and no dependencies outside
`[propext, Classical.choice, Quot.sound]`.

Honest scope: source lookup and acquisition context only.  No Cammarota theorem,
Balaban eligible-carrier theorem, Eq. (2.29), Eq. (2.31), Eq. (2.37),
activity/termwise estimate, Gaussian/root/Hessian/locality, continuum, or Clay
obligation was promoted.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 424 (2026-06-26, **Batch 006 Gaussian/root/Hessian live fields and v5 patch harness**)

Files touched:
`CURRENT-STATE.md`, `docs/source-db/catalogs/gaussian-root-hessian-live-fields.json`,
`docs/source-db/indices/GAUSSIAN-ROOT-HESSIAN-*.md`,
`docs/source-db/indices/RAW-SOURCE-M3-FIELD-ORDER.md`,
`docs/source-db/indices/HSHARP-ROOTED-REMAINDER-HANDOFF.md`,
`docs/source-db/indices/LLM-FAST-CONTEXT-UPDATE-BATCH-006.md`,
`docs/source-db/reports/BATCH-006-GAUSSIAN-ROOT-HESSIAN-LIVE-FIELDS.md`,
`docs/source-db/manifests/batch-006-gaussian-root-hessian-live-fields.json`,
`source-packets/manifests/batch-006-gaussian-root-hessian-live-fields.json`,
`docs/source-db/source_index.sqlite`,
`docs/idea-db/ym-creative-expansion/*`, and this ledger.

This checkpoint installs the safe Batch 006 operational source index for the
Gaussian/root/Hessian/activity/H# side of the raw-source M3 frontier.  It adds
11 `lean_linked` cards, headed by `proof.rawsource.m3.live-fields.v2`, that
separate covariance/root certificates, Gaussian pushforward, root localization,
Wilson Hessian identification, local activity construction, support and
measurability, raw pointwise decay, and rooted H# obligations.  These are
ordering and acquisition records only; they are not primary-source theorem
evidence.

The isolated creative expansion pack under
`docs/idea-db/ym-creative-expansion/` is updated to v5.  v5 adds a closed-loop
patch intake and scoring harness, source locks, mission contracts, theorem
skeletons, and review examples.  It remains outside `docs/source-db` and
outside the Lean import graph.  The Windows query helper is locally patched to
force UTF-8 stdout/stderr, and its manifest entry is updated to the local
patched hash.

Hashes checked:

```
THE-ERIKSSON-source-citations-batch-006-safe-patch-2026-06-26.zip
  9356093be1ea5f4d45c7e28b255f1cb652729849e83fadb4921de3a32b2a34bb
THE-ERIKSSON-source-citations-batch-006-preview-db-2026-06-26.zip
  c5a91936d9c9f00e71898efe0f14cb18f5cc0ab373de8f30dd0bfb2322cdb63e
ym-creative-expansion-pack-v5-20260626.zip
  0e291b873e6e7eb33e12ae419b62fe7eca95bc37dedf592355ceb99aeeba2714
```

Verification commands for this checkpoint:

```
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show proof.rawsource.m3.live-fields.v2
python scripts\source_db.py show proof.gaussian.covariance-root-certificate.v2
python scripts\source_db.py show proof.rooted-hsharp-remainder.identity.v2
python docs\idea-db\ym-creative-expansion\scripts\validate_pack.py
python docs\idea-db\ym-creative-expansion\scripts\validate_mission_contracts.py
python docs\idea-db\ym-creative-expansion\scripts\validate_v5_harness.py
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --list-cards
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --search eq231
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --queue
python docs\idea-db\ym-creative-expansion\scripts\mission_board.py --ranked
python docs\idea-db\ym-creative-expansion\scripts\score_patch_intake.py docs\idea-db\ym-creative-expansion\patch_review\examples\accept_removed_field_example.json
python -m pytest tests\test_source_db.py
lake build +YangMills.RG.BalabanCMP116Eq229:olean
lake build +YangMills.RG.BalabanCMP116Eq231:olean
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: source-citation validation passed with 18 citations from 4 sources.
Source-db validation/build/stats passed with 8 catalog files and rebuilt SQLite
hash `939ccd191d082a5037d0ba042d2ddf3c63e2cc989be2afa4046ae8ca544ff28c`.
The rebuilt source database reports 14 sources, 90 citation/crosswalk/
proof-card records, 352 claim/formula/proof-obligation records, 361 Lean target
links, 220 open questions, 44 artifact records, and 9 coverage records.
Batch 006 `show` queries expose the raw-source M3, covariance-root, and rooted
H# live fields.  The v5 idea pack validation passed with 75 formula cards and
15 mission contracts; mission-contract and v5-harness validation passed; query,
queue, mission-board, and patch-score smoke checks passed.  The full
`lake build YangMillsCore` passed at 8364 jobs with only pre-existing linter
warnings.  `lake env lean oracle_check.lean` passed; the oracle output contains
1274 axiom reports and no dependencies outside
`[propext, Classical.choice, Quot.sound]`.

Honest scope: this is source-routing and patch-governance infrastructure only.
No covariance/root certificate, Gaussian pushforward, Wilson Hessian
identification, local activity construction, raw pointwise decay, rooted H#
identity, Eq. (2.29), Eq. (2.31), Eq. (2.37), continuum, or Clay obligation was
promoted.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 425 (2026-06-26, **source DB frontier queue command**)

Files touched:
`scripts/source_db.py`, `tests/test_source_db.py`, `docs/source-db/README.md`,
`CURRENT-STATE.md`, and this ledger.

This checkpoint adds `python scripts\source_db.py frontier`, a compact queue
view for citations that still have open questions.  Unlike `blockers`, it also
surfaces `lean_linked` operational cards such as the Batch 006 raw-source M3
frontier.  The command reports status, Lean target count, open-question count,
the first next question, the first local-text pointer, and compact source
acquisition availability.  It is intended to prevent repeated manual `show`
lookups across operational cards before choosing the next exact source field.

Verification commands for this checkpoint:

```
python scripts\source_db.py frontier --term rawsource --status lean_linked --limit 8
python -m pytest tests\test_source_db.py
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: the new `frontier` command exposed the raw-source M3, rooted H#,
Gaussian/root/Hessian, and related live operational cards.  The source-db pytest
suite passed with 8 tests.  Source-citation validation passed with 18 citations
from 4 sources.  Source-db validation/build/stats passed with 8 catalog files
and rebuilt SQLite hash
`939ccd191d082a5037d0ba042d2ddf3c63e2cc989be2afa4046ae8ca544ff28c`.  The
rebuilt source database still reports 14 sources, 90 citation/crosswalk/
proof-card records, 352 claim/formula/proof-obligation records, 361 Lean target
links, 220 open questions, 44 artifact records, and 9 coverage records.  Diff
checks, consistency check, forbidden-token scan, full `YangMillsCore` build, and
oracle check passed.  The full build passed at 8364 jobs with only pre-existing
linter warnings; the oracle output contains 1274 axiom reports and no
dependencies outside `[propext, Classical.choice, Quot.sound]`.

Honest scope: source-routing tooling only.  No citation status, source theorem,
Lean theorem, covariance/root certificate, Gaussian pushforward, Wilson Hessian
identification, local activity construction, raw pointwise decay, rooted H#,
Eq. (2.29), Eq. (2.31), Eq. (2.37), continuum, or Clay obligation was promoted.
Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 426 (2026-06-26, **Batch 007 source DB and Gaussian normalization interface**)

Files touched: `YangMills/RG/PhysicalGaugeCMP116ActivityConstruction.lean`,
`oracle_check.lean`, `CURRENT-STATE.md`, this ledger,
`docs/source-db/source_index.sqlite`, new Batch 007 files under
`docs/source-db/` and `source-packets/manifests/`, and the v6 creative
expansion pack under `docs/idea-db/ym-creative-expansion/`.

This checkpoint installs the safe Batch 007 Eq. (2.37)/post-P source-db
frontier pack and the v6 creative expansion pack.  Batch 007 adds
`lean_linked` operational cards for the fixed-`Z0'` Eq. (2.37) estimate, the
post-(2.37) final summation, the `Z0`/`Z0'` dictionary, constants, residual
exponent budget, and a guard against unsourced theorem splitting.  v6 remains
an experimental idea/mission harness outside the Lean import graph and outside
the source-evidence layer.

On the Lean side, this checkpoint adds
`PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization`, with
`gaussian_pushforward` deriving the existing dictionary/root pushforward from a
structured source coordinate-map normalization record.  The localized Gaussian
source packages now have `of_gaussianNormalization` constructors that consume
that structured record plus the remaining separated source facts.  This narrows
the Gaussian-pushforward interface for future source work; it does not prove
the analytic Gaussian normalization, Jacobian/determinant statement,
covariance/root certificate, Wilson Hessian identification, local activity
construction, raw pointwise decay, or rooted H# identity.

Hashes checked before installation:

```
THE-ERIKSSON-source-citations-batch-007-safe-patch-2026-06-26 (1).zip
  066a8ad31a9c101f581d18a794f6aba32f9de6d38c940865cfc6d4ad84f20a62
THE-ERIKSSON-source-citations-batch-007-preview-db-2026-06-26 (1).zip
  5706d72925e032b0ffc9f7505578d51270d645960daf611e8efd27b5018ef07b
ym-creative-expansion-pack-v6-20260626 (1).zip
  3c5e54b07242c92723bb47e8732fb73dc69e9128938b27b3e306b14db3ca41f0
```

Verification commands for this checkpoint:

```
lake build +YangMills.RG.PhysicalGaugeCMP116ActivityConstruction:olean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python scripts\source_db.py show proof.eq237.live-fields.v2
python scripts\source_db.py show guard.eq237.no-unsourced-splitting.v2
python scripts\source_db.py frontier --term eq237 --status lean_linked --limit 8
python docs\idea-db\ym-creative-expansion\scripts\validate_pack.py
python docs\idea-db\ym-creative-expansion\scripts\validate_mission_contracts.py
python docs\idea-db\ym-creative-expansion\scripts\validate_v5_harness.py
python docs\idea-db\ym-creative-expansion\scripts\validate_v6_live_fields.py
python docs\idea-db\ym-creative-expansion\scripts\field_board.py --order
python docs\idea-db\ym-creative-expansion\scripts\batch006_prompt_compiler.py gaussian_pushforward
python docs\idea-db\ym-creative-expansion\scripts\query_expansion_db.py --search gaussian
python docs\idea-db\ym-creative-expansion\scripts\check_no_backfill.py docs\idea-db\ym-creative-expansion\patch_review\examples\accept_source_lock_example.json
python -m pytest tests\test_source_db.py
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests YangMills\RG\PhysicalGaugeCMP116ActivityConstruction.lean YangMills\RG\BalabanCMP116SourceTheorem.lean
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: the focused `PhysicalGaugeCMP116ActivityConstruction` build passed.
The separate focused `BalabanCMP116SourceTheorem` build was attempted but did
not finish within a 10-minute local timeout; the subsequent full
`YangMillsCore` build did cover the graph and passed at 8364 jobs with only
pre-existing linter warnings.  Source-citation validation passed with 18
citations from 4 sources.  Source-db validation/build/stats passed with 9
catalog files and rebuilt SQLite hash
`5009d7ac82929b924af2f7dddbb90e8edf0f25c184cbdc9e3be817d9461cb94d`.
The rebuilt database reports 14 sources, 90 citation/crosswalk/proof-card
records, 352 claim/formula/proof-obligation records, 361 Lean target links, 220
open questions, 44 artifact records, and 9 coverage records.  Batch 007 `show`
and `frontier` queries expose the Eq. (2.37) live fields and the no-unsourced
splitting guard.  The v6 idea pack validation passed with 105 formula cards, 30
mission contracts, and 10 live fields; mission-contract, v5-harness, v6
live-field, field-board, prompt-compiler, query, and no-backfill smoke checks
passed.  The source-db pytest suite passed with 8 tests.  Diff checks,
consistency check, forbidden-token scan, full `YangMillsCore` build, and oracle
check passed.  `lake env lean oracle_check.lean` exited 0 with empty stderr and
1277 axiom-report lines; no reported dependency lies outside
`[propext, Classical.choice, Quot.sound]`.

Honest scope: this is a source-frontier intake plus a structured Gaussian
normalization interface.  No Gaussian pushforward source theorem, covariance
root theorem, Wilson Hessian theorem, local activity construction theorem, raw
pointwise decay theorem, rooted H# identity, Eq. (2.29), Eq. (2.31), Eq. (2.37),
continuum, or Clay obligation was discharged.  Clay distance **~0% (<0.1%)**,
unchanged.

## Addendum 427 (2026-06-26, **Eq. (2.31) eligible-bond carrier interface**)

Files touched: `YangMills/RG/BalabanCMP116Eq231.lean`,
`oracle_check.lean`, `CURRENT-STATE.md`, and this ledger.

This checkpoint adds the source-facing record
`CMP116Eq231EligibleBondCarrierSource`, which splits the remaining
projected-bond carrier premise into two narrower source obligations:
`eligible_iff_gapCarrier` identifies a source-side eligible positive bond with
membership of its first coordinate in `gapCubes`, and
`sourceAdmissible_bonds_eligible` says each source-admissible `P` uses only
eligible bonds.  The theorem
`cmp116Eq231_bond_fst_mem_gapCubes_of_sourceEligible` derives the existing
`bond_fst_mem_gapCubes` premise from that record, and
`CMP116Eq231BalabanPFamilySourcePackage.of_sourceEligibleBondCarrier` builds
the existing Eq. (2.31) source package through the older
`of_bond_fst_mem_gapCubes` constructor.

This is a strict interface narrowing, not a source-theorem promotion.  The
source-db entries for `cmp116.eq231.p-family-carrier-source-target` and
`cmp109.bond-convention.positive-oriented` still report the carrier theorem as
`source_pending`: CMP109 supports the positive-oriented convention, and CMP116
anchors the P-family/gap context, but the exact source-to-Lean eligible-bond
ownership theorem is still open.

Verification commands for this checkpoint:

```
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_citations.py show cmp109.bond-convention.positive-oriented
python scripts\source_citations.py show cmp109.b0-corridor-bond
python scripts\source_db.py lean CMP116Eq231BalabanPFamilySourcePackage
python scripts\source_db.py frontier --term eq231 --status lean_linked --limit 8
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_citations.py validate
python scripts\source_db.py verify
python scripts\source_db.py build
python scripts\source_db.py stats
python -m pytest tests\test_source_db.py
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: the source lookups confirmed that the relevant CMP116/CMP109 entries
remain source-pending for the exact carrier ownership theorem.  The focused
`BalabanCMP116Eq231` build passed after a transient first `lake build` failure
with only a pre-existing warning visible; direct `lake env lean` of the file and
the repeated focused build passed.  Source-citation validation passed with 18
citations from 4 sources.  Source-db validation/build/stats passed with 9
catalog files and SQLite hash
`5009d7ac82929b924af2f7dddbb90e8edf0f25c184cbdc9e3be817d9461cb94d`; the
current index reports 15 sources, 100 citation/crosswalk/proof-card records,
393 claim/formula/proof-obligation records, 427 Lean target links, 259 open
questions, 44 artifact records, and 10 coverage records.  The source-db pytest
suite passed with 8 tests.  Diff checks, consistency check, forbidden-token
scan, full `YangMillsCore` build, and oracle check passed.  The full build
passed at 8364 jobs with only pre-existing linter warnings.  `lake env lean
oracle_check.lean` exited 0 with empty stderr and 1280 axiom-report lines; no
reported dependency lies outside `[propext, Classical.choice, Quot.sound]`.

Honest scope: this narrows Eq. (2.31) carrier ownership to a smaller
eligible-bond dictionary.  It does not prove the CMP116 source carrier theorem,
the P-family membership iff, `admissible_iff_source`, the pointwise P-residual
estimate, Eq. (2.29), Eq. (2.37), Gaussian/root/Hessian fields, H#, continuum,
or Clay.  Clay distance **~0% (<0.1%)**, unchanged.

## Addendum 428 (2026-06-26, **source metadata control-escape guard**)

Files touched: `docs/source-db/catalogs/eq237-postp-live-fields.json`,
`docs/source-db/source_index.sqlite`,
`docs/idea-db/ym-creative-expansion/formulas/derived_formula_cards.jsonl`,
`tests/test_source_db.py`, `CURRENT-STATE.md`, and this ledger.

The post-`eeac8b4` Extra High audit found corrupted JSON LaTeX text in
Eq. (2.37)/Eq. (2.29) operational metadata: JSON strings contained
`\u0007lpha` where the intended formula text was `\alpha`.  This checkpoint
normalizes those formula strings to explicit JSON `\\alpha` escapes, rebuilds
the source DB SQLite index from the corrected catalog, and adds
`test_source_metadata_has_no_control_escapes` so future JSON/JSONL source and
idea metadata fails pytest if it contains C0 Unicode control escapes or actual
non-whitespace control bytes.

Verification commands for this checkpoint:

```
rg -n "u0007|\\x07" docs\source-db docs\idea-db source-packets -S
python scripts\source_db.py verify
python scripts\source_citations.py validate
python docs\idea-db\ym-creative-expansion\scripts\validate_pack.py
python scripts\source_db.py build
python -m pytest tests\test_source_db.py
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests
lake build +YangMills.RG.BalabanCMP116Eq231:olean
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: source-db validation passed with 9 catalog files and no structural
errors; source-citation validation passed with 18 citations from 4 sources; the
v4/v6 idea-pack validation passed with 105 formula cards and 30 mission
contracts; `python -m pytest tests\test_source_db.py` passed with 9 tests; the
rebuilt SQLite source DB hash is
`614154cd6a2977832a320d5ed4d302d01ee4452474ddff1a9f801989f5789129`.
Diff checks passed with only line-ending warnings.  Consistency checks and the
forbidden-token scan found no new `sorry`, `admit`, or `axiom`.  The focused
`BalabanCMP116Eq231` build passed, and full `lake build YangMillsCore` passed
at 8364 jobs with only pre-existing linter warnings.  The first direct oracle
run exceeded the 10-minute wrapper timeout before an exit code was captured, so
it was not accepted as verification; the rerun of `lake env lean
oracle_check.lean` exited 0 with empty stderr.  The oracle log reports 1280
reported dependency lines, all within `[propext, Classical.choice, Quot.sound]`.

Honest scope: this is source/idea metadata hygiene and a regression guard.  It
does not promote any source claim, prove an Eq. (2.31)/Eq. (2.37)/Eq. (2.29)
field, or change Clay distance.

## Addendum 429 (2026-06-26, **Eq. (2.31) positive-tail ownership target**)

Files touched: `YangMills/RG/BalabanCMP116Eq231.lean`, `oracle_check.lean`,
`CURRENT-STATE.md`, `docs/source-db/catalogs/eq231-source-package-live-fields.json`,
`docs/source-db/indices/EQ231-CITATION-EXTRACTION-REQUESTS.md`,
`docs/source-db/indices/EQ231-SOURCE-PACKAGE-LIVE-FIELDS.md`,
`docs/source-db/source_index.sqlite`, and this ledger.

The new record `CMP116Eq231PositiveTailOwnershipSource` names the one-field
fallback target for the CMP116/CMP109 Eq. (2.31) carrier blocker:

```
sourceAdmissible Z D P -> b in P -> b.1 in gapCubes Z D
```

This is weaker than a full independently transcribed eligible-bond iff.  It is
the honest target when the source pages support base/tail ownership but do not
yet justify a separate source-side predicate
`sourceEligibleBond Z D b <-> b.1 in gapCubes Z D`.

The theorem `cmp116Eq231_bond_fst_mem_gapCubes_of_positiveTailOwnership`
projects the one-field record to the older bond-first-coordinate premise.
`CMP116Eq231EligibleBondCarrierSource.of_positiveTailOwnership` recovers the
eligible-bond carrier record by choosing
`sourceEligibleBond Z D b := b.1 in gapCubes Z D`, and
`CMP116Eq231BalabanPFamilySourcePackage.of_positiveTailOwnership` feeds the
existing source-package route.  The source-db Eq. (2.31) live-field metadata and
extraction-request page now name this endpoint/base theorem explicitly.

Verification commands for this checkpoint:

```
python scripts\source_citations.py show cmp116.eq231.p-family-carrier-source-target
python scripts\source_citations.py show cmp109.bond-convention.positive-oriented
python scripts\source_citations.py show cmp109.b0-corridor-bond
python scripts\source_db.py show proof.eq231.field.bond-fst-mem-gapCubes
lake env lean YangMills\RG\BalabanCMP116Eq231.lean
python scripts\source_db.py verify
python scripts\source_citations.py validate
python -m pytest tests\test_source_db.py
lake build +YangMills.RG.BalabanCMP116Eq231:olean
python scripts\source_db.py build
python scripts\source_db.py lean CMP116Eq231PositiveTailOwnershipSource
python scripts\source_db.py lean CMP116Eq231EligibleBondCarrierSource
git diff --check
git diff --cached --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db docs\idea-db scripts tests YangMills\RG\BalabanCMP116Eq231.lean
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: the source lookups still mark the full CMP116/CMP109 carrier theorem
as source-pending.  The inspected text supports the current extraction request
but not a theorem promotion: CMP116 page 12 gives the `Y0^{c,*}`/`P` setup,
interior/boundary restrictions, and minimal `Z0`; CMP116 pages 18--19 give the
Eq. (2.31) `P`-sum and lower bound; CMP109 gives endpoint and positive
orientation windows.  The missing source sentence remains the base/tail
ownership assertion for every bond in a source-admissible `P`.  Source-db
validation passed with 9 catalog files; citation validation passed with 18
citations from 4 sources; pytest passed with 9 tests.  The focused Eq. (2.31)
file elaboration and focused `BalabanCMP116Eq231` build passed.  Diff checks
passed with only line-ending warnings; consistency checks and forbidden-token
scan found no new `sorry`, `admit`, or `axiom`.  Full `lake build
YangMillsCore` passed at 8364 jobs with only pre-existing linter warnings.
`lake env lean oracle_check.lean` exited 0 with empty stderr and 1284 reported
dependency lines, all within `[propext, Classical.choice, Quot.sound]`.  The
rebuilt SQLite source DB hash is
`b372d4705952097523f0ca7d709c186ba1ca075f0c4f61f3ed5621413a6d1a98`.

Honest scope: this removes no source-pending status.  It narrows the Eq. (2.31)
carrier branch from two eligible-bond fields to one endpoint/base theorem in the
fallback route.  It does not prove the CMP116 carrier theorem, `mem_iff_source`,
`admissible_iff_source`, pointwise P-residual majorization, Eq. (2.29), Eq.
(2.37), Gaussian/root/Hessian fields, H#, continuum, or Clay.  Clay distance
**~0% (<0.1%)**, unchanged.

## Addendum 430 (2026-06-26, **Gaussian-normalization scale raw-source routes**)

Files touched: `YangMills/RG/BalabanCMP116Lemma3ScaleFamily.lean`,
`oracle_check.lean`, `CURRENT-STATE.md`,
`docs/source-db/indices/GAUSSIAN-ROOT-HESSIAN-LIVE-FIELDS.md`, and this ledger.

This checkpoint promotes the structured CMP116 Gaussian-normalization interface
from the single localized-Gaussian source packages to the scale-family
raw-source routes.  The new constructors are:

```
rawSource_of_lemma3ActivityEstimate_gaussianNormalization
rawSource_of_weightedPostPBoundaries_gaussianNormalization
rawSource_of_eq231_weightedPostPBoundaries_gaussianNormalization
```

They replace the old caller-supplied per-scale equality

```
(balabanCMP116Dmu0 (Cube d L) lieDim).map
  ((D t k).gaussianRootMap (root t k)) = physicalGaussian t k
```

by one per-scale
`PhysicalGaugeCMP116Dictionary.CMP116GaussianPushforwardNormalization` record,
then derive the old equality through
`CMP116GaussianPushforwardNormalization.gaussian_pushforward` before feeding the
existing raw-source constructors.

Verification commands for this checkpoint:

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
lake build +YangMills.RG.BalabanCMP116Lemma3ScaleFamily:olean
python scripts\source_db.py verify
python scripts\source_citations.py validate
git diff --check
python scripts\check_consistency.py
rg -n "^\s*(sorry|admit|axiom)\b" YangMillsCore.lean oracle_check.lean CURRENT-STATE.md docs\SOURCE-CLAIM-AUDIT.md docs\VERIFICATION-LEDGER.md docs\source-citations docs\source-db YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
python -m pytest tests\test_source_db.py
lake build YangMillsCore
lake env lean oracle_check.lean
```

Results: the first focused

```
lake env lean YangMills\RG\BalabanCMP116Lemma3ScaleFamily.lean
```

124-second wrapper run timed out without a Lean error; the rerun with a larger
timeout exited 0.  The focused `BalabanCMP116Lemma3ScaleFamily` build passed at
8256 jobs with only pre-existing linter warnings.  Source-db validation passed
with 9 catalog files; citation validation passed with 18 citations from 4
sources; `python -m pytest tests\test_source_db.py` passed with 9 tests.
`git diff --check` passed with only line-ending warnings.  Consistency checks
reported zero `sorry` and zero verified-core axioms, and the forbidden-token
scan found no new `sorry`, `admit`, or `axiom`.  Full `lake build
YangMillsCore` passed at 8364 jobs with only pre-existing warnings.
`lake env lean oracle_check.lean` exited 0 with empty stderr and 2723 stdout
lines; the three new symbols printed with dependency axioms within Lean's
standard `[propext, Classical.choice, Quot.sound]` set.

Honest scope: this is a theorem-interface narrowing, not an analytic Gaussian
normalization proof.  The CMP116 Eq. (2.5)--(2.6) determinant/Jacobian
normalization, source coordinate-map dictionary, covariance-root certificate,
root localization, Wilson Hessian, local activity construction, raw decay, H#,
continuum, and Clay obligations remain open.
