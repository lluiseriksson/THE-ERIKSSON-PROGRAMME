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

This addendum formalises the remaining Phase 8 targets:

* **`walk_union_connected`** — Proves that if we have a path in the incompatibility graph of a polymer cluster, we can connect the endpoints of the path in the big union of their closed neighborhoods.
* **`cluster_closedNeigh_union_connected`** — Proves that if `IsCluster` holds, then the union of the closed neighborhoods of all polymers in the cluster is connected.
* **`clusterRemainderSum_summable`** — Proves the absolute volume-uniform convergence of the cluster activity remainder sum under the local Kotecký–Preiss criterion.
* **`discreteModifiedMetric_le_clusterModifiedMetric`** — Establishes the metric monotonicity for the base case $n=1$, showing the polymer modified metric is bounded by the cluster modified metric.

**How compilation was resolved.**
We defined the connectivity of the union of closed neighborhoods using a path induction on the incompatibility graph. The remainder sum absolute convergence was bounded by introducing a parameter $t > 0$ and scaling the polymer activities, then applying the Kotecký–Preiss criterion to the scaled system to achieve a volume-uniform bound. The metric monotonicity target was resolved for the base case $n=1$ by using subsingleton elimination on the single polymer cluster index.

**Honest scope.** This completes the Phase 8 targets. Clay distance **~0% (<0.1%), unchanged**.

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


