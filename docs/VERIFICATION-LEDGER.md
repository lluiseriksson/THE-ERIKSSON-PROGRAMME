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
