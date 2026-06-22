/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

/-
# YangMillsCore — the sound, self-contained core of the project

This root module imports **only** the parts of the development that are:

* mathematically sound (no `sorry`, no project-specific axioms),
* genuinely about Yang–Mills / SU(N) (not a vacuous target predicate), and
* structurally separable from the LSI / legacy Balaban-RG sprawl.

Its entire import closure was verified (by `import`-graph analysis, 2026-05-28)
to avoid `YangMills/ClayCore/BalabanRG/**`, `YangMills/P8_PhysicalGap/BalabanToLSI`
and the vacuous `L8_Terminal/ClayTheorem` chain.  See `CLEANUP_PLAN.md` and
`FOUNDATIONS.md` for the keep/discard rationale.

Build just this target to check the salvaged core in isolation:

    lake build YangMillsCore

Expected oracle on every declaration reachable from here:
`[propext, Classical.choice, Quot.sound]`.

## What is in the core

* Lattice + gauge scaffolding (`L0_Lattice`): finite lattice geometry, gauge
  configurations, the Wilson action, gauge invariance.
* The lattice Gibbs measure (`L1_GibbsMeasure.GibbsMeasure`).
* SU(N) compactness / measurability and the Haar state construction
  (`P8_PhysicalGap.SUN_Compact`, `SUN_StateConstruction`).
* The Schur-orthogonality programme on SU(N) Haar (`ClayCore/Schur*`):
    - `sunHaarProb_trace_re_integral_zero`  (F0: ∫ tr U = 0),
    - `sunHaarProb_trace_pow_complex_integral_zero`  (Z_N selection rule:
      ∫ (tr U)^k = 0 for N ∤ k),
    - `…trace_normSq_integral_le`  (L2.5: ∫ |tr U|² ≤ N),
    - entry/character orthogonality steps, and the physical-observable bridge.
* The sound `L^p → L·log·L` envelope lemma
  (`P8_PhysicalGap.MemLpLogIntegrability.memLp_gt_two_integrable_sq_mul_log_sq`).

## What is deliberately NOT in the core

The vacuous targets (`ClayYangMillsTheorem`, `ClayYangMillsStrong`), the
LSI/Bakry–Émery pipeline, the legacy Balaban-RG packet/coherence/frontier
sprawl, and the ~25 BFS-dead axioms.  They route only to the empty `∃ m > 0`
statement; keeping them out of this root is the point.  The modern
`YangMills/RG/**` modules imported below are the clean, explicit-hypothesis
replacement track, not the excluded legacy packet.  `CLEANUP_PLAN.md` lists the
legacy material and the staged plan for removing it once this core is confirmed
green.
-/

-- Lattice + gauge layer (L0)
import YangMills.L0_Lattice.FiniteLattice
import YangMills.L0_Lattice.GaugeConfigurations
import YangMills.L0_Lattice.WilsonAction
import YangMills.L0_Lattice.GaugeInvariance
import YangMills.L0_Lattice.FiniteLatticeGeometryInstance
import YangMills.L0_Lattice.ChainComplex

-- Lattice Gibbs measure (L1)
import YangMills.L1_GibbsMeasure.GibbsMeasure
import YangMills.L1_GibbsMeasure.CenterInvariance
import YangMills.L1_GibbsMeasure.SUNSelectionRule
import YangMills.L1_GibbsMeasure.GibbsSelectionRule
import YangMills.L1_GibbsMeasure.PolymerExpansion
import YangMills.L1_GibbsMeasure.WilsonObservable
import YangMills.L1_GibbsMeasure.PolymerFactorization
import YangMills.L1_GibbsMeasure.LatticePolymerSystem
import YangMills.L1_GibbsMeasure.ConnectedEntropy
import YangMills.L1_GibbsMeasure.ClusterGeometry
import YangMills.L1_GibbsMeasure.PolymerRepresentation
import YangMills.L1_GibbsMeasure.WeightedGas
import YangMills.L1_GibbsMeasure.TwoPlaquetteCorrelator
import YangMills.L1_GibbsMeasure.EdgeFactorization
import YangMills.L1_GibbsMeasure.WilsonLoopExpansion
import YangMills.L1_GibbsMeasure.ExpActivityExpansion
import YangMills.L1_GibbsMeasure.SupportFactorization
import YangMills.L1_GibbsMeasure.RestrictedGate
import YangMills.KP.PinnedCluster
import YangMills.KP.PinnedWalk
import YangMills.KP.PinnedBound
import YangMills.KP.RootedChildCount
import YangMills.KP.RootedLeafSummation
import YangMills.KP.SharpMajorant
import YangMills.KP.SharpShell
import YangMills.KP.SharpKP
import YangMills.KP.ClusterTail
import YangMills.KP.MayerInversion
import YangMills.KP.Restriction

-- SU(N) compactness and Haar state construction
import YangMills.P8_PhysicalGap.SUN_Compact
import YangMills.P8_PhysicalGap.SUN_StateConstruction

-- Sound L^p → L·log·L envelope lemma (the salvaged piece of the LSI work)
import YangMills.P8_PhysicalGap.MemLpLogIntegrability

-- Schur-orthogonality programme on SU(N) Haar (the genuine assets)
import YangMills.ClayCore.SchurZeroMean
import YangMills.ClayCore.SchurTwoSitePhase
import YangMills.ClayCore.SchurOffDiagonal
import YangMills.ClayCore.SchurNormSquared
import YangMills.ClayCore.SchurDiagPhase
import YangMills.ClayCore.SchurEntryOrthogonality
import YangMills.ClayCore.SchurEntryOffDiag
import YangMills.ClayCore.SchurNormOne
import YangMills.ClayCore.ContinuousUnitaryRep
import YangMills.ClayCore.GenericSchurOrthogonality
import YangMills.ClayCore.SchurFundamentalOrthogonality
import YangMills.ClayCore.SchurL25
import YangMills.ClayCore.SchurPhysicalBridge
import YangMills.ClayCore.SchurMomentVanishing
import YangMills.ClayCore.SchurMixedMomentVanishing
import YangMills.ClayCore.SchurEntryNAlitySelection
import YangMills.ClayCore.CenterVanishing
import YangMills.ClayCore.SchurPowerSumVanishing
import YangMills.ClayCore.LeftInvariantVanishing
import YangMills.ClayCore.SchurMixedPowerSumVanishing
import YangMills.ClayCore.SUOneDegenerate
import YangMills.ClayCore.U1FourierOrthogonality
import YangMills.ClayCore.GaugeMarginal
import YangMills.ClayCore.GaugeEdgeExpectation
import YangMills.ClayCore.GaugeMeasureProps
import YangMills.ClayCore.WilsonLoopCenter
import YangMills.ClayCore.WilsonLine
import YangMills.ClayCore.TracePathExpansion
import YangMills.ClayCore.WilsonLoopMonomial

-- Paper (Eriksson, Bloque 4) — the §4/§6/§7 conditional skeleton, formalized as
-- explicit-hypothesis theorems (the imported Balaban/KP estimates are carried as
-- hypotheses, never as axioms).  See `docs/` and the per-file headers.
import YangMills.Paper.CouplingControl
import YangMills.Paper.MassGapAssembly
import YangMills.Paper.UVSummation
import YangMills.Paper.ClusteringToGap
import YangMills.Paper.GapRefinementChallenge

-- Kotecký–Preiss / Mayer cluster-expansion layer (`docs/kp-cluster-expansion-plan.md`).
-- KP0–KP2a (substrate, partition identities, incompatibility graph, Ursell coefficient)
-- plus the completed cluster-expansion campaigns: the cluster sum (Mayer RHS), its
-- support on clusters, the Mayer-Ursell inversion `Ξ = exp(clusterSum)`, the sharp
-- KP convergence bound, and the pinned-tail estimates consumed by the lattice
-- correlation and area-law layers.
import YangMills.KP.Basic
import YangMills.KP.Cluster
import YangMills.KP.Ursell
import YangMills.KP.Expansion
import YangMills.KP.Criterion
import YangMills.KP.Convergence
import YangMills.KP.SinglePolymer
import YangMills.KP.UrsellRecurrence
import YangMills.KP.ClusterWeight
import YangMills.KP.PenrosePrep
import YangMills.KP.PenroseScheme
import YangMills.KP.PenroseBFS
import YangMills.KP.PenroseFiber
import YangMills.KP.WalkBound
import YangMills.KP.KPBound

-- Balaban gauge-RG layer (continuum track, `docs/BALABAN-RG-PLAN.md`).
-- B1: the block-lattice geometry (Bałaban CMP 98 eqs (1)–(3)); pure
-- lattice geometry, the substrate of the block-spin renormalization group.
-- B3-linear: the linear averaging operator Q (Bałaban CMP 95 eq (1.8)),
-- the Gaussian/small-field limit of the gauge-covariant averaging.
-- B2: coarse/fine block maps (block basepoint section, iterated-shift
-- coordinate formula; Bałaban CMP 98 (4)–(5), CMP 109 (0.4)/(0.12)).
-- B3-full (interface): Bałaban's axiomatic group average (CMP 109 eqs
-- (0.5)–(0.9), algebraic part) — the source-faithful route to the
-- non-abelian averaging operator Ū.
import YangMills.RG.BlockLattice
import YangMills.RG.LinearAveraging
import YangMills.RG.BlockMaps
import YangMills.RG.GroupAverage
-- B4-prep: the holonomy gauge-covariance law along a connected path
-- (Bałaban CMP 98 (11) / CMP 109 §0) — the foundation of `Ū` gauge covariance.
import YangMills.RG.HolonomyGauge
-- B4: gauge covariance of the averaged contour variable (CMP 109 (0.11)) —
-- the holonomy law (B4-prep) composed with the bi-equivariance of `M`.
import YangMills.RG.AveragedContour
-- matrix-`log` layer M-log-1: the near-identity logarithm series
-- log(1+Y) = Σ (-1)^{n+1}/n Y^n, its convergence and norm bound (the
-- analytic substrate of `Ū`, CMP 109 (0.12); built since Mathlib has no
-- Banach-algebra logarithm).
import YangMills.RG.NearLog
-- B4-Ū lattice bridge: a matrix realization of the abstract lattice gauge
-- group, transporting the holonomy gauge law into the matrix algebra where
-- `Ū`'s `exp`/`log` covariance lives.
import YangMills.RG.MatrixRealization
-- UV-U1 brick S1: the ℓ² averaging bound for `Q` — the `L^{1-d}` per-bond
-- mean-square contraction (deterministic seed of the small-field RG step).
import YangMills.RG.AveragingL2
-- Hilbert-space adjoint mass for the linear averaging operator:
-- the scaled `Q†Q` operator on the bond ℓ²/PiLp space, PSD with norm ≤ ‖Q‖².
import YangMills.RG.AveragingAdjoint
-- Abstract gauge-precision coercivity bookkeeping: a block Poincare/Hodge
-- estimate plus a positive `Q†Q` mass gives coercivity of `K + a Q†Q`.
import YangMills.RG.GaugePrecision
-- Operator-norm perturbation budgets for coercive continuous linear maps:
-- subtracting a summable perturbation family lowers the coercivity constant by
-- at most the summable norm budget.
import YangMills.RG.CoercivePerturbation
-- Gauge-fixed precision composition layer: base `K + a Q†Q` coercivity plus
-- summable and finite Schur-Catalan perturbation budgets.
import YangMills.RG.GaugeFixedPrecision
-- Exact finite-dimensional covariance from strict coercivity: construct the
-- inverse precision operator, prove both inverse identities, PSD, and the
-- operator bound `‖C‖ ≤ c⁻¹`.
import YangMills.RG.CoerciveCovariance
-- Abstract gauge-fixed covariance assembly: block-Poincare plus perturbation
-- budgets produce an exact inverse covariance for `K0 + a Q†Q - Σ`.
import YangMills.RG.GaugeFixedCovariance
-- Finite physical gauge-operator interface: positive-bond cochains, active
-- regions, flat coboundaries/gauge constraint, positive-bond block `Q`, and
-- the soft full-space precision shell `Kslice + a Q†Q`.
import YangMills.RG.PhysicalGaugeCochains
import YangMills.RG.PhysicalGaugeOperator
-- UV-S2 brick G3: the free RG step on a Gaussian field — the covariance
-- transformation law `Cov(μ.map Q) = Q·Cov(μ)·Qᵀ` (on Mathlib's IsGaussian),
-- the free fixed-point half of the small-field per-scale contraction.
import YangMills.RG.GaussianStep
-- Finite Gaussian block collar: the translated fluctuation kernel and product
-- block transform are probability measures before interacting activities enter.
import YangMills.RG.GaussianBlockKernel
-- UV audit-gap closer: the coupling-flow bridge — the only logical step
-- from Bałaban's faithful polymer bound `|R_k| ≤ A·g_k^{κ₀}` + coupling decay
-- `g_k ≤ C·rᵏ` to the surrogate `|R_k| ≤ M·rᵏ` the assembly consumes.
import YangMills.RG.CouplingFlowBridge
-- UV `hg` discharge: geometric coupling decay from the irrelevant logistic RG
-- recursion (`g_{k+1} ≤ r·g_k(1−β g_k)` ⟹ `g_k ≤ r^k·g_0`), composed with the
-- bridge into the geometric remainder bound. Honest caveat: irrelevant-operator
-- mechanism (4D marginal coupling is only logarithmic) — see the module header.
import YangMills.RG.CouplingFlow
-- The YM coupling is MARGINAL (asymptotically free, logarithmic), NOT geometric.
-- `g_k ≤ C·rᵏ` is false for YM; yet the marginal coupling still gives a summable
-- scale-series `∑ g_k^{κ₀}` for activity power `κ₀ > 1` (the honest YM coupling side).
import YangMills.RG.MarginalCoupling
-- UV `hpoly` summation step: the polymer cluster-sum bound — `|∑ activities|
-- ≤ amplitude·K₀` from Dimock's activity-decay + geometric-summability
-- estimates (carried hypotheses), and the assembled conditional geometric
-- remainder bound chaining cluster-sum → coupling decay → bridge.
import YangMills.RG.PolymerRemainder
-- Abstract activity-limit bridge: a profile bound uniform in a regulator
-- passes to the pointwise limiting activity.
import YangMills.RG.ActivityLimit
-- End-to-end UV conditional: composes the coupling-flow bridge with the banked
-- mass-gap assembly into one theorem — (RG remainder activity bound + coupling
-- decay) ⟹ the lattice mass gap. The §6.3 obligation in faithful assembled form.
import YangMills.RG.UVMassGap
-- Semantic split of the UV producer/consumer interface: raw activities,
-- renormalized with-holes activities, and scalar `SingleScaleUVDecay`, with
-- the summation bridge from hole activities to the scalar bound.
import YangMills.RG.SingleScaleUVDecay
-- Relative BV/BRST one-step retraction interface: an abstract homotopy identity
-- whose boundary defect can later be localized on holes before norms are taken.
import YangMills.RG.RelativeBVRetraction
-- Residual Appendix-F with-holes bridge: the loss `κ - 3κ₀ - 3` only feeds
-- the existing `κ₀`-geometric summability substrate under the explicit
-- stronger margin `κ₀ ≤ κ - 3κ₀ - 3` (e.g. `κ ≥ 4κ₀ + 3`).
import YangMills.RG.PolymerClusterWithHolesBridge
-- Residual summability interface: package a pointwise with-holes expansion
-- estimate and keep the residual-rate and reference-`κ₀` summation routes
-- formally separate.
import YangMills.RG.PolymerSummabilityBridge
-- Type-local functional/activity substrate for the constructive Dimock-F.1
-- compiler: local activities can only inspect restricted fields on their finite
-- supports; global adapters are invariant under changes off support.
import YangMills.RG.LocalFunctional
-- Ultralocal product-measure factorization for disjoint type-local supports:
-- the finite independence step used by future fluctuation-integral compilers.
import YangMills.RG.UltralocalFactorization
-- Raw Mayer transform on the type-local substrate: `H ↦ exp H - 1` preserves
-- supports, inherits off-support invariance, and satisfies the elementary
-- small-activity bound `‖exp H - 1‖ ≤ 2‖H‖`.
import YangMills.RG.RawMayerWithHoles
-- Ω-connected Mayer covers: source-shaped Ω-overlap graph on cover indices and
-- the finite product `∏ᵢ (exp Hᵢ - 1)` as a type-local activity with support
-- equal to the union of factor supports.
import YangMills.RG.OmegaConnectedCover
-- Appendix-F target covers: finite Ω-connected cover packages carrying the
-- explicit active target union consumed by future source-derived P3 estimates.
import YangMills.RG.AppendixFCover
-- Ultralocal factorization specialized to finite Mayer-cover products:
-- disconnected fluctuation-support components factor under product measure.
import YangMills.RG.MayerCoverFactorization
-- Appendix-F target-cover wrapper for the existing Ω-component Mayer
-- factorization, keeping the explicit active target union in the interface.
import YangMills.RG.AppendixFFactorization
-- Appendix-F finite-cover compiler: exact finite raw-Mayer expansion,
-- canonical Ω-connected component families, connected activity `K(Y)`,
-- grouping by target union, and local influence.
import YangMills.RG.AppendixFFiniteCover
-- The honest YM end-to-end UV conditional with the MARGINAL coupling: the
-- geometric-profile assembly generalized to any nonnegative summable scale
-- profile, specialized to the (asymptotically-free) marginal coupling flow.
import YangMills.RG.MarginalUVMassGap
-- Analytic substrate for the YM activity decay: the exponential-decay kernel
-- calculus (decay preserved under sum/scalar/composition — the Combes-Thomas /
-- Neumann-series engine), consuming the lattice exponential summability.
import YangMills.RG.KernelDecay
-- Schur boundedness of exponentially-decaying kernels (finite lattice): the
-- ℓ¹ row-sum bound and the quadratic-form (covariance) bound ≤ a·S.
import YangMills.RG.KernelSchur
-- Scalar Schur-Catalan budget closure: base coercivity remains positive when
-- finite multiscale defect budgets sum below the base coercivity.
import YangMills.RG.SchurCatalanBudget
-- PSD covariance-kernel interface: diagonal/variance bounds and the covariance
-- Cauchy–Schwarz, connecting ExpDecay/Schur to the Gaussian covariance form.
import YangMills.RG.CovarianceKernel
-- Gaussian field-size / MGF bound from a covariance bound: a Gaussian
-- fluctuation field with bounded covariance has bounded exponential moments.
import YangMills.RG.GaussianMGF
-- The finite-dimensional multivariate Gaussian as a concrete `IsGaussian` measure
-- (`isGaussian_pi`) and its closure under linear images (`isGaussian_pi_map_clm`) —
-- the missing constructive Gaussian-from-covariance object the fluctuation integral
-- consumes; built from Mathlib's `iIndepFun.hasGaussianLaw`.
import YangMills.RG.GaussianPi
-- CMP116 small-field bridge seed: after `B' = (C^(k))^(1/2) X`, the `X`
-- fluctuation law `dmu0` is an ultralocal product Gaussian over bonds.
import YangMills.RG.BalabanCMP116Dmu0
-- CMP116 localization bridge: once Balaban's generalized random-walk support
-- theorem supplies localized `H(Z)` supports, `dmu0` gives Ω-component
-- factorization for the Appendix-F local-activity substrate.
import YangMills.RG.BalabanCMP116Localization
-- CMP116-to-Appendix-F `K#` adapter: localized Balaban activities feed the
-- first connected with-holes compiler and its rooted estimate under explicit
-- source support/decay/integrability obligations.
import YangMills.RG.BalabanCMP116KsharpAdapter
-- CMP116-to-second-gas adapter: the specialized `K#` activity becomes the
-- evaluated and spectator-integrated hard-core gas consumed by the `H#` layer.
import YangMills.RG.BalabanCMP116SecondGasAdapter
-- hRpoly campaign brick P1a: the bounded-degree walk-count engine (≤ Δⁿ) — the
-- combinatorial substrate for the lattice animal count `c_n ≤ Cⁿ` (branch C of
-- `hRpoly`). Pure graph combinatorics; consumer = animal count → polymer_weight_summability.
import YangMills.RG.AnimalCount
-- hRpoly campaign bricks P1b/P1c: the spanning closed walk (tree Euler tour)
-- and the lattice animal count `c_n ≤ Δ^{2(n-1)}` (branch C of `hRpoly`).
import YangMills.RG.AnimalTour
-- hRpoly campaign P2 geometry: the M-cube king-adjacency graph (Dimock II
-- §3.1.2), its degree bound ≤ 3^d, and the concrete lattice polymer summability.
import YangMills.RG.CubeLattice

-- hRpoly campaign brick P2b-i: polymer modified metric
import YangMills.RG.ModifiedMetric
-- hRpoly P3 substrate: touching hard-core hole polymers plus the source-facing
-- Appendix-F `Ω`-active polymer system, with local KP consumers for both.
import YangMills.RG.HolePolymerSystem
import YangMills.RG.Translation
import YangMills.RG.LocalKP
import YangMills.RG.ClusterDecay
-- Source-faithful Appendix-F hole targets: skeleton connectivity, full target unions.
import YangMills.RG.AppendixFHoleTarget
-- Source-faithful two-support Appendix-F finite target-family compiler:
-- active-skeleton hard-core admissibility, full-target fiber activities, and
-- the exact finite reindexing back to the raw Mayer product.
import YangMills.RG.AppendixFHoleTargetFamily
-- First integrated Appendix-F activity K#: turn the connected local activity
-- K(Y,ψ,φ) into the fluctuation-integrated local functional K#(Y,ψ), with
-- explicit integrability in norm bounds.
import YangMills.RG.AppendixFKsharp
-- Finite quantitative first-activity step above the target-family compiler:
-- a raw exponential pointwise bound yields a connected-cover metric majorant.
import YangMills.RG.AppendixFQuantitative
-- Finite target-fiber entropy step: overcount a target fiber by the nonempty
-- powerset of raw supports contained in the target and absorb it into exp(sum)-1.
import YangMills.RG.AppendixFFiberEntropy
-- Appendix-F local modified-metric summability adapters: restrict rooted
-- geometric sums to finite raw families and convert rooted control to
-- target-contained local control.
import YangMills.RG.AppendixFLocalSummability
-- Source-shaped first K# estimate: raw metric decay plus local summability
-- give the exact exponential-minus-one K(Y) bound and its integrated K# form.
import YangMills.RG.AppendixFKsharpEstimate
-- Second Appendix-F hard-core gas: evaluated K# becomes the scalar activity
-- of the source-facing omega-hole polymer system, with KP kept as an explicit
-- majorant hypothesis.
import YangMills.RG.AppendixFSecondGas
-- Second Ursell layer H#: union-fiber fixed-size terms and the totalized
-- target activity, with convergence and residual estimates kept explicit for
-- later source theorems.
import YangMills.RG.AppendixFHsharp
-- Residual H# adapter: a source-supplied complex-norm bound for the second
-- Ursell activity feeds the real omega-rooted `SingleScaleUVDecay` producer.
import YangMills.RG.AppendixFHsharpResidual
-- Finite partial H# truncations: convergence-free Ursell partial sums and the
-- same residual UV adapter at finite cutoff.
import YangMills.RG.AppendixFHsharpPartial
-- Convergence interface for H# truncations: summability of fixed-target terms
-- plus uniform finite-partial bounds feeds the totalized residual adapter.
import YangMills.RG.AppendixFHsharpConvergence
-- Pointwise limit API for H# truncations: explicit convergence hypotheses
-- transfer uniform finite-cutoff bounds to the totalized H# activity.
import YangMills.RG.AppendixFHsharpLimit
-- Termwise majorant API for H#: a summable second-Ursell majorant supplies
-- fixed-target summability, finite-partial bounds, tails, and the UV consumer.
import YangMills.RG.AppendixFHsharpMajorant
-- Closed-form geometric H# majorants: term bounds of the form A·q^n discharge
-- the summability, finite-partial, tail, and total residual bookkeeping.
import YangMills.RG.AppendixFHsharpGeometricMajorant
-- Triple-infinity closure: a root factor, geometric leaf budget, rooted
-- target summability, and scale summability give a single total influence
-- bound over expansion order, target geometry, and RG scales.
import YangMills.RG.TripleInfinityClosure
-- Source-facing absolute H# majorant bridge: finite absolute union-fiber
-- terms feed packaged geometric source contracts and the existing consumers.
import YangMills.RG.AppendixFHsharpSourceMajorant
-- Finite source-facing tree majorant for H#: Penrose tree-graph domination
-- of the exact fixed-union absolute second-Ursell coefficient.
import YangMills.RG.AppendixFSecondUrsellSource
-- Weighted finite tree transfer for H#: separates the activity-size factor
-- from the geometric/source leaf-summation obligation.
import YangMills.RG.AppendixFSecondUrsellWeightedTree
-- Finite marker insertion for weighted H#: target skeleton membership marks
-- at least one vertex inside every fixed-union tree tuple.
import YangMills.RG.AppendixFSecondUrsellMarkedFugacity
-- Finite second-Ursell geometry: a KP tree in the omega-hole polymer system
-- stitches leaf modified metrics into the modified metric of the full union.
import YangMills.RG.AppendixFSecondUrsellGeometry
-- Finite leaf-summation input for weighted H#: packages the hard-core
-- neighbor moment estimate as a nonnegative child-choice kernel.
import YangMills.RG.AppendixFSecondUrsellLeafSummation
-- Elementary half-budget closure for the second-Ursell denominator obligations.
import YangMills.RG.AppendixFSecondUrsellClosure
-- Source-facing cluster3 hole geometry: package holes/Ω/skeletons and expose
-- the rooted local incompatibility contract for direct Dimock-II inputs.
import YangMills.RG.AppendixFCluster3Geometry
-- Source-facing closed Dimock-II `cluster3` contract for H#: consumes the
-- final Appendix-F with-holes theorem directly, while keeping the Yang-Mills
-- input decay/locality obligations explicit.
import YangMills.RG.AppendixFHsharpCluster3
-- CMP116-specialized H# consumers: source/tree majorants and cluster3
-- contracts for the spectator-integrated first activity with dmu0 fixed.
import YangMills.RG.BalabanCMP116HsharpAdapter
-- Source-facing H# profile: a single packaged geometric majorant record
-- exposes summability, tail, residual, and UV consumers.
import YangMills.RG.AppendixFHsharpProfile
-- CMP116 source-facing H# contracts: source theorems stated directly for the
-- named CMP116 integrated H# object package into cluster3/profile consumers.
import YangMills.RG.BalabanCMP116HsharpSource
-- Marked-vertex source contracts for H#: a bound on the root-marked
-- vertex-product sum feeds the CMP116 profile/cluster3/UV consumers.
import YangMills.RG.AppendixFHsharpMarkedVertexSource
-- Leaf-summation source contracts for H#: the finite marked-root
-- leaf-summation theorem feeds the CMP116 profile/cluster3/UV consumers.
import YangMills.RG.AppendixFHsharpLeafSource
import YangMills.RG.Ubar
-- Abstract approximate Ward-complex layer: if a local activity decomposes as
-- Q-exact plus a remainder, the Q-exact contribution is killed up to a
-- quantitative Ward defect before norms are applied.
import YangMills.SUSY.WardComplex
-- Cohomological valence-carry interface: closed-shell contraction
-- Q h + h Q = id - Π leaves only valence under Ward cancellation.
import YangMills.SUSY.ValenceCarry
-- Algebraic finite Berezin substrate: the top-coefficient functional on a
-- finite complex exterior algebra, the first concrete layer underneath future
-- supergaussian/Ward-model instantiations.
import YangMills.SUSY.FiniteBerezin
-- Ward-cancelled polymer activities: exact/approximate Ward decomposition
-- hypotheses feed the source-facing `Ω`-active skeleton-tail consumer.
import YangMills.SUSY.WardPolymer
