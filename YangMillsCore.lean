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
import YangMills.KP.RootedCatalanExact
import YangMills.KP.RootedCatalanMajorant
import YangMills.KP.SharpMajorant
import YangMills.KP.ActivityDomain
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
-- Finite physical gauge interfaces: full-periodic positive-bond cochains,
-- their flat Hodge/block-Poincare predicate, and the separate active-region
-- soft full-space precision shell `Kslice + a Q†Q`.
import YangMills.RG.PhysicalGaugeCochains
import YangMills.RG.FiniteTorusCurlDiv
import YangMills.RG.PhysicalGaugeFlatPoincare
import YangMills.RG.PhysicalGaugeFixedPrecision
import YangMills.RG.PhysicalGaugeCovarianceLocalization
import YangMills.RG.PhysicalGaugeCMP116OperatorTransport
import YangMills.RG.PhysicalGaugeFluctuationActivity
import YangMills.RG.PhysicalGaugeCMP116ActivityAdapter
import YangMills.RG.PhysicalGaugeHodgePoincare
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
-- Experimental PR1 substrate for finite killed-region walks and isometric
-- transport sums; the concrete matrix-unitary bridge remains open.
import YangMills.RG.Diamagnetic
-- UV `hpoly` summation step: the polymer cluster-sum bound — `|∑ activities|
-- ≤ amplitude·K₀` from Dimock's activity-decay + geometric-summability
-- estimates (carried hypotheses), and the assembled conditional geometric
-- remainder bound chaining cluster-sum → coupling decay → bridge.
import YangMills.RG.PolymerRemainder
-- Abstract activity-limit bridge: a profile bound uniform in a regulator
-- passes to the pointwise limiting activity.
import YangMills.RG.ActivityLimit
-- Source-independent activity error budgets: source-shaped activity plus
-- covariance/dictionary/support/Jacobian defects combine by a minimum-rate
-- triangle inequality before feeding the `hRpoly` frontier.
import YangMills.RG.YMActivityBudget
-- End-to-end UV conditional: composes the coupling-flow bridge with the banked
-- mass-gap assembly into one theorem — (RG remainder activity bound + coupling
-- decay) ⟹ the lattice mass gap. The §6.3 obligation in faithful assembled form.
import YangMills.RG.UVMassGap
-- Semantic split of the UV producer/consumer interface: raw activities,
-- renormalized with-holes activities, and scalar `SingleScaleUVDecay`, with
-- the summation bridge from hole activities to the scalar bound.
import YangMills.RG.SingleScaleUVDecay
-- UV-facing consumer for the activity error budget: component estimates for a
-- source-shaped activity and four named defects produce `RawYMActivityDecay`.
import YangMills.RG.YMActivityBudgetUV
-- Source-only specialization of the UV activity consumers: when the raw
-- activity is definitionally a source term, the four defect obligations and
-- finite-carrier profile summability are theorem-fed.
import YangMills.RG.SourceOnlyUVDecay
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
-- Resolvent-first local precision layer: finite-range/small Neumann data give
-- resolvent decay, and inverse-square-root binomial tails obey geometric
-- scalar bounds before any physical Hessian/root theorem is claimed.
import YangMills.RG.LocalSPDPrecision
-- Physical local-SPD covariance-root frontier: normalized finite-range
-- physical precision data derive coercivity/exact covariance and package the
-- remaining source-supplied root/kernel fields into the existing certificate.
import YangMills.RG.PhysicalGaugeLocalSPDPrecisionRoot
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
import YangMills.RG.BalabanCMP116QuadraticGaussian
import YangMills.RG.BalabanCMP116GaussianOrthogonal
import YangMills.RG.BalabanCMP116QuadraticGaussianSpectral
import YangMills.RG.BalabanCMP116QuadraticGaussianMatrix
import YangMills.RG.BalabanCMP116Eq223Gaussian
import YangMills.RG.BalabanCMP116CorrelatedGaussian
-- The finite-dimensional multivariate Gaussian as a concrete `IsGaussian` measure
-- (`isGaussian_pi`) and its closure under linear images (`isGaussian_pi_map_clm`) —
-- the missing constructive Gaussian-from-covariance object the fluctuation integral
-- consumes; built from Mathlib's `iIndepFun.hasGaussianLaw`.
import YangMills.RG.GaussianPi
-- CMP116 small-field bridge seed: after `B' = (C^(k))^(1/2) X`, the `X`
-- fluctuation law `dmu0` is an ultralocal product Gaussian over bonds.
import YangMills.RG.BalabanCMP116Dmu0
-- Finite physical/CMP116 coordinate dictionary: exact scalar-coordinate
-- packing between CMP116 cube fields and physical positive-bond cochains,
-- with support-agreement transfer but no analytic raw-activity assertion.
import YangMills.RG.PhysicalGaugeCMP116Dictionary
-- Dictionary-backed construction layer: canonical continuous coordinate map,
-- root transport, Gaussian-change record, localized family, and transport
-- constructors without new analytic estimates.
import YangMills.RG.PhysicalGaugeCMP116ActivityConstruction
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
-- hRpoly P2a consumer bridge: rooted animal/cube summability now feeds
-- `SingleScaleUVDecay` directly, removing the external `hwsum`/`hwK`
-- obligations on the finite rooted-connected cube-polymer route.
import YangMills.RG.HRpolyAnimalSummability

-- hRpoly campaign brick P2b-i: polymer modified metric
import YangMills.RG.ModifiedMetric
-- Exact finite support calculus for CMP116 linear operators before raw
-- activity construction.
import YangMills.RG.LocalLinearOperator
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
-- Canonical-root K# estimates: the rooted modified-metric summability theorem
-- discharges the K# estimator's `hroot` premise.
import YangMills.RG.AppendixFKsharpCanonicalRoot
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
-- Certified finite-prefix/geometric-tail H# majorants: finite checked prefix
-- plus closed geometric tail discharges summability and total `tsum` budget.
import YangMills.RG.AppendixFHsharpCertifiedTail
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
-- Source-fed residual H# bound: Dimock-II rate extraction feeds the all-tail
-- certified residual theorem without exposing intermediate tree bookkeeping.
import YangMills.RG.AppendixFHsharpSourceResidual
-- Canonical-root source-fed residual H# bound: raw metric decay plus the
-- canonical-root half-budget/profile conditions feed the residual theorem
-- without exposing the intermediate K# activity hypothesis.
import YangMills.RG.AppendixFHsharpSourceResidualCanonicalRoot
-- hRpoly P3.5 brick B2: bounded-hole cardinality compression
-- #X ≤ (1+3^d·B)·(d_M(X)+1), discharging the carried card-le-metric binder of
-- the K#-estimate tilt lemmas; with bulk-exactness and genuine-hole strict
-- non-vacuity guards (method deviation vs Dimock's Gaussian hole payment
-- recorded in docs/HRPOLY-CAMPAIGN-PLAN.md §3bis).
import YangMills.RG.AppendixFHoleCompression
-- hRpoly P3.5 brick B3: residual H# decay plus the bounded-hole cardinality
-- tilt now supplies the exact pointwise hact majorant and the volume-uniform
-- active-skeleton KP criterion.  The raw YM residual estimate remains explicit.
import YangMills.RG.AppendixFHsharpCardTilt
-- hRpoly P3.5 brick B4: explicit nonzero constant-activity witness showing
-- that the complete conditional B1--B3 parameter region is jointly inhabited.
import YangMills.RG.AppendixFEndToEndWitness
-- Source-facing composition: raw metric decay now feeds the actual integrated
-- H# activity and then the B3 active-skeleton KP criterion without a residual
-- H# hypothesis at the call site.
import YangMills.RG.AppendixFHsharpRawToKP
-- hRpoly P3.5 brick B1: numeric parameter witness — κ₀(d) collapses the
-- Appendix-F geometric smallness to EXACTLY e⁻¹; root/moment/leaf constants
-- bounded (2/2/16); the O2 joint witness (κ₀, 4κ₀+3, H₀=1/256) with factor-2
-- half-budget margin; plus the θ-shifted residual budget identity for B3.
import YangMills.RG.AppendixFParameterWitness
-- hRpoly P4-CT bricks CT1+CT2 (O1 attack, propagator-decay leg): the coercive
-- Combes-Thomas route on PHYSICAL gauge cochains — exponential tilt algebra,
-- conjugation entry identity, range preservation, block Schur bound
-- ‖A‖ ≤ β·N_R, tilt perturbation bound ‖K_θ−K‖ ≤ M(e^{θR}−1)N_R, and
-- coercivity survival for the tilted operator.  Interface = the same probes
-- and predicates as PhysicalGaugeCovarianceLocalization, so CT4 can
-- instantiate literally on flatGaugeFixedPrecision/CovarianceCLM.
import YangMills.RG.PhysicalCoerciveCombesThomas
-- hRpoly P4-CT, owner obligation 1: the CONCRETE physicalBondDist —
-- circular ZMod distance (four-case min triangle), Chebyshev site distance,
-- discrete direction join; symmetry, triangle, dist p p = 0, and the
-- explicit ball bound N_R = (2(R+1))^d · d consumed by the CT2 Schur bound.
import YangMills.RG.PhysicalBondDistance
-- hRpoly P4-CT, toward owner obligation 2: Gram-kernel calculus for adjoint
-- compositions B†B — probe Gram identity, finite range from probe-image
-- orthogonality, kernel bound M² via the ‖y‖² trick, and sum/smul assembly
-- combinators for K₀ + a·Q†Q.  The concrete D1/div/Q stencil inputs are the
-- next brick; nothing here localizes flatGaugeFixedPrecisionCLM yet.
import YangMills.RG.PhysicalGramKernel
-- hRpoly P4-CT, owner obligation 2 FIRST SHELL TERM: concrete locality of the
-- flat curl D1†D1 — plaquette bond slots within distance 1 of the base slot,
-- Gram orthogonality beyond distance 2, probe-image bound 4d via per-slot
-- plaquette counting; endpoints FiniteRange (D1†D1) physicalBondDist 2 and
-- KernelBound (4d)² for the CONCRETE operator at trivial background.
import YangMills.RG.PhysicalShellLocalityD1
-- hRpoly P4-CT, owner obligation 2 SECOND SHELL TERM: concrete locality of
-- the flat backward divergence div†div — both slot sites within distance 1
-- of the evaluation site, Gram orthogonality beyond 2, probe-image bound 2
-- (each slot family has exactly one global match via shiftBack bijectivity);
-- endpoints FiniteRange (div†div) physicalBondDist 2 and KernelBound 2².
-- Common range 2 with the curl term for the K₀ assembly.
import YangMills.RG.PhysicalShellLocalityDiv
-- hRpoly P4-CT, owner obligations 2 (COMPLETE) + 3: the long-stencil block
-- constraint Q†Q — same-block diameter L−1, iterate-shift reach, Gram
-- orthogonality beyond 3L, probe bound L via block partition + shift^[k]
-- bijectivity (no block counting); assembled base precision K₀ + a·Q†Q at
-- range 3L with bound (4d)²+4+|a|L²; and the named zeroSigma free shell:
-- flatGaugeFixedPrecisionCLM with the Empty Sigma family IS the base
-- precision (empty tsum, nothing hidden in norm hypotheses).
import YangMills.RG.PhysicalShellLocalityQ
-- hRpoly P4-CT bricks CT3+CT4: the tilted inverse at the θ-budget
-- M(e^{θR}−1)N_R ≤ c/2 (coercivity survives at c/2, two-sided inverse of
-- norm ≤ 2/c via covarianceOfIsCoerciveCLM) and the Combes–Thomas kernel
-- extraction at r := source — any right inverse of a coercive finite-range
-- operator satisfies PhysicalCovarianceExponentialKernelBound C dist (2/c) θ;
-- plus the explicit positive-tilt witness θ = log(1+c/(2MN_R))/(R+1).
import YangMills.RG.PhysicalCoerciveCombesThomasInverse
-- hRpoly P4-CT ENDPOINT CT_fixedVolume (owner acceptance criterion): the
-- fixed-volume flat physical covariance at the zeroSigma free shell is
-- exponentially localized in physicalBondDist with amplitude 2/c at the
-- proved shell constants (M = (4d)²+4+|a|L², R = 3L, N_R = (2(3L+1))^d·d,
-- c = min 1 a / CP), including the positive-rate existence form.
import YangMills.RG.PhysicalShellCombesThomasEndpoint
-- P4-CT non-vacuity audit (external-review finding 2026-07-13): the NAMED
-- trivial SUNAdjointModel witness (exact for the flat lane, where only
-- adCLM 1 is consumed), Nonempty for the ρ-generic hypothesis class, and
-- the capstone CT_fixedVolume_nonvacuous — model, Poincaré constant, and
-- positive rate all EXIST for every volume and every a > 0, every
-- structural hypothesis discharged by proved theorems.  The TRUE matricial
-- adjoint model is registered open (plan §3ter, P4-ADJ).
import YangMills.RG.SUNAdjointModelWitness
-- P4-ADJ brick 1 (plan §3ter): the matricial su(n) substrate — su(n) as a
-- real submodule of complex matrices (skew-Hermitian + traceless), the trace
-- form re tr(Xᴴ·Y) with symmetry/positivity/definiteness (PSD trace order),
-- and the adjoint action Ad(g)X = g·X·gᴴ of the special unitary group:
-- preserves the submodule, preserves the trace form (the ad_inner
-- orthogonality at matrix level), and is a real-linear group action.
-- Bricks 2-3 (coordinate isometry with SUNLieCoord, finrank = n²−1, the
-- SUNAdjointModel instance) remain open.
import YangMills.RG.SUNAdjointMatrixSubstrate
-- P4-ADJ brick 2a: the inner-product packaging of su(n) — SuLie n type
-- synonym (anti-diamond), the trace form as a genuine InnerProductSpace ℝ
-- instance via PreInnerProductSpace.Core + definite, and the adjoint action
-- packaged as a linear map on the subtype with inner/norm preservation and
-- the group-action laws.  Brick 2b (finrank = n²−1) and brick 3 (isometric
-- transport to SUNLieCoord + the SUNAdjointModel instance) remain open.
import YangMills.RG.SUNAdjointInnerSpace
-- P4-ADJ brick 2b (THE HARD PIECE): finrank ℝ su(n) = n²−1 — explicit
-- Hermitian/skew decomposition Matrix ≃ self × skew, multiplication-by-i
-- equivalence self ≃ skew, ambient real dimension 2n² via the entry-module
-- generalized finrank_matrix, hence finrank skew = n²; the imaginary-trace
-- functional (composition of linear maps, surjective via i·𝟙) with
-- su(n) ≃ its kernel, and rank-nullity closes the count.  Brick 3 (the
-- isometric transport to SUNLieCoord + the SUNAdjointModel instance)
-- remains open.
import YangMills.RG.SUNAdjointDimension
-- P4-ADJ brick 3 (THE LAST BRICK — P4-ADJ CLOSED): the TRUE adjoint model.
-- Module.Finite ℝ su(n) by the Noetherian route (subtype injection into the
-- finite ambient matrix space), the isometric coordinate transport
-- suLieCoordIso : SuLie n ≃ₗᵢ[ℝ] SUNLieCoord n (stdOrthonormalBasis reindexed
-- along the brick-2b count), and matrixSUNAdjointModel : SUNAdjointModel n —
-- Ad(g) X = g·X·gᴴ read through fixed orthonormal coordinates, with
-- ad_one/ad_mul from the brick-2a action laws and ad_inner from
-- inner_suAdActLin transported by inner_map_map.  The Addendum-477 trivial
-- witness is no longer the only instance.
import YangMills.RG.SUNAdjointModelInstance
-- The volume-uniform Poincaré WALL (post-P4-ADJ lane, W-1): the fixed-volume
-- constant-sector audit promoted to the honest obstruction — every flat
-- block-Poincaré constant obeys L^d/L^2 ≤ CP (witness discharged, Nc ≥ 2),
-- hence L ≤ CP for d ≥ 3; the CT coercivity min 1 a / CP through this route
-- dies as L → ∞ (no positive c₀ survives all volumes,
-- no_volumeUniform_coercivity_via_flatPoincare), and the uniform-constant
-- gate VolumeUniformFlatPoincareGate is PROVED FALSE.  Non-vacuity: the
-- per-volume constants exist (perVolume_flatPoincare_family).  A
-- volume-uniform CT must re-route (rescaled block map, sector quotient, or
-- interacting-Hessian coercivity).
import YangMills.RG.PhysicalPoincareWall
-- W-2 (continuation (b) of the wall): the constant-sector quotient interface.
-- The constant sector packaged as a linear inclusion (harmonic under the flat
-- Hodge operator — WHY it is the dangerous sector), the fluctuation space as
-- generator-wise orthogonality (IsFluctuationCochain; the Submodule.orthogonal
-- route whnf-times-out at this pin), the quotient Poincaré predicate, full →
-- quotient at the same constant, fixed-volume non-vacuity, THE NON-TRANSFER
-- LEMMA (the W-1 wall witness is excluded from the fluctuation space by
-- construction), and the volume-uniform quotient gate — REGISTERED OPEN,
-- neither proved nor refuted; W-3 (the lowest-mode falsifier) is ONE-SIDED:
-- it can refute the gate (second wall) but a bounded mode only keeps the
-- route open — proving the gate needs an all-modes/spectral estimate.
import YangMills.RG.PhysicalPoincareSectorQuotient
-- W-3a (the falsifier's witness family, first brick of the W-3 ladder): the
-- half-period ±1 square profile on even circles (exact zero-sum identity, no
-- trigonometry), the lowest-mode cochain (oscillation direction j, bond
-- direction i, internal vector w), EXACT orthogonality to every constant
-- generator (IsFluctuationCochain proved), the exact norm (M+M)^d·‖w‖²,
-- genuine non-constancy, and non-vacuity of the fluctuation space (Nc ≥ 2).
-- W-3 remains a ONE-SIDED falsifier; the quadratic-form evaluation (Hodge
-- term W-3b, block term + Rayleigh quotient + endpoint W-3c) is registered,
-- and no gate claim is made in either direction.
import YangMills.RG.PhysicalPoincareLowModeFalsifier
-- W-3b (the exact Hodge term on the falsifier family): the two-interface
-- square mode has flat-Hodge energy exactly 8·(M+M)^(d-1)·‖w‖².  The
-- mechanism is separated: i=j gives zero curl and the full divergence
-- energy; i≠j gives zero divergence and the full curl energy in the unique
-- ordered {i,j} plane.  Even side, positive dimension/half-period/internal
-- rank remain explicit.  W-3c below supplies the physical block response,
-- Rayleigh lower-bound divergence, and the resulting second wall.
import YangMills.RG.PhysicalPoincareLowModeHodge
import YangMills.RG.PhysicalPoincareLowModeBlock
-- Raw-source CMP116 family consumer: source-packaged physical activities feed
-- the source-measurable H# endpoint by discharging its `hraw` premise.
import YangMills.RG.PhysicalGaugeCMP116RawHsharp
-- Raw-source CMP116/H# consumer for the marginal lattice M3 assembly.
import YangMills.RG.PhysicalGaugeCMP116RawM3
-- Executable dependency graph for the raw-source M3 frontier fields.
import YangMills.RG.M3FrontierDependencies
-- CMP116 Lemma 3 activity-only lane: isolated Nat-source-metric estimate
-- interface, finite resummation bridge, and downstream raw-source adapters.
import YangMills.RG.BalabanCMP116Lemma3Estimate
import YangMills.RG.BalabanCMP116Lemma3
import YangMills.RG.BalabanCMP116Eq23Cutoff
import YangMills.RG.BalabanCMP116Eq23PhysicalBondIndex
import YangMills.RG.BalabanCMP116Eq214Cauchy
import YangMills.RG.BalabanCMP116Eq214Geometry
import YangMills.RG.BalabanCMP116Eq214Incidence
import YangMills.RG.BalabanCMP116Eq214Interior
import YangMills.RG.BalabanCMP116Eq214LocalizationCore
import YangMills.RG.BalabanCMP116Eq214PhysicalIndices
import YangMills.RG.BalabanCMP116Eq214PhysicalResummation
import YangMills.RG.BalabanCMP116Eq214PhysicalTerm
import YangMills.RG.BalabanCMP116Eq214AnalyticResummation
import YangMills.RG.BalabanCMP116Eq214CauchyEstimate
import YangMills.RG.BalabanCMP116Eq214CauchyMajorant
import YangMills.RG.BalabanCMP116Eq214IntegrandEstimate
import YangMills.RG.BalabanCMP116Eq214FiniteGaussianData
import YangMills.RG.BalabanCMP116Eq214FiniteGaussianMajorant
import YangMills.RG.BalabanCMP116Eq214FiniteGaussianResidualStages
import YangMills.RG.BalabanCMP116Eq229
import YangMills.RG.BalabanCMP116Eq229Criteria
import YangMills.RG.BalabanCMP116Eq229CammarotaSource
import YangMills.RG.BalabanCMP116Eq231
import YangMills.RG.BalabanCMP116Lemma3ResidualStages
import YangMills.RG.BalabanCMP116Lemma3RawSourceAdapter
import YangMills.RG.BalabanCMP116Lemma3ScaleFamily
import YangMills.RG.BalabanCMP116Eq237
import YangMills.RG.BalabanCMP116Lemma3AdmissibleAdapter
-- Source-facing Balaban CMP116 theorem target with the raw-source package
-- unfolded into individually auditable source fields.
import YangMills.RG.BalabanCMP116SourceTheorem
-- Named frontier for the raw-source CMP116/H# hypothesis surface.
import YangMills.RG.PhysicalGaugeCMP116RawHsharpFrontier
-- Single-scale source dictionary for the Wilson Hessian / Green inverse:
-- keeps CMP102 expansion, CMP99 Green identification, inverse-on-slice,
-- sign/normalization, and covariance transport separate from roots/pushforwards.
import YangMills.RG.PhysicalGaugeWilsonHessianDictionary
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
import YangMills.RG.CorrelatorBridge
-- RG-provenant correlator bridge (C6 B-1'): step-generated effective family,
-- telescoping decomposition theorem, Rsc PRODUCED not selected, honest gate.
import YangMills.RG.CorrelatorBridgeProvenance

-- Concrete gauge RG step (C6 B-1''): defined decimation blockMap 2M -> M,
-- effective measure BY CONSTRUCTION (no step field), multi-scale tower over
-- sizes 2^n*M0, produced Rsc, volume-uniform gate (constants before volumes).
import YangMills.RG.ConcreteGaugeRGStep

-- Physical fidelity of the concrete RG step (C6 B-1'''): plaquette-embedding
-- metric transport (factor-3 general bound; naive factor 2 refuted; EXACT
-- factor 2 on the canonical pair family), canonical/sup correlators replacing
-- the Classical.choose ray pair, scale-corrected tower telescoping at ONE
-- physical separation, Wilson probability instances threaded through the
-- tower, typed dyadic sufficiency (cofinality + literal-gate implication).
import YangMills.RG.ConcreteGaugeRGFidelity

-- Literal-gate integration + de-lacunarization + observable-support
-- transport (C6 B-1''''): integrated literal fidelity gate (one constant
-- pack before base AND depth, honest M0 >= 4 guard), covering arithmetic
-- with the formalized odd/small-t refutations, the all-separations
-- (thermodynamic-form) canonical gate with the unconditional literal->
-- forall-t and forall-t->dyadic implications, the named open
-- doubling-domination clause with the proved conditional tower
-- de-lacunarization, blockPlaquetteSupport (the 2x2 fine loop, 8 edges,
-- pullback locality, radius-2 ball) and the canonical support separation
-- lower bound 2*tau - 3 (walk and dist forms); k-step support object as a
-- definition (metric theorem open).
import YangMills.RG.ConcreteGaugeRGLiteralGate
import YangMills.RG.ConcreteGaugeRGTerminalGate
import YangMills.RG.ConcreteGaugeRGPhysicalGate
-- B-1^7 (Amendment 7): the operational support theorem - the k-fold
-- composed block map (towerMeasure as literal pushforward), the k-step
-- pullback-support congruence, the three-term integration identity, the
-- terminal support bridge importing the B-1^6 separation metric onto the
-- operational supports, and the capstone terminal_support_certified in
-- the exact objects of the physical gate's IR clause.
import YangMills.RG.ConcreteGaugeRGSupport
