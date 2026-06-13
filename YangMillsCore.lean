/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

/-
# YangMillsCore — the sound, self-contained core of the project

This root module imports **only** the parts of the development that are:

* mathematically sound (no `sorry`, no project-specific axioms),
* genuinely about Yang–Mills / SU(N) (not a vacuous target predicate), and
* structurally separable from the LSI / Balaban-RG sprawl.

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
LSI/Bakry–Émery pipeline, the Balaban-RG packet/coherence/frontier sprawl, and
the ~25 BFS-dead axioms.  They route only to the empty `∃ m > 0` statement;
keeping them out of this root is the point.  `CLEANUP_PLAN.md` lists them and
the staged plan for removing them once this core is confirmed green.
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
-- NOTE: SchurEntryOffDiag bit-rotted against current Mathlib (v4.29):
--   `star_mul` ambiguous, `Filter.EventuallyEq.of_forall` removed, NeZero synthesis.
--   Excluded from the verified core until repaired; not needed by the headline results.
-- import YangMills.ClayCore.SchurEntryOffDiag
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

-- Kotecký–Preiss / Mayer cluster-expansion layer (`docs/kp-cluster-expansion-plan.md`).
-- KP0–KP2a (substrate, partition identities, incompatibility graph, Ursell coefficient)
-- plus the KP2b attack: the cluster sum (Mayer RHS), its support on clusters, the
-- empty-system and first-order checks of `Ξ = exp(clusterSum)`, and the KP smallness
-- criterion with its base estimates.  The general Ursell value on complete graphs and
-- the inductive KP convergence bound remain open (and are NOT imported as axioms).
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
