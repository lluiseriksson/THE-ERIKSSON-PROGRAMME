/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceEq395TerminalReindex

/-!
# Ambient physical decay of the CMP99 equation (3.95) global middle

The global source region in equation (3.95) is the complete coarse torus.
This file identifies the existing ambient middle exactly with zero extension
and restriction of the source-reindexed generated middle.  Since the region
is `univ`, its exponential kernel estimate then transfers to the literal
ambient operator with no support loss or volume-dependent constant.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {M Nc Q : ℕ} [NeZero M] [NeZero Nc] [NeZero Q]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- Explicit isometric reindexing agrees with the dependent Hilbert-bundle
transport used by the generated tower. -/
theorem cmp99Eq395GeneratedPhysicalMiddleOnSource_eq_transport
    (Omega : ActiveGaugeRegion 4 (2 * Q))
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    let regions := cmp99SourceIteratedLiftActiveRegionChain
      (M := M) Omega (depth + 1)
    let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
    let hPhys :=
      cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
        (Nc := Nc) (M := M) Omega (depth + 1)
    let h := hCoord.symm.trans hPhys
    cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
        background budget fineSmall hsmall =
      cmp99SourceTerminalCLMTransport h h
        (cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing background
          budget fineSmall hsmall) := by
  apply ContinuousLinearMap.ext
  intro f
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let hsite := cmp99SourceIteratedLiftActiveRegionChain_terminalSite_eq
    (M := M) Omega (depth + 1)
  let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhys :=
    cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
      (Nc := Nc) (M := M) Omega (depth + 1)
  let h := hCoord.symm.trans hPhys
  let G := cmp99Eq395GeneratedPhysicalMiddle Omega hM depth hspacing
    background budget fineSmall hsmall
  let sourceBack :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (Equiv.cast hsite).symm).toContinuousLinearEquiv
  let targetMap :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
      (Equiv.cast hsite)).toContinuousLinearEquiv
  change targetMap (G (sourceBack f)) =
    cmp99SourceTerminalCLMTransport h h G f
  have hback : HEq (sourceBack f) f := by
    simpa only [sourceBack, Equiv.cast_symm] using
      (finitePiLpCongrLeft_cast_heq hsite.symm f)
  have hG : HEq (G (sourceBack f))
      (cmp99SourceTerminalCLMTransport h h G f) :=
    cmp99SourceTerminalCLMTransport_apply_heq h h G hback
  have hforward : HEq (targetMap (G (sourceBack f)))
      (G (sourceBack f)) := by
    exact finitePiLpCongrLeft_cast_heq hsite (G (sourceBack f))
  exact eq_of_heq (hforward.trans hG)

namespace CMP99SourceDependentOmegaGeometry

set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 8000000 in
/-- The literal ambient global middle is exactly the reindexed generated
middle sandwiched between restriction and zero extension on the full region.
-/
theorem cmp99Eq395PhysicalGlobalMiddle_eq_extend_onSource
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall =
      let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
      (extendZeroZeroCLM Omega).comp
        ((cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
          background budget fineSmall hsmall).comp (restrictZeroCLM Omega)) := by
  dsimp only
  unfold cmp99Eq395PhysicalGlobalMiddle
  dsimp only
  let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
  let regions := cmp99SourceIteratedLiftActiveRegionChain
    (M := M) Omega (depth + 1)
  let T := regions.weightedQprimeTower (show 2 ≤ 4 by norm_num) hM
    (matrixSUNAdjointModel Nc) spacing epsilon background
    budget.toRadiusChain fineSmall
  let Middle := cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle
    (show 2 ≤ 4 by norm_num) hM Omega depth hspacing background budget
    fineSmall hsmall
  let hT := regions.weightedQprimeTower_terminalSpace_eq
    (show 2 ≤ 4 by norm_num) hM (matrixSUNAdjointModel Nc)
    spacing epsilon background budget.toRadiusChain fineSmall
  let hCoord := regions.terminalHilbertSpace_eq_coordinate (Nc := Nc)
  let hPhys := cmp99SourceIteratedLiftActiveRegionChain_terminalHilbertSpace_eq
    (Nc := Nc) (M := M) Omega (depth + 1)
  have hgenerated :=
    cmp99SourceGeneratedPhysicalCoarseCovarianceMiddle_transport_eq
      Omega hM depth hspacing background budget fineSmall hsmall
  have hsource := cmp99Eq395GeneratedPhysicalMiddleOnSource_eq_transport
    Omega hM depth hspacing background budget fineSmall hsmall
  have htrans := cmp99SourceTerminalCLMTransport_trans
    (hT.trans hCoord) (hT.trans hCoord)
    (hCoord.symm.trans hPhys) (hCoord.symm.trans hPhys) Middle
  rw [hgenerated] at htrans
  rw [hsource, htrans]
  congr

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
/-- The literal ambient global middle has volume-independent fixed-rate
exponential decay in the physical coarse-block metric. -/
theorem cmp99Eq395PhysicalGlobalMiddle_exponentialKernelBound
    (hM : 2 ≤ M) (depth : ℕ) {spacing epsilon : ℝ}
    (hspacing : 0 < spacing)
    (background : GaugeConfig 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)) (SUN Nc))
    (budget : CMP99SourceUbarClosedBudget 4 M Nc (depth + 1) epsilon)
    (fineSmall : ∀ e : ConcreteEdge 4
      (cmp99RegionalLatticeSize M (2 * Q) (depth + 1)),
      ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff 4 M (depth + 1)
      spacing epsilon < 1) :
    FinitePiLpTypedExponentialKernelBound
      (cmp99Eq395PhysicalGlobalMiddle hM depth hspacing background budget
        fineSmall hsmall)
      (finBoxDist : FinBox 4 (2 * Q) → FinBox 4 (2 * Q) → ℕ)
      (cmp99Eq395GeneratedMiddleDecayAmplitude M depth spacing epsilon)
      (cmp99SourceGeneratedCombesThomasRate 4 M depth spacing epsilon / 4) := by
  let Omega := cmp99Eq395FullCoarseRegion (Q := Q)
  let A := cmp99Eq395GeneratedPhysicalMiddleOnSource Omega hM depth hspacing
    background budget fineSmall hsmall
  have hA := cmp99Eq395GeneratedPhysicalMiddleOnSource_exponentialKernelBound
    Omega hM depth hspacing background budget fineSmall hsmall
  rw [cmp99Eq395PhysicalGlobalMiddle_eq_extend_onSource]
  refine ⟨hA.1, hA.2.1, ?_⟩
  intro source target v
  let sourceOmega : ActiveGaugeRegion.Site Omega :=
    ⟨source, by simp [Omega, cmp99Eq395FullCoarseRegion]⟩
  let targetOmega : ActiveGaugeRegion.Site Omega :=
    ⟨target, by simp [Omega, cmp99Eq395FullCoarseRegion]⟩
  have hrestrict :
      restrictZeroCLM Omega (singleFinitePiLp source v) =
        singleFinitePiLp sourceOmega v := by
    apply PiLp.ext
    intro x
    by_cases hx : x.1 = source
    · have heq : x = sourceOmega := Subtype.ext hx
      subst x
      simp [restrictZeroCLM, sourceOmega]
    · have hne : x ≠ sourceOmega := by
        intro heq
        exact hx (congrArg Subtype.val heq)
      simp [restrictZeroCLM, singleFinitePiLp, hx, hne]
  have htarget : target ∈ Omega.sites := by
    simp [Omega, cmp99Eq395FullCoarseRegion]
  change ‖extendZeroZeroCLM Omega
      (A (restrictZeroCLM Omega (singleFinitePiLp source v))) target‖ ≤ _
  rw [extendZeroZeroCLM_apply_of_mem Omega _ target htarget, hrestrict]
  change ‖A (singleFinitePiLp sourceOmega v) targetOmega‖ ≤ _
  exact hA.2.2 sourceOmega targetOmega v

end CMP99SourceDependentOmegaGeometry

end
end YangMills.RG
