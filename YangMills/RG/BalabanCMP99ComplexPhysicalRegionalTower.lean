import YangMills.RG.BalabanCMP99ComplexRegionalTower
import YangMills.RG.BalabanCMP99SourceWeightedPhysicalTower

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# Background-faithful analytic regional tower for CMP99 (3.59)

Each source step builds its contour holonomies from the background indexing
that step.  The constructor is private, so a caller cannot replace the
internally composed forward or starred terminal operators.
-/

namespace YangMills.RG

noncomputable section

variable {d Nc : ℕ} [NeZero Nc]

/-- The complex contour is the exact physical block contour with only its
phantom gauge-group parameter changed.  In particular, no second
`Classical.choice` may select a different edge list on the complex side. -/
noncomputable def cmp99SpecialLinearBlockContainedContourSystem
    {M N' : ℕ} [NeZero M] [NeZero N'] :
    CMP99ContourSystem d M N'
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ) :=
  fun y x ↦
    let physical :=
      cmp99BlockContainedContourSystem (G := SUN Nc) y x
    { edges := physical.edges
      isPath := physical.isPath
      ends := physical.ends }

/-- Literal complex block-contour holonomy of one analytically continued
background. -/
noncomputable def cmp99ComplexPhysicalBlockHolonomy
    {M N' : ℕ} [NeZero M] [NeZero N']
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ)) :
    FinBox d N' → FinBox d (M * N') →
      Matrix.SpecialLinearGroup (Fin Nc) ℂ :=
  fun y x ↦
    (cmp99SpecialLinearBlockContainedContourSystem
      (d := d) (Nc := Nc) y x).holonomy background

/-- Analytic tower indexed by the physical complex background consumed by
its first printed average. -/
structure CMP99ComplexPhysicalRegionalTower
    {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ)
    (background : GaugeConfig d N
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ)) where
  private mk ::
  toComplexTower : CMP99ComplexRegionalTower (Nc := Nc) Omega spacing

/-- Empty physical analytic tower. -/
noncomputable def CMP99ComplexPhysicalRegionalTower.stop
    {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ)
    (background : GaugeConfig d N
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ)) :
    CMP99ComplexPhysicalRegionalTower Omega spacing background where
  toComplexTower := CMP99ComplexRegionalTower.stop (Nc := Nc) Omega spacing

/-- Add one physical analytic scale.  Both contour transports are generated
from `background`; only the recursively generated tail is accepted. -/
noncomputable def CMP99ComplexPhysicalRegionalTower.step
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (nextBackground : GaugeConfig d N'
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (tail : CMP99ComplexPhysicalRegionalTower
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing) nextBackground) :
    CMP99ComplexPhysicalRegionalTower Omega spacing background where
  toComplexTower := CMP99ComplexRegionalTower.step Omega hOmega spacing
    (cmp99ComplexPhysicalBlockHolonomy background) tail.toComplexTower

@[simp] theorem CMP99ComplexPhysicalRegionalTower.toComplexTower_stop
    {N : ℕ} [NeZero N]
    (Omega : ActiveGaugeRegion d N) (spacing : ℝ)
    (background : GaugeConfig d N
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ)) :
    (CMP99ComplexPhysicalRegionalTower.stop Omega spacing background).
        toComplexTower =
      CMP99ComplexRegionalTower.stop (Nc := Nc) Omega spacing := rfl

theorem CMP99ComplexPhysicalRegionalTower.Qprime_step
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (nextBackground : GaugeConfig d N'
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (tail : CMP99ComplexPhysicalRegionalTower
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing) nextBackground) :
    (CMP99ComplexPhysicalRegionalTower.step Omega hOmega spacing background
        nextBackground tail).toComplexTower.Qprime =
      tail.toComplexTower.Qprime.comp
        (cmp99ComplexAdjointBlockAverageCLM Omega
          (cmp99ComplexPhysicalBlockHolonomy background)) := rfl

theorem CMP99ComplexPhysicalRegionalTower.starred_step
    {M N' : ℕ} [NeZero M] [NeZero N']
    (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (spacing : ℝ)
    (background : GaugeConfig d (M * N')
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (nextBackground : GaugeConfig d N'
      (Matrix.SpecialLinearGroup (Fin Nc) ℂ))
    (tail : CMP99ComplexPhysicalRegionalTower
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      ((M : ℝ) * spacing) nextBackground) :
    (CMP99ComplexPhysicalRegionalTower.step Omega hOmega spacing background
        nextBackground tail).toComplexTower.starred =
      (cmp99ComplexAdjointBlockStarSynthesisCLM Omega hOmega
          (cmp99ComplexPhysicalBlockHolonomy background)).comp
        tail.toComplexTower.starred := rfl

end

end YangMills.RG
