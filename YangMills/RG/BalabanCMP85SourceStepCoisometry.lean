import YangMills.RG.BalabanCMP85TypedGreenInverse
/-!
source dictionary for the one-step weighted adjoint used by P3.

`CMP99SourceRetainedPhysicalTower.nextAverage` stores the literal step but does not expose its weighted coisometry as a field. The theorem below must derive it from the adjacent prefix recursion, both prefix coisometries, and the exact lattice-volume ratios.

PRE-VALIDATION: this module's source is present, its `.olean` has not yet
been materialized, and its result has not yet been verified by the compiler.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Pointwise, the weighted adjoint of the next retained prefix factors as
the current weighted adjoint followed by the literal one-step weighted
adjoint.  The pointwise statement avoids an expensive dependent operator
equality at the elaboration boundary. -/
theorem cmp85SourceWeightedAdjoint_succ
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (hspacing : 0 < spacing) (k : Fin depth)
    (eta : (T.towerAt k.succ).TerminalSpace.carrier) :
    (T.towerAt k.succ).weightedAdjoint eta =
      (T.towerAt k.castSucc).weightedAdjoint
        (cmp85SourceStepWeightedAdjoint
          (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth) T k eta) := by
  apply ext_inner_left ℝ
  intro phi
  have hQ := congrArg
    (fun Q : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      (T.towerAt k.succ).TerminalSpace.carrier => Q phi)
    (T.Qprime_succ k)
  simp only [ContinuousLinearMap.comp_apply] at hQ
  have hnext := (T.towerAt k.succ).weightedAdjoint_pairing phi eta
  rw [hQ] at hnext
  have hstep := cmp85SourceStepWeightedAdjoint_pairing
    (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth)
    T k ((T.towerAt k.castSucc).Qprime phi) eta
  have hcurrent := (T.towerAt k.castSucc).weightedAdjoint_pairing phi
    (cmp85SourceStepWeightedAdjoint
      (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth) T k eta)
  change (T.towerAt k.succ).terminalSpacing ^ d *
      inner ℝ ((T.nextAverage k) ((T.towerAt k.castSucc).Qprime phi)) eta =
    spacing ^ d * inner ℝ phi ((T.towerAt k.succ).weightedAdjoint eta)
    at hnext
  change (T.towerAt k.succ).terminalSpacing ^ d *
      inner ℝ ((T.nextAverage k) ((T.towerAt k.castSucc).Qprime phi)) eta =
    (T.towerAt k.castSucc).terminalSpacing ^ d *
      inner ℝ ((T.towerAt k.castSucc).Qprime phi)
        (cmp85SourceStepWeightedAdjoint T k eta) at hstep
  change (T.towerAt k.castSucc).terminalSpacing ^ d *
      inner ℝ ((T.towerAt k.castSucc).Qprime phi)
        (cmp85SourceStepWeightedAdjoint T k eta) =
    spacing ^ d * inner ℝ phi
      ((T.towerAt k.castSucc).weightedAdjoint
        (cmp85SourceStepWeightedAdjoint T k eta)) at hcurrent
  have hscaled :
      spacing ^ d * inner ℝ phi ((T.towerAt k.succ).weightedAdjoint eta) =
        spacing ^ d * inner ℝ phi
          ((T.towerAt k.castSucc).weightedAdjoint
            (cmp85SourceStepWeightedAdjoint T k eta)) :=
    hnext.symm.trans (hstep.trans hcurrent)
  exact mul_left_cancel₀ (pow_ne_zero d hspacing.ne') hscaled

/-- Exact source coisometry of the literal one-step retained average.  No
new normalization constant is accepted. -/
theorem cmp85SourceStep_comp_weightedAdjoint
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (hspacing : 0 < spacing) (k : Fin depth) :
    (T.nextAverage k).comp
        (cmp85SourceStepWeightedAdjoint
          (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth) T k) =
      ContinuousLinearMap.id ℝ (T.towerAt k.succ).TerminalSpace.carrier := by
  have hnext := T.prefix_comp_weightedAdjoint k.succ
  have hcurrent := T.prefix_comp_weightedAdjoint k.castSucc
  have hQ := T.Qprime_succ k
  have hW (eta : (T.towerAt k.succ).TerminalSpace.carrier) :=
    cmp85SourceWeightedAdjoint_succ
      (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth)
      T hspacing k eta
  calc
    (T.nextAverage k).comp
        (cmp85SourceStepWeightedAdjoint
          (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth) T k) =
        (T.nextAverage k).comp
          (((T.towerAt k.castSucc).Qprime.comp
            (T.towerAt k.castSucc).weightedAdjoint).comp
              (cmp85SourceStepWeightedAdjoint
                (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth) T k)) := by
        rw [hcurrent]
        rfl
    _ = ((T.nextAverage k).comp (T.towerAt k.castSucc).Qprime).comp
          ((T.towerAt k.castSucc).weightedAdjoint.comp
            (cmp85SourceStepWeightedAdjoint
              (d := d) (M := M) (N := N) (Nc := Nc) (depth := depth) T k)) := rfl
    _ = (T.towerAt k.succ).Qprime.comp
          (T.towerAt k.succ).weightedAdjoint := by
      apply ContinuousLinearMap.ext
      intro eta
      simp only [ContinuousLinearMap.comp_apply]
      have hQeta := congrArg
        (fun Q : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
          (T.towerAt k.succ).TerminalSpace.carrier =>
          Q ((T.towerAt k.castSucc).weightedAdjoint
            (cmp85SourceStepWeightedAdjoint T k eta))) hQ
      simp only [ContinuousLinearMap.comp_apply] at hQeta
      exact hQeta.symm.trans
        (congrArg (T.towerAt k.succ).Qprime (hW eta).symm)
    _ = ContinuousLinearMap.id ℝ
          (T.towerAt k.succ).TerminalSpace.carrier := hnext

end

end YangMills.RG
