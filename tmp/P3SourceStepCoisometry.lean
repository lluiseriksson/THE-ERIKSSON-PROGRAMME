import tmp.P3TypedGreenInverse

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only source dictionary for the one-step weighted adjoint used by P3.

`CMP99SourceRetainedPhysicalTower.nextAverage` stores the literal step but
does not expose its weighted coisometry as a field.  The theorem below must
derive it from the adjacent prefix recursion, both prefix coisometries, and
the exact lattice-volume ratios.  This file is not compiler evidence and is
not imported by the tracked tree.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- The weighted adjoint of the next retained prefix factors as the current
weighted adjoint followed by the literal one-step weighted adjoint. -/
theorem scratch_cmp85SourceWeightedAdjoint_succ
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (hspacing : 0 < spacing) (k : Fin depth) :
    (T.towerAt k.succ).weightedAdjoint =
      (T.towerAt k.castSucc).weightedAdjoint.comp
        (scratch_cmp85SourceStepWeightedAdjoint T k) := by
  let R := T.nextAverage k
  let Wstep := scratch_cmp85SourceStepWeightedAdjoint T k
  let current := T.towerAt k.castSucc
  let next := T.towerAt k.succ
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (NeZero.pos M)
  have hcurrent : 0 < current.terminalSpacing := by
    rw [current, T.towerAt_terminalSpacing]
    exact mul_pos (pow_pos hMpos k.castSucc.val) hspacing
  have hnext : 0 < next.terminalSpacing := by
    rw [next, T.towerAt_terminalSpacing]
    exact mul_pos (pow_pos hMpos k.succ.val) hspacing
  have hspacingPow : spacing ^ d ≠ 0 := pow_ne_zero d hspacing.ne'
  have hcurrentPow : current.terminalSpacing ^ d ≠ 0 :=
    pow_ne_zero d hcurrent.ne'
  have hnextPow : next.terminalSpacing ^ d ≠ 0 :=
    pow_ne_zero d hnext.ne'
  have hterminal :
      next.terminalSpacing = (M : ℝ) * current.terminalSpacing := by
    rw [next, current, T.towerAt_terminalSpacing,
      T.towerAt_terminalSpacing]
    simp only [Fin.val_succ, Fin.val_castSucc]
    rw [pow_succ]
    ring
  have hratio :
      (spacing ^ d / next.terminalSpacing ^ d) * (M : ℝ) ^ d =
        spacing ^ d / current.terminalSpacing ^ d := by
    rw [hterminal, mul_pow]
    field_simp [hspacingPow, hcurrentPow, hnextPow,
      pow_ne_zero d hMpos.ne']
  have hQ := T.Qprime_succ k
  have hQadj := congrArg
    (fun A => ContinuousLinearMap.adjoint A) hQ
  rw [ContinuousLinearMap.adjoint_comp] at hQadj
  have hcurrentAdj :=
    current.adjoint_eq_spacingRatio_smul_weightedAdjoint hcurrent.ne'
  have hnextAdj :=
    next.adjoint_eq_spacingRatio_smul_weightedAdjoint hnext.ne'
  apply ContinuousLinearMap.ext
  intro eta
  have hadjPoint := congrArg
    (fun A : next.TerminalSpace.carrier →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) => A eta) hQadj
  rw [hnextAdj, hcurrentAdj] at hadjPoint
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_smul] at hadjPoint
  have hscaled :
      (spacing ^ d / next.terminalSpacing ^ d) • next.weightedAdjoint eta =
        (spacing ^ d / next.terminalSpacing ^ d) •
          ((M : ℝ) ^ d • current.weightedAdjoint (R.adjoint eta)) := by
    calc
      (spacing ^ d / next.terminalSpacing ^ d) •
          next.weightedAdjoint eta =
        (spacing ^ d / current.terminalSpacing ^ d) •
          current.weightedAdjoint (R.adjoint eta) := hadjPoint
      _ = (spacing ^ d / next.terminalSpacing ^ d) •
          ((M : ℝ) ^ d • current.weightedAdjoint (R.adjoint eta)) := by
        rw [smul_smul, hratio]
  have hratioNonzero : spacing ^ d / next.terminalSpacing ^ d ≠ 0 :=
    div_ne_zero hspacingPow hnextPow
  have hcancel :=
    ((isUnit_iff_ne_zero).2 hratioNonzero).smul_left_cancel.mp hscaled
  simpa only [current, next, R, Wstep,
    scratch_cmp85SourceStepWeightedAdjoint,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul] using hcancel

/-- Exact source coisometry of the literal one-step retained average.  No
new normalization constant is accepted. -/
theorem scratch_cmp85SourceStep_comp_weightedAdjoint
    {rho : SUNAdjointModel Nc} {Omega : ActiveGaugeRegion d N}
    {spacing : ℝ} {background : GaugeConfig d N (SUN Nc)}
    (T : CMP99SourceRetainedPhysicalTower rho Omega M spacing background depth)
    (hspacing : 0 < spacing) (k : Fin depth) :
    (T.nextAverage k).comp (scratch_cmp85SourceStepWeightedAdjoint T k) =
      ContinuousLinearMap.id ℝ (T.towerAt k.succ).TerminalSpace.carrier := by
  have hnext := T.prefix_comp_weightedAdjoint k.succ
  have hcurrent := T.prefix_comp_weightedAdjoint k.castSucc
  have hQ := T.Qprime_succ k
  have hW := scratch_cmp85SourceWeightedAdjoint_succ T hspacing k
  calc
    (T.nextAverage k).comp (scratch_cmp85SourceStepWeightedAdjoint T k) =
        (T.nextAverage k).comp
          (((T.towerAt k.castSucc).Qprime.comp
            (T.towerAt k.castSucc).weightedAdjoint).comp
              (scratch_cmp85SourceStepWeightedAdjoint T k)) := by
        rw [hcurrent]
        rfl
    _ = ((T.nextAverage k).comp (T.towerAt k.castSucc).Qprime).comp
          ((T.towerAt k.castSucc).weightedAdjoint.comp
            (scratch_cmp85SourceStepWeightedAdjoint T k)) := rfl
    _ = (T.towerAt k.succ).Qprime.comp
          (T.towerAt k.succ).weightedAdjoint := by rw [← hQ, ← hW]
    _ = ContinuousLinearMap.id ℝ
          (T.towerAt k.succ).TerminalSpace.carrier := hnext

end

end YangMills.RG
