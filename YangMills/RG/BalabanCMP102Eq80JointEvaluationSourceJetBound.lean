/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeEvaluationJetBound

/-!
# Source-only majorant for the equation-(80) joint evaluation

The auxiliary evaluation majorant contains jets of the two maps
`q ↦ q.1` and `q ↦ D q.2`.  Here these are reduced to the value and unique
first derivative of the operator projection, and to the literal derivatives
of `D` at the physical field point.  No bound for the joint evaluation is
assumed.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- Exact scalar majorant for the jets of the operator projection. -/
noncomputable def cmp102Eq80JointOperatorProjectionJetMajorant
    (p : JointSpace (E := E) (F := F)) (i : ℕ) : ℝ :=
  if i = 0 then ‖p.1‖ else if i = 1 then 1 else 0

/-- The operator projection contributes its value in order zero, its norm-one
linear derivative in order one, and zero thereafter. -/
theorem norm_iteratedFDeriv_jointOperatorProjection_le
    (i : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ i
        (fun q : JointSpace (E := E) (F := F) => q.1) p‖ ≤
      cmp102Eq80JointOperatorProjectionJetMajorant p i := by
  cases i with
  | zero =>
      simp [cmp102Eq80JointOperatorProjectionJetMajorant]
  | succ k =>
      cases k with
      | zero =>
          unfold cmp102Eq80JointOperatorProjectionJetMajorant
          simpa [norm_iteratedFDeriv_one, fderiv_fst] using
            (ContinuousLinearMap.norm_fst_le ℝ (F →L[ℝ] E) E)
      | succ k =>
          unfold cmp102Eq80JointOperatorProjectionJetMajorant
          have hderiv :
              (fun y : JointSpace (E := E) (F := F) =>
                fderiv ℝ
                  (fun q : JointSpace (E := E) (F := F) => q.1) y) =
                fun _ =>
                  ContinuousLinearMap.fst ℝ (F →L[ℝ] E) E := by
            funext y
            exact fderiv_fst
          rw [show (k + 1 + 1) = (k + 1) + 1 by omega]
          rw [iteratedFDeriv_succ_eq_comp_right, hderiv]
          have hzero :
              (iteratedFDeriv ℝ (k + 1)
                (fun _ : JointSpace (E := E) (F := F) =>
                  ContinuousLinearMap.fst ℝ (F →L[ℝ] E) E)) = 0 :=
            iteratedFDeriv_const_of_ne (by omega) _
          rw [hzero]
          have hne : k + 1 + 1 ≠ 0 := by omega
          rw [if_neg hne]
          have hneOne : k + 1 + 1 ≠ 1 := by omega
          rw [if_neg hneOne]
          simp only [Function.comp_apply, Pi.zero_apply]
          have hcurryZero :
              (continuousMultilinearCurryRightEquiv'
                ℝ (k + 1) (JointSpace (E := E) (F := F))
                (F →L[ℝ] E)).symm 0 = 0 :=
            (continuousMultilinearCurryRightEquiv'
              ℝ (k + 1) (JointSpace (E := E) (F := F))
              (F →L[ℝ] E)).symm.map_zero
          rw [hcurryZero]
          change
            ‖(0 : ContinuousMultilinearMap ℝ
              (fun _ : Fin (k + 2) =>
                JointSpace (E := E) (F := F))
              (F →L[ℝ] E))‖ ≤ 0
          rw [ContinuousMultilinearMap.opNorm_zero]

/-- Composing `D` with the second projection does not enlarge any jet norm. -/
theorem norm_iteratedFDeriv_comp_jointSnd_le
    (D : E → F) (hD : ContDiff ℝ ⊤ D)
    (i : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ i
        (fun q : JointSpace (E := E) (F := F) => D q.2) p‖ ≤
      ‖iteratedFDeriv ℝ i D p.2‖ := by
  let sndCLM :
      JointSpace (E := E) (F := F) →L[ℝ] E :=
    ContinuousLinearMap.snd ℝ (F →L[ℝ] E) E
  have hfun :
      (fun q : JointSpace (E := E) (F := F) => D q.2) =
        D ∘ sndCLM := by
    rfl
  rw [hfun, sndCLM.iteratedFDeriv_comp_right hD p le_top]
  calc
    ‖(iteratedFDeriv ℝ i D (sndCLM p)).compContinuousLinearMap
        (fun _ => sndCLM)‖ ≤
        ‖iteratedFDeriv ℝ i D (sndCLM p)‖ *
          ∏ _ : Fin i, ‖sndCLM‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ i D (sndCLM p)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one
        (fun _ _ => by exact norm_nonneg sndCLM)
        (fun _ _ => ContinuousLinearMap.norm_snd_le _ _ _)
    _ = ‖iteratedFDeriv ℝ i D p.2‖ := by
      simp [sndCLM]

/-- Binomial source majorant containing only the literal jets of `D`. -/
noncomputable def cmp102Eq80JointEvaluationSourceJetMajorant
    (D : E → F) (n : ℕ)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      cmp102Eq80JointOperatorProjectionJetMajorant p i *
      ‖iteratedFDeriv ℝ (n - i) D p.2‖

/-- The operator-projection majorant is nonnegative. -/
theorem cmp102Eq80JointOperatorProjectionJetMajorant_nonneg
    (p : JointSpace (E := E) (F := F)) (i : ℕ) :
    0 ≤ cmp102Eq80JointOperatorProjectionJetMajorant p i := by
  unfold cmp102Eq80JointOperatorProjectionJetMajorant
  split_ifs <;> positivity

/-- The existing joint-evaluation majorant is bounded by the source-only
binomial expression. -/
theorem cmp102Eq80JointEvaluationJetMajorant_le_sourceJetMajorant
    (D : E → F) (hD : ContDiff ℝ ⊤ D)
    (n : ℕ) (p : JointSpace (E := E) (F := F)) :
    cmp102Eq80JointEvaluationJetMajorant D n p ≤
      cmp102Eq80JointEvaluationSourceJetMajorant D n p := by
  unfold cmp102Eq80JointEvaluationJetMajorant
  unfold cmp102Eq80JointEvaluationSourceJetMajorant
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_jointOperatorProjection_le i p)
      (Nat.cast_nonneg _)
  · exact norm_iteratedFDeriv_comp_jointSnd_le D hD (n - i) p
  · positivity
  · exact mul_nonneg (Nat.cast_nonneg _)
      (cmp102Eq80JointOperatorProjectionJetMajorant_nonneg p i)

end

end YangMills.RG
