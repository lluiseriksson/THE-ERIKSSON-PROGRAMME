import YangMills.RG.PhysicalGramKernel
import YangMills.RG.PhysicalShellLocalityDiv
import YangMills.RG.BalabanCMP116WilsonBackgroundFactorBounds

/-!
# Background-dependent gauge-fixing defect

The complete interacting precision contains the gauge-fixing mass
`Q_U† Q_U`, not only the Wilson Hessian.  This module introduces its exact
defect and exposes the mixed telescoping identity

`Q_U†Q_U - Q_1†Q_1 = (Q_U-Q_1)†Q_U + Q_1†(Q_U-Q_1)`.

The identity is preferable to a three-term expansion because it remains
linear in the small constraint defect.  Quantitative bounds are developed in
the following modules.
-/

namespace YangMills.RG

open scoped RealInnerProductSpace

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Pointwise smallness of the adjoint action on positive physical bonds.
This is the correct model-independent API; it is stronger than fundamental
matrix smallness for an abstract `SUNAdjointModel`. -/
def PhysicalAdjointSmallBackground
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) (δ : ℝ) : Prop :=
  ∀ b : PhysicalBond d N, ∀ X : SUNLieCoord Nc,
    ‖ρ.adCLM (U (positiveEdgeOfPhysicalBond b)) X - X‖ ≤ δ * ‖X‖

/-- Smallness propagates to the inverse adjoint action without loss because
the action is isometric. -/
theorem PhysicalAdjointSmallBackground.inverse_apply_sub
    {ρ : SUNAdjointModel Nc} {U : PhysicalGaugeBackground d N Nc}
    {δ : ℝ} (hsmall : PhysicalAdjointSmallBackground ρ U δ)
    (b : PhysicalBond d N) (X : SUNLieCoord Nc) :
    ‖ρ.adCLM (U (positiveEdgeOfPhysicalBond b))⁻¹ X - X‖ ≤ δ * ‖X‖ := by
  let g : SUN Nc := U (positiveEdgeOfPhysicalBond b)
  have hid :
      ρ.adCLM g⁻¹ X - X =
        ρ.adCLM g⁻¹ (X - ρ.adCLM g X) := by
    rw [ContinuousLinearMap.map_sub, ρ.ad_inv_apply_ad]
  rw [hid, ρ.norm_ad]
  rw [norm_sub_rev]
  exact hsmall b X

/-- Move one adjoint action across the real inner product. -/
theorem SUNAdjointModel.inner_ad_left
    (ρ : SUNAdjointModel Nc) (g : SUN Nc)
    (X Y : SUNLieCoord Nc) :
    inner ℝ (ρ.adCLM g X) Y =
      inner ℝ X (ρ.adCLM g⁻¹ Y) := by
  calc
    inner ℝ (ρ.adCLM g X) Y =
        inner ℝ (ρ.adCLM g X)
          (ρ.adCLM g (ρ.adCLM g⁻¹ Y)) := by
            rw [ρ.ad_apply_ad_inv]
    _ = inner ℝ X (ρ.adCLM g⁻¹ Y) :=
      ρ.ad_inner g X (ρ.adCLM g⁻¹ Y)

/-- Reindex the transported forward term as a backward-divergence term. -/
theorem sum_inner_ad_shift_eq
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (φ : PhysicalGaugeZeroCochain d N Nc) :
    (∑ x : FinBox d N, ∑ i : Fin d,
        inner ℝ (A (x, i))
          (ρ.adCLM
            (U (positiveEdgeOfPhysicalBond ((x, i) : PhysicalBond d N)))
            (φ (x.shift i)))) =
      ∑ x : FinBox d N, ∑ i : Fin d,
        inner ℝ
          (ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (A (FinBox.shiftBack x i, i)))
          (φ x) := by
  calc
    (∑ x : FinBox d N, ∑ i : Fin d,
        inner ℝ (A (x, i))
          (ρ.adCLM
            (U (positiveEdgeOfPhysicalBond ((x, i) : PhysicalBond d N)))
            (φ (x.shift i)))) =
        ∑ i : Fin d, ∑ x : FinBox d N,
          inner ℝ
            (ρ.adCLM
              (U (positiveEdgeOfPhysicalBond ((x, i) : PhysicalBond d N)))⁻¹
              (A (x, i)))
            (φ (x.shift i)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro x _
          calc
            inner ℝ (A (x, i))
                (ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((x, i) : PhysicalBond d N)))
                  (φ (x.shift i))) =
              inner ℝ
                (ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((x, i) : PhysicalBond d N)))
                  (φ (x.shift i)))
                (A (x, i)) := real_inner_comm _ _
            _ = inner ℝ (φ (x.shift i))
                (ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((x, i) : PhysicalBond d N)))⁻¹
                  (A (x, i))) :=
              ρ.inner_ad_left
                (U (positiveEdgeOfPhysicalBond
                  ((x, i) : PhysicalBond d N)))
                (φ (x.shift i)) (A (x, i))
            _ = inner ℝ
                (ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((x, i) : PhysicalBond d N)))⁻¹
                  (A (x, i)))
                (φ (x.shift i)) := real_inner_comm _ _
    _ = ∑ i : Fin d, ∑ x : FinBox d N,
          inner ℝ
            (ρ.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
              (A (FinBox.shiftBack x i, i)))
            (φ x) := by
          apply Finset.sum_congr rfl
          intro i _
          let f : FinBox d N → ℝ := fun y =>
            inner ℝ
              (ρ.adCLM
                (U (positiveEdgeOfPhysicalBond
                  ((FinBox.shiftBack y i, i) : PhysicalBond d N)))⁻¹
                (A (FinBox.shiftBack y i, i)))
              (φ y)
          have hf := FinBox.sum_shift f i
          simpa [f, FinBox.shiftBack_shift] using hf
    _ = ∑ x : FinBox d N, ∑ i : Fin d,
          inner ℝ
            (ρ.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
              (A (FinBox.shiftBack x i, i)))
            (φ x) := by
          rw [Finset.sum_comm]

/-- Concrete backward-divergence stencil at an arbitrary background. -/
theorem gaugeConstraintQCLM_apply_background
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) :
    gaugeConstraintQCLM ρ U A x =
      ∑ i : Fin d,
        (A (x, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (A (FinBox.shiftBack x i, i))) := by
  let B : PhysicalGaugeZeroCochain d N Nc :=
    WithLp.toLp 2 fun x : FinBox d N =>
      ∑ i : Fin d,
        (A (x, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (A (FinBox.shiftBack x i, i)))
  have hB : gaugeConstraintQCLM ρ U A = B := by
    apply ext_inner_right ℝ
    intro φ
    rw [gaugeConstraintQCLM, covariantDivCLM,
      ContinuousLinearMap.adjoint_inner_left]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    rw [Fintype.sum_prod_type]
    simp only [covariantD0CLM_apply, inner_sub_right, B]
    calc
      (∑ x : FinBox d N, ∑ i : Fin d,
          (inner ℝ (A (x, i)) (φ x) -
            inner ℝ (A (x, i))
              (ρ.adCLM
                (U (positiveEdgeOfPhysicalBond ((x, i) : PhysicalBond d N)))
                (φ (x.shift i)))))
          = (∑ x : FinBox d N, ∑ i : Fin d,
              inner ℝ (A (x, i)) (φ x)) -
            ∑ x : FinBox d N, ∑ i : Fin d,
              inner ℝ (A (x, i))
                (ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond ((x, i) : PhysicalBond d N)))
                (φ (x.shift i))) := by
            simp [Finset.sum_sub_distrib]
      _ = (∑ x : FinBox d N, ∑ i : Fin d,
              inner ℝ (A (x, i)) (φ x)) -
            ∑ x : FinBox d N, ∑ i : Fin d,
              inner ℝ
                (ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond
                  ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
                  (A (FinBox.shiftBack x i, i)))
                (φ x) := by
            rw [sum_inner_ad_shift_eq ρ U A φ]
      _ = ∑ x : FinBox d N, ∑ i : Fin d,
            (inner ℝ (A (x, i)) (φ x) -
              inner ℝ
                (ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
                  (A (FinBox.shiftBack x i, i)))
                (φ x)) := by
            simp [Finset.sum_sub_distrib]
      _ = ∑ x : FinBox d N, ∑ i : Fin d,
            inner ℝ
              (A (x, i) -
                ρ.adCLM
                  (U (positiveEdgeOfPhysicalBond
                    ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
                  (A (FinBox.shiftBack x i, i)))
              (φ x) := by
            simp [inner_sub_left]
      _ = ∑ x : FinBox d N,
            inner ℝ
              (∑ i : Fin d,
                (A (x, i) -
                  ρ.adCLM
                    (U (positiveEdgeOfPhysicalBond
                      ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
                    (A (FinBox.shiftBack x i, i))))
              (φ x) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [← sum_inner]
  have hx := congrArg
    (fun B : PhysicalGaugeZeroCochain d N Nc => B x) hB
  simpa [B] using hx

/-- Linear constraint defect `Q_U-Q_1`. -/
noncomputable def gaugeConstraintDefectCLM
    (ρ : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeZeroCochain d N Nc :=
  gaugeConstraintQCLM ρ U -
    gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc)

/-- Gauge-fixing mass defect `Q_U†Q_U-Q_1†Q_1`. -/
noncomputable def gaugeFixingMassDefectCLM
    (ρ : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc) :
    PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc :=
  gaugeFixingMassCLM ρ U -
    gaugeFixingMassCLM ρ (trivialPhysicalGaugeBackground d N Nc)

@[simp]
theorem gaugeConstraintDefectCLM_apply
    (ρ : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    gaugeConstraintDefectCLM ρ U A =
      gaugeConstraintQCLM ρ U A -
        gaugeConstraintQCLM ρ
          (trivialPhysicalGaugeBackground d N Nc) A := rfl

/-- Pointwise stencil of the constraint defect: only the transported backward
slot changes with the background. -/
theorem gaugeConstraintDefectCLM_apply_background
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) :
    gaugeConstraintDefectCLM ρ U A x =
      ∑ i : Fin d,
        (A (FinBox.shiftBack x i, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (A (FinBox.shiftBack x i, i))) := by
  rw [gaugeConstraintDefectCLM_apply]
  change
    gaugeConstraintQCLM ρ U A x -
        gaugeConstraintQCLM ρ
          (trivialPhysicalGaugeBackground d N Nc) A x =
      _
  rw [gaugeConstraintQCLM_apply_background,
    gaugeConstraintQCLM_trivial_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

/-- Per-site bound for the constraint defect on a single-bond probe. -/
theorem gaugeConstraintDefect_single_norm_apply_le
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) {δ : ℝ}
    (hsmall : PhysicalAdjointSmallBackground ρ U δ)
    (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (x : FinBox d N) :
    ‖gaugeConstraintDefectCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v) x‖ ≤
      ∑ i : Fin d,
        if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
          δ * ‖v‖
        else 0 := by
  rw [gaugeConstraintDefectCLM_apply_background]
  calc
    ‖∑ i : Fin d,
        (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v
            (FinBox.shiftBack x i, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) p v
              (FinBox.shiftBack x i, i)))‖ ≤
      ∑ i : Fin d,
        ‖singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v
            (FinBox.shiftBack x i, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) p v
              (FinBox.shiftBack x i, i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin d,
        if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
          δ * ‖v‖
        else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hip :
          ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p
      · rw [if_pos hip, hip, singlePhysicalBondCochain_self]
        rw [norm_sub_rev]
        exact hsmall.inverse_apply_sub p v
      · rw [if_neg hip,
          singlePhysicalBondCochain_of_ne v hip,
          ContinuousLinearMap.map_zero, sub_zero, norm_zero]

/-- The constraint defect has one backward slot per bond probe, hence
`‖(Q_U-Q_1)δ_p v‖ ≤ δ‖v‖`. -/
theorem gaugeConstraintDefect_single_norm_le
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) {δ : ℝ}
    (hsmall : PhysicalAdjointSmallBackground ρ U δ)
    (p : PhysicalBond d N) (v : SUNLieCoord Nc) :
    ‖gaugeConstraintDefectCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v)‖ ≤
      δ * ‖v‖ := by
  classical
  have hbwd : ∀ i : Fin d,
      ∑ x : FinBox d N,
        (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
            δ * ‖v‖
          else 0) =
        (if i = p.2 then δ * ‖v‖ else 0) := by
    intro i
    by_cases hi : i = p.2
    · rw [if_pos hi]
      have hbij : Function.Bijective
          (fun x : FinBox d N => FinBox.shiftBack x i) := by
        constructor
        · intro a b hab
          have h1 := congrArg (fun z => FinBox.shift z i) hab
          simpa [FinBox.shift_shiftBack] using h1
        · intro y
          exact ⟨FinBox.shift y i, FinBox.shiftBack_shift y i⟩
      calc
        ∑ x : FinBox d N,
            (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
                δ * ‖v‖
              else 0) =
          ∑ x : FinBox d N,
            (if FinBox.shiftBack x i = p.1 then δ * ‖v‖ else 0) := by
              refine Finset.sum_congr rfl (fun x _ => if_congr ?_ rfl rfl)
              constructor
              · intro h
                exact congrArg Prod.fst h
              · intro h
                rw [h, hi]
        _ = ∑ y : FinBox d N,
            (if y = p.1 then δ * ‖v‖ else 0) :=
              hbij.sum_comp (fun y => if y = p.1 then δ * ‖v‖ else 0)
        _ = δ * ‖v‖ := by
              rw [Finset.sum_ite_eq' Finset.univ p.1]
              rw [if_pos (Finset.mem_univ _)]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      intro h
      exact hi (congrArg Prod.snd h)
  calc
    ‖gaugeConstraintDefectCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v)‖ ≤
      ∑ x : FinBox d N,
        ‖gaugeConstraintDefectCLM ρ U
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v) x‖ :=
        piLp_norm_le_sum_norm _
    _ ≤ ∑ x : FinBox d N, ∑ i : Fin d,
        if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
          δ * ‖v‖
        else 0 :=
      Finset.sum_le_sum
        (fun x _ =>
          gaugeConstraintDefect_single_norm_apply_le ρ U hsmall p v x)
    _ = ∑ i : Fin d, ∑ x : FinBox d N,
        if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
          δ * ‖v‖
        else 0 := Finset.sum_comm
    _ = ∑ i : Fin d,
        (if i = p.2 then δ * ‖v‖ else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hbwd i
    _ = δ * ‖v‖ := by
      rw [Finset.sum_ite_eq' Finset.univ p.2]
      rw [if_pos (Finset.mem_univ _)]

/-- Per-site norm bound for a general-background constraint probe. -/
theorem gaugeConstraint_background_single_norm_apply_le
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (x : FinBox d N) :
    ‖gaugeConstraintQCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v) x‖ ≤
      ∑ i : Fin d,
        ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) +
          (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
            ‖v‖
          else 0)) := by
  rw [gaugeConstraintQCLM_apply_background]
  calc
    ‖∑ i : Fin d,
        (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v (x, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) p v
              (FinBox.shiftBack x i, i)))‖ ≤
      ∑ i : Fin d,
        ‖singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v (x, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) p v
              (FinBox.shiftBack x i, i))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin d,
        ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) +
          (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
            ‖v‖
          else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v (x, i) -
          ρ.adCLM
            (U (positiveEdgeOfPhysicalBond
              ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
            (singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) p v
              (FinBox.shiftBack x i, i))‖ ≤
          ‖singlePhysicalBondCochain
              (d := d) (N := N) (Nc := Nc) p v (x, i)‖ +
            ‖ρ.adCLM
              (U (positiveEdgeOfPhysicalBond
                ((FinBox.shiftBack x i, i) : PhysicalBond d N)))⁻¹
              (singlePhysicalBondCochain
                (d := d) (N := N) (Nc := Nc) p v
                (FinBox.shiftBack x i, i))‖ :=
            norm_sub_le _ _
        _ = ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) +
            (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
              ‖v‖
            else 0)) := by
          congr 1
          · by_cases h : ((x, i) : PhysicalBond d N) = p
            · rw [h, singlePhysicalBondCochain_self]
              simp
            · rw [singlePhysicalBondCochain_of_ne v h, norm_zero, if_neg h]
          · rw [ρ.norm_ad]
            by_cases h :
                ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p
            · rw [h, singlePhysicalBondCochain_self]
              simp
            · rw [singlePhysicalBondCochain_of_ne v h, norm_zero, if_neg h]

/-- A general-background divergence probe has the same `2‖v‖` norm budget
as at the trivial background, because adjoint transport is isometric. -/
theorem gaugeConstraint_background_single_norm_le
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (p : PhysicalBond d N) (v : SUNLieCoord Nc) :
    ‖gaugeConstraintQCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v)‖ ≤
      (2 : ℝ) * ‖v‖ := by
  classical
  have hfwd : ∀ i : Fin d,
      ∑ x : FinBox d N,
        (if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) =
        (if i = p.2 then ‖v‖ else 0) := by
    intro i
    by_cases hi : i = p.2
    · rw [if_pos hi]
      calc
        ∑ x : FinBox d N,
            (if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) =
          ∑ x : FinBox d N,
            (if x = p.1 then ‖v‖ else 0) := by
              refine Finset.sum_congr rfl (fun x _ => if_congr ?_ rfl rfl)
              constructor
              · intro h
                exact congrArg Prod.fst h
              · intro h
                rw [h, hi]
        _ = ‖v‖ := by
              rw [Finset.sum_ite_eq' Finset.univ p.1]
              rw [if_pos (Finset.mem_univ _)]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      intro h
      exact hi (congrArg Prod.snd h)
  have hbwd : ∀ i : Fin d,
      ∑ x : FinBox d N,
        (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
            ‖v‖
          else 0) =
        (if i = p.2 then ‖v‖ else 0) := by
    intro i
    by_cases hi : i = p.2
    · rw [if_pos hi]
      have hbij : Function.Bijective
          (fun x : FinBox d N => FinBox.shiftBack x i) := by
        constructor
        · intro a b hab
          have h1 := congrArg (fun z => FinBox.shift z i) hab
          simpa [FinBox.shift_shiftBack] using h1
        · intro y
          exact ⟨FinBox.shift y i, FinBox.shiftBack_shift y i⟩
      calc
        ∑ x : FinBox d N,
            (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
                ‖v‖
              else 0) =
          ∑ x : FinBox d N,
            (if FinBox.shiftBack x i = p.1 then ‖v‖ else 0) := by
              refine Finset.sum_congr rfl (fun x _ => if_congr ?_ rfl rfl)
              constructor
              · intro h
                exact congrArg Prod.fst h
              · intro h
                rw [h, hi]
        _ = ∑ y : FinBox d N,
            (if y = p.1 then ‖v‖ else 0) :=
              hbij.sum_comp (fun y => if y = p.1 then ‖v‖ else 0)
        _ = ‖v‖ := by
              rw [Finset.sum_ite_eq' Finset.univ p.1]
              rw [if_pos (Finset.mem_univ _)]
    · rw [if_neg hi]
      apply Finset.sum_eq_zero
      intro x _
      rw [if_neg]
      intro h
      exact hi (congrArg Prod.snd h)
  calc
    ‖gaugeConstraintQCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v)‖ ≤
      ∑ x : FinBox d N,
        ‖gaugeConstraintQCLM ρ U
          (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p v) x‖ :=
        piLp_norm_le_sum_norm _
    _ ≤ ∑ x : FinBox d N, ∑ i : Fin d,
        ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) +
          (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
            ‖v‖
          else 0)) :=
      Finset.sum_le_sum
        (fun x _ =>
          gaugeConstraint_background_single_norm_apply_le ρ U p v x)
    _ = ∑ i : Fin d, ∑ x : FinBox d N,
        ((if ((x, i) : PhysicalBond d N) = p then ‖v‖ else 0) +
          (if ((FinBox.shiftBack x i, i) : PhysicalBond d N) = p then
            ‖v‖
          else 0)) := Finset.sum_comm
    _ = ∑ i : Fin d,
        ((if i = p.2 then ‖v‖ else 0) +
          (if i = p.2 then ‖v‖ else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_add_distrib, hfwd i, hbwd i]
    _ = 2 * ‖v‖ := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq' Finset.univ p.2]
      rw [if_pos (Finset.mem_univ _)]
      ring

/-- If neither divergence slot at `x` is the probe bond, the
general-background constraint probe vanishes at `x`. -/
theorem gaugeConstraint_background_single_eq_zero
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc)
    (p : PhysicalBond d N) (v : SUNLieCoord Nc)
    (x : FinBox d N)
    (h : ∀ i : Fin d,
      ((x, i) : PhysicalBond d N) ≠ p ∧
      ((FinBox.shiftBack x i, i) : PhysicalBond d N) ≠ p) :
    gaugeConstraintQCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v) x = 0 := by
  rw [gaugeConstraintQCLM_apply_background]
  apply Finset.sum_eq_zero
  intro i _
  rw [singlePhysicalBondCochain_of_ne v (h i).1,
    singlePhysicalBondCochain_of_ne v (h i).2,
    ContinuousLinearMap.map_zero, sub_zero]

/-- Probe images of arbitrary background constraints are orthogonal beyond
bond distance two.  Only the divergence slot geometry enters. -/
theorem gaugeConstraint_background_gram_orthogonal
    (ρ : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc)
    (p q : PhysicalBond d N) (v w : SUNLieCoord Nc)
    (hfar : 2 < physicalBondDist q p) :
    inner ℝ
      (gaugeConstraintQCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v))
      (gaugeConstraintQCLM ρ V
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) q w)) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hp : ∀ i : Fin d,
      ((x, i) : PhysicalBond d N) ≠ p ∧
      ((FinBox.shiftBack x i, i) : PhysicalBond d N) ≠ p
  · rw [gaugeConstraint_background_single_eq_zero ρ U p v x hp,
      inner_zero_left]
  · by_cases hq : ∀ i : Fin d,
        ((x, i) : PhysicalBond d N) ≠ q ∧
        ((FinBox.shiftBack x i, i) : PhysicalBond d N) ≠ q
    · rw [gaugeConstraint_background_single_eq_zero ρ V q w x hq,
        inner_zero_right]
    · exfalso
      push_neg at hp hq
      obtain ⟨i, hpi⟩ := hp
      obtain ⟨j, hqj⟩ := hq
      have hpslot : ∃ sp : FinBox d N, ∃ ip : Fin d,
          ((sp, ip) : PhysicalBond d N) = p ∧
            finBoxDist x sp ≤ 1 := by
        by_cases h1 : ((x, i) : PhysicalBond d N) = p
        · refine ⟨x, i, h1, ?_⟩
          rw [finBoxDist_self]
          exact Nat.zero_le _
        · refine ⟨FinBox.shiftBack x i, i, hpi h1,
            finBoxDist_shiftBack_le x i⟩
      have hqslot : ∃ sq : FinBox d N, ∃ iq : Fin d,
          ((sq, iq) : PhysicalBond d N) = q ∧
            finBoxDist x sq ≤ 1 := by
        by_cases h1 : ((x, j) : PhysicalBond d N) = q
        · refine ⟨x, j, h1, ?_⟩
          rw [finBoxDist_self]
          exact Nat.zero_le _
        · refine ⟨FinBox.shiftBack x j, j, hqj h1,
            finBoxDist_shiftBack_le x j⟩
      obtain ⟨sp, ip, hpe, hpd⟩ := hpslot
      obtain ⟨sq, iq, hqe, hqd⟩ := hqslot
      have hd : physicalBondDist q p ≤ 2 := by
        rw [← hpe, ← hqe]
        exact div_slots_dist_le x sq sp iq ip hqd hpd
      omega

@[simp]
theorem gaugeFixingMassDefectCLM_apply
    (ρ : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    gaugeFixingMassDefectCLM ρ U A =
      gaugeFixingMassCLM ρ U A -
        gaugeFixingMassCLM ρ
          (trivialPhysicalGaugeBackground d N Nc) A := rfl

/-- Exact mixed telescoping of the gauge-fixing mass defect. -/
theorem gaugeFixingMassDefectCLM_eq_mixed
    (ρ : SUNAdjointModel Nc) (U : PhysicalGaugeBackground d N Nc) :
    gaugeFixingMassDefectCLM ρ U =
      (gaugeConstraintDefectCLM ρ U).adjoint.comp
          (gaugeConstraintQCLM ρ U) +
        (gaugeConstraintQCLM ρ
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
          (gaugeConstraintDefectCLM ρ U) := by
  apply ContinuousLinearMap.ext
  intro A
  apply ext_inner_right ℝ
  intro B
  have hmass (V : PhysicalGaugeBackground d N Nc) :
      inner ℝ (gaugeFixingMassCLM ρ V A) B =
        inner ℝ (gaugeConstraintQCLM ρ V A)
          (gaugeConstraintQCLM ρ V B) := by
    rw [gaugeFixingMassCLM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
  rw [gaugeFixingMassDefectCLM_apply, inner_sub_left,
    hmass U, hmass (trivialPhysicalGaugeBackground d N Nc)]
  simp only [
    ContinuousLinearMap.add_apply, inner_add_left,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left,
    gaugeConstraintDefectCLM_apply,
    inner_sub_right, inner_sub_left]
  ring

/-- A background constraint probe is orthogonal to a far constraint-defect
probe. -/
theorem gaugeConstraint_background_defect_gram_orthogonal
    (ρ : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc)
    (p q : PhysicalBond d N) (v w : SUNLieCoord Nc)
    (hfar : 2 < physicalBondDist q p) :
    inner ℝ
      (gaugeConstraintQCLM ρ V
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v))
      (gaugeConstraintDefectCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) q w)) = 0 := by
  rw [gaugeConstraintDefectCLM_apply, inner_sub_right,
    gaugeConstraint_background_gram_orthogonal ρ V U p q v w hfar,
    gaugeConstraint_background_gram_orthogonal ρ V
      (trivialPhysicalGaugeBackground d N Nc) p q v w hfar,
    sub_zero]

/-- A constraint-defect probe is orthogonal to a far background-constraint
probe. -/
theorem gaugeConstraint_defect_background_gram_orthogonal
    (ρ : SUNAdjointModel Nc)
    (U V : PhysicalGaugeBackground d N Nc)
    (p q : PhysicalBond d N) (v w : SUNLieCoord Nc)
    (hfar : 2 < physicalBondDist q p) :
    inner ℝ
      (gaugeConstraintDefectCLM ρ U
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p v))
      (gaugeConstraintQCLM ρ V
        (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) q w)) = 0 := by
  rw [gaugeConstraintDefectCLM_apply, inner_sub_left,
    gaugeConstraint_background_gram_orthogonal ρ U V p q v w hfar,
    gaugeConstraint_background_gram_orthogonal ρ
      (trivialPhysicalGaugeBackground d N Nc) V p q v w hfar,
    sub_zero]

/-- The background-dependent gauge-fixing mass defect has exact bond range
two. -/
theorem gaugeFixingMassDefectCLM_finiteRange
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) :
    PhysicalCovarianceFiniteRange
      (gaugeFixingMassDefectCLM ρ U) physicalBondDist 2 := by
  rw [gaugeFixingMassDefectCLM_eq_mixed]
  apply physicalCovarianceFiniteRange_add physicalBondDist
  · apply adjointCompMixed_finiteRange
    intro p q v w hfar
    exact gaugeConstraint_background_defect_gram_orthogonal
      ρ U U p q v w hfar
  · apply adjointCompMixed_finiteRange
    intro p q v w hfar
    exact gaugeConstraint_defect_background_gram_orthogonal
      ρ U (trivialPhysicalGaugeBackground d N Nc) p q v w hfar

/-- Under pointwise adjoint smallness `δ`, every kernel block of the
gauge-fixing mass defect is bounded by `4δ`. -/
theorem gaugeFixingMassDefectCLM_kernelBound
    (ρ : SUNAdjointModel Nc)
    (U : PhysicalGaugeBackground d N Nc) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hsmall : PhysicalAdjointSmallBackground ρ U δ) :
    PhysicalCovarianceKernelBound
      (gaugeFixingMassDefectCLM ρ U) (fun _ _ => 4 * δ) := by
  have hfirst :
      PhysicalCovarianceKernelBound
        ((gaugeConstraintDefectCLM ρ U).adjoint.comp
          (gaugeConstraintQCLM ρ U))
        (fun _ _ => (2 : ℝ) * δ) := by
    exact adjointCompMixed_kernelBound
      (gaugeConstraintDefectCLM ρ U)
      (gaugeConstraintQCLM ρ U)
      hδ (by norm_num)
      (gaugeConstraintDefect_single_norm_le ρ U hsmall)
      (gaugeConstraint_background_single_norm_le ρ U)
  have hsecond :
      PhysicalCovarianceKernelBound
        ((gaugeConstraintQCLM ρ
          (trivialPhysicalGaugeBackground d N Nc)).adjoint.comp
          (gaugeConstraintDefectCLM ρ U))
        (fun _ _ => δ * (2 : ℝ)) := by
    exact adjointCompMixed_kernelBound
      (gaugeConstraintQCLM ρ
        (trivialPhysicalGaugeBackground d N Nc))
      (gaugeConstraintDefectCLM ρ U)
      (by norm_num) hδ
      (gaugeConstraint_trivial_single_norm_le ρ)
      (gaugeConstraintDefect_single_norm_le ρ U hsmall)
  rw [gaugeFixingMassDefectCLM_eq_mixed]
  have hsum := physicalCovarianceKernelBound_add hfirst hsecond
  intro p q v
  simpa only [show (2 : ℝ) * δ + δ * 2 = 4 * δ by ring] using
    hsum p q v

end

end YangMills.RG
