import YangMills.RG.WeightedFlatRepairWall

/-! Actual stacked forward differences and the finite periodic cross-term
cancellation. The full curl/divergence energy identification is not assumed
here and remains a separate transport obligation. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1200000

section Summation
variable {d n : ℕ} [NeZero n]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem flat_forward_summation_by_parts (f h : FinBox d n → V) (i : Fin d) :
    (∑ x, inner ℝ (f (x.shift i) - f x) (h x)) =
      -(∑ x, inner ℝ (f x) (h x - h (x.shiftBack i))) := by
  classical
  have hs := FinBox.sum_shiftBack
    (fun x : FinBox d n => inner ℝ (f (x.shift i)) (h x)) i
  simp only [FinBox.shift_shiftBack] at hs
  simp only [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  linarith

theorem flat_commuting_cross_cancellation (f g : FinBox d n → V) (i j : Fin d) :
    (∑ x, inner ℝ (f (x.shift i) - f x) (g (x.shift j) - g x)) =
      ∑ x, inner ℝ (f x - f (x.shiftBack j)) (g x - g (x.shiftBack i)) := by
  classical
  let Dg := fun x : FinBox d n => g (x.shift j) - g x
  let Bg := fun x : FinBox d n => g x - g (x.shiftBack i)
  have hc (x : FinBox d n) :
      Dg x - Dg (x.shiftBack i) = Bg (x.shift j) - Bg x := by
    dsimp [Dg, Bg]
    rw [FinBox.shift_shiftBack_comm]
    abel
  have h₁ := flat_forward_summation_by_parts f Dg i
  simp_rw [hc] at h₁
  have h₂ := flat_forward_summation_by_parts Bg f j
  simp only [real_inner_comm] at h₂
  have hswap :
      (∑ x, inner ℝ (Bg x) (f x - f (x.shiftBack j))) =
        ∑ x, inner ℝ (f x - f (x.shiftBack j)) (g x - g (x.shiftBack i)) := by
    apply Finset.sum_congr rfl
    intro x _
    exact real_inner_comm _ _
  rw [hswap] at h₂
  change (∑ x, inner ℝ (f (x.shift i) - f x) (Dg x)) = _
  linarith

theorem flat_backward_forward_energy (f : FinBox d n → V) (i : Fin d) :
    (∑ x, ‖f x - f (x.shiftBack i)‖ ^ 2) =
      ∑ x, ‖f (x.shift i) - f x‖ ^ 2 := by
  classical
  have hs := FinBox.sum_shiftBack
    (fun x : FinBox d n => ‖f (x.shift i) - f x‖ ^ 2) i
  simpa only [FinBox.shift_shiftBack] using hs
end Summation

section Physical
variable {d n Nc : ℕ} [NeZero d] [NeZero n] [NeZero Nc]

abbrev PhysicalGradientIndex (d n : ℕ) [NeZero n] := Fin d × PhysicalBond d n
abbrev PhysicalStackedGradient (d n Nc : ℕ) [NeZero n] :=
  PiLp 2 (fun _ : PhysicalGradientIndex d n => SUNLieCoord Nc)

noncomputable def componentwiseFlatGradientCLM :
    PhysicalGaugeOneCochain d n Nc →L[ℝ] PhysicalStackedGradient d n Nc :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => WithLp.toLp 2
        (fun p => A ((p.2.1).shift p.1, p.2.2) - A p.2)
      map_add' := by
        intro A B
        apply PiLp.ext
        intro p
        change (A _ + B _) - (A _ + B _) = (A _ - A _) + (B _ - B _)
        abel
      map_smul' := by
        intro r A
        apply PiLp.ext
        intro p
        change r • A _ - r • A _ = r • (A _ - A _)
        exact (smul_sub r _ _).symm }

@[simp] theorem componentwiseFlatGradient_apply (A : PhysicalGaugeOneCochain d n Nc)
    (p : PhysicalGradientIndex d n) :
    componentwiseFlatGradientCLM A p =
      A ((p.2.1).shift p.1, p.2.2) - A p.2 := rfl

theorem componentwiseFlatGradient_energy (A : PhysicalGaugeOneCochain d n Nc) :
    ‖componentwiseFlatGradientCLM A‖ ^ 2 =
      ∑ p : PhysicalGradientIndex d n, ‖A ((p.2.1).shift p.1, p.2.2) - A p.2‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

noncomputable def componentwiseWeightedRepairCLM (w : PhysicalGradientIndex d n → ℝ) :
    PhysicalGaugeOneCochain d n Nc →L[ℝ] PhysicalGaugeOneCochain d n Nc :=
  let G : PhysicalGaugeOneCochain d n Nc →L[ℝ] PhysicalStackedGradient d n Nc :=
    componentwiseFlatGradientCLM
  G.adjoint.comp ((coordinateWeightCLM w).comp G)

theorem componentwiseWeightedRepair_energy (w : PhysicalGradientIndex d n → ℝ)
    (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM w A) =
      ∑ p : PhysicalGradientIndex d n,
        w p * ‖A ((p.2.1).shift p.1, p.2.2) - A p.2‖ ^ 2 := by
  simp only [componentwiseWeightedRepairCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, coordinateWeight_inner,
    componentwiseFlatGradient_apply]

theorem componentwiseWeightedRepair_nonneg (w : PhysicalGradientIndex d n → ℝ)
    (hw : ∀ p, 0 ≤ w p) (A : PhysicalGaugeOneCochain d n Nc) :
    0 ≤ inner ℝ A (componentwiseWeightedRepairCLM w A) := by
  rw [componentwiseWeightedRepair_energy]
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (hw p) (sq_nonneg _))

theorem componentwiseWeightedRepair_le_gradient (w : PhysicalGradientIndex d n → ℝ)
    (M : ℝ) (hw : ∀ p, w p ≤ M) (A : PhysicalGaugeOneCochain d n Nc) :
    inner ℝ A (componentwiseWeightedRepairCLM w A) ≤
      M * ‖componentwiseFlatGradientCLM A‖ ^ 2 := by
  simp only [componentwiseWeightedRepairCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact coordinateWeight_inner_le w M hw _
end Physical
end YangMills.RG
