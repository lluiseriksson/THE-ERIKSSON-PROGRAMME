import YangMills.RG.BalabanCMP99PatchedParametrixCorePartition

/-!
# Physical block Schur bound for exponential kernels

An entrywise exponential bound on a physical one-cochain operator implies a
volume-uniform operator-norm bound once the exponential weight has a uniform
row sum.  This is the block-valued Schur step needed to turn the CMP99 patched
parametrix defect estimate into the scalar smallness condition for a Neumann
series.
-/

namespace YangMills.RG

noncomputable section

/-- Block Schur test for a physical operator with exponentially decaying
single-bond columns. -/
theorem physicalOpNorm_le_of_exponentialKernelBound
    {d N Nc : ℕ} [NeZero N]
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (hsymm : ∀ p q, dist p q = dist q p)
    {A rate Ssum : ℝ} (hSsum : 0 ≤ Ssum)
    {D : PhysicalGaugeOneCochain d N Nc →L[ℝ]
      PhysicalGaugeOneCochain d N Nc}
    (hD : PhysicalCovarianceExponentialKernelBound D dist A rate)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(rate * (dist x z : ℝ))) ≤ Ssum) :
    ‖D‖ ≤ A * Ssum := by
  classical
  have hAS : 0 ≤ A * Ssum := mul_nonneg hD.1 hSsum
  apply ContinuousLinearMap.opNorm_le_bound _ hAS
  intro f
  let w : PhysicalBond d N → PhysicalBond d N → ℝ :=
    fun q p => Real.exp (-(rate * (dist q p : ℝ)))
  have hw : ∀ q p, 0 ≤ w q p := fun _ _ => (Real.exp_pos _).le
  have hdecomp :
      D f = ∑ p, D (singlePhysicalBondCochain
        (d := d) (N := N) (Nc := Nc) p (f p)) := by
    rw [← map_sum, sum_singlePhysicalBondCochain_eq]
  have hpoint : ∀ q : PhysicalBond d N,
      ‖D f q‖ ≤ A * ∑ p, w q p * ‖f p‖ := by
    intro q
    have happ :
        D f q = ∑ p, D (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p (f p)) q := by
      rw [hdecomp, physicalCochain_sum_apply]
    rw [happ]
    calc
      ‖∑ p, D (singlePhysicalBondCochain
          (d := d) (N := N) (Nc := Nc) p (f p)) q‖
          ≤ ∑ p, ‖D (singlePhysicalBondCochain
            (d := d) (N := N) (Nc := Nc) p (f p)) q‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p, A * w q p * ‖f p‖ :=
        Finset.sum_le_sum (fun p _ => hD.2.2 p q (f p))
      _ = A * ∑ p, w q p * ‖f p‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hweightedCS : ∀ q : PhysicalBond d N,
      (∑ p, w q p * ‖f p‖) ^ 2 ≤
        (∑ p, w q p) * ∑ p, w q p * ‖f p‖ ^ 2 := by
    intro q
    let F : PhysicalBond d N → ℝ := fun p => Real.sqrt (w q p)
    let G : PhysicalBond d N → ℝ := fun p => Real.sqrt (w q p) * ‖f p‖
    have hFG : ∑ p, F p * G p = ∑ p, w q p * ‖f p‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [F, G]
      rw [show Real.sqrt (w q p) * (Real.sqrt (w q p) * ‖f p‖) =
          (Real.sqrt (w q p) * Real.sqrt (w q p)) * ‖f p‖ by ring,
        Real.mul_self_sqrt (hw q p)]
    have hFsq : ∑ p, (F p) ^ 2 = ∑ p, w q p := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [F, Real.sq_sqrt (hw q p)]
    have hGsq : ∑ p, (G p) ^ 2 = ∑ p, w q p * ‖f p‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [G, mul_pow, Real.sq_sqrt (hw q p)]
    rw [← hFG, ← hFsq, ← hGsq]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  have hterm : ∀ q : PhysicalBond d N,
      ‖D f q‖ ^ 2 ≤
        A ^ 2 * Ssum * ∑ p, w q p * ‖f p‖ ^ 2 := by
    intro q
    have h1 : ‖D f q‖ ^ 2 ≤
        (A * ∑ p, w q p * ‖f p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hpoint q) 2
    have hrow : ∑ p, w q p ≤ Ssum := hsum q
    have hweighted : 0 ≤ ∑ p, w q p * ‖f p‖ ^ 2 :=
      Finset.sum_nonneg (fun p hp => mul_nonneg (hw q p) (sq_nonneg _))
    calc
      ‖D f q‖ ^ 2 ≤ (A * ∑ p, w q p * ‖f p‖) ^ 2 := h1
      _ = A ^ 2 * (∑ p, w q p * ‖f p‖) ^ 2 := by ring
      _ ≤ A ^ 2 * ((∑ p, w q p) *
            ∑ p, w q p * ‖f p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hweightedCS q) (sq_nonneg A)
      _ ≤ A ^ 2 * (Ssum * ∑ p, w q p * ‖f p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrow hweighted) (sq_nonneg A)
      _ = A ^ 2 * Ssum * ∑ p, w q p * ‖f p‖ ^ 2 := by ring
  have hcol : ∀ p : PhysicalBond d N, ∑ q, w q p ≤ Ssum := by
    intro p
    calc
      ∑ q, w q p = ∑ q, w p q := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [w]
        rw [hsymm q p]
      _ ≤ Ssum := hsum p
  have hdouble :
      ∑ q, ∑ p, w q p * ‖f p‖ ^ 2 ≤
        Ssum * ∑ p, ‖f p‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol p) (sq_nonneg _)
  have hDf : ‖D f‖ ^ 2 = ∑ q, ‖D f q‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ (D f)
  have hff : ‖f‖ ^ 2 = ∑ p, ‖f p‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ f
  have hsq : ‖D f‖ ^ 2 ≤ (A * Ssum * ‖f‖) ^ 2 := by
    calc
      ‖D f‖ ^ 2 = ∑ q, ‖D f q‖ ^ 2 := hDf
      _ ≤ ∑ q, A ^ 2 * Ssum * ∑ p, w q p * ‖f p‖ ^ 2 :=
        Finset.sum_le_sum (fun q hq => hterm q)
      _ = A ^ 2 * Ssum *
          (∑ q, ∑ p, w q p * ‖f p‖ ^ 2) := by
        rw [← Finset.mul_sum]
      _ ≤ A ^ 2 * Ssum * (Ssum * ∑ p, ‖f p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdouble
          (mul_nonneg (sq_nonneg A) hSsum)
      _ = (A * Ssum * ‖f‖) ^ 2 := by
        rw [← hff]
        ring
  have hleft : 0 ≤ ‖D f‖ := norm_nonneg _
  have hright : 0 ≤ A * Ssum * ‖f‖ := by positivity
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

end

end YangMills.RG
