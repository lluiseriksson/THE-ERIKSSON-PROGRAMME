import YangMills.RG.BalabanCMP89CenteredPeriodicL1ResidueSum

/-!
PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

Varying-period product estimate for the rectangular CMP89 image fibre.  Each
coordinate retains its literal period; no rectangle-cardinality factor and no
replacement by a common scalar period are admitted.
-/

namespace YangMills.RG

noncomputable section

/-- Product weight with a distinct positive period in every coordinate. -/
def cmp89CenteredRectangularL1ResidueWeight {d : ℕ}
    (delta : ℝ) (P : Fin d → ℕ) (u n : Fin d → ℤ) : ℝ :=
  ∏ mu, cmp89CenteredPeriodicOneDimensionalExpWeight
    delta (P mu) (u mu) (n mu)

/-- The varying-period product is exactly the signed `l1` exponential weight
of the coordinatewise affine image. -/
theorem cmp89CenteredRectangularL1ResidueWeight_eq_signedLatticeWeight
    {d : ℕ} (delta : ℝ) (P : Fin d → ℕ) (u n : Fin d → ℤ) :
    cmp89CenteredRectangularL1ResidueWeight delta P u n =
      cmp89SignedLatticeL1ExponentialWeight delta
        (fun mu => u mu + (P mu : ℤ) * n mu) := by
  rfl

/-- Positive coordinatewise periods make the rectangular product fibre
summable. -/
theorem summable_cmp89CenteredRectangularL1ResidueWeight
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {P : Fin d → ℕ} (hP : ∀ mu, 0 < P mu) (u : Fin d → ℤ) :
    Summable (cmp89CenteredRectangularL1ResidueWeight delta P u) := by
  unfold cmp89CenteredRectangularL1ResidueWeight
  apply summable_pi_int_prod_nonneg
  · intro mu n
    exact cmp89CenteredPeriodicOneDimensionalExpWeight_nonneg
      delta (P mu) (u mu) n
  · intro mu
    exact summable_cmp89CenteredPeriodicOneDimensionalExpWeight
      hdelta (hP mu) (u mu)

/-- Exact rectangular residue estimate.  The cost is the literal product of
one-dimensional geometric constants and the centered direct weight survives.
-/
theorem tsum_cmp89CenteredRectangularL1ResidueWeight_le
    {d : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    {P : Fin d → ℕ} (hP : ∀ mu, 0 < P mu) (u : Fin d → ℤ)
    (hcenter : ∀ mu, 2 * ((u mu).natAbs : ℤ) ≤ (P mu : ℤ)) :
    (∑' n : Fin d → ℤ,
        cmp89CenteredRectangularL1ResidueWeight delta P u n) ≤
      (∏ mu, 2 / (1 - Real.exp (-delta * (P mu : ℝ)))) *
        cmp89SignedLatticeL1ExponentialWeight delta u := by
  let a : Fin d → ℤ → ℝ := fun mu n =>
    cmp89CenteredPeriodicOneDimensionalExpWeight
      delta (P mu) (u mu) n
  have ha0 : ∀ mu n, 0 ≤ a mu n := fun mu n =>
    cmp89CenteredPeriodicOneDimensionalExpWeight_nonneg
      delta (P mu) (u mu) n
  have ha : ∀ mu, Summable (a mu) := by
    intro mu
    exact summable_cmp89CenteredPeriodicOneDimensionalExpWeight
      hdelta (hP mu) (u mu)
  change (∑' n : Fin d → ℤ, ∏ mu, a mu (n mu)) ≤ _
  rw [tsum_pi_int_prod_nonneg a ha0 ha]
  calc
    (∏ mu, ∑' k : ℤ, a mu k) ≤
        ∏ mu,
          (2 / (1 - Real.exp (-delta * (P mu : ℝ)))) *
            Real.exp (-delta * ((u mu).natAbs : ℝ)) := by
      apply Finset.prod_le_prod
      · intro mu _
        exact tsum_nonneg fun n => ha0 mu n
      · intro mu _
        exact tsum_cmp89CenteredPeriodicOneDimensionalExpWeight_le
          hdelta (hP mu) (u mu) (hcenter mu)
    _ = (∏ mu, 2 / (1 - Real.exp (-delta * (P mu : ℝ)))) *
        cmp89SignedLatticeL1ExponentialWeight delta u := by
      simp only [Finset.prod_mul_distrib]
      rw [cmp89SignedLatticeL1ExponentialWeight]
      rfl

end

end YangMills.RG
