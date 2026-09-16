/-
STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

Mass-uniform periodization of the literal CMP89 fine-lattice left derivative.
The coefficient is constructed from the normalized derivative kernel, and
the divided difference is transported through the zero-residue `tsum` using
absolute summability.  No positive-mass premise, supplied derivative family,
regional `B0`, window-15 attainment or terminal field is asserted here.
-/

-- Promotion imports:
-- import YangMills.RG.BalabanCMP89Eq249FineLatticeLeftDerivativeMassUniformBound
-- import YangMills.RG.BalabanCMP89CenteredGreenFourierSummability
-- import YangMills.RG.BalabanCMP99CenteredPeriodicEndpointDictionary

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- Literal normalized left-derivative coefficient in the affine residue
fibre based at `u` and lattice scale `L^j`. -/
def cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
    (L j : ℕ) [NeZero L] (mass a : ℝ) (mu : Fin 4)
    (u n : Fin 4 → ℤ) : ℂ :=
  cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
    L j mass a mu (cmp89SignedLatticeResidueAffineMap (L ^ j) u n)

/-- The ordinary coordinate shift commutes with the affine residue map.  This
small algebraic lemma prevents D4c from relying on simplifier normalization
of two differently parenthesized integer additions. -/
theorem cmp89SignedLatticeResidueAffineMap_forwardCoordinateShift_draft
    {d M : ℕ} (mu : Fin d) (u n : Fin d → ℤ) :
    cmp89SignedLatticeResidueAffineMap M
        (cmp89Eq248FineLatticeForwardCoordinateShift mu u) n =
      cmp89Eq248FineLatticeForwardCoordinateShift mu
        (cmp89SignedLatticeResidueAffineMap M u n) := by
  funext nu
  by_cases hnu : nu = mu
  · subst nu
    simp [cmp89SignedLatticeResidueAffineMap,
      cmp89Eq248FineLatticeForwardCoordinateShift]
    ring
  · simp [cmp89SignedLatticeResidueAffineMap,
      cmp89Eq248FineLatticeForwardCoordinateShift, hnu]

/-- The literal affine-residue derivative coefficients are absolutely
summable at every positive common radius. -/
theorem summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_draft
    {L j : ℕ} [NeZero L] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (u : Fin 4 → ℤ) :
    Summable
      (cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
        L j mass a mu u) := by
  let M : ℕ := L ^ j
  let amplitude : ℝ :=
    cmp89Eq251ComplexFineLatticeStabilizedEndpointAmplitudeBound a rho
  have hM : 0 < M := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j
  have hweight :=
    summable_cmp89SignedLatticeL1ExponentialWeight_physicalResidue
      (d := 4) hM hrho u
  have hmajor := hweight.mul_right amplitude
  apply Summable.of_norm_bounded hmajor
  intro n
  have hderiv :=
    norm_cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel_le_massUniform_draft
      (L := L) (j := j) (mass := mass) (a := a) (rho := rho)
      ha hrho.le hamplitude hradius hwindow hmass mu
      (cmp89SignedLatticeResidueAffineMap M u n)
  simpa [cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient,
    M, amplitude,
    cmp89Eq248PhysicalFineGreenDecay_eq_signedLatticeWeight_draft]
    using hderiv

/-- Restricting the absolutely summable derivative family to the exact
zero-residue subtype preserves summability. -/
theorem summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_zeroResidue_draft
    {K N : ℕ} [NeZero K] [NeZero N] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (u : Fin 4 → ℤ) :
    Summable (fun n : CMP99FlatIntegerResidueClass 4 N 0 ⇒
      cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
        K 1 mass a mu u n.1) := by
  have hfull :=
    summable_cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient_draft
      (L := K) (j := 1) (mass := mass) (a := a) (rho := rho)
      ha hrho hamplitude hradius hwindow hmass mu u
  exact hfull.subtype _

/-- The forward difference of the two periodized Green series is the
periodized literal derivative series.  The equality is mass-uniform and thus
specializes directly to the physical `mass = 0` branch. -/
theorem tsum_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_forwardDifference_eq_derivative_draft
    {K N : ℕ} [NeZero K] [NeZero N] {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (mu : Fin 4) (u : Fin 4 → ℤ) :
    ((∑' n : CMP99FlatIntegerResidueClass 4 N 0,
          cmp89Eq248CenteredGreenPhysicalFourierCoefficient K 1 mass a
            (cmp89Eq248FineLatticeForwardCoordinateShift mu u) n.1) -
        ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
          cmp89Eq248CenteredGreenPhysicalFourierCoefficient
            K 1 mass a u n.1) /
        (cmp89Eq249FineLatticeSpacing K 1 : ℂ) =
      ∑' n : CMP99FlatIntegerResidueClass 4 N 0,
        cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
          K 1 mass a mu u n.1 := by
  let shifted := fun n : CMP99FlatIntegerResidueClass 4 N 0 ⇒
    cmp89Eq248CenteredGreenPhysicalFourierCoefficient K 1 mass a
      (cmp89Eq248FineLatticeForwardCoordinateShift mu u) n.1
  let base := fun n : CMP99FlatIntegerResidueClass 4 N 0 ⇒
    cmp89Eq248CenteredGreenPhysicalFourierCoefficient K 1 mass a u n.1
  let deriv := fun n : CMP99FlatIntegerResidueClass 4 N 0 ⇒
    cmp89Eq249CenteredGreenPhysicalFourierLeftDerivativeCoefficient
      K 1 mass a mu u n.1
  have hshifted : Summable shifted := by
    have hfull :=
      summable_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_draft
        (L := K) (j := 1) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass
        (cmp89Eq248FineLatticeForwardCoordinateShift mu u)
    exact hfull.subtype _
  have hbase : Summable base := by
    have hfull :=
      summable_cmp89Eq248CenteredGreenPhysicalFourierCoefficient_draft
        (L := K) (j := 1) (mass := mass) (a := a) (rho := rho)
        ha hrho hamplitude hradius hwindow hmass u
    exact hfull.subtype _
  have hpoint : ∀ n, (shifted n - base n) /
      (cmp89Eq249FineLatticeSpacing K 1 : ℂ) = deriv n := by
    intro n
    change
      (cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen K 1 mass a
            (cmp89SignedLatticeResidueAffineMap K
              (cmp89Eq248FineLatticeForwardCoordinateShift mu u) n.1) -
          cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen K 1 mass a
            (cmp89SignedLatticeResidueAffineMap K u n.1)) /
          (cmp89Eq249FineLatticeSpacing K 1 : ℂ) =
        cmp89Eq249NormalizedFineLatticeStabilizedFourierLeftDerivativeKernel
          K 1 mass a mu (cmp89SignedLatticeResidueAffineMap K u n.1)
    rw [cmp89SignedLatticeResidueAffineMap_forwardCoordinateShift_draft]
    exact
      (cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_forwardDifference_massUniform_draft
        (L := K) (j := 1) (mass := mass) (a := a) (rho := rho)
        ha hrho.le hamplitude hradius hwindow hmass mu
        (cmp89SignedLatticeResidueAffineMap K u n.1))
  change ((∑' n, shifted n) - ∑' n, base n) /
      (cmp89Eq249FineLatticeSpacing K 1 : ℂ) = ∑' n, deriv n
  rw [div_eq_mul_inv, ← hshifted.tsum_sub hbase,
    (hshifted.sub hbase).tsum_mul_right]
  apply tsum_congr
  intro n
  simpa [div_eq_mul_inv] using hpoint n

end

end YangMills.RG
