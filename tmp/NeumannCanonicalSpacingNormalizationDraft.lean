import YangMills.RG.NeumannCanonicalPrecisionOffsetAction
import YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse

/-!
PRE-VALIDATION: source present; .olean not materialized and this draft has
not been compiler-verified. R1 scalar normalization, not an inverse theorem.

The scale is fixed in the signature: fine spacing (M^(steps+1))^-1.
The internally constructed retained tower then has terminal spacing one.
Its counting-Hilbert coefficient includes B^d exactly once; the counting
mass has weight B^(-2d), giving a_r B^(-d). No fibre count is inserted.
The bare mass, Laplacian, boundary equations, B0 and window15 are untouched.
-/

namespace YangMills.RG

open YangMills Matrix
open scoped BigOperators Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

/-- Unit terminal spacing is derived from the literal fine spacing. -/
theorem neumannCanonicalFourierSpacing_terminal_eq_one
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N) (steps : ℕ) :
    let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
      (Nc := Nc) hd hM Omega steps ((M : ℝ) ^ (steps + 1))⁻¹
    let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
    (T.towerAt r.1).terminalSpacing = 1 := by
  dsimp only
  rw [CMP99SourceRetainedPhysicalTower.towerAt_terminalSpacing]
  change (M : ℝ) ^ (steps + 1) * ((M : ℝ) ^ (steps + 1))⁻¹ = 1
  exact mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M)))

/-- Counting coefficient before applying the counting mass: a_r B^d. -/
theorem neumannCanonicalFourierSpacing_countingCoefficient
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (steps : ℕ) (a : ℝ) :
    let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
      (Nc := Nc) hd hM Omega steps ((M : ℝ) ^ (steps + 1))⁻¹
    let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
    cmp85SourcePrefixCountingCoefficient T a r =
      cmp85SourcePrefixA (M := M) a r * ((M : ℝ) ^ (steps + 1)) ^ d := by
  dsimp only
  rw [cmp85SourcePrefixCountingCoefficient_eq hd _ a
    (inv_pos.mpr (pow_pos (by exact_mod_cast (NeZero.pos M)) _))]
  rw [neumannCanonicalFourierSpacing_terminal_eq_one hd hM Omega steps]
  simp only [one_pow, mul_one, inv_pow, div_inv_eq_mul]

/-- Combined coefficient has one, not two, averaging weights. This does not
sum the fibre again and does not identify a Fourier inverse. -/
theorem neumannCanonicalFourierSpacing_countingMassCoefficient
    (hd : 2 ≤ d) (hM : 2 ≤ M) (Omega : ActiveGaugeRegion d N)
    (steps : ℕ) (a : ℝ) :
    let T := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannTower
      (Nc := Nc) hd hM Omega steps ((M : ℝ) ^ (steps + 1))⁻¹
    let r := cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannLastPrefix steps
    cmp85SourcePrefixCountingCoefficient T a r *
        (cmp99SourceBlockAverageWeight M d) ^ (2 * (steps + 1)) =
      cmp85SourcePrefixA (M := M) a r *
        cmp99SourceBlockAverageWeight (M ^ (steps + 1)) d := by
  dsimp only
  rw [neumannCanonicalFourierSpacing_countingCoefficient hd hM Omega steps a,
    cmp99SourceBlockAverageWeight_two_mul_eq_oneBlock_sq]
  unfold cmp99SourceBlockAverageWeight
  rw [Nat.cast_pow]
  have hB : (M : ℝ) ^ (steps + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have hBd : ((M : ℝ) ^ (steps + 1)) ^ d ≠ 0 := pow_ne_zero _ hB
  field_simp [hBd]
  <;> ring

#print axioms neumannCanonicalFourierSpacing_terminal_eq_one
#print axioms neumannCanonicalFourierSpacing_countingCoefficient
#print axioms neumannCanonicalFourierSpacing_countingMassCoefficient

end
end YangMills.RG
