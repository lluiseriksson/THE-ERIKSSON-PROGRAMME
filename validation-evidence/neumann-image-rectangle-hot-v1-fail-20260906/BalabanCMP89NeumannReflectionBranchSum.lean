import YangMills.RG.BalabanCMP89SignedLatticeL1ExponentialSum

/-!
# CMP89 Neumann reflection-branch counting budget

CMP89 (2.42) expands the rectangular free/Neumann Green into positive
reflections.  In `d` coordinates there are `2^d` parity branches, while each
branch still carries an infinite signed translation lattice.  This module
records only that finite branch multiplicity and combines it with the
already sealed finite-box `Int^d` exponential-sum bound.

It deliberately does not assert the reflection representation itself, an
image-orbit injection, a distance comparison, a rectangle/carrier
dictionary, or any regional Green estimate.  In particular, the factor
`2^d` below is not substituted for the infinite image series.
-/

namespace YangMills.RG

noncomputable section

/-- One of the two reflection parities in every coordinate. -/
abbrev CMP89NeumannReflectionBranch (d : ℕ) := Fin d → Bool

/-- A branch carries one copy of the signed-translation finite-box sum.
The branch argument is intentionally visible even though the present weight
does not depend on it: later geometry must provide the branch-specific image
map before this algebra can feed a physical Green estimate. -/
def cmp89NeumannReflectionBranchCenteredWeight
    (d N : ℕ) (delta : ℝ)
    (_branch : CMP89NeumannReflectionBranch d) : ℝ :=
  cmp89SignedLatticeCenteredL1ExponentialSum d N delta

/-- Sum over all `2^d` reflection-parity branches and a finite centered
signed-translation box. -/
def cmp89NeumannReflectionBranchCenteredSum
    (d N : ℕ) (delta : ℝ) : ℝ :=
  ∑ branch : CMP89NeumannReflectionBranch d,
    cmp89NeumannReflectionBranchCenteredWeight d N delta branch

/-- Exact separation of the finite parity multiplicity from the signed
translation sum. -/
theorem cmp89NeumannReflectionBranchCenteredSum_eq_two_pow_mul
    (d N : ℕ) (delta : ℝ) :
    cmp89NeumannReflectionBranchCenteredSum d N delta =
      (2 : ℝ) ^ d *
        cmp89SignedLatticeCenteredL1ExponentialSum d N delta := by
  simp [cmp89NeumannReflectionBranchCenteredSum,
    cmp89NeumannReflectionBranchCenteredWeight]

/-- Uniform finite-box budget: the source reflection parity costs `2^d`,
while the infinite-translation majorant retains the exact product geometric
constant. -/
theorem cmp89NeumannReflectionBranchCenteredSum_le_geometric
    (d N : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    cmp89NeumannReflectionBranchCenteredSum d N delta ≤
      (2 : ℝ) ^ d *
        ((1 + Real.exp (-delta)) / (1 - Real.exp (-delta))) ^ d := by
  rw [cmp89NeumannReflectionBranchCenteredSum_eq_two_pow_mul]
  exact mul_le_mul_of_nonneg_left
    (cmp89SignedLatticeCenteredL1ExponentialSum_le_geometric_pow
      d N hdelta)
    (pow_nonneg (by norm_num) d)

end

end YangMills.RG
