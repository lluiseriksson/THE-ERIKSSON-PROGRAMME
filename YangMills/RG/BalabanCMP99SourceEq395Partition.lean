/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99Eq395Algebra
import YangMills.RG.BalabanCMP99SourcePartitionCutoffs
import YangMills.RG.FinitePiLpTypedCutoff

/-!
# The square-partition operator identity used in CMP99 equation (3.95)

CMP99 uses the source normalization `sum_Pi h_Pi(x)^2 = 1` as an operator
identity.  This file proves that passage on the actual finite `L²` fields.
It is independent of the local covariance inverse, which remains the other
source-specific producer needed by (3.95).
-/

namespace YangMills.RG

noncomputable section

/-- Composition of two scalar multipliers is pointwise multiplication, with
the order of the two scalar functions retained literally. -/
theorem finitePiLpScalarMultiplier_comp
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h k : ι → ℝ) :
    (finitePiLpScalarMultiplier (g := g) h).comp
        (finitePiLpScalarMultiplier (g := g) k) =
      finitePiLpScalarMultiplier (g := g) (fun x => h x * k x) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro x
  simp [finitePiLpScalarMultiplier_apply, mul_smul]

/-- A pointwise support relation becomes the exact multiplier relation used
in each localized inverse term of (3.95). -/
theorem finitePiLpScalarMultiplier_comp_eq_of_pointwise_mul
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (h chi : ι → ℝ) (hsupport : ∀ x, h x * chi x = h x) :
    (finitePiLpScalarMultiplier (g := g) h).comp
        (finitePiLpScalarMultiplier (g := g) chi) =
      finitePiLpScalarMultiplier (g := g) h := by
  rw [finitePiLpScalarMultiplier_comp]
  congr
  funext x
  exact hsupport x

/-- The finite square partition of CMP99 resolves the identity on every
finite typed `L²` field after pulling block coordinates back along `blockOf`. -/
theorem sum_cmp99SourceSquarePartition_multiplier_sq_eq_id
    {Q : ℕ} [NeZero Q]
    {ι g : Type*} [Fintype ι]
    [NormedAddCommGroup g] [NormedSpace ℝ g] [FiniteDimensional ℝ g]
    (P : CMP99SourceSquarePartition Q)
    (blockOf : ι → FinBox 4 (2 * Q)) :
    (∑ cell : FinBox 4 Q,
      (finitePiLpScalarMultiplier (g := g)
        (fun x => P.value cell (blockOf x))).comp
      (finitePiLpScalarMultiplier (g := g)
        (fun x => P.value cell (blockOf x)))) =
      ContinuousLinearMap.id ℝ (FinitePiLpField ι g) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [finitePiLpScalarMultiplier_apply]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]
  have hsquare := P.square_sum (blockOf x)
  simp only [pow_two] at hsquare
  rw [hsquare]
  exact one_smul ℝ (f x)

end

end YangMills.RG
