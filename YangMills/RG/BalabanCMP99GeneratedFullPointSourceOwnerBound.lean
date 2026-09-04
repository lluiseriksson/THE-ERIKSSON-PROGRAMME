import YangMills.RG.BalabanCMP99PhysicalFullGreenOwnerResidueBound
import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPointSourceResidueClass

/-!
# PRE-VALIDATION: generated full point-source bound, fixed coefficient

Source is present; the `.olean` is not materialized and this result is not
verified by the compiler. This consumer and its step-14 dependency are PRE-VALIDATION.
They are not imported into the verified root.

Fine-block K^-4 is paid exactly once. The point-source reconstruction is
obtained by the existing theorem, not supplied as a free equality. The
generated averaging coefficient is retained literally; it is not identified
with the source-flow coefficient. This does not give a depth-uniform B0,
attain window 15, move 20/41 or instantiate TermSource.
-/

namespace YangMills.RG

noncomputable section

/-- All fixed-coefficient value costs, with normalization and contour
amplitude separate. This is not a source-flow uniformity certificate. -/
def cmp99PhysicalFullGreenOwnerAmplitude (K : ℕ) (a rho : ℝ) : ℝ :=
  (((K : ℝ) ^ 4)⁻¹) *
    (cmp89Eq246DirectedFullSolutionSumBound K 1 a rho *
      ((2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho)))

/-- Convert only the scalar normalization in the literal residue sum.
There is no additional site-cardinality factor in this identity. -/
theorem norm_cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum_eq
    {M Q : ℕ} [NeZero M] [NeZero Q] (depth : ℕ) (a : ℝ)
    (source target : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q)))) :
    ‖cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum
      (M := M) (Q := Q) depth a source target‖ =
      ((((M ^ (depth + 1) : ℕ) : ℝ) ^ 4)⁻¹) *
        ‖cmp99PhysicalFullGreenUnscaledOwnerResidueSum
          (K := M ^ (depth + 1)) (N := 2 * (M * Q)) a source target‖ := by
  change ‖(((((M ^ (depth + 1) : ℕ) : ℂ) ^ 4)⁻¹) *
    cmp99PhysicalFullGreenUnscaledOwnerResidueSum
      (K := M ^ (depth + 1)) (N := 2 * (M * Q)) a source target)‖ = _
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]

/-- The normalized literal scalar residue sum inherits owner decay. -/
theorem norm_cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum_le_owner
    {M Q : ℕ} [NeZero M] [NeZero Q] (depth : ℕ) {a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hdenWindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho)
    (source target : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q)))) :
    ‖cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum
      (M := M) (Q := Q) depth a source target‖ ≤
      cmp99PhysicalFullGreenOwnerAmplitude (M ^ (depth + 1)) a rho *
        Real.exp (-rho * (finBoxDist
          (blockSite (M ^ (depth + 1)) (2 * (M * Q)) source)
          (blockSite (M ^ (depth + 1)) (2 * (M * Q)) target) : ℝ)) := by
  rw [norm_cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum_eq]
  have h := norm_cmp99PhysicalFullGreenUnscaledOwnerResidueSum_le_owner
    (K := M ^ (depth + 1)) (N := 2 * (M * Q))
    ha hrho hamplitude hradius hdenWindow hpairWindow source target
  have hscale : 0 ≤ ((((M ^ (depth + 1) : ℕ) : ℝ) ^ 4)⁻¹) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left h hscale
  simpa only [cmp99PhysicalFullGreenOwnerAmplitude, mul_assoc] using hscaled

/-- Proposition-valued endpoint certificate keeps the specialized physical
operator out of the producer's reducible theorem header. Every cost is literal. -/
structure CMP99GeneratedFullPointSourceOwnerBoundCertificate
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    (data : CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassData M Q Nc) : Prop where
  owner_bound :
    ‖cmp99SourceGeneratedFlatPhysicalPointSourceGreenValue
      (M := M) (Q := Q) (Nc := Nc) data.hM data.depth
      data.source data.target data.v data.A‖ ≤
      (cmp99PhysicalFullGreenOwnerAmplitude (M ^ (data.depth + 1))
        (cmp99SourceGeneratedFullComplexA 4 M (data.depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing M (data.depth + 1)) 0) data.rho *
        Real.exp (-data.rho * (finBoxDist
          (blockSite (M ^ (data.depth + 1)) (2 * (M * Q)) data.source)
          (blockSite (M ^ (data.depth + 1)) (2 * (M * Q)) data.target) : ℝ))) *
        ‖data.v data.A‖

/-- Construct the equality certificate internally and then apply the
fixed-coefficient scalar estimate; no reconstruction hypothesis is added. -/
theorem cmp99GeneratedFullPointSourceOwnerBound
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    (data : CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassData M Q Nc) :
    CMP99GeneratedFullPointSourceOwnerBoundCertificate data := by
  constructor
  have heq :=
    (cmp99SourceGeneratedFlatPhysicalPointSourceGreen_apply_eq_scaledResidueClass
      data).eq_scaledResidueClass
  rw [heq, norm_mul]
  have ha := (cmp99SourceGeneratedFullComplexA_pos_physical M data.depth).le
  have h := norm_cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum_le_owner
    (M := M) (Q := Q) data.depth ha data.hrho data.hamplitude
    data.hradius data.hdenWindow data.hpairWindow data.source data.target
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end

end YangMills.RG
