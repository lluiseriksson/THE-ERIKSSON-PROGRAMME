import tmp.P1CoefficientMonotonicity
import YangMills.RG.BalabanCMP99SourceTowerCoarseCovariance

/-!
PRE-VALIDATION SCRATCH: source present under `tmp`; no `.olean` has been
materialized and no declaration in this file has been compiler-verified.

Scratch-only elaboration target for Step 8b.24/P2a.

The generic lemmas below do not construct any physical coefficient or
operator.  In their future source-facing consumer, `b` is the coefficient of
`Q.adjoint Q` in Lean's counting Hilbert structure.  It is therefore the
printed coefficient multiplied by the exact terminal/fine volume ratio, not
the printed coefficient itself.  The consumer must derive that ratio from the
retained prefix package, prove equality with the source-weighted-adjoint
presentation, and keep the bare mass distinct from the flowing averaging
coefficient.
-/

namespace YangMills.RG

open scoped Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable section

/-- Scalar two-weight absorption with the exact robust floor used by the
counting-Hilbert presentation of the source-`a_j` precision. -/
theorem scratch_twoWeightPoincare_coercivity
    {fieldNorm energy qnorm A B C b : ℝ}
    (henergy : 0 ≤ energy) (hqnorm : 0 ≤ qnorm)
    (hA : 0 < A) (hC : 0 < C) (hb : 0 < b)
    (hraw : (1 - B) * fieldNorm ≤ A * energy + C * qnorm) :
    (1 - B) * min A⁻¹ (b * C⁻¹) * fieldNorm ≤
      energy + b * qnorm := by
  let weight := min A⁻¹ (b * C⁻¹)
  have hweight : 0 < weight := by
    exact lt_min (inv_pos.mpr hA) (mul_pos hb (inv_pos.mpr hC))
  have hweightA : weight * A ≤ 1 := by
    calc
      weight * A ≤ A⁻¹ * A :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hA.le
      _ = 1 := by field_simp [hA.ne']
  have hweightC : weight * C ≤ b := by
    calc
      weight * C ≤ (b * C⁻¹) * C :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
      _ = b := by field_simp [hC.ne']
  have hscaled := mul_le_mul_of_nonneg_left hraw hweight.le
  calc
    (1 - B) * min A⁻¹ (b * C⁻¹) * fieldNorm =
        weight * ((1 - B) * fieldNorm) := by ring
    _ ≤ weight * (A * energy + C * qnorm) := hscaled
    _ = (weight * A) * energy + (weight * C) * qnorm := by ring
    _ ≤ 1 * energy + b * qnorm :=
      add_le_add
        (mul_le_mul_of_nonneg_right hweightA henergy)
        (mul_le_mul_of_nonneg_right hweightC hqnorm)
    _ = energy + b * qnorm := by ring

/-- Strict positivity of the exact robust floor.  The smallness input
`B < 1` is consumed here, not carried as a dead premise by the absorption
lemma. -/
theorem scratch_twoWeightPoincare_coercivityConstant_pos
    {A B C b : ℝ} (hA : 0 < A) (hB : B < 1)
    (hC : 0 < C) (hb : 0 < b) :
    0 < (1 - B) * min A⁻¹ (b * C⁻¹) :=
  mul_pos (sub_pos.mpr hB)
    (lt_min (inv_pos.mpr hA) (mul_pos hb (inv_pos.mpr hC)))

/-- Operator form of the same absorption.  This lemma is intentionally
generic: the physical P2a theorem must derive `hraw` and `hDnonneg` from the
canonical retained prefix, rather than pass them through its public API. -/
theorem scratch_isCoerciveCLM_of_twoWeightPoincare
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : E →L[ℝ] E) (Q : E →L[ℝ] F)
    {A B C b : ℝ} (hA : 0 < A) (hC : 0 < C) (hb : 0 < b)
    (hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi))
    (hraw : ∀ phi,
      (1 - B) * ‖phi‖ ^ 2 ≤
        A * inner ℝ phi (D phi) + C * ‖Q phi‖ ^ 2) :
    IsCoerciveCLM (cmp99SourceGaugePrecision D Q b)
      ((1 - B) * min A⁻¹ (b * C⁻¹)) := by
  intro phi
  rw [inner_cmp99SourceGaugePrecision]
  exact scratch_twoWeightPoincare_coercivity
    (hDnonneg phi) (sq_nonneg ‖Q phi‖) hA hC hb (hraw phi)

/-- CMP85's bare physical precision before the block-average term.  The bare
mass is deliberately independent of the flowing averaging coefficient. -/
noncomputable def scratch_cmp85BareMassPrecision
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : E →L[ℝ] E) (mass : ℝ) : E →L[ℝ] E :=
  D + mass ^ 2 • ContinuousLinearMap.id ℝ E

theorem scratch_inner_cmp85BareMassPrecision
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : E →L[ℝ] E) (mass : ℝ) (phi : E) :
    inner ℝ phi (scratch_cmp85BareMassPrecision D mass phi) =
      inner ℝ phi (D phi) + mass ^ 2 * ‖phi‖ ^ 2 := by
  rw [scratch_cmp85BareMassPrecision, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [conj_trivial]

/-- The independent bare-mass square preserves symmetry. -/
theorem scratch_cmp85BareMassPrecision_isSymmetric
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : E →L[ℝ] E) (mass : ℝ) (hD : D.IsSymmetric) :
    (scratch_cmp85BareMassPrecision D mass).IsSymmetric := by
  let A := scratch_cmp85BareMassPrecision D mass
  have hAdj : A.adjoint = A := by
    simp [A, scratch_cmp85BareMassPrecision, hD.clm_adjoint_eq]
  exact (ContinuousLinearMap.eq_adjoint_iff A A).mp hAdj.symm

/-- Adding the independent nonnegative bare-mass quadratic form preserves the
exact two-weight floor.  No positivity of the bare mass itself is required;
only its literal square occurs. -/
theorem scratch_isCoerciveCLM_of_twoWeightPoincare_with_bareMass
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : E →L[ℝ] E) (Q : E →L[ℝ] F) (mass : ℝ)
    {A B C b : ℝ} (hA : 0 < A) (hC : 0 < C) (hb : 0 < b)
    (hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi))
    (hraw : ∀ phi,
      (1 - B) * ‖phi‖ ^ 2 ≤
        A * inner ℝ phi (D phi) + C * ‖Q phi‖ ^ 2) :
    IsCoerciveCLM
      (cmp99SourceGaugePrecision
        (scratch_cmp85BareMassPrecision D mass) Q b)
      ((1 - B) * min A⁻¹ (b * C⁻¹)) := by
  apply scratch_isCoerciveCLM_of_twoWeightPoincare
    (D := scratch_cmp85BareMassPrecision D mass) (Q := Q)
    hA hC hb
  · intro phi
    rw [scratch_inner_cmp85BareMassPrecision]
    exact add_nonneg (hDnonneg phi)
      (mul_nonneg (sq_nonneg mass) (sq_nonneg ‖phi‖))
  · intro phi
    calc
      (1 - B) * ‖phi‖ ^ 2 ≤
          A * inner ℝ phi (D phi) + C * ‖Q phi‖ ^ 2 := hraw phi
      _ ≤ A * inner ℝ phi
            (scratch_cmp85BareMassPrecision D mass phi) +
          C * ‖Q phi‖ ^ 2 := by
        rw [scratch_inner_cmp85BareMassPrecision]
        gcongr
        exact mul_nonneg (sq_nonneg mass) (sq_nonneg ‖phi‖)

/-! ## Source-weighted versus counting-Hilbert coefficient -/

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable {rho : SUNAdjointModel Nc}
variable {Omega : ActiveGaugeRegion d N} {spacing : ℝ}
variable {background : GaugeConfig d N (SUN Nc)}

/-- A positive physical prefix.  CMP85 source index one is the first member;
the empty retained prefix is excluded by the type. -/
abbrev ScratchCMP85PositivePrefix (depth : ℕ) :=
  {r : Fin (depth + 1) // 0 < r.val}

/-- CMP85's `a_j`, with source index one represented by recurrence index
zero in `cmp99SourceMassParameter`. -/
def scratch_cmp85SourcePrefixA
    (a : ℝ) (r : ScratchCMP85PositivePrefix depth) : ℝ :=
  cmp99SourceMassParameter a (M : ℝ) (r.1.val - 1)

/-- The literal coefficient `a_j (L^j epsilon)^(-2)` multiplying the
source-weighted adjoint in CMP85 (2.20). -/
def scratch_cmp85SourcePrefixWeightedCoefficient
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (a : ℝ) (r : ScratchCMP85PositivePrefix depth) : ℝ :=
  scratch_cmp85SourcePrefixA (M := M) a r *
    (T.towerAt r.1).terminalSpacing⁻¹ ^ 2

/-- Exact conversion factor from the source-weighted adjoint to Lean's
counting-Hilbert adjoint. -/
def scratch_cmp85SourcePrefixVolumeRatio
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (r : ScratchCMP85PositivePrefix depth) : ℝ :=
  (T.towerAt r.1).terminalSpacing ^ d / spacing ^ d

/-- Coefficient multiplying `Q.adjoint Q` in Lean's counting Hilbert
structure.  This is not the printed coefficient: it includes the exact
terminal/fine volume ratio. -/
def scratch_cmp85SourcePrefixCountingCoefficient
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (a : ℝ) (r : ScratchCMP85PositivePrefix depth) : ℝ :=
  scratch_cmp85SourcePrefixWeightedCoefficient T a r *
    scratch_cmp85SourcePrefixVolumeRatio T r

theorem scratch_cmp85SourcePrefixWeightedCoefficient_pos
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    {a : ℝ} (ha : 0 < a) (hspacing : 0 < spacing)
    (r : ScratchCMP85PositivePrefix depth) :
    0 < scratch_cmp85SourcePrefixWeightedCoefficient T a r := by
  unfold scratch_cmp85SourcePrefixWeightedCoefficient
  exact mul_pos
    (cmp99SourceMassParameter_pos ha
      (by exact_mod_cast (NeZero.pos M)) (r.1.val - 1))
    (pow_pos (inv_pos.mpr (by
      rw [T.towerAt_terminalSpacing]
      exact mul_pos (pow_pos (by exact_mod_cast (NeZero.pos M)) r.1.val)
        hspacing)) 2)

theorem scratch_cmp85SourcePrefixCountingCoefficient_pos
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    {a : ℝ} (ha : 0 < a) (hspacing : 0 < spacing)
    (r : ScratchCMP85PositivePrefix depth) :
    0 < scratch_cmp85SourcePrefixCountingCoefficient T a r := by
  have hterminal : 0 < (T.towerAt r.1).terminalSpacing := by
    rw [T.towerAt_terminalSpacing]
    exact mul_pos (pow_pos (by exact_mod_cast (NeZero.pos M)) r.1.val)
      hspacing
  unfold scratch_cmp85SourcePrefixCountingCoefficient
  exact mul_pos
    (scratch_cmp85SourcePrefixWeightedCoefficient_pos T ha hspacing r)
    (div_pos (pow_pos hterminal d) (pow_pos hspacing d))

/-- Closed counting-Hilbert formula.  The exponent is `d-2`, exactly the
source lattice-volume cancellation; this is the convention gate that rules
out applying the terminal/fine ratio twice. -/
theorem scratch_cmp85SourcePrefixCountingCoefficient_eq
    (hd : 2 ≤ d)
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (a : ℝ) (hspacing : 0 < spacing)
    (r : ScratchCMP85PositivePrefix depth) :
    scratch_cmp85SourcePrefixCountingCoefficient T a r =
      scratch_cmp85SourcePrefixA (M := M) a r *
        (T.towerAt r.1).terminalSpacing ^ (d - 2) / spacing ^ d := by
  have hterminal : (T.towerAt r.1).terminalSpacing ≠ 0 := by
    rw [T.towerAt_terminalSpacing]
    exact (mul_pos
      (pow_pos (by exact_mod_cast (NeZero.pos M)) r.1.val) hspacing).ne'
  unfold scratch_cmp85SourcePrefixCountingCoefficient
  unfold scratch_cmp85SourcePrefixWeightedCoefficient
  unfold scratch_cmp85SourcePrefixVolumeRatio
  rw [show d = (d - 2) + 2 by omega, pow_add]
  field_simp [hterminal, hspacing.ne']

/-- The source-weighted and counting-Hilbert presentations of the prefix
precision are exactly the same operator.  This theorem is the mandatory
normalization gate before the counting coercivity proof can feed CMP85's
printed formulas. -/
theorem scratch_cmp85SourcePrefixPrecision_weighted_eq_counting
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (D : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc))
    {a : ℝ} (hspacing : 0 < spacing)
    (r : ScratchCMP85PositivePrefix depth) :
    D + scratch_cmp85SourcePrefixWeightedCoefficient T a r •
        ((T.towerAt r.1).weightedAdjoint.comp (T.towerAt r.1).Qprime) =
      cmp99SourceGaugePrecision D (T.towerAt r.1).Qprime
        (scratch_cmp85SourcePrefixCountingCoefficient T a r) := by
  have hterminal : 0 < (T.towerAt r.1).terminalSpacing := by
    rw [T.towerAt_terminalSpacing]
    exact mul_pos (pow_pos (by exact_mod_cast (NeZero.pos M)) r.1.val)
      hspacing
  have hbridge :=
    (T.towerAt r.1).adjoint_eq_spacingRatio_smul_weightedAdjoint
      hterminal.ne'
  rw [cmp99SourceGaugePrecision]
  apply ContinuousLinearMap.ext
  intro phi
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [hbridge]
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  have hscalar :
      scratch_cmp85SourcePrefixCountingCoefficient T a r *
          (spacing ^ d / (T.towerAt r.1).terminalSpacing ^ d) =
        scratch_cmp85SourcePrefixWeightedCoefficient T a r := by
    unfold scratch_cmp85SourcePrefixCountingCoefficient
    unfold scratch_cmp85SourcePrefixVolumeRatio
    field_simp [pow_ne_zero d hspacing.ne', pow_ne_zero d hterminal.ne']
  rw [hscalar]

/-! ## Physical positive-prefix producer -/

/-- The single retained tower used by every P2a object.  This abbreviation is
generated from the physical chain; it is never a public caller input. -/
noncomputable def scratch_cmp85SourceGeneratedPrefixTower
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon) :=
  cmp99SourceGeneratedRetainedPhysicalTower hd hM
    (matrixSUNAdjointModel Nc) Omega0 depth spacing epsilon background0 chain
    fineSmall

/-- CMP85 (2.20) on one generated positive prefix, represented in Lean's
counting Hilbert structure.  The bare mass, flowing coefficient, average and
volume conversion are all literal data generated inside the definition. -/
noncomputable def scratch_cmp85SourceGeneratedPrefixPrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon mass a : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : ScratchCMP85PositivePrefix depth) :
    ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (SUNLieCoord Nc) :=
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  cmp99SourceGaugePrecision
    (scratch_cmp85BareMassPrecision
      (cmp99ActiveRegionSourceCovariantLaplacian
        (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
        (matrixSUNAdjointModel Nc) background0 spacing)
      mass)
    (T.towerAt r.1).Qprime
    (scratch_cmp85SourcePrefixCountingCoefficient T a r)

/-- The exact robust coercivity floor of the generated positive-prefix
precision. -/
noncomputable def scratch_cmp85SourceGeneratedPrefixCoercivity
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon a : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : ScratchCMP85PositivePrefix depth) : ℝ :=
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  (1 - cmp99SourcePoincareErrorCoeff d M r.1.val spacing epsilon) *
    min (cmp99SourcePoincareEnergyCoeff d M r.1.val spacing epsilon)⁻¹
      (scratch_cmp85SourcePrefixCountingCoefficient T a r *
        (cmp99OneScaleBlockPoincareConstant d M ^ r.1.val)⁻¹)

/-- P2a coercivity is generated from the single retained physical tower and
one terminal scalar budget.  No family of precisions, `Q_j`, source
coefficients or coercivity witnesses is accepted. -/
theorem scratch_isCoerciveCLM_cmp85SourceGeneratedPrefixPrecision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :
    IsCoerciveCLM
      (scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall r)
      (scratch_cmp85SourceGeneratedPrefixCoercivity hd hM Omega0 depth
        spacing epsilon a background0 chain fineSmall r) := by
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  let D := cmp99ActiveRegionSourceCovariantLaplacian
    (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
    (matrixSUNAdjointModel Nc) background0 spacing
  let Q := (T.towerAt r.1).Qprime
  let A := cmp99SourcePoincareEnergyCoeff d M r.1.val spacing epsilon
  let B := cmp99SourcePoincareErrorCoeff d M r.1.val spacing epsilon
  let C := cmp99OneScaleBlockPoincareConstant d M ^ r.1.val
  let b := scratch_cmp85SourcePrefixCountingCoefficient T a r
  have hA : 0 < A :=
    scratch_cmp99SourcePoincareEnergyCoeff_pos r.2 hspacing
  have hB : B < 1 :=
    scratch_cmp99SourcePoincareErrorCoeff_lt_of_le_depth
      (Nat.lt_succ_iff.mp r.1.isLt) hsmall
  have hC : 0 < C :=
    scratch_cmp99OneScaleBlockPoincareConstant_pow_pos r.1.val
  have hb : 0 < b :=
    scratch_cmp85SourcePrefixCountingCoefficient_pos T ha hspacing r
  have hp :=
    scratch_cmp99SourceGeneratedRetainedPhysicalTower_prefix_poincare
      hd hM Omega0 depth hspacing background0 chain fineSmall hsmall r.1
  have hrawNorm : ∀ phi,
      (1 - B) * ‖phi‖ ^ 2 ≤
        A * ‖cmp99ActiveRegionSourceCovariantD0CLM
          (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
          (matrixSUNAdjointModel Nc) background0 spacing phi‖ ^ 2 +
        C * ‖Q phi‖ ^ 2 := by
    intro phi
    have hpPhi := hp phi
    simpa only [mul_comm] using
      (le_div_iff₀ (sub_pos.mpr hB)).mp hpPhi
  have hraw : ∀ phi,
      (1 - B) * ‖phi‖ ^ 2 ≤
        A * inner ℝ phi (D phi) + C * ‖Q phi‖ ^ 2 := by
    intro phi
    simpa only [D, inner_cmp99ActiveRegionSourceCovariantLaplacian] using
      hrawNorm phi
  have hDnonneg : ∀ phi, 0 ≤ inner ℝ phi (D phi) := by
    intro phi
    rw [D, inner_cmp99ActiveRegionSourceCovariantLaplacian]
    exact sq_nonneg _
  have hcoercive :=
    scratch_isCoerciveCLM_of_twoWeightPoincare_with_bareMass
      D Q mass hA hC hb hDnonneg hraw
  simpa only [scratch_cmp85SourceGeneratedPrefixPrecision,
    scratch_cmp85SourceGeneratedPrefixCoercivity, T, D, Q, A, B, C, b,
    scratch_cmp85SourceGeneratedPrefixTower] using hcoercive

theorem scratch_cmp85SourceGeneratedPrefixCoercivity_pos
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :
    0 < scratch_cmp85SourceGeneratedPrefixCoercivity hd hM Omega0 depth
      spacing epsilon a background0 chain fineSmall r := by
  let T := scratch_cmp85SourceGeneratedPrefixTower hd hM Omega0 depth
    spacing epsilon background0 chain fineSmall
  have hA := scratch_cmp99SourcePoincareEnergyCoeff_pos
    (d := d) (M := M) r.2 hspacing
  have hB := scratch_cmp99SourcePoincareErrorCoeff_lt_of_le_depth
    (d := d) (M := M) (Nat.lt_succ_iff.mp r.1.isLt) hsmall
  have hC := scratch_cmp99OneScaleBlockPoincareConstant_pow_pos
    (d := d) (M := M) r.1.val
  have hb := scratch_cmp85SourcePrefixCountingCoefficient_pos T ha hspacing r
  unfold scratch_cmp85SourceGeneratedPrefixCoercivity
  dsimp only
  exact scratch_twoWeightPoincare_coercivityConstant_pos hA hB hC hb

/-- The generated source precision is symmetric; this is constructed from
the literal covariant Laplacian and the independent bare-mass square. -/
theorem scratch_cmp85SourceGeneratedPrefixPrecision_isSymmetric
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    (spacing epsilon mass a : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (r : ScratchCMP85PositivePrefix depth) :
    (scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
      spacing epsilon mass a background0 chain fineSmall r).IsSymmetric := by
  let D := cmp99ActiveRegionSourceCovariantLaplacian
    (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
    (matrixSUNAdjointModel Nc) background0 spacing
  apply cmp99SourceGaugePrecision_isSymmetric
  apply scratch_cmp85BareMassPrecision_isSymmetric
  exact cmp99ActiveRegionSourceCovariantLaplacian_isSymmetric
    (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
    (matrixSUNAdjointModel Nc) background0 spacing

/-- The P2a Green operator is constructed from the generated positive
coercivity theorem, never supplied as a family. -/
noncomputable def scratch_cmp85SourceGeneratedPrefixGreen
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :=
  covarianceOfIsCoerciveCLM
    (scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
      spacing epsilon mass a background0 chain fineSmall r)
    (scratch_cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0 depth
      hspacing ha background0 chain fineSmall hsmall r)
    (scratch_isCoerciveCLM_cmp85SourceGeneratedPrefixPrecision hd hM Omega0
      depth hspacing ha mass background0 chain fineSmall hsmall r)

theorem scratch_cmp85SourceGeneratedPrefixPrecision_comp_green
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :
    (scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
      spacing epsilon mass a background0 chain fineSmall r).comp
      (scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
        mass background0 chain fineSmall hsmall r) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
          (SUNLieCoord Nc)) := by
  exact precision_comp_covarianceOfIsCoerciveCLM _
    (scratch_cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0 depth
      hspacing ha background0 chain fineSmall hsmall r) _

theorem scratch_cmp85SourceGeneratedPrefixGreen_comp_precision
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :
    (scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
      mass background0 chain fineSmall hsmall r).comp
      (scratch_cmp85SourceGeneratedPrefixPrecision hd hM Omega0 depth
        spacing epsilon mass a background0 chain fineSmall r) =
      ContinuousLinearMap.id ℝ
        (ActiveGaugeZeroCochain
          (cmp99IteratedLiftActiveRegion (M := M) Omega0 depth)
          (SUNLieCoord Nc)) := by
  exact covarianceOfIsCoerciveCLM_comp_precision _
    (scratch_cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0 depth
      hspacing ha background0 chain fineSmall hsmall r) _

/-- The P2a Green operator is symmetric because it is the constructed inverse
of the symmetric generated precision. -/
theorem scratch_cmp85SourceGeneratedPrefixGreen_isSymmetric
    (hd : 2 ≤ d) (hM : 2 ≤ M)
    (Omega0 : ActiveGaugeRegion d N) (depth : ℕ)
    {spacing epsilon a : ℝ} (hspacing : 0 < spacing) (ha : 0 < a)
    (mass : ℝ)
    (background0 : GaugeConfig d
      (cmp99RegionalLatticeSize M N depth) (SUN Nc))
    (chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon)
    (fineSmall : ∀ e : ConcreteEdge d
      (cmp99RegionalLatticeSize M N depth),
      ‖(background0 e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon)
    (hsmall : cmp99SourcePoincareErrorCoeff d M depth spacing epsilon < 1)
    (r : ScratchCMP85PositivePrefix depth) :
    (scratch_cmp85SourceGeneratedPrefixGreen hd hM Omega0 depth hspacing ha
      mass background0 chain fineSmall hsmall r).IsSymmetric := by
  exact covarianceOfIsCoerciveCLM_isSymmetric _
    (scratch_cmp85SourceGeneratedPrefixCoercivity_pos hd hM Omega0 depth
      hspacing ha background0 chain fineSmall hsmall r)
    (scratch_isCoerciveCLM_cmp85SourceGeneratedPrefixPrecision hd hM Omega0
      depth hspacing ha mass background0 chain fineSmall hsmall r)
    (scratch_cmp85SourceGeneratedPrefixPrecision_isSymmetric hd hM Omega0
      depth spacing epsilon mass a background0 chain fineSmall r)

end

end YangMills.RG
