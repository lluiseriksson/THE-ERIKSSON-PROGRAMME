/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.AveragingL2
import YangMills.RG.PhysicalPoincareLowModeHodge

/-!
# W-3c — physical block response and the quotient Poincaré second wall

This module completes the registered one-sided W-3 falsifier.  A canonical
linear-isometric reindexing places the W-3a/W-3b square mode on the exact fine
side `(M+M) * N'` without opaque dependent casts.  It preserves constants,
fluctuations, curl, divergence, norms, and flat Hodge energy.

For the current unscaled line-integral block map, the certified physical block
response is

`‖Q A‖² ≤ (M+M)⁻¹ ‖A‖²`  (`d ≥ 3`),

while the exact W-3b term is

`⟪A,K₀A⟫ = 8 / ((M+M)N') * ‖A‖²`.

Thus the physical Rayleigh numerator is at most `9/(M+M) * ‖A‖²`, every
quotient Poincaré constant satisfies `(M+M)/9 ≤ CP`, and the registered
constant-before-volume gate is false for every positive `N'`, `d ≥ 3`,
`Nc ≥ 2`, and every adjoint model.

This is a negative theorem for the CURRENT unscaled `Q` and CURRENT unweighted
coarse norm.  A rescaled or weighted block gate is different and remains
outside this theorem.  No uniform CT theorem, interacting Hessian, covariance
root, `hRpoly`, mass gap, or Clay progress is claimed.
-/

namespace YangMills.RG

open Matrix Module

/-- Physical-cochain form of the exact-normalization lattice `Q` contraction.
No field rescaling or weighted coarse norm is inserted. -/
theorem norm_sq_flatBlockConstraintQCLM_le_inv_mul
    {d L N' Nc : ℕ} [NeZero L] [NeZero N']
    (hd : 3 ≤ d) (A : FinePhysicalOneCochain d L N' Nc) :
    ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) L N' A‖ ^ 2
      ≤ (L : ℝ)⁻¹ * ‖A‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simpa only [flatBlockConstraintQCLM_apply, physicalBondOfEdge_mk_true]
    using
      (linAvg_l2_contraction (d := d) (V := SUNLieCoord Nc) L N' hd
        (fun e : ConcreteEdge d (L * N') => A (physicalBondOfEdge e)))

/-! ## Canonical reindexing across propositionally equal side lengths -/

/-- Coordinatewise reindexing of periodic boxes.  Unlike `Eq.mp` on the
cochain abbreviation, this equivalence does not transport a dependent
`NeZero` instance through the type. -/
def finBoxSideCongr {d N K : ℕ} (h : N = K) : FinBox d N ≃ FinBox d K :=
  Equiv.piCongrRight fun _ => finCongr h

/-- Reindex positive physical bonds while leaving their direction unchanged. -/
def physicalBondSideCongr {d N K : ℕ} (h : N = K) :
    (FinBox d N × Fin d) ≃ (FinBox d K × Fin d) :=
  (finBoxSideCongr (d := d) h).prodCongr (Equiv.refl _)

/-- The induced linear isometry between physical one-cochain Hilbert spaces. -/
noncomputable def physicalOneCochainSideCongr
    (d N K Nc : ℕ) [NeZero N] [NeZero K] (h : N = K) :
    PhysicalGaugeOneCochain d N Nc ≃ₗᵢ[ℝ]
      PhysicalGaugeOneCochain d K Nc :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
    (physicalBondSideCongr (d := d) h)

@[simp]
theorem physicalOneCochainSideCongr_apply
    {d N K Nc : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d K) :
    physicalOneCochainSideCongr d N K Nc h A b =
      A ((physicalBondSideCongr (d := d) h).symm b) := rfl

@[simp]
theorem physicalOneCochainSideCongr_constant
    {d N K Nc : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (v : Fin d → SUNLieCoord Nc) :
    physicalOneCochainSideCongr d N K Nc h
        (constantPhysicalGaugeOneCochain (d := d) (N := N) (Nc := Nc) v)
      = constantPhysicalGaugeOneCochain (d := d) (N := K) (Nc := Nc) v := by
  apply PiLp.ext
  intro b
  rw [physicalOneCochainSideCongr_apply,
    constantPhysicalGaugeOneCochain_apply,
    constantPhysicalGaugeOneCochain_apply]
  rfl

theorem physicalOneCochainSideCongr_isFluctuation
    {d N K Nc : ℕ} [NeZero N] [NeZero K] (h : N = K)
    {A : PhysicalGaugeOneCochain d N Nc}
    (hA : IsFluctuationCochain A) :
    IsFluctuationCochain (physicalOneCochainSideCongr d N K Nc h A) := by
  intro v
  rw [← physicalOneCochainSideCongr_constant h v,
    LinearIsometryEquiv.inner_map_map]
  exact hA v

@[simp]
theorem finBoxSideCongr_shift
    {d N K : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (x : FinBox d N) (i : Fin d) :
    finBoxSideCongr h (FinBox.shift x i) =
      FinBox.shift (finBoxSideCongr h x) i := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [finBoxSideCongr, FinBox.shift, h]
  · simp [finBoxSideCongr, FinBox.shift, hk]

@[simp]
theorem finBoxSideCongr_shiftBack
    {d N K : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (x : FinBox d N) (i : Fin d) :
    finBoxSideCongr h (FinBox.shiftBack x i) =
      FinBox.shiftBack (finBoxSideCongr h x) i := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [finBoxSideCongr, FinBox.shiftBack, h]
  · simp [finBoxSideCongr, FinBox.shiftBack, hk]

@[simp]
theorem finBoxSideCongr_symm_shift
    {d N K : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (x : FinBox d K) (i : Fin d) :
    (finBoxSideCongr h).symm (FinBox.shift x i) =
      FinBox.shift ((finBoxSideCongr h).symm x) i := by
  simpa [finBoxSideCongr] using
    (finBoxSideCongr_shift (d := d) h.symm x i)

@[simp]
theorem finBoxSideCongr_symm_shiftBack
    {d N K : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (x : FinBox d K) (i : Fin d) :
    (finBoxSideCongr h).symm (FinBox.shiftBack x i) =
      FinBox.shiftBack ((finBoxSideCongr h).symm x) i := by
  simpa [finBoxSideCongr] using
    (finBoxSideCongr_shiftBack (d := d) h.symm x i)

/-- Reindex periodic site fields. -/
noncomputable def physicalZeroCochainSideCongr
    (d N K Nc : ℕ) [NeZero N] [NeZero K] (h : N = K) :
    PhysicalGaugeZeroCochain d N Nc ≃ₗᵢ[ℝ]
      PhysicalGaugeZeroCochain d K Nc :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
    (finBoxSideCongr (d := d) h)

/-- Reindex periodic plaquettes by their site; directions and ordering stay
unchanged. -/
def physicalPlaquetteSideCongr {d N K : ℕ} (h : N = K) :
    ConcretePlaquette d N ≃ ConcretePlaquette d K where
  toFun p := ⟨finBoxSideCongr h p.site, p.dir1, p.dir2, p.hlt⟩
  invFun p := ⟨(finBoxSideCongr h).symm p.site, p.dir1, p.dir2, p.hlt⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

@[simp]
theorem physicalBondSideCongr_symm_apply
    {d N K : ℕ} (h : N = K) (b : FinBox d K × Fin d) :
    (physicalBondSideCongr (d := d) h).symm b =
      ((finBoxSideCongr h).symm b.1, b.2) := rfl

@[simp]
theorem physicalPlaquetteSideCongr_symm_site
    {d N K : ℕ} (h : N = K) (p : ConcretePlaquette d K) :
    ((physicalPlaquetteSideCongr (d := d) h).symm p).site =
      (finBoxSideCongr h).symm p.site := rfl

@[simp]
theorem physicalPlaquetteSideCongr_symm_dir1
    {d N K : ℕ} (h : N = K) (p : ConcretePlaquette d K) :
    ((physicalPlaquetteSideCongr (d := d) h).symm p).dir1 = p.dir1 := rfl

@[simp]
theorem physicalPlaquetteSideCongr_symm_dir2
    {d N K : ℕ} (h : N = K) (p : ConcretePlaquette d K) :
    ((physicalPlaquetteSideCongr (d := d) h).symm p).dir2 = p.dir2 := rfl

/-- Reindex periodic two-cochains. -/
noncomputable def physicalTwoCochainSideCongr
    (d N K Nc : ℕ) [NeZero N] [NeZero K] (h : N = K) :
    PhysicalGaugeTwoCochain d N Nc ≃ₗᵢ[ℝ]
      PhysicalGaugeTwoCochain d K Nc :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (SUNLieCoord Nc)
    (physicalPlaquetteSideCongr (d := d) h)

@[simp]
theorem physicalZeroCochainSideCongr_apply
    {d N K Nc : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (φ : PhysicalGaugeZeroCochain d N Nc) (x : FinBox d K) :
    physicalZeroCochainSideCongr d N K Nc h φ x =
      φ ((finBoxSideCongr (d := d) h).symm x) := rfl

@[simp]
theorem physicalTwoCochainSideCongr_apply
    {d N K Nc : ℕ} [NeZero N] [NeZero K] (h : N = K)
    (F : PhysicalGaugeTwoCochain d N Nc) (p : ConcretePlaquette d K) :
    physicalTwoCochainSideCongr d N K Nc h F p =
      F ((physicalPlaquetteSideCongr (d := d) h).symm p) := rfl

theorem physicalSideCongr_covariantD1_trivial
    {d N K Nc : ℕ} [NeZero d] [NeZero N] [NeZero K] [NeZero Nc]
    (h : N = K) (ρ : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    physicalTwoCochainSideCongr d N K Nc h
        (covariantD1CLM ρ (trivialPhysicalGaugeBackground d N Nc) A)
      = covariantD1CLM ρ (trivialPhysicalGaugeBackground d K Nc)
          (physicalOneCochainSideCongr d N K Nc h A) := by
  apply PiLp.ext
  intro p
  rw [physicalTwoCochainSideCongr_apply,
    covariantD1CLM_trivial_apply, covariantD1CLM_trivial_apply]
  simp

theorem physicalSideCongr_gaugeConstraint_trivial
    {d N K Nc : ℕ} [NeZero d] [NeZero N] [NeZero K] [NeZero Nc]
    (h : N = K) (ρ : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    physicalZeroCochainSideCongr d N K Nc h
        (gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d N Nc) A)
      = gaugeConstraintQCLM ρ (trivialPhysicalGaugeBackground d K Nc)
          (physicalOneCochainSideCongr d N K Nc h A) := by
  apply PiLp.ext
  intro x
  rw [physicalZeroCochainSideCongr_apply,
    gaugeConstraintQCLM_trivial_apply, gaugeConstraintQCLM_trivial_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

/-- Flat Hodge energy is invariant under the canonical side reindexing. -/
theorem flatGaugeHodgeK0_inner_sideCongr
    {d N K Nc : ℕ} [NeZero d] [NeZero N] [NeZero K] [NeZero Nc]
    (h : N = K) (ρ : SUNAdjointModel Nc)
    (A : PhysicalGaugeOneCochain d N Nc) :
    inner ℝ (physicalOneCochainSideCongr d N K Nc h A)
        (flatGaugeHodgeK0CLM d K Nc ρ
          (physicalOneCochainSideCongr d N K Nc h A))
      = inner ℝ A (flatGaugeHodgeK0CLM d N Nc ρ A) := by
  rw [flatGaugeHodgeK0_inner_right, flatGaugeHodgeK0_inner_right]
  rw [← physicalSideCongr_covariantD1_trivial h ρ A,
    ← physicalSideCongr_gaugeConstraint_trivial h ρ A]
  simp

/-! ## The W-3a witness on the exact fine side `(M+M) * N'` -/

theorem blockScale_side_eq (M N' : ℕ) :
    (M * N') + (M * N') = (M + M) * N' := by ring

noncomputable def blockScaleSquareModeCochain
    (d M N' Nc : ℕ) [NeZero M] [NeZero N']
    (i j : Fin d) (w : SUNLieCoord Nc) :
    FinePhysicalOneCochain d (M + M) N' Nc :=
  physicalOneCochainSideCongr d
    ((M * N') + (M * N')) ((M + M) * N') Nc
    (blockScale_side_eq M N')
    (squareModeCochain d (M * N') Nc i j w)

theorem blockScaleSquareModeCochain_isFluctuation
    (d M N' Nc : ℕ) [NeZero M] [NeZero N']
    (i j : Fin d) (w : SUNLieCoord Nc) :
    IsFluctuationCochain (blockScaleSquareModeCochain d M N' Nc i j w) :=
  physicalOneCochainSideCongr_isFluctuation (blockScale_side_eq M N')
    (squareModeCochain_isFluctuation d (M * N') Nc i j w)

theorem norm_sq_blockScaleSquareModeCochain
    (d M N' Nc : ℕ) [NeZero M] [NeZero N']
    (i j : Fin d) (w : SUNLieCoord Nc) :
    ‖blockScaleSquareModeCochain d M N' Nc i j w‖ ^ 2
      = ((((M + M) * N' : ℕ) : ℝ) ^ d) * ‖w‖ ^ 2 := by
  rw [blockScaleSquareModeCochain, LinearIsometryEquiv.norm_map,
    norm_sq_squareModeCochain]
  congr 2
  norm_num [blockScale_side_eq]

/-- W-3b transported to the exact fine side `(M+M) * N'`. -/
theorem flatGaugeHodgeK0_inner_blockScaleSquareModeCochain
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    inner ℝ (blockScaleSquareModeCochain d M N' Nc i j w)
        (flatGaugeHodgeK0CLM d ((M + M) * N') Nc ρ
          (blockScaleSquareModeCochain d M N' Nc i j w))
      = 8 * ((((M + M) * N' : ℕ) : ℝ) ^ (d - 1)) * ‖w‖ ^ 2 := by
  rw [blockScaleSquareModeCochain,
    flatGaugeHodgeK0_inner_sideCongr,
    flatGaugeHodgeK0_inner_squareModeCochain]
  congr 3
  norm_num [blockScale_side_eq]

/-- Exact Hodge-to-norm ratio of the block-scale witness. -/
theorem flatGaugeHodgeK0_inner_blockScaleSquareModeCochain_eq_div
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (ρ : SUNAdjointModel Nc) (i j : Fin d) (w : SUNLieCoord Nc) :
    inner ℝ (blockScaleSquareModeCochain d M N' Nc i j w)
        (flatGaugeHodgeK0CLM d ((M + M) * N') Nc ρ
          (blockScaleSquareModeCochain d M N' Nc i j w))
      = 8 / (((M + M) * N' : ℕ) : ℝ)
          * ‖blockScaleSquareModeCochain d M N' Nc i j w‖ ^ 2 := by
  rw [flatGaugeHodgeK0_inner_blockScaleSquareModeCochain,
    norm_sq_blockScaleSquareModeCochain]
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hNnat : 0 < (M + M) * N' :=
    Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne N'))
  have hN : (0 : ℝ) < (((M + M) * N' : ℕ) : ℝ) := by exact_mod_cast hNnat
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : 1 ≤ d := hd
  have hpow : ((((M + M) * N' : ℕ) : ℝ)) ^ (d - 1)
          * (((M + M) * N' : ℕ) : ℝ)
      = ((((M + M) * N' : ℕ) : ℝ)) ^ d := by
    rw [← pow_succ]
    congr 1
    exact Nat.sub_add_cancel hd1
  field_simp
  nlinarith [hpow]

/-- The physical Rayleigh numerator of the witness is at most `9/(M+M)`
times its norm squared for `d ≥ 3`.  The `8` is the exact two-interface
Hodge cost; the `1` is the physical unscaled-block contraction. -/
theorem blockScaleSquareMode_rayleigh_numerator_le
    (d M N' Nc : ℕ) [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (hd : 3 ≤ d) (ρ : SUNAdjointModel Nc)
    (i j : Fin d) (w : SUNLieCoord Nc) :
    inner ℝ (blockScaleSquareModeCochain d M N' Nc i j w)
        (flatGaugeHodgeK0CLM d ((M + M) * N') Nc ρ
          (blockScaleSquareModeCochain d M N' Nc i j w))
      + ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) (M + M) N'
          (blockScaleSquareModeCochain d M N' Nc i j w)‖ ^ 2
      ≤ 9 / ((M + M : ℕ) : ℝ)
          * ‖blockScaleSquareModeCochain d M N' Nc i j w‖ ^ 2 := by
  let A := blockScaleSquareModeCochain d M N' Nc i j w
  have hQ := norm_sq_flatBlockConstraintQCLM_le_inv_mul
    (d := d) (L := M + M) (N' := N') (Nc := Nc) hd A
  have hH := flatGaugeHodgeK0_inner_blockScaleSquareModeCochain_eq_div
    d M N' Nc ρ i j w
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMnat : 0 < M + M := by omega
  have hM : (0 : ℝ) < (M + M : ℕ) := by exact_mod_cast hMnat
  have hNp : (1 : ℝ) ≤ N' := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N')
  have hratio :
      8 / ((((M + M) * N' : ℕ) : ℝ)) + ((M + M : ℕ) : ℝ)⁻¹
        ≤ 9 / ((M + M : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have h8 : 8 / (((M + M : ℕ) : ℝ) * (N' : ℝ))
        ≤ 8 / ((M + M : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) hM
      nlinarith [mul_le_mul_of_nonneg_left hNp hM.le]
    calc
      8 / (((M + M : ℕ) : ℝ) * (N' : ℝ)) + ((M + M : ℕ) : ℝ)⁻¹
          ≤ 8 / ((M + M : ℕ) : ℝ) + ((M + M : ℕ) : ℝ)⁻¹ :=
            add_le_add h8 (le_refl _)
      _ = 9 / ((M + M : ℕ) : ℝ) := by
        rw [inv_eq_one_div]
        field_simp
        ring
  rw [hH]
  calc
    8 / (((M + M) * N' : ℕ) : ℝ) * ‖A‖ ^ 2
          + ‖flatBlockConstraintQCLM (d := d) (Nc := Nc) (M + M) N' A‖ ^ 2
        ≤ 8 / (((M + M) * N' : ℕ) : ℝ) * ‖A‖ ^ 2
          + ((M + M : ℕ) : ℝ)⁻¹ * ‖A‖ ^ 2 :=
            add_le_add (le_refl _) hQ
    _ = (8 / (((M + M) * N' : ℕ) : ℝ) + ((M + M : ℕ) : ℝ)⁻¹)
          * ‖A‖ ^ 2 := by ring
    _ ≤ 9 / ((M + M : ℕ) : ℝ) * ‖A‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖A‖)

/-- Every quotient Poincaré constant at even block scale `M+M` is at least
`(M+M)/9` for `d ≥ 3`, `Nc ≥ 2`. -/
theorem quotientPoincare_squareMode_linear_lower_bound
    {d M N' Nc : ℕ} [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]
    (hd : 3 ≤ d) (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc)
    {CP : ℝ}
    (hP : QuotientFlatGaugeHodgePoincare d (M + M) N' Nc ρ CP) :
    ((M + M : ℕ) : ℝ) / 9 ≤ CP := by
  have hdim : 0 < Nc ^ 2 - 1 := by
    have h4 : 2 * 2 ≤ Nc * Nc := Nat.mul_le_mul hNc hNc
    have hsq : Nc ^ 2 = Nc * Nc := by ring
    rw [hsq]
    omega
  let w : SUNLieCoord Nc :=
    EuclideanSpace.single (⟨0, hdim⟩ : Fin (Nc ^ 2 - 1)) (1 : ℝ)
  let i : Fin d := ⟨0, by omega⟩
  let A := blockScaleSquareModeCochain d M N' Nc i i w
  have hw : ‖w‖ ^ 2 = 1 := by
    dsimp [w]
    rw [EuclideanSpace.norm_single]
    norm_num
  have hnorm : ‖A‖ ^ 2 = (((M + M) * N' : ℕ) : ℝ) ^ d := by
    dsimp [A]
    rw [norm_sq_blockScaleSquareModeCochain, hw, mul_one]
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hApos : 0 < ‖A‖ ^ 2 := by
    rw [hnorm]
    have hside : 0 < (M + M) * N' :=
      Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne N'))
    positivity
  have hmain := hP.2 A
    (blockScaleSquareModeCochain_isFluctuation d M N' Nc i i w)
  have henergy := blockScaleSquareMode_rayleigh_numerator_le
    d M N' Nc hd ρ i i w
  have hCP : 0 < CP := hP.1
  have hscaled :
      ‖A‖ ^ 2 ≤ CP * (9 / ((M + M : ℕ) : ℝ) * ‖A‖ ^ 2) :=
    hmain.trans (mul_le_mul_of_nonneg_left henergy hCP.le)
  have hcoef : 1 ≤ CP * (9 / ((M + M : ℕ) : ℝ)) := by
    have hre0 : ‖A‖ ^ 2
        ≤ (CP * (9 / ((M + M : ℕ) : ℝ))) * ‖A‖ ^ 2 := by
      convert hscaled using 1 <;> ring
    have hre : (1 : ℝ) * ‖A‖ ^ 2
        ≤ (CP * (9 / ((M + M : ℕ) : ℝ))) * ‖A‖ ^ 2 := by
      simpa only [one_mul] using hre0
    exact (mul_le_mul_iff_of_pos_right hApos).mp hre
  have hMnat : 0 < M + M := by omega
  have hM : (0 : ℝ) < (M + M : ℕ) := by exact_mod_cast hMnat
  have hlin : ((M + M : ℕ) : ℝ) ≤ 9 * CP := by
    calc
      ((M + M : ℕ) : ℝ) = ((M + M : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((M + M : ℕ) : ℝ) * (CP * (9 / ((M + M : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hcoef hM.le
      _ = 9 * CP := by field_simp
  linarith

/-- **The quotient Poincaré second wall.**  Under the current unscaled block
map and unweighted coarse norm, the volume-uniform quotient gate is false for
every positive `N'` when `d ≥ 3`, `Nc ≥ 2`. -/
theorem volumeUniformQuotientPoincareGate_false
    {d N' Nc : ℕ} [NeZero d] [NeZero N'] [NeZero Nc]
    (hd : 3 ≤ d) (hNc : 2 ≤ Nc) (ρ : SUNAdjointModel Nc) :
    ¬ VolumeUniformQuotientPoincareGate d N' Nc ρ := by
  rintro ⟨CP, _hCP, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (9 * CP)
  let M := n + 1
  haveI : NeZero M := ⟨by simp [M]⟩
  let k := (M + M) - 1
  have hk : k + 1 = M + M := by dsimp [k]; omega
  have hP : QuotientFlatGaugeHodgePoincare d (M + M) N' Nc ρ CP := by
    simpa only [hk] using hall k
  have hlower := quotientPoincare_squareMode_linear_lower_bound
    (d := d) (M := M) (N' := N') (Nc := Nc) hd hNc ρ hP
  have hbig : 9 * CP < ((M + M : ℕ) : ℝ) := by
    dsimp [M]
    push_cast
    linarith
  linarith

end YangMills.RG
