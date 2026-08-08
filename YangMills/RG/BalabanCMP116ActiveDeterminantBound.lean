/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116SourcePi4FullComplexR2Norm
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Quantitative bounds for the finite active-state determinant

The restricted CMP116 contour determinant lives on a finite active-state
type.  This file supplies the dimension-local estimate needed to turn its
exact determinant identity into a bound for the contour density.

The key determinant estimate is adapted to the `L∞` matrix operator norm:
the absolute determinant is bounded by the product of the absolute row sums,
and hence by `‖A‖ ^ card ι`.  Applying this to the Neumann inverse of `1 + D`
gives a bound whose exponent is the active-state cardinality, never the
ambient lattice volume.
-/

namespace YangMills.RG

noncomputable section

open scoped Matrix.Norms.Operator

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000

namespace Matrix

/-- Every nonzero eigenvalue of the smaller rectangular product `B * A`
is an eigenvalue of `A * B`, and is therefore bounded by the physical
ambient defect norm. -/
theorem norm_root_charpoly_rectangular_mul_le
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty ι]
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    {r : ℂ}
    (hr : r ∈ (B * A).charpoly.roots)
    (hr0 : r ≠ 0) :
    ‖r‖ ≤ ‖A * B‖ := by
  have hrRoot : (B * A).charpoly.IsRoot r :=
    Polynomial.mem_roots'.mp hr |>.2
  have hpoly := congrArg (Polynomial.eval r)
    (Matrix.charpoly_mul_comm' A B)
  have hpoly' :
      r ^ Fintype.card κ * Polynomial.eval r (A * B).charpoly =
        r ^ Fintype.card ι * Polynomial.eval r (B * A).charpoly := by
    simpa using hpoly
  have hleft :
      r ^ Fintype.card κ * Polynomial.eval r (A * B).charpoly = 0 := by
    rw [hpoly', hrRoot, mul_zero]
  have hpow : r ^ Fintype.card κ ≠ 0 := pow_ne_zero _ hr0
  have hABRoot : (A * B).charpoly.IsRoot r := by
    exact (mul_eq_zero.mp hleft).resolve_left hpow
  have hspectrum : r ∈ spectrum ℂ (A * B) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hABRoot
  exact spectrum.norm_le_norm_of_mem hspectrum

/-- A near-identity defect on the ambient physical space gives a determinant
lower bound on the smaller active-state product.  No norm estimate for
`B * A` is required: every nonzero root of its characteristic polynomial is
transported to `A * B` by the rectangular characteristic-polynomial
identity. -/
theorem one_sub_norm_pow_card_le_norm_det_one_add_rectangular_mul
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    (hAB : ‖A * B‖ < 1) :
    (1 - ‖A * B‖) ^ Fintype.card κ ≤ ‖(1 + B * A).det‖ := by
  let M : Matrix κ κ ℂ := B * A
  let p : Polynomial ℂ := M.charpoly
  have hpSplits : p.Splits := IsAlgClosed.splits p
  have hpMonic : p.Monic := by
    exact Matrix.charpoly_monic M
  have hcard : p.roots.card = Fintype.card κ := by
    rw [← hpSplits.natDegree_eq_card_roots]
    exact Matrix.charpoly_natDegree_eq_dim M
  have hrootLower :
      ∀ r ∈ p.roots, 1 - ‖A * B‖ ≤ ‖(-1 : ℂ) - r‖ := by
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      simp
    · have hrAB : ‖r‖ ≤ ‖A * B‖ := by
        exact norm_root_charpoly_rectangular_mul_le A B hr hr0
      have hreverse :
          1 - ‖r‖ ≤ ‖(1 : ℂ) + r‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (-r)
        simpa [norm_neg, sub_neg_eq_add] using h
      calc
        1 - ‖A * B‖ ≤ 1 - ‖r‖ := sub_le_sub_left hrAB 1
        _ ≤ ‖(1 : ℂ) + r‖ := hreverse
        _ = ‖(-1 : ℂ) - r‖ := by
          rw [show (-1 : ℂ) - r = -((1 : ℂ) + r) by ring, norm_neg]
  have hprod :
      (1 - ‖A * B‖) ^ p.roots.card ≤
        (p.roots.map fun r => ‖(-1 : ℂ) - r‖).prod := by
    let lower : NNReal := ⟨1 - ‖A * B‖, (sub_pos.mpr hAB).le⟩
    have h :=
      Multiset.pow_card_le_prod
        (s := p.roots.map fun r => ‖(-1 : ℂ) - r‖₊)
        (a := lower) (by
          intro x hx
          obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
          exact_mod_cast hrootLower r hr)
    have hc := NNReal.coe_le_coe.mpr h
    have hcoe :
        (↑((p.roots.map fun r => ‖(-1 : ℂ) - r‖₊).prod) : ℝ) =
          (p.roots.map fun r => ‖(-1 : ℂ) - r‖).prod := by
      induction p.roots using Multiset.induction_on with
      | empty => simp
      | cons r s ih => simp [ih]
    rw [hcoe] at hc
    simpa [lower] using hc
  have heval :
      Polynomial.eval (-1 : ℂ) p =
        (p.roots.map fun r => (-1 : ℂ) - r).prod :=
    hpSplits.eval_eq_prod_roots_of_monic hpMonic (-1)
  have hevalDet :
      Polynomial.eval (-1 : ℂ) p = (-(1 + M)).det := by
    dsimp [p]
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply]
      ring
    · simp [Matrix.scalar_apply, hij]
  have hnormEval :
      ‖Polynomial.eval (-1 : ℂ) p‖ = ‖(1 + M).det‖ := by
    rw [hevalDet, Matrix.det_neg, norm_mul, norm_pow]
    simp
  have hnormProd :
      ‖Polynomial.eval (-1 : ℂ) p‖ =
        (p.roots.map fun r => ‖(-1 : ℂ) - r‖).prod := by
    rw [heval]
    induction p.roots using Multiset.induction_on with
    | empty => simp
    | cons r s ih =>
        simp [ih]
  calc
    (1 - ‖A * B‖) ^ Fintype.card κ =
        (1 - ‖A * B‖) ^ p.roots.card := by rw [hcard]
    _ ≤ (p.roots.map fun r => ‖(-1 : ℂ) - r‖).prod := hprod
    _ = ‖Polynomial.eval (-1 : ℂ) p‖ := hnormProd.symm
    _ ≤ ‖(1 + B * A).det‖ := by
      have heq :
          ‖Polynomial.eval (-1 : ℂ) p‖ =
            ‖(1 + B * A).det‖ := by
        simpa [M] using hnormEval
      exact heq.le
  exact le_rfl

/-- The exact reduced determinant identity yields a localized contour-density
bound from ambient Neumann smallness alone.  The exponent is the cardinality
of the active intermediate type `κ`, even when the factorization itself has
large rectangular legs. -/
theorem norm_density_le_inv_one_sub_ambient_norm_pow_activeCard
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ]
    (density : ℂ)
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ)
    (hAB : ‖A * B‖ < 1)
    (hexact : density ^ 2 * (1 + B * A).det = 1) :
    ‖density‖ ≤
      ((1 - ‖A * B‖) ^ Fintype.card κ)⁻¹ := by
  let lower : ℝ := (1 - ‖A * B‖) ^ Fintype.card κ
  have hbase : 0 < 1 - ‖A * B‖ := sub_pos.mpr hAB
  have hlowerPos : 0 < lower := by
    exact pow_pos hbase _
  have hdetLower :
      lower ≤ ‖(1 + B * A).det‖ := by
    exact one_sub_norm_pow_card_le_norm_det_one_add_rectangular_mul
      A B hAB
  have hdetPos : 0 < ‖(1 + B * A).det‖ :=
    hlowerPos.trans_le hdetLower
  have hsquareMul :
      ‖density‖ ^ 2 * ‖(1 + B * A).det‖ = 1 := by
    have h := congrArg norm hexact
    simpa [norm_mul, norm_pow] using h
  have hsquareEq :
      ‖density‖ ^ 2 = ‖(1 + B * A).det‖⁻¹ := by
    calc
      ‖density‖ ^ 2 =
          (‖density‖ ^ 2 * ‖(1 + B * A).det‖) *
            ‖(1 + B * A).det‖⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hdetPos.ne', mul_one]
      _ = ‖(1 + B * A).det‖⁻¹ := by rw [hsquareMul, one_mul]
    rfl
  have hsquareBound : ‖density‖ ^ 2 ≤ lower⁻¹ := by
    rw [hsquareEq]
    exact (inv_le_inv₀ hdetPos hlowerPos).2 hdetLower
  have hlowerLeOne : lower ≤ 1 := by
    have hbaseLe : 1 - ‖A * B‖ ≤ 1 := by
      linarith [norm_nonneg (A * B)]
    exact pow_le_one₀ hbase.le hbaseLe
  have honeBound : 1 ≤ lower⁻¹ :=
    (one_le_inv₀ hlowerPos).2 hlowerLeOne
  by_cases hnorm : ‖density‖ ≤ 1
  · exact hnorm.trans honeBound
  · have honeNorm : 1 ≤ ‖density‖ := le_of_not_ge hnorm
    calc
      ‖density‖ ≤ ‖density‖ ^ 2 := by
        nlinarith [norm_nonneg density]
      _ ≤ lower⁻¹ := hsquareBound

/-- Every absolute row sum is bounded by the `L∞` matrix operator norm. -/
theorem row_sum_norm_le_linfty_opNorm
    {ι κ 𝕜 : Type*}
    [Fintype ι] [Fintype κ] [Nonempty ι]
    [SeminormedAddCommGroup 𝕜]
    (A : Matrix ι κ 𝕜) (i : ι) :
    ∑ j, ‖A i j‖ ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hnn :
      (∑ j : κ, ‖A i j‖₊) ≤
        (Finset.univ : Finset ι).sup
          (fun i => ∑ j : κ, ‖A i j‖₊) :=
    Finset.le_sup
      (s := (Finset.univ : Finset ι))
      (f := fun i => ∑ j : κ, ‖A i j‖₊)
      (Finset.mem_univ i)
  simpa using (NNReal.coe_le_coe.mpr hnn)

/-- The determinant is bounded by the `L∞` operator norm to the matrix
dimension.  The proof embeds the permutation sum into the sum over all row
choices, avoiding a factorial loss. -/
theorem norm_det_le_linfty_opNorm_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) :
    ‖A.det‖ ≤ ‖A‖ ^ Fintype.card ι := by
  let permFunctions : Finset (ι → ι) :=
    (Finset.univ : Finset (Equiv.Perm ι)).map
      ⟨fun σ : Equiv.Perm ι => (σ : ι → ι), by
        intro σ τ h
        exact Equiv.ext (congrFun h)⟩
  have hdet :
      ‖A.det‖ ≤
        ∑ σ : Equiv.Perm ι, ∏ i, ‖A i (σ i)‖ := by
    rw [← Matrix.det_transpose A, Matrix.det_apply']
    calc
      ‖∑ σ : Equiv.Perm ι,
          Equiv.Perm.sign σ * ∏ i, A.transpose (σ i) i‖ ≤
          ∑ σ : Equiv.Perm ι,
            ‖Equiv.Perm.sign σ * ∏ i, A.transpose (σ i) i‖ :=
        norm_sum_le _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A i (σ i)‖ := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [norm_mul, norm_prod]
        have hsign :
            ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
          rw [Complex.norm_intCast, ← Int.cast_abs,
            Equiv.Perm.sign_abs]
          norm_num
        rw [hsign, one_mul]
        rfl
  have hperm :
      (∑ σ : Equiv.Perm ι, ∏ i, ‖A i (σ i)‖) ≤
        ∑ f : ι → ι, ∏ i, ‖A i (f i)‖ := by
    have hpermEq :
      (∑ σ : Equiv.Perm ι, ∏ i, ‖A i (σ i)‖) =
        ∑ f ∈ permFunctions, ∏ i, ‖A i (f i)‖ := by
      simp [permFunctions]
    rw [hpermEq]
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ permFunctions)
        (fun f hf hnot => Finset.prod_nonneg fun i hi => norm_nonneg _)
  calc
    ‖A.det‖ ≤ ∑ σ : Equiv.Perm ι, ∏ i, ‖A i (σ i)‖ := hdet
    _ ≤ ∑ f : ι → ι, ∏ i, ‖A i (f i)‖ := hperm
    _ = ∏ i, ∑ j, ‖A i j‖ :=
      (Fintype.prod_sum (fun i j => ‖A i j‖)).symm
    _ ≤ ∏ _i : ι, ‖A‖ := by
      exact Finset.prod_le_prod
        (fun i hi => Finset.sum_nonneg fun j hj => norm_nonneg _)
        (fun i hi => row_sum_norm_le_linfty_opNorm A i)
    _ = ‖A‖ ^ Fintype.card ι := by simp

/-- The inverse determinant of a near-identity active matrix has a
dimension-local geometric bound. -/
theorem norm_det_inv_one_add_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (D : Matrix ι ι ℂ) (hD : ‖D‖ < 1) :
    ‖((1 + D)⁻¹).det‖ ≤
      ((1 - ‖D‖)⁻¹) ^ Fintype.card ι := by
  calc
    ‖((1 + D)⁻¹).det‖ ≤
        ‖(1 + D)⁻¹‖ ^ Fintype.card ι :=
      norm_det_le_linfty_opNorm_pow _
    _ ≤ ((1 - ‖D‖)⁻¹) ^ Fintype.card ι := by
      exact pow_le_pow_left₀
        (norm_nonneg _)
        (Matrix.linfty_opNorm_inv_one_add_le D hD)
        _

/-- An exact identity `density² det(1+D)=1` and active-state Neumann
smallness bound the density by an exponential in the active dimension.

The slightly coarse exponent `card ι` avoids choosing another square-root
branch and is already linear in the localized state count. -/
theorem norm_density_le_inv_one_sub_norm_pow_card
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (density : ℂ) (D : Matrix ι ι ℂ)
    (hD : ‖D‖ < 1)
    (hexact : density ^ 2 * (1 + D).det = 1) :
    ‖density‖ ≤
      ((1 - ‖D‖)⁻¹) ^ Fintype.card ι := by
  have hunit : IsUnit (1 + D) := by
    have hneg : ‖-D‖ < 1 := by simpa using hD
    simpa only [sub_neg_eq_add] using
      (isUnit_one_sub_of_norm_lt_one hneg)
  have hdetUnit : IsUnit (1 + D).det :=
    (Matrix.isUnit_iff_isUnit_det (1 + D)).mp hunit
  have hdet : (1 + D).det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  have hsquare : density ^ 2 = ((1 + D)⁻¹).det := by
    apply mul_right_cancel₀ hdet
    rw [hexact]
    exact (Matrix.det_nonsing_inv_mul_det (1 + D) hdetUnit).symm
  let bound : ℝ := ((1 - ‖D‖)⁻¹) ^ Fintype.card ι
  have hbound : 1 ≤ bound := by
    have hdenom : 0 < 1 - ‖D‖ := sub_pos.mpr hD
    have hone : 1 ≤ (1 - ‖D‖)⁻¹ := by
      exact (one_le_inv₀ hdenom).2 (by linarith [norm_nonneg D])
    exact_mod_cast one_le_pow₀ hone
  have hsquareBound : ‖density‖ ^ 2 ≤ bound := by
    calc
      ‖density‖ ^ 2 = ‖density ^ 2‖ := by simp
      _ = ‖((1 + D)⁻¹).det‖ := congrArg norm hsquare
      _ ≤ bound := norm_det_inv_one_add_le D hD
  by_cases hnorm : ‖density‖ ≤ 1
  · exact hnorm.trans hbound
  · have honeNorm : 1 ≤ ‖density‖ := le_of_not_ge hnorm
    calc
      ‖density‖ ≤ ‖density‖ ^ 2 := by
        nlinarith [norm_nonneg density]
      _ ≤ bound := hsquareBound

end Matrix

end

end YangMills.RG
