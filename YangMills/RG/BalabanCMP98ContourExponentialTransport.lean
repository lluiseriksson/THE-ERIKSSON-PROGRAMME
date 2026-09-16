/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98SourceGeneratorWordBound
import YangMills.RG.BalabanCMP98FourContourRightTrivialization
import YangMills.RG.SUNProductDeviation

/-!
# Exact exponential transport of the CMP98 four-contour word

The quantitative ordered-word estimate is useful only after its word has
been identified with the literal physical holonomy.  This file performs
that identification.  A reversed edge is first rewritten as a left
exponential increment followed by its fixed background matrix.  The
increments are then conjugated by the accumulated background prefix.

Consequently the complete four-factor product, including the inverse coarse
contour, is exactly an ordered exponential word times its background value.
No commutativity and no Taylor approximation are used in this transport.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

local instance cmp98ContourTransportMatrixL2NormOneClass :
    NormOneClass (Matrix (Fin Nc) (Fin Nc) ℂ) where
  norm_one := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp

/-- The fixed special-unitary matrix carried by an oriented edge. -/
def cmp98OrientedBackgroundSUN
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) : SUN Nc :=
  if e.sign then U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e))
  else (U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e)))⁻¹

/-- The generator moved to the left of its oriented background factor.
For a positive edge it is unchanged; for a negative edge it is conjugated
by the inverse background link. -/
def cmp98OrientedLeftGenerator
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then orientedWilsonGenerator A e
  else
    (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) *
      orientedWilsonGenerator A e *
        Matrix.conjTranspose
          (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ)

/-- Background prefixes transport every left generator to the common
starting frame of the contour. -/
def cmp98PrefixTransportedGenerators
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc) :
    SUN Nc → List (ConcreteEdge d (M * N')) →
      List (Matrix (Fin Nc) (Fin Nc) ℂ)
  | _, [] => []
  | p, e :: es =>
      ((p : Matrix (Fin Nc) (Fin Nc) ℂ) *
          cmp98OrientedLeftGenerator U A e *
          Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ)) ::
        cmp98PrefixTransportedGenerators U A
          (p * cmp98OrientedBackgroundSUN U e) es

/-- The transported word based at the identity prefix. -/
def cmp98ContourTransportedGenerators
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    List (Matrix (Fin Nc) (Fin Nc) ℂ) :=
  cmp98PrefixTransportedGenerators U A 1 es

/-- Ordered exponential product with the matrix topology fixed explicitly. -/
def cmp98OrderedPhysicalExpProduct
    (t : ℝ) (xs : List (Matrix (Fin Nc) (Fin Nc) ℂ)) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  (xs.map fun X => physicalMatrixExp (t • X)).prod

/-- The explicit physical spelling agrees with the generic Banach-algebra
word used by the quantitative estimate. -/
theorem cmp98OrderedPhysicalExpProduct_eq_orderedExpProduct
    (t : ℝ) (xs : List (Matrix (Fin Nc) (Fin Nc) ℂ)) :
    cmp98OrderedPhysicalExpProduct t xs = orderedExpProduct t xs := by
  rfl

@[simp] theorem cmp98PrefixTransportedGenerators_length
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (p : SUN Nc) (es : List (ConcreteEdge d (M * N'))) :
    (cmp98PrefixTransportedGenerators U A p es).length = es.length := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih => simp [cmp98PrefixTransportedGenerators, ih]

@[simp] theorem cmp98ContourTransportedGenerators_length
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) :
    (cmp98ContourTransportedGenerators U A es).length = es.length := by
  simp [cmp98ContourTransportedGenerators]

/-- The oriented background matrix is literally the defining matrix of the
physical gauge configuration on that oriented edge. -/
theorem cmp98OrientedBackgroundSUN_coe
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) =
      orientedWilsonBackgroundFactor U e := by
  cases h : e.sign
  · simp only [cmp98OrientedBackgroundSUN, orientedWilsonBackgroundFactor,
      h, Bool.false_eq_true, if_false, orientedWilsonPositiveBase]
    let V : SUN Nc :=
      U (positiveEdgeOfPhysicalBond (physicalBondOfEdge e))
    have hunit : (V : Matrix (Fin Nc) (Fin Nc) ℂ) *
        Matrix.conjTranspose (V : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 :=
      su_mul_conjTranspose_self V
    have hinv : ((V⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) *
        (V : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 := by
      change ((V⁻¹ * V : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) = 1
      simp
    change ((V⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) =
      Matrix.conjTranspose (V : Matrix (Fin Nc) (Fin Nc) ℂ)
    calc
      ((V⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) =
          ((V⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) * 1 := by
            rw [mul_one]
      _ = ((V⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) *
          ((V : Matrix (Fin Nc) (Fin Nc) ℂ) *
            Matrix.conjTranspose (V : Matrix (Fin Nc) (Fin Nc) ℂ)) := by
              rw [hunit]
      _ = (((V⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) *
            (V : Matrix (Fin Nc) (Fin Nc) ℂ)) *
          Matrix.conjTranspose (V : Matrix (Fin Nc) (Fin Nc) ℂ) := by
              rw [mul_assoc]
      _ = Matrix.conjTranspose (V : Matrix (Fin Nc) (Fin Nc) ℂ) := by
              rw [hinv, one_mul]
  · simp [cmp98OrientedBackgroundSUN, orientedWilsonBackgroundFactor,
      orientedWilsonPositiveBase, h, physicalBondOfEdge,
      positiveEdgeOfPhysicalBond]

/-- Matrix exponential commutes with conjugation by a physical unitary.
This bridge uses the nonsingular matrix inverse only internally. -/
theorem physicalMatrixExp_unitary_conj
    (u : UN Nc) (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    physicalMatrixExp ((u : Matrix (Fin Nc) (Fin Nc) ℂ) * X *
        Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ)) =
      (u : Matrix (Fin Nc) (Fin Nc) ℂ) * physicalMatrixExp X *
        Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  have hi : IsUnit (u : Matrix (Fin Nc) (Fin Nc) ℂ) := Unitary.isUnit_coe
  have hdet : IsUnit (u : Matrix (Fin Nc) (Fin Nc) ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hi
  have hunit : (u : Matrix (Fin Nc) (Fin Nc) ℂ) *
      Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self u
  have hinv : (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ =
      Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
    calc
      (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ =
          (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ * 1 := by rw [mul_one]
      _ = (u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ *
          ((u : Matrix (Fin Nc) (Fin Nc) ℂ) *
            Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ)) := by
              rw [hunit]
      _ = ((u : Matrix (Fin Nc) (Fin Nc) ℂ)⁻¹ *
            (u : Matrix (Fin Nc) (Fin Nc) ℂ)) *
          Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
              rw [mul_assoc]
      _ = Matrix.conjTranspose (u : Matrix (Fin Nc) (Fin Nc) ℂ) := by
              rw [Matrix.nonsing_inv_mul _ hdet, one_mul]
  unfold physicalMatrixExp
  rw [← hinv]
  exact Matrix.exp_conj _ _ hi

/-- Right multiplication by the adjoint of a special-unitary matrix is
contractive in the L2 operator norm. -/
theorem norm_matrix_mul_sun_conjTranspose_le
    (X : Matrix (Fin Nc) (Fin Nc) ℂ) (p : SUN Nc) :
    ‖X * Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ)‖ ≤ ‖X‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact (norm_sun_mul_matrix_le p (Matrix.conjTranspose X)).trans_eq
    (Matrix.l2_opNorm_conjTranspose X)

/-- Conjugation by a special-unitary matrix is contractive. -/
theorem norm_sun_conj_matrix_le (p : SUN Nc)
    (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖(p : Matrix (Fin Nc) (Fin Nc) ℂ) * X *
        Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ)‖ ≤ ‖X‖ :=
  (norm_matrix_mul_sun_conjTranspose_le
    ((p : Matrix (Fin Nc) (Fin Nc) ℂ) * X) p).trans
      (norm_sun_mul_matrix_le p X)

/-- Each oriented edge curve is a left exponential increment followed by
its fixed oriented background matrix. -/
theorem orientedWilsonFactor_eq_exp_leftGenerator_mul_background
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) (t : ℝ) :
    orientedWilsonFactor U A e t =
      physicalMatrixExp (t • cmp98OrientedLeftGenerator U A e) *
        (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  cases h : e.sign
  · let u : UN Nc := specialUnitaryToUnitary
        (cmp98OrientedBackgroundSUN U e)
    have hexp := physicalMatrixExp_unitary_conj u
      (t • orientedWilsonGenerator A e)
    change physicalMatrixExp
        ((cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) *
          (t • orientedWilsonGenerator A e) *
          Matrix.conjTranspose
            (cmp98OrientedBackgroundSUN U e :
              Matrix (Fin Nc) (Fin Nc) ℂ)) =
      (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) *
        physicalMatrixExp (t • orientedWilsonGenerator A e) *
        Matrix.conjTranspose
          (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) at hexp
    have hsmul :
        t • ((cmp98OrientedBackgroundSUN U e :
              Matrix (Fin Nc) (Fin Nc) ℂ) *
            orientedWilsonGenerator A e *
            Matrix.conjTranspose
              (cmp98OrientedBackgroundSUN U e :
                Matrix (Fin Nc) (Fin Nc) ℂ)) =
          (cmp98OrientedBackgroundSUN U e :
              Matrix (Fin Nc) (Fin Nc) ℂ) *
            (t • orientedWilsonGenerator A e) *
            Matrix.conjTranspose
              (cmp98OrientedBackgroundSUN U e :
                Matrix (Fin Nc) (Fin Nc) ℂ) := by
      rw [← smul_mul_assoc, ← mul_smul_comm]
    change orientedWilsonFactor U A e t =
      physicalMatrixExp (t • cmp98OrientedLeftGenerator U A e) *
        (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ)
    rw [show cmp98OrientedLeftGenerator U A e =
        (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) *
          orientedWilsonGenerator A e *
          Matrix.conjTranspose
            (cmp98OrientedBackgroundSUN U e :
              Matrix (Fin Nc) (Fin Nc) ℂ) by
        simp [cmp98OrientedLeftGenerator, h], hsmul, hexp]
    rw [mul_assoc]
    rw [show Matrix.conjTranspose
          (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) *
          (cmp98OrientedBackgroundSUN U e : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 by
        exact Unitary.coe_star_mul_self u]
    rw [mul_one]
    simp only [orientedWilsonFactor, h, Bool.false_eq_true, if_false]
    rw [cmp98OrientedBackgroundSUN_coe]
    simp [orientedWilsonBackgroundFactor, h]
  · simp [orientedWilsonFactor, cmp98OrientedLeftGenerator,
      cmp98OrientedBackgroundSUN, orientedWilsonPositiveBase,
      physicalMatrixExp, h]

/-- Unitary conjugation preserves the source generator bound. -/
theorem norm_cmp98OrientedLeftGenerator_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    ‖cmp98OrientedLeftGenerator U A e‖ ≤
      cmp98SourceFieldSupNorm A := by
  cases h : e.sign
  · have hconj := norm_sun_conj_matrix_le
      (cmp98OrientedBackgroundSUN U e) (orientedWilsonGenerator A e)
    have hleft : ‖cmp98OrientedLeftGenerator U A e‖ ≤
        ‖orientedWilsonGenerator A e‖ := by
      simpa [cmp98OrientedLeftGenerator, h] using hconj
    exact hleft.trans
      (norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm A e)
  · simpa [cmp98OrientedLeftGenerator, h] using
      norm_orientedWilsonGenerator_le_cmp98SourceFieldSupNorm A e

/-- Every common-frame transported generator obeys the same volume-free
source bound. -/
theorem norm_of_mem_cmp98PrefixTransportedGenerators_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (p : SUN Nc) (es : List (ConcreteEdge d (M * N')))
    (X : Matrix (Fin Nc) (Fin Nc) ℂ)
    (hX : X ∈ cmp98PrefixTransportedGenerators U A p es) :
    ‖X‖ ≤ cmp98SourceFieldSupNorm A := by
  induction es generalizing p with
  | nil => simp [cmp98PrefixTransportedGenerators] at hX
  | cons e es ih =>
      simp only [cmp98PrefixTransportedGenerators, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact (norm_sun_conj_matrix_le p
          (cmp98OrientedLeftGenerator U A e)).trans
            (norm_cmp98OrientedLeftGenerator_le U A e)
      · exact ih _ hX

/-- The oriented background element agrees with the original physical
gauge configuration, including on reverse edges. -/
theorem cmp98OrientedBackgroundSUN_eq_apply
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (e : ConcreteEdge d (M * N')) :
    cmp98OrientedBackgroundSUN U e = U e := by
  rcases e with ⟨x, i, s⟩
  cases s
  · have hmap := U.map_reverse (ConcreteEdge.mk x i true)
    change U (ConcreteEdge.mk x i false) =
      (U (ConcreteEdge.mk x i true))⁻¹ at hmap
    simpa [cmp98OrientedBackgroundSUN, physicalBondOfEdge,
      positiveEdgeOfPhysicalBond] using hmap.symm
  · rfl

/-- Exact factorization with an arbitrary physical background prefix. -/
theorem cmp98_prefix_mul_contourMatrixCurve_eq_orderedExpProduct
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (p : SUN Nc) (es : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
        cmp98ContourMatrixCurve U A es t =
      cmp98OrderedPhysicalExpProduct t
          (cmp98PrefixTransportedGenerators U A p es) *
        ((p * wilsonLine U es : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) := by
  induction es generalizing p with
  | nil =>
      simp only [cmp98ContourMatrixCurve,
        cmp98PrefixTransportedGenerators,
        cmp98OrderedPhysicalExpProduct, List.map_nil, List.prod_nil,
        mul_one, one_mul]
      rw [show wilsonLine U [] = 1 by rfl, mul_one]
  | cons e es ih =>
      let q : SUN Nc := p * cmp98OrientedBackgroundSUN U e
      let Z : Matrix (Fin Nc) (Fin Nc) ℂ :=
        (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
          cmp98OrientedLeftGenerator U A e *
          Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ)
      have hp : Matrix.conjTranspose
          (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
          (p : Matrix (Fin Nc) (Fin Nc) ℂ) = 1 :=
        su_conjTranspose_mul_self p
      have hsmul :
          t • ((p : Matrix (Fin Nc) (Fin Nc) ℂ) *
              cmp98OrientedLeftGenerator U A e *
              Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ)) =
            (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
              (t • cmp98OrientedLeftGenerator U A e) *
              Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ) := by
            rw [← smul_mul_assoc, ← mul_smul_comm]
      have hexp : physicalMatrixExp (t • Z) =
          (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
            physicalMatrixExp
              (t • cmp98OrientedLeftGenerator U A e) *
            Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ) := by
        rw [show t • Z =
            (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
              (t • cmp98OrientedLeftGenerator U A e) *
              Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ) by
              simpa only [Z] using hsmul]
        exact physicalMatrixExp_unitary_conj
          (specialUnitaryToUnitary p)
          (t • cmp98OrientedLeftGenerator U A e)
      rw [cmp98ContourMatrixCurve,
        orientedWilsonFactor_eq_exp_leftGenerator_mul_background]
      have hreassociate :
          (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
              (physicalMatrixExp
                  (t • cmp98OrientedLeftGenerator U A e) *
                (cmp98OrientedBackgroundSUN U e :
                  Matrix (Fin Nc) (Fin Nc) ℂ) *
                cmp98ContourMatrixCurve U A es t) =
            physicalMatrixExp (t • Z) *
              ((q : Matrix (Fin Nc) (Fin Nc) ℂ) *
                cmp98ContourMatrixCurve U A es t) := by
        rw [hexp]
        have hqcoe : (q : Matrix (Fin Nc) (Fin Nc) ℂ) =
            (p : Matrix (Fin Nc) (Fin Nc) ℂ) *
              (cmp98OrientedBackgroundSUN U e :
                Matrix (Fin Nc) (Fin Nc) ℂ) := by rfl
        rw [hqcoe]
        simp only [mul_assoc]
        rw [← mul_assoc
          (Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ))
          (p : Matrix (Fin Nc) (Fin Nc) ℂ), hp, one_mul]
      rw [hreassociate, ih q]
      simp only [cmp98PrefixTransportedGenerators,
        cmp98OrderedPhysicalExpProduct,
        List.map_cons, List.prod_cons]
      change physicalMatrixExp (t • Z) *
          (cmp98OrderedPhysicalExpProduct t
              (cmp98PrefixTransportedGenerators U A q es) *
            ((q * wilsonLine U es : SUN Nc) :
              Matrix (Fin Nc) (Fin Nc) ℂ)) = _
      rw [← mul_assoc]
      congr 1
      dsimp [q]
      rw [cmp98OrientedBackgroundSUN_eq_apply, wilsonLine_cons, mul_assoc]
      rfl

/-- Identity-prefix form of the exact contour factorization. -/
theorem cmp98_contourMatrixCurve_eq_orderedExpProduct_mul_background
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    cmp98ContourMatrixCurve U A es t =
      cmp98OrderedPhysicalExpProduct t
          (cmp98ContourTransportedGenerators U A es) *
        ((wilsonLine U es : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) := by
  simpa [cmp98ContourTransportedGenerators] using
    cmp98_prefix_mul_contourMatrixCurve_eq_orderedExpProduct
      U A (1 : SUN Nc) es t

/-- Contour curves multiply under literal path concatenation. -/
theorem cmp98ContourMatrixCurve_append
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es₁ es₂ : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    cmp98ContourMatrixCurve U A (es₁ ++ es₂) t =
      cmp98ContourMatrixCurve U A es₁ t *
        cmp98ContourMatrixCurve U A es₂ t := by
  induction es₁ with
  | nil => simp [cmp98ContourMatrixCurve]
  | cons e es ih =>
      simp only [List.cons_append, cmp98ContourMatrixCurve, ih, mul_assoc]

/-- Reversing a literal contour gives the conjugate-transposed physical
curve at every real chart parameter. -/
theorem cmp98ContourMatrixCurve_reverseLatticePath
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    cmp98ContourMatrixCurve U A
        (reverseLatticePath (d := d) (N := M * N') (G := SUN Nc) es) t =
      Matrix.conjTranspose (cmp98ContourMatrixCurve U A es t) := by
  let X : PhysicalSuMatrixTangent d (M * N') Nc :=
    physicalCochainToSuMatrixTangent A
  have htangent :
      physicalTwoParameterAmbientTangent X 0 t 0 =
        t • physicalSuTangentToAmbient X := by
    funext b
    change t • (X b).toMatrix +
      (0 : ℝ) • ((0 : PhysicalSuMatrixTangent d (M * N') Nc) b).toMatrix =
        t • (X b).toMatrix
    have hz : (0 : ℝ) •
        ((0 : PhysicalSuMatrixTangent d (M * N') Nc) b).toMatrix = 0 :=
      zero_smul ℝ _
    rw [hz, add_zero]
  have hcurve (ws : List (ConcreteEdge d (M * N'))) :
      cmp98ContourMatrixCurve U A ws t =
        (wilsonLine (physicalSuUnitaryLeftVariation U X 0 t 0) ws :
          UN Nc).val := by
    rw [← cmp98AmbientWilsonLineMatrix_line_eq_contourMatrixCurve U A ws t,
      ← htangent]
    exact cmp98AmbientWilsonLineMatrix_twoParameter_eq_unitaryWilsonLine
      U X 0 t 0 ws
  rw [hcurve, hcurve]
  change ((wilsonLine (physicalSuUnitaryLeftVariation U X 0 t 0)
      (reverseLatticePath (d := d) (N := M * N') (G := UN Nc) es) : UN Nc) :
        Matrix (Fin Nc) (Fin Nc) ℂ) = _
  unfold reverseLatticePath
  rw [wilsonLine_reverse_list]
  rw [← Unitary.star_eq_inv, Unitary.coe_star]
  rfl

/-- The literal four-factor curve is one contour: the final coarse path is
traversed backwards. -/
theorem cmp98UbarFourFactorProduct_eq_sourceContourMatrixCurve
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ) :
    fourFactorProduct (cmp98UbarContourFactors U A b x) t =
      cmp98ContourMatrixCurve U A
        (cmp98SourceFourContourEdges (Nc := Nc) b x) t := by
  simp [fourFactorProduct, cmp98UbarContourFactors,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, cmp98SourceFourContourEdges]
  rw [cmp98ContourMatrixCurve_append, cmp98ContourMatrixCurve_append,
    cmp98ContourMatrixCurve_append,
    cmp98ContourMatrixCurve_reverseLatticePath]
  simp only [mul_assoc]

/-- Right trivialization by the background contour removes the final
background factor and leaves exactly the transported exponential word. -/
theorem cmp98ContourMatrixCurve_mul_backgroundConjTranspose_eq_expProduct
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (es : List (ConcreteEdge d (M * N'))) (t : ℝ) :
    cmp98ContourMatrixCurve U A es t *
        Matrix.conjTranspose (cmp98ContourMatrixCurve U A es 0) =
      cmp98OrderedPhysicalExpProduct t
        (cmp98ContourTransportedGenerators U A es) := by
  rw [cmp98_contourMatrixCurve_eq_orderedExpProduct_mul_background,
    cmp98ContourMatrixCurve_zero_eq_wilsonLine, mul_assoc]
  rw [su_mul_conjTranspose_self, mul_one]

/-- Source specialization: the relative physical four-contour holonomy is
literally the transported ordered exponential word. -/
theorem cmp98UbarRelativeFourFactorProduct_eq_expProduct
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ) :
    fourFactorProduct (cmp98UbarContourFactors U A b x) t *
        Matrix.conjTranspose
          (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) =
      cmp98OrderedPhysicalExpProduct t
        (cmp98ContourTransportedGenerators U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x)) := by
  rw [cmp98UbarFourFactorProduct_eq_sourceContourMatrixCurve,
    cmp98UbarFourFactorProduct_eq_sourceContourMatrixCurve]
  exact cmp98ContourMatrixCurve_mul_backgroundConjTranspose_eq_expProduct
    U A (cmp98SourceFourContourEdges (Nc := Nc) b x) t

/-- First-order displacement of the literal relative four-contour
holonomy, with its exact contour length. -/
theorem norm_cmp98UbarRelativeFourFactorProduct_sub_one_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let generators := cmp98ContourTransportedGenerators U A
      (cmp98SourceFourContourEdges (Nc := Nc) b x)
    ‖fourFactorProduct (cmp98UbarContourFactors U A b x) t *
          Matrix.conjTranspose
            (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) - 1‖ ≤
      generators.length * (2 * (|t| * cmp98SourceFieldSupNorm A)) *
        (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length := by
  dsimp only
  have hraw := norm_orderedExpProduct_sub_one_le
    t (cmp98SourceFieldSupNorm A)
      (cmp98ContourTransportedGenerators U A
        (cmp98SourceFourContourEdges (Nc := Nc) b x))
      (cmp98SourceFieldSupNorm_nonneg A)
      (fun X hX => norm_of_mem_cmp98PrefixTransportedGenerators_le
        U A 1 (cmp98SourceFourContourEdges (Nc := Nc) b x) X hX)
      hsmall
  rw [← cmp98OrderedPhysicalExpProduct_eq_orderedExpProduct,
    ← cmp98UbarRelativeFourFactorProduct_eq_expProduct U A b x t] at hraw
  exact hraw

/-- Volume-independent source-length version of the relative displacement
bound. -/
theorem norm_cmp98UbarRelativeFourFactorProduct_sub_one_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let sourceLength : ℕ := 2 * (d + 1) * M
    ‖fourFactorProduct (cmp98UbarContourFactors U A b x) t *
          Matrix.conjTranspose
            (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) - 1‖ ≤
      sourceLength * (2 * (|t| * cmp98SourceFieldSupNorm A)) *
        (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength := by
  dsimp only
  let generators := cmp98ContourTransportedGenerators U A
    (cmp98SourceFourContourEdges (Nc := Nc) b x)
  let sourceLength : ℕ := 2 * (d + 1) * M
  let q : ℝ := |t| * cmp98SourceFieldSupNorm A
  have hraw := norm_cmp98UbarRelativeFourFactorProduct_sub_one_le
    U A b x t hsmall
  have hlen : generators.length ≤ sourceLength := by
    simpa [generators, sourceLength] using
      cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx
  have hcast : (generators.length : ℝ) ≤ sourceLength := by
    exact_mod_cast hlen
  have hq : 0 ≤ q := by
    exact mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
  have hq0 : 0 ≤ 2 * q := by linarith
  have hbase : 1 ≤ 1 + 2 * q := by linarith
  have hpow : (1 + 2 * q) ^ generators.length ≤
      (1 + 2 * q) ^ sourceLength := pow_le_pow_right₀ hbase hlen
  dsimp only [generators, sourceLength, q] at hraw ⊢
  refine hraw.trans ?_
  calc
    (generators.length : ℝ) *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length
        ≤ (sourceLength : ℝ) *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcast hq0)
              (pow_nonneg (by linarith [hbase]) generators.length)
    _ ≤ (sourceLength : ℝ) *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength := by
            exact mul_le_mul_of_nonneg_left hpow
              (mul_nonneg (Nat.cast_nonneg _) hq0)

/-- The same source-scale estimate controls the displacement of the
unnormalized physical four-contour curve itself. -/
theorem norm_cmp98UbarFourFactorProduct_sub_zero_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let sourceLength : ℕ := 2 * (d + 1) * M
    ‖fourFactorProduct (cmp98UbarContourFactors U A b x) t -
        fourFactorProduct (cmp98UbarContourFactors U A b x) 0‖ ≤
      sourceLength * (2 * (|t| * cmp98SourceFieldSupNorm A)) *
        (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength := by
  dsimp only
  let Ft := fourFactorProduct (cmp98UbarContourFactors U A b x) t
  let F0 := fourFactorProduct (cmp98UbarContourFactors U A b x) 0
  have hunit : Matrix.conjTranspose F0 * F0 = 1 := by
    exact cmp98UbarFourFactorProduct_zero_conjTranspose_mul U A b x
  have hdecomp : Ft - F0 =
      (Ft * Matrix.conjTranspose F0 - 1) * F0 := by
    rw [sub_mul, one_mul, mul_assoc, hunit, mul_one]
  have hnorm0 : ‖F0‖ = 1 := by
    dsimp only [F0]
    rw [cmp98UbarFourFactorProduct_zero_eq_sourceDeviation]
    exact norm_SUN_coe_l2_opNorm _
  rw [hdecomp]
  calc
    ‖(Ft * Matrix.conjTranspose F0 - 1) * F0‖
        ≤ ‖Ft * Matrix.conjTranspose F0 - 1‖ * ‖F0‖ := norm_mul_le _ _
    _ = ‖Ft * Matrix.conjTranspose F0 - 1‖ := by rw [hnorm0, mul_one]
    _ ≤ _ := norm_cmp98UbarRelativeFourFactorProduct_sub_one_le_sourceScale
      U A b x hx t hsmall

/-- The source-scale displacement bound in the exact ambient-deviation
coordinates consumed by the local Mercator logarithm. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_physicalLine_sub_zero_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let sourceLength : ℕ := 2 * (d + 1) * M
    ‖cmp98UbarAmbientDeviationMatrix U b x
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) -
        cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤
      sourceLength * (2 * (|t| * cmp98SourceFieldSupNorm A)) *
        (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength := by
  dsimp only
  have ht := cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
    U A b x t
  have hzero : (0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
  have h0 := cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
    U A b x 0
  rw [hzero] at h0
  rw [ht, h0]
  simpa [cmp98UbarDeviationCurve] using
    norm_cmp98UbarFourFactorProduct_sub_zero_le_sourceScale
      U A b x hx t hsmall

/-- A concrete source-scale margin keeps the physical contour deviation in
the open Mercator unit ball.  This is the quantitative domain bridge needed
before bounding the nonlinear logarithm. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_physicalLine_lt_one
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t δ₀ : ℝ)
    (hbase : ‖cmp98UbarAmbientDeviationMatrix U b x 0‖ ≤ δ₀)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2)
    (hmargin : δ₀ +
        (2 * (d + 1) * M : ℕ) *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
            (2 * (d + 1) * M) < 1) :
    ‖cmp98UbarAmbientDeviationMatrix U b x
      (t • physicalSuTangentToAmbient
        (physicalCochainToSuMatrixTangent A))‖ < 1 := by
  let Dt := cmp98UbarAmbientDeviationMatrix U b x
    (t • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A))
  let D0 := cmp98UbarAmbientDeviationMatrix U b x 0
  have hdisp :=
    norm_cmp98UbarAmbientDeviationMatrix_physicalLine_sub_zero_le
      U A b x hx t hsmall
  have htri : ‖Dt‖ ≤ ‖Dt - D0‖ + ‖D0‖ := by
    have h := norm_add_le (Dt - D0) D0
    simpa [Dt, D0] using h
  dsimp only [Dt, D0] at htri
  have hm :
      (2 * (d + 1) * M : ℕ) *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
            (2 * (d + 1) * M) + δ₀ < 1 := by
    linarith
  exact htri.trans_lt ((add_le_add hdisp hbase).trans_lt hm)

/-- The literal linear term of the transported word is the genuine
right-trivialized first variation of the physical four-contour product. -/
theorem cmp98UbarFirstVariation_mul_backgroundConjTranspose_eq_generatorSum
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) :
    cmp98UbarDeviationFirstVariation U A b x 0 *
        Matrix.conjTranspose
          (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) =
      (cmp98ContourTransportedGenerators U A
        (cmp98SourceFourContourEdges (Nc := Nc) b x)).sum := by
  have hfour : HasDerivAt
      (fun t => fourFactorProduct (cmp98UbarContourFactors U A b x) t)
      (cmp98UbarDeviationFirstVariation U A b x 0) 0 := by
    exact hasDerivAt_fourFactorProduct
      (cmp98UbarContourFactors U A b x)
      (cmp98UbarContourFactorVariations U A b x) 0
      (hasDerivAt_cmp98UbarContourFactors U A b x · 0)
  have hleft := hfour.mul_const
    (Matrix.conjTranspose
      (fourFactorProduct (cmp98UbarContourFactors U A b x) 0))
  have hright : HasDerivAt
      (fun t => cmp98OrderedPhysicalExpProduct t
        (cmp98ContourTransportedGenerators U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x)))
      (cmp98ContourTransportedGenerators U A
        (cmp98SourceFourContourEdges (Nc := Nc) b x)).sum 0 := by
    simpa [cmp98OrderedPhysicalExpProduct_eq_orderedExpProduct] using
      hasDerivAt_orderedExpProduct_zero
        (cmp98ContourTransportedGenerators U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x))
  have hfun :
      (fun t => fourFactorProduct (cmp98UbarContourFactors U A b x) t *
        Matrix.conjTranspose
          (fourFactorProduct (cmp98UbarContourFactors U A b x) 0)) =
      fun t => cmp98OrderedPhysicalExpProduct t
        (cmp98ContourTransportedGenerators U A
          (cmp98SourceFourContourEdges (Nc := Nc) b x)) := by
    funext t
    exact cmp98UbarRelativeFourFactorProduct_eq_expProduct U A b x t
  rw [hfun] at hleft
  exact hleft.unique hright

/-- Exact-length quadratic estimate for the literal relative physical
holonomy.  The linear term is its genuine first variation, not a supplied
matrix. -/
theorem norm_cmp98UbarRelativeFourFactorProduct_sub_linear_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N')) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let generators := cmp98ContourTransportedGenerators U A
      (cmp98SourceFourContourEdges (Nc := Nc) b x)
    ‖fourFactorProduct (cmp98UbarContourFactors U A b x) t *
          Matrix.conjTranspose
            (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) - 1 -
        t • (cmp98UbarDeviationFirstVariation U A b x 0 *
          Matrix.conjTranspose
            (fourFactorProduct (cmp98UbarContourFactors U A b x) 0))‖ ≤
      (generators.length : ℝ) ^ 2 *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length +
        generators.length *
          (2 * (|t| * cmp98SourceFieldSupNorm A) ^ 2) := by
  dsimp only
  have hraw := norm_orderedExpProduct_sub_one_sub_smul_sum_le
    t (cmp98SourceFieldSupNorm A)
      (cmp98ContourTransportedGenerators U A
        (cmp98SourceFourContourEdges (Nc := Nc) b x))
      (cmp98SourceFieldSupNorm_nonneg A)
      (fun X hX => norm_of_mem_cmp98PrefixTransportedGenerators_le
        U A 1 (cmp98SourceFourContourEdges (Nc := Nc) b x) X hX)
      hsmall
  rw [← cmp98OrderedPhysicalExpProduct_eq_orderedExpProduct,
    ← cmp98UbarRelativeFourFactorProduct_eq_expProduct U A b x t,
    ← cmp98UbarFirstVariation_mul_backgroundConjTranspose_eq_generatorSum
      U A b x] at hraw
  exact hraw

/-- Volume-independent source-scale form of the physical quadratic
holonomy estimate. -/
theorem norm_cmp98UbarRelativeFourFactorProduct_sub_linear_le_sourceScale
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let sourceLength : ℕ := 2 * (d + 1) * M
    ‖fourFactorProduct (cmp98UbarContourFactors U A b x) t *
          Matrix.conjTranspose
            (fourFactorProduct (cmp98UbarContourFactors U A b x) 0) - 1 -
        t • (cmp98UbarDeviationFirstVariation U A b x 0 *
          Matrix.conjTranspose
            (fourFactorProduct (cmp98UbarContourFactors U A b x) 0))‖ ≤
      (sourceLength : ℝ) ^ 2 *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength +
        sourceLength *
          (2 * (|t| * cmp98SourceFieldSupNorm A) ^ 2) := by
  dsimp only
  let generators := cmp98ContourTransportedGenerators U A
    (cmp98SourceFourContourEdges (Nc := Nc) b x)
  let sourceLength : ℕ := 2 * (d + 1) * M
  let q : ℝ := |t| * cmp98SourceFieldSupNorm A
  have hraw := norm_cmp98UbarRelativeFourFactorProduct_sub_linear_le
    U A b x t hsmall
  have hlen : generators.length ≤ sourceLength := by
    simpa [generators, sourceLength] using
      cmp98SourceFourContourEdges_length_le (Nc := Nc) b x hx
  have hcast : (generators.length : ℝ) ≤ sourceLength := by
    exact_mod_cast hlen
  have hbase : 1 ≤ 1 + 2 * q := by
    have hq : 0 ≤ q :=
      mul_nonneg (abs_nonneg t) (cmp98SourceFieldSupNorm_nonneg A)
    linarith
  have hpow : (1 + 2 * q) ^ generators.length ≤
      (1 + 2 * q) ^ sourceLength :=
    pow_le_pow_right₀ hbase hlen
  dsimp only [generators, q, sourceLength] at hraw ⊢
  refine hraw.trans (add_le_add ?_ ?_)
  · have hsq : (generators.length : ℝ) ^ 2 ≤
        (sourceLength : ℝ) ^ 2 := by
      exact sq_le_sq₀ (by positivity) (by positivity) |>.2 hcast
    have hfactor : 0 ≤
        (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 := sq_nonneg _
    calc
      (generators.length : ℝ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length
          ≤ (sourceLength : ℝ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ generators.length := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hsq hfactor)
                (pow_nonneg (by linarith [hbase]) generators.length)
      _ ≤ (sourceLength : ℝ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength := by
              exact mul_le_mul_of_nonneg_left hpow
                (mul_nonneg (sq_nonneg _) hfactor)
  · exact mul_le_mul_of_nonneg_right hcast
      (mul_nonneg (by positivity) (sq_nonneg _))

/-- The relative quadratic holonomy estimate transports back to the exact
ambient-deviation coordinates without any loss: multiplication by the
unitary background word has norm one.  The linear term is the literal
first variation of the physical contour at the background. -/
theorem norm_cmp98UbarAmbientDeviationMatrix_physicalLine_sub_zero_sub_linear_le
    (U : PhysicalGaugeBackground d (M * N') Nc)
    (A : PhysicalGaugeOneCochain d (M * N') Nc)
    (b : PhysicalBond d N') (x : FinBox d (M * N'))
    (hx : x ∈ blockOf M N' b.1) (t : ℝ)
    (hsmall : |t| * cmp98SourceFieldSupNorm A ≤ 1 / 2) :
    let sourceLength : ℕ := 2 * (d + 1) * M
    ‖cmp98UbarAmbientDeviationMatrix U b x
          (t • physicalSuTangentToAmbient
            (physicalCochainToSuMatrixTangent A)) -
        cmp98UbarAmbientDeviationMatrix U b x 0 -
        t • cmp98UbarDeviationFirstVariation U A b x 0‖ ≤
      (sourceLength : ℝ) ^ 2 *
          (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
          (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^ sourceLength +
        sourceLength *
          (2 * (|t| * cmp98SourceFieldSupNorm A) ^ 2) := by
  dsimp only
  let Ft := fourFactorProduct (cmp98UbarContourFactors U A b x) t
  let F0 := fourFactorProduct (cmp98UbarContourFactors U A b x) 0
  let Dp := cmp98UbarDeviationFirstVariation U A b x 0
  have hunit : Matrix.conjTranspose F0 * F0 = 1 := by
    exact cmp98UbarFourFactorProduct_zero_conjTranspose_mul U A b x
  have hbase : (Ft * Matrix.conjTranspose F0 - 1) * F0 = Ft - F0 := by
    rw [sub_mul, one_mul, mul_assoc, hunit, mul_one]
  have hlinear : (t • (Dp * Matrix.conjTranspose F0)) * F0 = t • Dp := by
    rw [smul_mul_assoc, mul_assoc, hunit, mul_one]
  have hdecomp :
      (Ft - 1) - (F0 - 1) - t • Dp =
        (Ft * Matrix.conjTranspose F0 - 1 -
          t • (Dp * Matrix.conjTranspose F0)) * F0 := by
    calc
      (Ft - 1) - (F0 - 1) - t • Dp = (Ft - F0) - t • Dp := by abel
      _ = (Ft * Matrix.conjTranspose F0 - 1) * F0 -
          (t • (Dp * Matrix.conjTranspose F0)) * F0 := by
            rw [hbase, hlinear]
      _ = (Ft * Matrix.conjTranspose F0 - 1 -
          t • (Dp * Matrix.conjTranspose F0)) * F0 := by
            exact (sub_mul
              (Ft * Matrix.conjTranspose F0 - 1)
              (t • (Dp * Matrix.conjTranspose F0)) F0).symm
  have hnorm0 : ‖F0‖ = 1 := by
    dsimp only [F0]
    rw [cmp98UbarFourFactorProduct_zero_eq_sourceDeviation]
    exact norm_SUN_coe_l2_opNorm _
  have hrelative :=
    norm_cmp98UbarRelativeFourFactorProduct_sub_linear_le_sourceScale
      U A b x hx t hsmall
  have htransport :
      ‖(Ft - 1) - (F0 - 1) - t • Dp‖ ≤
        (2 * (d + 1) * M : ℕ) ^ 2 *
            (2 * (|t| * cmp98SourceFieldSupNorm A)) ^ 2 *
            (1 + 2 * (|t| * cmp98SourceFieldSupNorm A)) ^
              (2 * (d + 1) * M) +
          (2 * (d + 1) * M : ℕ) *
            (2 * (|t| * cmp98SourceFieldSupNorm A) ^ 2) := by
    rw [hdecomp]
    calc
      ‖(Ft * Matrix.conjTranspose F0 - 1 -
            t • (Dp * Matrix.conjTranspose F0)) * F0‖
          ≤ ‖Ft * Matrix.conjTranspose F0 - 1 -
              t • (Dp * Matrix.conjTranspose F0)‖ * ‖F0‖ := norm_mul_le _ _
      _ = ‖Ft * Matrix.conjTranspose F0 - 1 -
              t • (Dp * Matrix.conjTranspose F0)‖ := by rw [hnorm0, mul_one]
      _ ≤ _ := by simpa [Ft, F0, Dp] using hrelative
  have ht := cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
    U A b x t
  have hzero : (0 : ℝ) • physicalSuTangentToAmbient
      (physicalCochainToSuMatrixTangent A) = 0 := zero_smul ℝ _
  have h0 := cmp98UbarAmbientDeviationMatrix_line_eq_deviationCurve
    U A b x 0
  rw [hzero] at h0
  rw [ht, h0]
  simpa [cmp98UbarDeviationCurve, Ft, F0, Dp] using htransport

end

end YangMills.RG
