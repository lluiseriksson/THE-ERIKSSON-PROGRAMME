import Mathlib
import YangMills.RG.BalabanCMP116WilsonHessianDifferential
import YangMills.RG.SUNAdjointModelInstance

/-!
# Flat coordinate dictionary for the literal Wilson Hessian

This is the first WIL-H3 module.  It identifies the first-order plaquette
tangent produced by the concrete exponential chart with the repository's
flat covariant curl `D1`, after the already formalized isometric coordinate
transport between `su(N)` matrices and `SUNLieCoord`.

No second-variation formula is asserted here: the remaining WIL-H3 step is to
differentiate `1 - Re tr` twice and identify its bilinear form with the inner
product of these curls.
-/

namespace YangMills.RG

open Matrix
open scoped BigOperators

noncomputable section

variable {d N Nc : ℕ} [NeZero d] [NeZero N] [NeZero Nc]

/-- Convert the repository's orthonormal Lie coordinates on every positive
bond into the genuine `su(N)` matrices used by the exponential chart. -/
def physicalCochainToSuMatrixTangent
    (A : PhysicalGaugeOneCochain d N Nc) :
    PhysicalSuMatrixTangent d N Nc :=
  fun b => (suLieCoordIso Nc).symm (A b)

@[simp]
theorem physicalCochainToSuMatrixTangent_apply
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N) :
    physicalCochainToSuMatrixTangent A b =
      (suLieCoordIso Nc).symm (A b) := rfl

/-- The matrix tangent attached to an oriented edge at the trivial background:
positive edges carry `A_b`, negative edges carry `-A_b`. -/
def flatOrientedSuMatrixTangent
    (A : PhysicalGaugeOneCochain d N Nc) (e : ConcreteEdge d N) :
    Matrix (Fin Nc) (Fin Nc) ℂ :=
  if e.sign then
    ((suLieCoordIso Nc).symm (A (physicalBondOfEdge e))).toMatrix
  else
    -((suLieCoordIso Nc).symm (A (physicalBondOfEdge e))).toMatrix

@[simp]
theorem flatOrientedSuMatrixTangent_pos
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (i : Fin d) :
    flatOrientedSuMatrixTangent A (ConcreteEdge.mk x i true) =
      ((suLieCoordIso Nc).symm (A (x, i))).toMatrix := by
  simp [flatOrientedSuMatrixTangent]

@[simp]
theorem flatOrientedSuMatrixTangent_neg
    (A : PhysicalGaugeOneCochain d N Nc)
    (x : FinBox d N) (i : Fin d) :
    flatOrientedSuMatrixTangent A (ConcreteEdge.mk x i false) =
      -((suLieCoordIso Nc).symm (A (x, i))).toMatrix := by
  simp [flatOrientedSuMatrixTangent]

/-- Matrix-valued oriented curl around one concrete plaquette. -/
def flatPlaquetteSuMatrixCurl
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  ∑ k : Fin 4, flatOrientedSuMatrixTangent A (p.edges k)

/-- The coordinate isometry commutes with the flat four-edge curl. -/
theorem flatPlaquetteSuMatrixCurl_eq_covariantD1
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    flatPlaquetteSuMatrixCurl A p =
      ((suLieCoordIso Nc).symm
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) A p)).toMatrix := by
  cases p with
  | mk site dir1 dir2 hlt =>
      rw [covariantD1CLM_trivial_apply]
      simp only [flatPlaquetteSuMatrixCurl, Fin.sum_univ_four,
        ConcretePlaquette.edges, flatOrientedSuMatrixTangent_pos,
        flatOrientedSuMatrixTangent_neg]
      rw [map_sub, map_sub, map_add]
      rfl

/-- Package the flat plaquette curl as a genuine `su(N)` element. -/
def flatPlaquetteSuLieCurl
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) : SuLie Nc :=
  ⟨flatPlaquetteSuMatrixCurl A p, by
    rw [flatPlaquetteSuMatrixCurl_eq_covariantD1]
    exact ((suLieCoordIso Nc).symm
      (covariantD1CLM (matrixSUNAdjointModel Nc)
        (trivialPhysicalGaugeBackground d N Nc) A p)).property⟩

theorem flatPlaquetteSuLieCurl_eq_covariantD1
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    flatPlaquetteSuLieCurl A p =
      (suLieCoordIso Nc).symm
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) A p) := by
  apply Subtype.ext
  exact flatPlaquetteSuMatrixCurl_eq_covariantD1 A p

/-- The trace inner product of the literal matrix curls is exactly the
coordinate inner product of the repository's flat `D1` curls. -/
theorem matrixTraceInner_flatPlaquetteSuMatrixCurl_eq_covariantD1
    (A B : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    matrixTraceInner (flatPlaquetteSuMatrixCurl A p)
        (flatPlaquetteSuMatrixCurl B p) =
      inner ℝ
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) A p)
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) B p) := by
  change inner ℝ (flatPlaquetteSuLieCurl A p)
    (flatPlaquetteSuLieCurl B p) = _
  rw [flatPlaquetteSuLieCurl_eq_covariantD1,
    flatPlaquetteSuLieCurl_eq_covariantD1]
  exact (suLieCoordIso Nc).symm.inner_map_map _ _

/-- Summing the literal matrix-curl trace form over plaquettes is exactly the
global Hilbert inner product of the flat `D1` images. -/
theorem sum_matrixTraceInner_flatPlaquetteSuMatrixCurl_eq_inner_covariantD1
    (A B : PhysicalGaugeOneCochain d N Nc) :
    (∑ p : ConcretePlaquette d N,
      matrixTraceInner (flatPlaquetteSuMatrixCurl A p)
        (flatPlaquetteSuMatrixCurl B p)) =
      inner ℝ
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) A)
        (covariantD1CLM (matrixSUNAdjointModel Nc)
          (trivialPhysicalGaugeBackground d N Nc) B) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro p hp
  exact matrixTraceInner_flatPlaquetteSuMatrixCurl_eq_covariantD1 A B p

/-- The same dictionary written in Lie coordinates. -/
theorem suLieCoordIso_flatPlaquetteSuMatrixCurl
    (A : PhysicalGaugeOneCochain d N Nc)
    (p : ConcretePlaquette d N) :
    suLieCoordIso Nc
        ⟨flatPlaquetteSuMatrixCurl A p, by
          rw [flatPlaquetteSuMatrixCurl_eq_covariantD1]
          exact ((suLieCoordIso Nc).symm
            (covariantD1CLM (matrixSUNAdjointModel Nc)
              (trivialPhysicalGaugeBackground d N Nc) A p)).property⟩ =
      covariantD1CLM (matrixSUNAdjointModel Nc)
        (trivialPhysicalGaugeBackground d N Nc) A p := by
  change suLieCoordIso Nc (flatPlaquetteSuLieCurl A p) = _
  rw [flatPlaquetteSuLieCurl_eq_covariantD1]
  exact (suLieCoordIso Nc).apply_symm_apply _

end

end YangMills.RG
