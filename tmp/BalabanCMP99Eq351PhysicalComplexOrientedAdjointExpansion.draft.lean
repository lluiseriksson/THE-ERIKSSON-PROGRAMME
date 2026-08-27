import tmp.BalabanCMP99Eq351PhysicalComplexPositiveAdjointExpansion.draft
import tmp.BalabanCMP99Eq351PhysicalComplexNegativeBondFactorization.draft

/-!
PRE-VALIDATION: scratch source. This file has no materialized `.olean` and
no compiler or axiom-oracle verdict.

# CMP99 (3.51): canonical oriented adjoint increment

The positive and negative source branches are unified only after both have
been constructed independently.  The theorem quantifies over a concrete
edge but supplies no free orientation dictionary, perturbed link, generator
or nonlinear remainder.
-/

namespace YangMills.RG

noncomputable section

open Matrix

variable {d N Nc : Nat} [NeZero d] [NeZero N] [NeZero Nc]

/-- The two non-baseline terms of the canonical oriented adjoint expansion.
This is a definition of the literal commutator plus the already named exact
exponential remainder, not a caller-supplied increment. -/
def cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (e : ConcreteEdge d N)
    (Z : SUNLieComplexCoord Nc) : Matrix (Fin Nc) (Fin Nc) ℂ :=
  let Y := cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta e
  let X := cmp99SUNLieComplexCoordMatrixLM Nc
    (cmp99SpecialLinearAdjointCoordLM
      (cmp99SUNToSpecialLinear Nc (U e)) Z)
  (Y * X - X * Y) + cmp99Eq351ExponentialAdjointRemainderCLM Y X

/-- Exact exponential-adjoint expansion on either canonical bond
orientation.  The negative case uses its separately proved compact transport
and is not obtained by renaming the positive source field. -/
theorem cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix_eq
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (e : ConcreteEdge d N)
    (Z : SUNLieComplexCoord Nc) :
    let Y := cmp99Eq351PhysicalComplexOrientedGeneratorMatrix U A eta e
    let X := cmp99SUNLieComplexCoordMatrixLM Nc
      (cmp99SpecialLinearAdjointCoordLM
        (cmp99SUNToSpecialLinear Nc (U e)) Z)
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM
          (cmp99Eq337PhysicalComplexPerturbedBackground U A eta e) Z) =
      X + (Y * X - X * Y) +
        cmp99Eq351ExponentialAdjointRemainderCLM Y X := by
  rcases e with ⟨x, mu, sign⟩
  cases sign
  · simpa only using
      cmp99Eq351PhysicalComplexPerturbedNegativeAdjointMatrix_eq
        U A eta x mu Z
  · simpa only [cmp99Eq351PhysicalComplexOrientedGeneratorMatrix_pos] using
      cmp99Eq351PhysicalComplexPerturbedPositiveAdjointMatrix_eq
        U A eta (x, mu) Z

/-- Subtracting the compact baseline adjoint action leaves exactly the named
oriented increment. -/
theorem cmp99Eq351PhysicalComplexOrientedAdjoint_sub_baseline_eq_increment
    (U : PhysicalGaugeBackground d N Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d N Nc)
    (eta : ℝ) (e : ConcreteEdge d N)
    (Z : SUNLieComplexCoord Nc) :
    cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM
          (cmp99Eq337PhysicalComplexPerturbedBackground U A eta e) Z) -
      cmp99SUNLieComplexCoordMatrixLM Nc
        (cmp99SpecialLinearAdjointCoordLM
          (cmp99SUNToSpecialLinear Nc (U e)) Z) =
      cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix
        U A eta e Z := by
  unfold cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix
  have h := cmp99Eq351PhysicalComplexOrientedAdjointIncrementMatrix_eq
    U A eta e Z
  dsimp only at h ⊢
  rw [h]
  module

end

end YangMills.RG
