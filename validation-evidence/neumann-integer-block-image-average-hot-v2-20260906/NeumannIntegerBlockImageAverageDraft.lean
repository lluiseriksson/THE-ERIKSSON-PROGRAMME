import YangMills.RG.NeumannHalfCellBlockReflection
import YangMills.RG.NeumannIntegerImageCountingKernel

/-!
PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.

R2d.1: the printed integer image maps a complete fine block to its
coarse-image block with the SAME finite offset reflection Fin.rev.
The finite sum is reindexed by a constructed involution; no multiplicity
or fibre-cardinality factor is introduced. This is pointwise algebra on
integer fields, not an l2 extension of a periodic field.

The coefficient w is transported unchanged, not identified with a physical
Q. R2d.2 must separately consume the literal generated average action and
its coefficient (M^-d)^depth; counting mass keeps its squared coefficient.
No right-inverse law, B0 or window15 is proved here.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Integer coordinates of the complete block with coarse owner y.
No periodic wrap or clipping back to the original region is performed. -/
def neumannIntegerFineBlockPoint {d B : ℕ}
    (y : Fin d → ℤ) (r : FinBox d B) : Fin d → ℤ :=
  fun mu => (B : ℤ) * y mu + ((r mu).val : ℤ)

private theorem neumannRev_val_int {B : ℕ} (r : Fin B) :
    ((r.rev.val : ℕ) : ℤ) = (B : ℤ) - 1 - (r.val : ℤ) := by
  have hn : r.rev.val + r.val + 1 = B := by
    rw [Fin.val_rev]
    omega
  have hz : ((r.rev.val : ℕ) : ℤ) + (r.val : ℤ) + 1 = (B : ℤ) := by
    exact_mod_cast hn
  linarith

/-- Coarse image and internal reflection are derived from the SAME
translation/parity. Fine sides are B*m, while the image period is 2*B*m. -/
theorem neumannIntegerImage_fineBlockPoint {d B : ℕ}
    (m y k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d)
    (r : FinBox d B) :
    cmp89NeumannReflectionImage (fun mu => (B : ℤ) * m mu)
        (neumannIntegerFineBlockPoint y r) k branch =
      neumannIntegerFineBlockPoint (cmp89NeumannReflectionImage m y k branch)
        (neumannHalfCellReflection branch r) := by
  funext mu
  cases hb : branch mu
  · simp only [cmp89NeumannReflectionImage, cmp89NeumannReflectionOrbit,
      neumannIntegerFineBlockPoint, neumannHalfCellReflection, hb, Bool.false_eq_true, if_false]
    ring
  · simp only [cmp89NeumannReflectionImage, cmp89NeumannReflectionOrbit,
      neumannIntegerFineBlockPoint, neumannHalfCellReflection, hb, if_true]
    rw [neumannRev_val_int]
    ring

/-- Exact finite block sum transport. The permutation is constructed from
the already sealed half-cell involution, not supplied as a dictionary. -/
theorem sum_neumannIntegerImage_fineBlockPoint {d B : ℕ}
    {V : Type*} [AddCommMonoid V]
    (m y k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d)
    (f : (Fin d → ℤ) → V) :
    (∑ r : FinBox d B, f
      (cmp89NeumannReflectionImage (fun mu => (B : ℤ) * m mu)
        (neumannIntegerFineBlockPoint y r) k branch)) =
      ∑ r : FinBox d B, f (neumannIntegerFineBlockPoint
        (cmp89NeumannReflectionImage m y k branch) r) := by
  let e : FinBox d B ≃ FinBox d B :=
    { toFun := neumannHalfCellReflection branch
      invFun := neumannHalfCellReflection branch
      left_inv := neumannHalfCellReflection_involutive branch
      right_inv := neumannHalfCellReflection_involutive branch }
  apply Fintype.sum_equiv e
  intro r
  exact congrArg f (neumannIntegerImage_fineBlockPoint m y k branch r)

/-- An unchanged averaging weight can be placed outside that finite sum.
Specialization to the literal generated weight remains a separate gate. -/
theorem weightedSum_neumannIntegerImage_fineBlockPoint {d B : ℕ}
    {V : Type*} [AddCommMonoid V] [SMul ℝ V]
    (w : ℝ) (m y k : Fin d → ℤ)
    (branch : CMP89NeumannReflectionBranch d) (f : (Fin d → ℤ) → V) :
    w • (∑ r : FinBox d B, f
      (cmp89NeumannReflectionImage (fun mu => (B : ℤ) * m mu)
        (neumannIntegerFineBlockPoint y r) k branch)) =
      w • (∑ r : FinBox d B, f (neumannIntegerFineBlockPoint
        (cmp89NeumannReflectionImage m y k branch) r)) :=
  congrArg (fun z : V => w • z)
    (sum_neumannIntegerImage_fineBlockPoint m y k branch f)

end YangMills.RG

#print axioms YangMills.RG.neumannIntegerImage_fineBlockPoint
#print axioms YangMills.RG.sum_neumannIntegerImage_fineBlockPoint
#print axioms YangMills.RG.weightedSum_neumannIntegerImage_fineBlockPoint
