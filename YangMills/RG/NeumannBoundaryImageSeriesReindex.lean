import YangMills.RG.NeumannBoundaryImagePermutation
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# PRE-VALIDATION: source-order image-series reindexing
Promoted source present; its .olean is not materialized and this production
module is not compiler-verified. Draft HOT evidence does not constitute a cold seal.
The index permutation factors into independent integer and Boolean bijections.
The finite sum is reindexed first, then the outer tsum: no exchange of sums.
This algebra also holds for totalized tsums and DOES NOT prove convergence.
The physical consumer retains its existing absolute-summability certificate.
-/

namespace YangMills.RG
noncomputable section

def neumannBoundaryIntegerIndexEquiv {d : ℕ} (mu : Fin d) (c : ℤ) :
    (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun k i := if i = mu then c - k i else k i
  invFun k i := if i = mu then c - k i else k i
  left_inv := by intro k; funext i; by_cases hi : i = mu <;> simp [hi]
  right_inv := by intro k; funext i; by_cases hi : i = mu <;> simp [hi]

def neumannBoundaryBranchIndexEquiv {d : ℕ} (mu : Fin d) :
    (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun b i := if i = mu then !(b i) else b i
  invFun b i := if i = mu then !(b i) else b i
  left_inv := by intro b; funext i; by_cases hi : i = mu <;> simp [hi]
  right_inv := by intro b; funext i; by_cases hi : i = mu <;> simp [hi]

theorem neumannBoundaryImageIndexEquiv_factor
    {d : ℕ} (mu : Fin d) (c : ℤ)
    (k : Fin d → ℤ) (b : Fin d → Bool) :
    neumannBoundaryImageIndexEquiv mu c (k,b) =
      (neumannBoundaryIntegerIndexEquiv mu c k,
       neumannBoundaryBranchIndexEquiv mu b) := rfl

theorem neumannBoundaryImage_tsum_sum_reindex
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (mu : Fin d) (c : ℤ)
    (f : ((Fin d → ℤ) × (Fin d → Bool)) → E) :
    (∑' k : Fin d → ℤ, ∑ b : Fin d → Bool,
      f (neumannBoundaryImageIndexEquiv mu c (k,b))) =
    ∑' k : Fin d → ℤ, ∑ b : Fin d → Bool, f (k,b) := by
  have hfinite : ∀ k : Fin d → ℤ,
      (∑ b : Fin d → Bool, f (neumannBoundaryImageIndexEquiv mu c (k,b))) =
      ∑ b : Fin d → Bool, f (neumannBoundaryIntegerIndexEquiv mu c k,b) := by
    intro k
    simp_rw [neumannBoundaryImageIndexEquiv_factor]
    exact (neumannBoundaryBranchIndexEquiv mu).sum_comp
      (fun b => f (neumannBoundaryIntegerIndexEquiv mu c k,b))
  simp_rw [hfinite]
  exact (neumannBoundaryIntegerIndexEquiv mu c).tsum_eq
    (fun k => ∑ b : Fin d → Bool, f (k,b))

theorem neumannBoundaryImage_reflected_source_sum
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (mu : Fin d) (c : ℤ) (m n : Fin d → ℤ)
    (F : (Fin d → ℤ) → E) :
    (∑' k : Fin d → ℤ, ∑ b : Fin d → Bool,
      F (fun i => if i = mu then
        2*c*m mu-1-cmp89NeumannReflectionImage m n k b i
        else cmp89NeumannReflectionImage m n k b i)) =
    ∑' k : Fin d → ℤ, ∑ b : Fin d → Bool,
      F (cmp89NeumannReflectionImage m n k b) := by
  have himage : ∀ k b,
      (fun i => if i = mu then
        2*c*m mu-1-cmp89NeumannReflectionImage m n k b i
        else cmp89NeumannReflectionImage m n k b i) =
      cmp89NeumannReflectionImage m n
        (neumannBoundaryImageIndexEquiv mu c (k,b)).1
        (neumannBoundaryImageIndexEquiv mu c (k,b)).2 := by
    intro k b
    exact neumannBoundaryImageIndexEquiv_image mu c m n (k,b)
  simp_rw [himage]
  exact neumannBoundaryImage_tsum_sum_reindex mu c
    (fun p => F (cmp89NeumannReflectionImage m n p.1 p.2))

end
end YangMills.RG
