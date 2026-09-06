import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! PRE-VALIDATION: extracted Mathlib-only repro, not a physical seal. -/
namespace YangMills.RG
abbrev CMP89NeumannReflectionBranch (d : ℕ) := Fin d → Bool

def cmp89NeumannReflectionOrbit (m n k : ℤ) (reflected : Bool) : ℤ :=
  if reflected then 2 * k * m - n - 1 else 2 * k * m + n

def cmp89NeumannReflectionImage {d : ℕ}
    (m n k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d) :
    Fin d → ℤ :=
  fun mu => cmp89NeumannReflectionOrbit (m mu) (n mu) (k mu) (branch mu)
end YangMills.RG

namespace YangMills.RG

theorem neumannIntegerHalfCellOwner (B n : ℤ) (hB : 0 < B) :
    (-n - 1) / B = -(n / B) - 1 := by
  rw [Int.ediv_eq_iff_of_pos hB]
  have hr0 := Int.emod_nonneg n (ne_of_gt hB)
  have hr1 := Int.emod_lt_of_pos n hB
  have hsplit := Int.ediv_mul_add_emod n B
  constructor <;> nlinarith

theorem neumannIntegerTranslatedOwner
    (B m n k : ℤ) (hB : 0 < B) :
    (2 * k * (B * m) + n) / B = 2 * k * m + n / B := by
  have halgebra : 2 * k * (B * m) + n = n + B * (2 * k * m) := by ring
  rw [halgebra, Int.add_mul_ediv_left _ _ (ne_of_gt hB)]
  ring

theorem neumannIntegerReflectedOwner
    (B m n k : ℤ) (hB : 0 < B) :
    (2 * k * (B * m) - n - 1) / B = 2 * k * m - n / B - 1 := by
  have halgebra : 2 * k * (B * m) - n - 1 =
      (-n - 1) + B * (2 * k * m) := by ring
  rw [halgebra, Int.add_mul_ediv_left _ _ (ne_of_gt hB),
    neumannIntegerHalfCellOwner B n hB]
  ring

/-- Integer owner in block-index units; no clipping or periodic wrap. -/
def neumannIntegerBlockOwner {d : ℕ} (B : ℤ) (n : Fin d → ℤ) : Fin d → ℤ :=
  fun mu => n mu / B

/-- Fine images with sides B*m project to the printed coarse image with
sides m. The image is not asserted to remain in the original rectangle. -/
theorem neumannIntegerBlockOwner_image {d : ℕ} (B : ℤ) (hB : 0 < B)
    (m n k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d) :
    neumannIntegerBlockOwner B
        (cmp89NeumannReflectionImage (fun mu => B * m mu) n k branch) =
      cmp89NeumannReflectionImage m (neumannIntegerBlockOwner B n) k branch := by
  funext mu
  change cmp89NeumannReflectionOrbit (B * m mu) (n mu) (k mu) (branch mu) / B =
    cmp89NeumannReflectionOrbit (m mu) (n mu / B) (k mu) (branch mu)
  cases branch mu with
  | false => exact neumannIntegerTranslatedOwner B (m mu) (n mu) (k mu) hB
  | true => exact neumannIntegerReflectedOwner B (m mu) (n mu) (k mu) hB

/-- Injectivity for a fixed translation/parity, not injectivity of the full
image-index family and not disjointness of different images. -/
theorem neumannIntegerReflectionImage_injective {d : ℕ}
    (m k : Fin d → ℤ) (branch : CMP89NeumannReflectionBranch d) :
    Function.Injective (fun n => cmp89NeumannReflectionImage m n k branch) := by
  intro x y h
  funext mu
  have he := congrFun h mu
  change cmp89NeumannReflectionOrbit (m mu) (x mu) (k mu) (branch mu) =
    cmp89NeumannReflectionOrbit (m mu) (y mu) (k mu) (branch mu) at he
  cases branch mu with
  | false =>
      change 2 * k mu * m mu + x mu = 2 * k mu * m mu + y mu at he
      linarith
  | true =>
      change 2 * k mu * m mu - x mu - 1 =
        2 * k mu * m mu - y mu - 1 at he
      linarith

/-- A common image preserves the exact equality of block owners. -/
theorem neumannIntegerBlockOwner_image_eq_iff {d : ℕ}
    (B : ℤ) (hB : 0 < B) (m x y k : Fin d → ℤ)
    (branch : CMP89NeumannReflectionBranch d) :
    neumannIntegerBlockOwner B
        (cmp89NeumannReflectionImage (fun mu => B * m mu) x k branch) =
      neumannIntegerBlockOwner B
        (cmp89NeumannReflectionImage (fun mu => B * m mu) y k branch) ↔
      neumannIntegerBlockOwner B x = neumannIntegerBlockOwner B y := by
  rw [neumannIntegerBlockOwner_image B hB, neumannIntegerBlockOwner_image B hB]
  exact (neumannIntegerReflectionImage_injective m k branch).eq_iff

/-- Owner-indicator algebra only. The coefficient c is unchanged: no fibre
cardinality, weighted-adjoint factor or hidden scale normalization is inserted.
The physical counting coefficient may later be specialized to (M^-d)^(2*depth),
but its physical operator dictionary is a separate obligation. -/
theorem neumannIntegerCountingIndicator_image {d : ℕ}
    {V : Type*} [Zero V] [SMul ℝ V]
    (B : ℤ) (hB : 0 < B) (m source target k : Fin d → ℤ)
    (branch : CMP89NeumannReflectionBranch d) (c : ℝ) (v : V) :
    (if neumannIntegerBlockOwner B
          (cmp89NeumannReflectionImage (fun mu => B * m mu) target k branch) =
        neumannIntegerBlockOwner B
          (cmp89NeumannReflectionImage (fun mu => B * m mu) source k branch)
      then c • v else 0) =
      (if neumannIntegerBlockOwner B target = neumannIntegerBlockOwner B source
        then c • v else 0) := by
  exact if_congr
    (neumannIntegerBlockOwner_image_eq_iff B hB m target source k branch) rfl rfl

end YangMills.RG

#print axioms YangMills.RG.neumannIntegerHalfCellOwner
#print axioms YangMills.RG.neumannIntegerTranslatedOwner
#print axioms YangMills.RG.neumannIntegerReflectedOwner
#print axioms YangMills.RG.neumannIntegerBlockOwner_image
#print axioms YangMills.RG.neumannIntegerReflectionImage_injective
#print axioms YangMills.RG.neumannIntegerBlockOwner_image_eq_iff
#print axioms YangMills.RG.neumannIntegerCountingIndicator_image
