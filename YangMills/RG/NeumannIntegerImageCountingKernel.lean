import YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
PRE-VALIDATION: source present, .olean not materialized, not compiler-verified.

R2 integer image dictionary, using the existing CMP89 (2.42) image definition.
B is the positive fine-site block side (later M^depth), m is the anisotropic
coarse rectangle side, and B*m is the fine rectangle side. Integer division
is Euclidean, including negative images. No m=N or rectangular invariance
assumption is introduced. The seven proof bodies passed the exact-source HOT diagnostic at
8a0714a03 (ledger1133). This promoted path still requires its cold gate.

The last theorem preserves the literal owner-indicator kernel under a COMMON
image of source and target. It does not identify that integer kernel with a
generated finite/retained Q, supply a Neumann Laplacian, interchange an image
sum with an operator, or prove a Green right inverse or window15.
-/

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
  cases hb : branch mu <;>
    simp [cmp89NeumannReflectionOrbit, hb] at he <;> linarith

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


