import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Positive trace/rank comparison on an actual finite subspace. The ambient
operator need not preserve the subspace. No spectral lower bound or positive
operator after subtraction of a kernel projection is assumed. -/
namespace YangMills.RG
open Module
open scoped RealInnerProductSpace
set_option maxHeartbeats 1200000

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem submodule_orthonormal_coe {ι : Type*} [Fintype ι]
    (S : Submodule ℝ E) (v : ι → S) (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (fun i => (v i : E)) := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  exact hv i j

theorem positive_trace_lower_on_subspace (T : E →ₗ[ℝ] E)
    (hpos : ∀ x : E, 0 ≤ inner ℝ x (T x))
    (H : Submodule ℝ E) (c : ℝ)
    (hbound : ∀ x : E, x ∈ H → c * ‖x‖ ^ 2 ≤ inner ℝ x (T x)) :
    c * (finrank ℝ H : ℝ) ≤ LinearMap.trace ℝ E T := by
  classical
  let bH := stdOrthonormalBasis ℝ H
  let v : Fin (finrank ℝ H) → E := fun i => (bH i : E)
  have hv : Orthonormal ℝ v := submodule_orthonormal_coe H bH bH.orthonormal
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hset : Orthonormal ℝ ((↑) : Set.range v → E) := by
    rwa [orthonormal_subtype_range hinj]
  obtain ⟨u, b, hsubset, hb⟩ := hset.exists_orthonormalBasis_extension
  let s : Finset E := Finset.univ.image v
  have hs : s ⊆ u := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact hsubset ⟨i, rfl⟩
  have hcard : s.card = finrank ℝ H := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hdiag : ∀ x ∈ s, c ≤ inner ℝ x (T x) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    have hn : ‖v i‖ = 1 := bH.norm_eq_one i
    have hm : v i ∈ H := (bH i).property
    simpa only [hn, one_pow, mul_one] using hbound (v i) hm
  calc
    c * (finrank ℝ H : ℝ) = ∑ x ∈ s, c := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      ring
    _ ≤ ∑ x ∈ s, inner ℝ x (T x) := Finset.sum_le_sum hdiag
    _ ≤ ∑ x ∈ u, inner ℝ x (T x) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun x _ _ => hpos x)
    _ = LinearMap.trace ℝ E T := by
      rw [T.trace_eq_sum_inner b]
      simp only [hb]
      exact (Finset.sum_coe_sort u (fun x : E => inner ℝ x (T x))).symm

theorem positive_trace_rank_bound (T : E →ₗ[ℝ] E)
    (hpos : ∀ x : E, 0 ≤ inner ℝ x (T x))
    (L : E →ₗ[ℝ] F) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x : E, L x = 0 → c * ‖x‖ ^ 2 ≤ inner ℝ x (T x)) :
    c * ((finrank ℝ E : ℝ) - (finrank ℝ F : ℝ)) ≤ LinearMap.trace ℝ E T := by
  have hrn := L.finrank_range_add_finrank_ker
  have hrle : finrank ℝ L.range ≤ finrank ℝ F := L.range.finrank_le
  have hrn' : (finrank ℝ L.range : ℝ) + (finrank ℝ L.ker : ℝ) =
      (finrank ℝ E : ℝ) := by exact_mod_cast hrn
  have hrle' : (finrank ℝ L.range : ℝ) ≤ (finrank ℝ F : ℝ) := by
    exact_mod_cast hrle
  have hdim : (finrank ℝ E : ℝ) - (finrank ℝ F : ℝ) ≤
      (finrank ℝ L.ker : ℝ) := by linarith
  calc
    _ ≤ c * (finrank ℝ L.ker : ℝ) := mul_le_mul_of_nonneg_left hdim hc
    _ ≤ _ := positive_trace_lower_on_subspace T hpos L.ker c (by
      intro x hx
      exact hbound x hx)

noncomputable def finiteSubspaceCompression (S : Submodule ℝ E)
    (T : E →ₗ[ℝ] E) : S →ₗ[ℝ] S :=
  S.subtype.adjoint.comp (T.comp S.subtype)

theorem finiteSubspaceCompression_inner (S : Submodule ℝ E)
    (T : E →ₗ[ℝ] E) (x y : S) :
    inner ℝ x (finiteSubspaceCompression S T y) = inner ℝ (x : E) (T (y : E)) := by
  exact LinearMap.adjoint_inner_right S.subtype x (T (y : E))

theorem finiteSubspaceCompression_nonneg (S : Submodule ℝ E)
    (T : E →ₗ[ℝ] E) (hpos : ∀ x : E, x ∈ S → 0 ≤ inner ℝ x (T x)) :
    ∀ x : S, 0 ≤ inner ℝ x (finiteSubspaceCompression S T x) := by
  intro x
  rw [finiteSubspaceCompression_inner]
  exact hpos x x.property

theorem positive_compressed_trace_rank_bound (S : Submodule ℝ E)
    (T : E →ₗ[ℝ] E) (hpos : ∀ x : E, x ∈ S → 0 ≤ inner ℝ x (T x))
    (L : E →ₗ[ℝ] F) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x : E, x ∈ S → L x = 0 → c * ‖x‖ ^ 2 ≤ inner ℝ x (T x)) :
    c * ((finrank ℝ S : ℝ) - (finrank ℝ F : ℝ)) ≤
      LinearMap.trace ℝ S (finiteSubspaceCompression S T) := by
  apply positive_trace_rank_bound (finiteSubspaceCompression S T)
    (finiteSubspaceCompression_nonneg S T hpos) (L.comp S.subtype) c hc
  intro x hx
  rw [finiteSubspaceCompression_inner]
  exact hbound x x.property hx

end YangMills.RG
