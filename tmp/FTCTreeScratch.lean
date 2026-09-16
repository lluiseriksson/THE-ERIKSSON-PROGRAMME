import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set MeasureTheory intervalIntegral

namespace YangMills.RG

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

inductive FTCTree (E : Type u) : ℕ → Type u
  | leaf (value : E) : FTCTree E 0
  | node {n : ℕ} (curve derivative : ℝ → E)
      (base : FTCTree E n) (fiber : ℝ → FTCTree E n) : FTCTree E (n + 1)

noncomputable def FTCTree.sum : {n : ℕ} → FTCTree E n → E
  | 0, .leaf value => value
  | _ + 1, .node _ _ base fiber =>
      base.sum + ∫ t in (0 : ℝ)..1, (fiber t).sum

def FTCTree.endpoint : {n : ℕ} → FTCTree E n → E
  | 0, .leaf value => value
  | _ + 1, .node curve _ _ _ => curve 1

def FTCTree.Valid : {n : ℕ} → FTCTree E n → Prop
  | 0, .leaf _ => True
  | _ + 1, .node curve derivative base fiber =>
      base.Valid ∧
      base.sum = curve 0 ∧
      (∀ t ∈ Set.uIcc (0 : ℝ) 1, (fiber t).Valid ∧ (fiber t).sum = derivative t) ∧
      (∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt curve (derivative t) t) ∧
      IntervalIntegrable derivative volume 0 1

theorem FTCTree.sum_eq_endpoint {n : ℕ} (T : FTCTree E n) (hT : T.Valid) :
    T.sum = T.endpoint := by
  induction T with
  | leaf value => rfl
  | @node n curve derivative base fiber ihBase ihFiber =>
      rcases hT with ⟨hbaseValid, hbase, hfiber, hderiv, hint⟩
      have hIntegral :
          (∫ t in (0 : ℝ)..1, (fiber t).sum) =
            ∫ t in (0 : ℝ)..1, derivative t := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (hfiber t ht).2
      have hFTC :
          (∫ t in (0 : ℝ)..1, derivative t) = curve 1 - curve 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      simp only [FTCTree.sum, FTCTree.endpoint]
      rw [hbase, hIntegral, hFTC]
      abel

theorem ftc_one_step (curve derivative : ℝ → E)
    (hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt curve (derivative t) t)
    (hint : IntervalIntegrable derivative volume 0 1) :
    curve 0 + ∫ t in (0 : ℝ)..1, derivative t = curve 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  abel

theorem ftc_tree_nontrivial_witness :
    ∃ T : FTCTree ℝ 1, T.Valid ∧ T.sum = 1 := by
  let base : FTCTree ℝ 0 := .leaf 0
  let fiber : ℝ → FTCTree ℝ 0 := fun _ => .leaf 1
  let T : FTCTree ℝ 1 := .node id (fun _ => 1) base fiber
  have hvalid : T.Valid := by
    dsimp [T, base, fiber, FTCTree.Valid, FTCTree.sum]
    refine ⟨trivial, ?_, ?_, ?_, ?_⟩
    · norm_num [FTCTree.sum]
    · intro t ht
      exact ⟨trivial, by simp [FTCTree.sum]⟩
    · intro t ht
      exact hasDerivAt_id t
    · exact continuous_const.intervalIntegrable 0 1
  exact ⟨T, hvalid, by simpa [T, FTCTree.endpoint] using T.sum_eq_endpoint hvalid⟩

end YangMills.RG
