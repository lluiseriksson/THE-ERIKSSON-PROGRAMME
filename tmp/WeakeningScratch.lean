import YangMills.RG.BalabanCMP116FTCInterpolation
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped BigOperators

namespace YangMills.RG

universe u v w
variable {Δ : Type u} {ω : Type v} {E : Type w}
variable [DecidableEq Δ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def mono (active : Finset Δ) (s : Δ → ℝ) : ℝ := ∏ d ∈ active, s d

theorem mono_update_of_mem (active : Finset Δ) (s : Δ → ℝ) (d : Δ)
    (hd : d ∈ active) (t : ℝ) :
    mono active (Function.update s d t) = t * mono (active.erase d) s := by
  calc
    mono active (Function.update s d t) =
        Function.update s d t d *
          ∏ x ∈ active \ {d}, Function.update s d t x := by
      exact Finset.prod_eq_mul_prod_diff_singleton_of_mem hd _
    _ = t * ∏ x ∈ active \ {d}, s x := by
      rw [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro x hx
      rw [Function.update_of_ne]
      simpa using (Finset.mem_sdiff.mp hx).2
    _ = t * mono (active.erase d) s := by
      simp [mono, Finset.erase_eq]

theorem mono_update_of_not_mem (active : Finset Δ) (s : Δ → ℝ) (d : Δ)
    (hd : d ∉ active) (t : ℝ) :
    mono active (Function.update s d t) = mono active s := by
  simp only [mono]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hd)]

theorem hasDerivAt_mono_update (active : Finset Δ) (s : Δ → ℝ) (d : Δ) (x : ℝ) :
    HasDerivAt (fun t => mono active (Function.update s d t))
      (if d ∈ active then mono (active.erase d) s else 0) x := by
  by_cases hd : d ∈ active
  · simp only [hd, if_true]
    have hfun : (fun t => mono active (Function.update s d t)) =
        fun t => t * mono (active.erase d) s := by
      funext t
      exact mono_update_of_mem active s d hd t
    rw [hfun]
    simpa using (hasDerivAt_id x).mul_const (mono (active.erase d) s)
  · simp only [hd, if_false]
    have hfun : (fun t => mono active (Function.update s d t)) =
        fun _ => mono active s := by
      funext t
      exact mono_update_of_not_mem active s d hd t
    rw [hfun]
    exact hasDerivAt_const x _

def weakenedSum (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (s : Δ → ℝ) : E :=
  ∑ w ∈ walks, mono (active w) s • term w

def weakenedDerivative (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (s : Δ → ℝ) (d : Δ) : E :=
  ∑ w ∈ walks,
    (if d ∈ active w then mono ((active w).erase d) s else 0) • term w

theorem weakenedSum_one (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) :
    weakenedSum walks active term (fun _ => 1) = ∑ w ∈ walks, term w := by
  simp [weakenedSum, mono]

def zeroOutside (K : Finset Δ) : Δ → ℝ := fun d => if d ∈ K then 1 else 0

theorem mono_zeroOutside (active K : Finset Δ) :
    mono active (zeroOutside K) = if active ⊆ K then 1 else 0 := by
  by_cases h : active ⊆ K
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro d hd
    simp [zeroOutside, h hd]
  · rw [if_neg h]
    obtain ⟨d, hdA, hdK⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hdA
    simp [zeroOutside, hdK]

theorem weakenedSum_zeroOutside (walks : Finset ω) (active : ω → Finset Δ)
    (term : ω → E) (K : Finset Δ) :
    weakenedSum walks active term (zeroOutside K) =
      ∑ w ∈ walks.filter fun w => active w ⊆ K, term w := by
  classical
  rw [Finset.sum_filter]
  simp [weakenedSum, mono_zeroOutside]

theorem hasDerivAt_weakenedSum_update (walks : Finset ω)
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (d : Δ) (x : ℝ) :
    HasDerivAt (fun t => weakenedSum walks active term (Function.update s d t))
      (weakenedDerivative walks active term s d) x := by
  unfold weakenedSum weakenedDerivative
  exact HasDerivAt.fun_sum fun w hw =>
    (hasDerivAt_mono_update (active w) s d x).smul_const (term w)

theorem weakenedSum_ftcStep (walks : Finset ω)
    (active : ω → Finset Δ) (term : ω → E) (s : Δ → ℝ) (d : Δ) :
    weakenedSum walks active term (Function.update s d 0) +
        ∫ _t in (0 : ℝ)..1, weakenedDerivative walks active term s d =
      weakenedSum walks active term (Function.update s d 1) := by
  apply cmp116FTC_oneStep
    (fun t => weakenedSum walks active term (Function.update s d t))
    (fun _ => weakenedDerivative walks active term s d)
  · intro t ht
    exact hasDerivAt_weakenedSum_update walks active term s d t
  · exact continuous_const.intervalIntegrable 0 1

end YangMills.RG
