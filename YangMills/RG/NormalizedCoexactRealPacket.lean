import YangMills.RG.NormalizedCoexactRealPairing
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! The actual two-quadrature real packet, its Kronecker Gram and actual
range span. No orthonormality or spanning certificate is supplied. -/
namespace YangMills.RG
open scoped BigOperators RealInnerProductSpace

def coexactQuadraturePhase (q : Bool) : ℂ := if q then Complex.I else 1

theorem coexactQuadraturePhase_gram (q r : Bool) :
    inner ℝ (coexactQuadraturePhase q) (coexactQuadraturePhase r) =
      if q = r then 1 else 0 := by
  cases q <;> cases r <;> norm_num [coexactQuadraturePhase, Complex.inner]

theorem counting_single_real_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (k l : I) (z w : ℂ) :
    (∑ s, inner ℝ (Pi.single k z s) (Pi.single l w s)) =
      if k = l then inner ℝ z w else 0 := by
  classical
  rw [Finset.sum_eq_single k]
  · by_cases h : k = l
    · subst l
      simp
    · simp [Pi.single_apply, h, Ne.symm h]
  · intro b _ hb
    simp [Pi.single_apply, hb, Ne.symm hb]
  · simp

variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

noncomputable def normalizedCoexactRealPacket (hNc : 2 ≤ Nc) (R : ℕ)
    (p : CoexactPositiveIndex d R × Bool) : PhysicalGaugeOneCochain (d + 2) n Nc := by
  classical
  exact normalizedCoexactSynthesis (n := n) hNc R
    (Pi.single p.1 (coexactQuadraturePhase p.2))

theorem normalizedCoexactRealPacket_gram (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n)
    (p q : CoexactPositiveIndex d R × Bool) :
    inner ℝ (normalizedCoexactRealPacket (n := n) hNc R p)
      (normalizedCoexactRealPacket (n := n) hNc R q) = if p = q then 1 else 0 := by
  classical
  unfold normalizedCoexactRealPacket
  rw [normalizedCoexactSynthesis_real_pairing hNc R hR,
    counting_single_real_pairing, coexactQuadraturePhase_gram]
  by_cases hk : p.1 = q.1
  · by_cases hq : p.2 = q.2
    · have h : p = q := Prod.ext hk hq
      simp [hk, hq, h]
    · have h : p ≠ q := fun h => hq (congrArg Prod.snd h)
      simp [hk, hq, h]
  · have h : p ≠ q := fun h => hk (congrArg Prod.fst h)
    simp [hk, h]

theorem normalizedCoexactRealPacket_orthonormal (hNc : 2 ≤ Nc)
    (R : ℕ) (hR : 2 * R < n) :
    Orthonormal ℝ (normalizedCoexactRealPacket (n := n) hNc R) := by
  classical
  exact orthonormal_iff_ite.mpr (normalizedCoexactRealPacket_gram hNc R hR)

theorem complex_real_quadrature_decomposition (z : ℂ) :
    z.re • (1 : ℂ) + z.im • Complex.I = z := by
  apply Complex.ext <;> simp [Complex.real_smul]

theorem coexactCoefficient_real_expansion (R : ℕ)
    (c : CoexactPositiveIndex d R → ℂ) :
    c = ∑ k, ((c k).re • Pi.single k (1 : ℂ) +
      (c k).im • Pi.single k Complex.I) := by
  classical
  funext l
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single l]
  · simpa using (complex_real_quadrature_decomposition (c l)).symm
  · intro b _ hb
    simp [Pi.single_apply, hb, Ne.symm hb]
  · simp

theorem normalizedCoexactSynthesis_real_expansion (hNc : 2 ≤ Nc) (R : ℕ)
    (c : CoexactPositiveIndex d R → ℂ) :
    normalizedCoexactSynthesis (n := n) hNc R c =
      ∑ k, ((c k).re • normalizedCoexactRealPacket (n := n) hNc R (k, false) +
        (c k).im • normalizedCoexactRealPacket (n := n) hNc R (k, true)) := by
  classical
  have h := congrArg (normalizedCoexactRealLinear (n := n) hNc R)
    (coexactCoefficient_real_expansion R c)
  change normalizedCoexactSynthesis (n := n) hNc R c = _ at h
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_add, map_smul, map_smul]
  rfl

theorem normalizedCoexactRealPacket_span (hNc : 2 ≤ Nc) (R : ℕ) :
    LinearMap.range (normalizedCoexactRealLinear (n := n) (d := d) hNc R) =
      Submodule.span ℝ (Set.range (normalizedCoexactRealPacket (n := n) hNc R)) := by
  classical
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    change normalizedCoexactSynthesis (n := n) hNc R c ∈ _
    rw [normalizedCoexactSynthesis_real_expansion]
    apply Submodule.sum_mem
    intro k _
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(k, false), rfl⟩
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(k, true), rfl⟩
  · apply Submodule.span_le.mpr
    rintro y ⟨p, rfl⟩
    exact ⟨Pi.single p.1 (coexactQuadraturePhase p.2), rfl⟩
end YangMills.RG
