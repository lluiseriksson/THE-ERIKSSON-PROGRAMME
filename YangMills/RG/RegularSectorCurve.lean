import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Actual implicit-function charts and curves for exact regular sectors.
These statements do not assume a sector curve as a structure field.
They do not yet prove a quadratic-energy coercivity obstruction. -/
namespace YangMills.RG
open Filter Module
open scoped Topology
noncomputable section

variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem regular_sector_chart
    (P : E → G) (A : E →L[ℝ] G)
    (hP : HasStrictFDerivAt P A 0) (hP0 : P 0 = 0)
    (hA : Function.Surjective A) :
    ∃ ψ : A.ker → E, ψ 0 = 0 ∧
      HasFDerivAt ψ A.ker.subtypeL 0 ∧
      ∀ᶠ u in 𝓝 (0 : A.ker), P (ψ u) = 0 := by
  have htop : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  let ψ := hP.implicitFunction P A htop (P 0)
  refine ⟨ψ, ?_, ?_, ?_⟩
  · exact hP.implicitFunction_apply_image htop
  · exact (hP.to_implicitFunction htop).hasFDerivAt
  · have ht : Tendsto (fun u : A.ker => (P 0, u)) (𝓝 0) (𝓝 (P 0, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    have hh := ht.eventually (hP.map_implicitFunction_eq htop)
    simpa [ψ, hP0] using hh

theorem regular_sector_curve
    (P : E → G) (A : E →L[ℝ] G)
    (hP : HasStrictFDerivAt P A 0) (hP0 : P 0 = 0)
    (hA : Function.Surjective A) (v : E) (hv : A v = 0) :
    ∃ γ : ℝ → E, γ 0 = 0 ∧ HasDerivAt γ v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), P (γ t) = 0 := by
  rcases regular_sector_chart P A hP hP0 hA with ⟨ψ, hψ0, hψ, hlevel⟩
  let u : A.ker := ⟨v, hv⟩
  have hray : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  refine ⟨fun t => ψ (t • u), ?_, ?_, ?_⟩
  · simpa using hψ0
  · have hc : HasFDerivAt ψ A.ker.subtypeL ((fun t : ℝ => t • u) 0) := by
      simpa using hψ
    simpa [Function.comp_def, u] using hc.comp_hasDerivAt 0 hray
  · have ht : Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 (0 : A.ker)) := by
      simpa using hray.continuousAt.tendsto
    exact ht.eventually hlevel

theorem C1_regular_sector_curve
    (P : E → G) (A : E →L[ℝ] G)
    (hP : ContDiffAt ℝ 1 P 0) (hd : HasFDerivAt P A 0)
    (hP0 : P 0 = 0) (hA : Function.Surjective A)
    (v : E) (hv : A v = 0) :
    ∃ γ : ℝ → E, γ 0 = 0 ∧ HasDerivAt γ v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), P (γ t) = 0 := by
  exact regular_sector_curve P A (hP.hasStrictFDerivAt' hd (by norm_num)) hP0 hA v hv

variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_unseen_regular_sector_curve
    (S : Submodule ℝ E) (P : E → G) (A : E →L[ℝ] G)
    (hP : ContDiffAt ℝ 1 P 0) (hdP : HasFDerivAt P A 0)
    (hP0 : P 0 = 0) (hA : Function.Surjective A)
    (C : E → F) (L : E →L[ℝ] F) (hC : HasFDerivAt C L 0)
    (hdim : finrank ℝ F + finrank ℝ G < finrank ℝ S) :
    ∃ v : E, v ∈ S ∧ v ≠ 0 ∧
      ∃ γ : ℝ → E, γ 0 = 0 ∧ HasDerivAt γ v 0 ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), P (γ t) = 0) ∧ HasDerivAt (C ∘ γ) 0 0 := by
  classical
  let f : S →ₗ[ℝ] F × G := (L.prod A).toLinearMap.comp S.subtype
  have hnotinj : ¬ Function.Injective f := by
    intro hi
    have hh := LinearMap.finrank_le_finrank_of_injective hi
    have hgt : finrank ℝ (F × G) < finrank ℝ S := by simpa using hdim
    exact (not_le_of_gt hgt) hh
  have hex : ∃ x : S, x ≠ 0 ∧ f x = 0 := by
    by_contra hn
    push_neg at hn
    apply hnotinj
    intro x y hxy
    have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hs : x - y = 0 := by
      by_contra hne
      exact hn (x - y) hne hz
    exact sub_eq_zero.mp hs
  rcases hex with ⟨x, hx, hfx⟩
  have hL : L (x : E) = 0 := by
    simpa [f] using congrArg Prod.fst hfx
  have hAx : A (x : E) = 0 := by
    simpa [f] using congrArg Prod.snd hfx
  rcases C1_regular_sector_curve P A hP hdP hP0 hA x hAx with ⟨γ, hγ0, hγ, hlevel⟩
  refine ⟨x, x.property, ?_, γ, hγ0, hγ, hlevel, ?_⟩
  · intro hz
    exact hx (Subtype.ext hz)
  · have hc : HasFDerivAt C L (γ 0) := by simpa [hγ0] using hC
    simpa [hL] using hc.comp_hasDerivAt 0 hγ

end
end YangMills.RG
