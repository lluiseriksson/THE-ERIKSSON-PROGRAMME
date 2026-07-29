/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local quantitative composition

Mathlib's quantitative Faà di Bruno bound is stated for globally `C^n`
maps, or for derivatives within sets.  Source maps built from local analytic
charts naturally provide only `ContDiffAt` at the physical point.

This file bridges the two formulations.  It extracts an open neighborhood
on which the outer map is `ContDiffOn`, pulls it back under the globally
smooth inner map, applies the within-set estimate, and identifies all within
derivatives with the ordinary Fréchet derivatives at the point.
-/

namespace YangMills.RG

noncomputable section

variable {𝕜 D E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Local quantitative Faà di Bruno bound.**  Only the outer map's germ
at `inner x` is required to be `C^n`; the inner map is globally `C^n`.
The conclusion concerns the ordinary iterated derivative at `x`. -/
theorem norm_iteratedFDeriv_comp_le_at
    {outer : F → G} {inner : E → F}
    {n : ℕ} {x : E} {C D : ℝ}
    (houter : ContDiffAt 𝕜 n outer (inner x))
    (hinner : ContDiff 𝕜 n inner)
    (hC : ∀ i, i ≤ n →
      ‖iteratedFDeriv 𝕜 i outer (inner x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv 𝕜 i inner x‖ ≤ D ^ i) :
    ‖iteratedFDeriv 𝕜 n (outer ∘ inner) x‖ ≤
      (n.factorial : ℝ) * C * D ^ n := by
  rcases houter.contDiffOn
      (m := (n : WithTop ℕ∞)) le_rfl (by simp) with
    ⟨u, hu, houterU⟩
  rcases mem_nhds_iff.mp hu with
    ⟨t, htu, htOpen, hfx⟩
  have houterT : ContDiffOn 𝕜 n outer t :=
    houterU.mono htu
  let s : Set E := inner ⁻¹' t
  have hsOpen : IsOpen s :=
    htOpen.preimage hinner.continuous
  have hx : x ∈ s := hfx
  have hmaps : Set.MapsTo inner s t := by
    intro y hy
    exact hy
  have htUnique : UniqueDiffOn 𝕜 t :=
    htOpen.uniqueDiffOn
  have hsUnique : UniqueDiffOn 𝕜 s :=
    hsOpen.uniqueDiffOn
  have hCWithin : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin 𝕜 i outer t (inner x)‖ ≤ C := by
    intro i hi
    have hin :
        (i : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr hi)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv
      htUnique (houter.of_le hin) hfx]
    exact hC i hi
  have hDWithin : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin 𝕜 i inner s x‖ ≤ D ^ i := by
    intro i hi hinNat
    have hin :
        (i : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr
        (WithTop.coe_le_coe.mpr hinNat)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv
      hsUnique (hinner.contDiffAt.of_le hin) hx]
    exact hD i hi hinNat
  have hmain :=
    norm_iteratedFDerivWithin_comp_le
      houterT hinner.contDiffOn le_rfl
      htUnique hsUnique hmaps hx hCWithin hDWithin
  have hcompAt :
      ContDiffAt 𝕜 n (outer ∘ inner) x :=
    houter.comp x hinner.contDiffAt
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    hsUnique hcompAt hx] at hmain
  exact hmain

/-- Local second-jet Leibniz bound for a bilinear map.  The left factor
need only be `C²` at `x`; the right factor is globally `C²`. -/
theorem norm_iteratedFDeriv_two_bilinear_le_at
    (B : E →L[𝕜] F →L[𝕜] G)
    {left : D → E} {right : D → F} {x : D}
    (hleft : ContDiffAt 𝕜 2 left x)
    (hright : ContDiff 𝕜 2 right)
    (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv 𝕜 2
      (fun y => B (left y) (right y)) x‖ ≤
      ‖iteratedFDeriv 𝕜 0 left x‖ *
          ‖iteratedFDeriv 𝕜 2 right x‖ +
        2 * ‖iteratedFDeriv 𝕜 1 left x‖ *
          ‖iteratedFDeriv 𝕜 1 right x‖ +
        ‖iteratedFDeriv 𝕜 2 left x‖ *
          ‖iteratedFDeriv 𝕜 0 right x‖ := by
  rcases hleft.contDiffOn
      (m := (2 : WithTop ℕ∞)) le_rfl (by simp) with
    ⟨u, hu, hleftU⟩
  rcases mem_nhds_iff.mp hu with
    ⟨s, hsu, hsOpen, hx⟩
  have hleftS : ContDiffOn 𝕜 2 left s :=
    hleftU.mono hsu
  have hsUnique : UniqueDiffOn 𝕜 s :=
    hsOpen.uniqueDiffOn
  have hmain :=
    B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
      hleftS hright.contDiffOn hsUnique hx
      (n := 2) le_rfl hB
  have hcombined :
      ContDiffAt 𝕜 2 (fun y => B (left y) (right y)) x :=
    (B.contDiff.contDiffAt.comp x hleft).clm_apply
      hright.contDiffAt
  have hleftEq : ∀ i, i ≤ 2 →
      iteratedFDerivWithin 𝕜 i left s x =
        iteratedFDeriv 𝕜 i left x := by
    intro i hi
    have hin :
        (i : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr
        (WithTop.coe_le_coe.mpr hi)
    exact iteratedFDerivWithin_eq_iteratedFDeriv
      hsUnique (hleft.of_le hin) hx
  have hrightEq : ∀ i, i ≤ 2 →
      iteratedFDerivWithin 𝕜 i right s x =
        iteratedFDeriv 𝕜 i right x := by
    intro i hi
    have hin :
        (i : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr
        (WithTop.coe_le_coe.mpr hi)
    exact iteratedFDerivWithin_eq_iteratedFDeriv
      hsUnique (hright.contDiffAt.of_le hin) hx
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    hsUnique hcombined hx] at hmain
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    Nat.choose_one_right, Nat.cast_ofNat, Nat.choose_self] at hmain
  rw [hleftEq 0 (by norm_num), hleftEq 1 (by norm_num),
    hleftEq 2 (by norm_num), hrightEq 0 (by norm_num),
    hrightEq 1 (by norm_num), hrightEq 2 (by norm_num)] at hmain
  simpa [add_assoc] using hmain

end

end YangMills.RG
