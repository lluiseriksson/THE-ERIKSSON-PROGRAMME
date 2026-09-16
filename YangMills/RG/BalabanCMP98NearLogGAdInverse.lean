/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP98GAdInverse
import YangMills.RG.BalabanCMP98LeftTrivializedExp
import YangMills.RG.NearLogLocalInverse

/-!
# The physical Mercator derivative is the printed `g(ad)⁻¹` correction

Inside the Mercator ball, the preceding local-inverse theorem identifies
`exp (nearLog Y)` literally with `1 + Y`.  Differentiating that identity gives

`D exp_(nearLog Y) ∘ D nearLog_Y = id`.

After left trivialisation, the exact CMP98 exponential derivative is
`g(ad (nearLog Y))`.  The certified Neumann inverse therefore yields the
source formula

`D nearLog_Y[H] = g(ad (nearLog Y))⁻¹ (exp(-nearLog Y) H)`.

No inverse derivative, symbolic logarithm, or postulated `g(ad)⁻¹` occurs in
the public interface.
-/

namespace YangMills.RG

open Filter

noncomputable section

variable {𝔸 : Type*}
variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- Differentiating the exact local identity `exp (nearLog Y) = 1 + Y` gives
the right-inverse identity for the two genuine Fréchet derivatives. -/
theorem fderiv_exp_nearLog_comp_fderiv_nearLog_eq_id
    {Y : 𝔸} (hY : ‖Y‖ < 1) :
    (fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (nearLog Y)).comp
        (∑' n : ℕ, nearLogTermFDeriv Y n) =
      ContinuousLinearMap.id ℝ 𝔸 := by
  have hopen : IsOpen {Z : 𝔸 | ‖Z‖ < 1} :=
    isOpen_lt continuous_norm continuous_const
  have hnhds : {Z : 𝔸 | ‖Z‖ < 1} ∈ nhds Y := hopen.mem_nhds hY
  have heq :
      (fun Z : 𝔸 => 1 + Z) =ᶠ[nhds Y]
        ((NormedSpace.exp : 𝔸 → 𝔸) ∘ nearLog) := by
    filter_upwards [hnhds] with Z hZ
    exact (exp_nearLog_eq_one_add hZ).symm
  have hcomp := (hasFDerivAt_exp_ordered (nearLog Y)).comp Y
    (hasFDerivAt_nearLog_of_norm_lt_one hY)
  have hcomp' : HasFDerivAt (fun Z : 𝔸 => 1 + Z)
      ((fderiv ℝ (NormedSpace.exp : 𝔸 → 𝔸) (nearLog Y)).comp
        (∑' n : ℕ, nearLogTermFDeriv Y n)) Y := by
    have h := hcomp.congr_of_eventuallyEq heq
    convert h using 1
    exact congrArg
      (fun f : 𝔸 →L[ℝ] 𝔸 => f.comp
        (∑' n : ℕ, nearLogTermFDeriv Y n))
      (hasFDerivAt_exp_ordered (nearLog Y)).fderiv
  have hid : HasFDerivAt (fun Z : 𝔸 => 1 + Z)
      (ContinuousLinearMap.id ℝ 𝔸) Y := by
    simpa using (hasFDerivAt_id Y).const_add (1 : 𝔸)
  exact hcomp'.unique hid

/-- Left-trivialised chain rule: applying `g(ad log)` to the genuine
Mercator derivative returns the left-translated physical variation. -/
theorem cmp98GAd_nearLog_fderiv_apply
    {Y : 𝔸} (hY : ‖Y‖ < 1) (H : 𝔸) :
    cmp98GAd (nearLog Y)
        ((∑' n : ℕ, nearLogTermFDeriv Y n) H) =
      NormedSpace.exp (-(nearLog Y)) * H := by
  rw [← cmp98_exp_neg_mul_fderiv_exp_eq_gad_apply]
  have hcomp := congrArg (fun T : 𝔸 →L[ℝ] 𝔸 => T H)
    (fderiv_exp_nearLog_comp_fderiv_nearLog_eq_id hY)
  simpa [ContinuousLinearMap.comp_apply] using congrArg
    (fun Z : 𝔸 => NormedSpace.exp (-(nearLog Y)) * Z) hcomp

/-- **Printed CMP98 correction formula.**  Under the explicit `g(ad)`
smallness condition, the ordered Mercator derivative is exactly the
certified `g(ad log)⁻¹` applied to the left-translated variation. -/
theorem nearLog_fderiv_apply_eq_cmp98GAdInv
    {Y : 𝔸} (hY : ‖Y‖ < 1)
    (hg : Real.exp (2 * ‖nearLog Y‖) < 2) (H : 𝔸) :
    (∑' n : ℕ, nearLogTermFDeriv Y n) H =
      cmp98GAdInv (nearLog Y)
        (NormedSpace.exp (-(nearLog Y)) * H) := by
  rw [← cmp98GAd_nearLog_fderiv_apply hY H]
  exact (cmp98GAdInv_cmp98GAd_apply_of_exp_lt_two
    (nearLog Y) ((∑' n : ℕ, nearLogTermFDeriv Y n) H) hg).symm

/-- A deviation of norm at most `1/3` has Mercator logarithm of norm at
most `1/2`, exactly the source radius needed by the sharp `g(ad)` tail. -/
theorem norm_nearLog_le_half_of_norm_le_third
    {Y : 𝔸} (hY : ‖Y‖ ≤ 1 / 3) :
    ‖nearLog Y‖ ≤ 1 / 2 := by
  have hYlt : ‖Y‖ < 1 := by linarith [norm_nonneg Y]
  have hden : 0 < 1 - ‖Y‖ := by linarith
  calc
    ‖nearLog Y‖ ≤ ‖Y‖ / (1 - ‖Y‖) := norm_nearLog_le_linear hYlt
    _ ≤ 1 / 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith

/-- **Source-radius version of the printed CMP98 correction.**  A single
geometric smallness hypothesis on the literal near-identity deviation now
generates both the Mercator derivative and the certified `g(ad)⁻¹`. -/
theorem nearLog_fderiv_apply_eq_cmp98GAdInv_of_norm_le_third
    {Y : 𝔸} (hY : ‖Y‖ ≤ 1 / 3) (H : 𝔸) :
    (∑' n : ℕ, nearLogTermFDeriv Y n) H =
      cmp98GAdInv (nearLog Y)
        (NormedSpace.exp (-(nearLog Y)) * H) := by
  have hYlt : ‖Y‖ < 1 := by linarith [norm_nonneg Y]
  rw [← cmp98GAd_nearLog_fderiv_apply hYlt H]
  exact (cmp98GAdInv_cmp98GAd_apply_of_norm_le_half
    (nearLog Y) ((∑' n : ℕ, nearLogTermFDeriv Y n) H)
    (norm_nearLog_le_half_of_norm_le_third hY)).symm

end

end YangMills.RG
