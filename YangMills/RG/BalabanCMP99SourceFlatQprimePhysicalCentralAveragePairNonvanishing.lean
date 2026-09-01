/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249CentralStabilizedRealLower
import YangMills.RG.BalabanCMP99SourceFlatQprimeSignedAliasMomentumDictionary

/-!
# PRE-VALIDATION: physical central averaging pair is nonzero

The literal uncentered coarse representative lies in the strict interval
`(-2*pi, 0]` coordinatewise. Its finite geometric average cannot vanish: for
a nonzero coordinate the terminal power is a nontrivial `N'`-th root of
unity, while at the zero coordinate the normalized sum is exactly one.

Source is present, its `.olean` has not yet been materialized, and the result
has not yet been verified by the compiler.
-/

namespace YangMills.RG

open YangMills

noncomputable section

private theorem complex_exp_two_pi_I_mul_ne_one_of_mem_Ioo
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Complex.exp ((t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ≠ 1 := by
  intro hexp
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨n, hn⟩ := hexp
  have hperiod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hcast : (t : ℂ) = (n : ℂ) :=
    mul_right_cancel₀ hperiod hn
  have hreal : t = (n : ℝ) := by
    have := congrArg Complex.re hcast
    simpa using this
  have hn0 : (0 : ℤ) < n := by
    exact_mod_cast (hreal ▸ ht0)
  have hn1 : n < (1 : ℤ) := by
    exact_mod_cast (hreal ▸ ht1)
  omega

private theorem cmp89Eq245EntireAverageFactor_physicalCoarse_ne_zero
    {M N' : ℕ} [NeZero M] [NeZero N'] (k : Fin N') :
    cmp89Eq245EntireAverageFactor M
        (-((2 * Real.pi : ℂ) * (k.val : ℂ) / (N' : ℂ))) ≠ 0 := by
  by_cases hk : k.val = 0
  · simp [hk, cmp89Eq245EntireAverageFactor,
      cmp89Eq245EntireAverageBase, NeZero.ne M]
  · let z : ℂ := -((2 * Real.pi : ℂ) * (k.val : ℂ) / (N' : ℂ))
    let x : ℂ := cmp89Eq245EntireAverageBase M z
    have hM0 : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
    have hN0 : (0 : ℝ) < N' := by exact_mod_cast NeZero.pos N'
    have hk0 : (0 : ℝ) < k.val := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hkN : (k.val : ℝ) < N' := by exact_mod_cast k.isLt
    have htSmall0 : 0 < (k.val : ℝ) / ((M : ℝ) * N') := by positivity
    have htSmall1 : (k.val : ℝ) / ((M : ℝ) * N') < 1 := by
      apply (div_lt_one (mul_pos hM0 hN0)).2
      calc
        (k.val : ℝ) < N' := hkN
        _ ≤ (M : ℝ) * N' := by nlinarith
    have htCoarse0 : 0 < (k.val : ℝ) / N' := by positivity
    have htCoarse1 : (k.val : ℝ) / N' < 1 :=
      (div_lt_one hN0).2 hkN
    have hxExp :
        x = Complex.exp
          ((((k.val : ℝ) / ((M : ℝ) * N') : ℝ) : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) := by
      unfold x z cmp89Eq245EntireAverageBase
      congr 1
      push_cast
      field_simp [show (M : ℂ) ≠ 0 by exact_mod_cast NeZero.ne M,
        show (N' : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N']
      ring
    have hx : x ≠ 1 := by
      rw [hxExp]
      exact complex_exp_two_pi_I_mul_ne_one_of_mem_Ioo htSmall0 htSmall1
    have hxPowExp :
        x ^ M = Complex.exp
          ((((k.val : ℝ) / N' : ℝ) : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) := by
      rw [hxExp, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp [show (M : ℝ) ≠ 0 by exact_mod_cast NeZero.ne M,
        show (N' : ℝ) ≠ 0 by exact_mod_cast NeZero.ne N']
      ring
    have hxPow : x ^ M ≠ 1 := by
      rw [hxPowExp]
      exact complex_exp_two_pi_I_mul_ne_one_of_mem_Ioo htCoarse0 htCoarse1
    rw [cmp89Eq245EntireAverageFactor, show
      cmp89Eq245EntireAverageBase M
          (-((2 * Real.pi : ℂ) * (k.val : ℂ) / (N' : ℂ))) = x by rfl,
      geom_sum_eq hx]
    exact mul_ne_zero
      (inv_ne_zero (by exact_mod_cast NeZero.ne M))
      (div_ne_zero (sub_ne_zero.mpr hxPow) (sub_ne_zero.mpr hx))

/-- The central opposite-momentum averaging pair is nonzero at every literal
physical coarse representative. -/
theorem cmp89Eq249CentralEntireAveragePair_physicalCoarse_ne_zero
    {d M N' : ℕ} [NeZero M] [NeZero N'] (ell : FinBox d N') :
    cmp89Eq249CentralEntireAveragePair d M 1
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell) ≠ 0 := by
  let p : Fin d → ℝ := fun mu =>
    -(2 * Real.pi * (ell mu).val / N')
  have hbase :
      cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell =
        fun mu => (p mu : ℂ) := by
    funext mu
    simp [p, cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum]
    push_cast
    ring
  have hamp :
      cmp89Eq245EntireAverageAmplitude d M (fun mu => (p mu : ℂ)) ≠ 0 := by
    rw [cmp89Eq245EntireAverageAmplitude]
    apply Finset.prod_ne_zero
    intro mu _
    simpa [p] using
      (cmp89Eq245EntireAverageFactor_physicalCoarse_ne_zero
        (M := M) (N' := N') (ell mu))
  rw [hbase, cmp89Eq249CentralEntireAveragePair, pow_one,
    cmp89Eq245EntireAveragePair_ofReal_eq]
  exact pow_ne_zero 2
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hamp))

end

end YangMills.RG
