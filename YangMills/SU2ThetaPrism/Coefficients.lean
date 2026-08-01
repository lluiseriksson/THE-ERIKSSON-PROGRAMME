import YangMills.SU2ThetaPrism.Representation
import YangMills.SU2ThetaPrism.Analysis
import YangMills.SU2ThetaPrism.QuaternionMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Character coefficients, central multipliers, and the fixed beta gate
-/

noncomputable section

open MeasureTheory

namespace YangMills.SU2ThetaPrism

/-- The fabrication domain is exactly `0 < beta <= 1`. -/
def BetaDomain (beta : ℝ) : Prop :=
  0 < beta ∧ beta ≤ 1

theorem one_mem_betaDomain : BetaDomain 1 := by
  constructor <;> norm_num

/-- Real-valued probes indexed by twice-spin.  The abstract coefficient lemma
uses this neutral function-space name; the front door below instantiates it
with `su2WeylPolynomial`, whose low-spin entries have explicit
representation-ring bridges. -/
abbrev RealProbeFamily := TwiceSpin → SU2 → ℝ

/-- The concrete low-spin SU(2) Weyl polynomials consumed by this gate.
Only labels `1` (spin one-half) and `2` (spin one) occur in the endpoint. -/
def su2WeylPolynomial : RealProbeFamily
  | 1, g => (chi g).re
  | 2, g => (chi g).re ^ 2 - 1
  | _, _ => 0

@[simp] theorem su2WeylPolynomial_spinHalf (g : SU2) :
    su2WeylPolynomial 1 g = (chi g).re := rfl

@[simp] theorem su2WeylPolynomial_spinOne (g : SU2) :
    su2WeylPolynomial 2 g = (chi g).re ^ 2 - 1 := rfl

/-- The label-one probe is literally the character of the constructed
fundamental continuous unitary representation. -/
theorem su2WeylPolynomial_spinHalf_representation_bridge (g : SU2) :
    (su2WeylPolynomial 1 g : ℂ) =
      YangMills.ClayCore.ContinuousUnitaryMatrixRep.character fundamentalRep g := by
  rw [YangMills.ClayCore.ContinuousUnitaryMatrixRep.character_apply]
  change ((chi g).re : ℂ) = chi g
  have him : (chi g).im = 0 := by
    have h := congrArg Complex.im (chi_star_eq g)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext <;> simp [him]

/-- Clebsch--Gordan character-ring bridge at the only higher label consumed:
the spin-one Weyl polynomial plus the trivial character is the character of
the tensor square of the constructed fundamental representation.  This avoids
presenting an arbitrary family of functions as representation data. -/
theorem su2WeylPolynomial_spinOne_tensor_square_bridge (g : SU2) :
    (su2WeylPolynomial 2 g : ℂ) + 1 =
      (YangMills.ClayCore.ContinuousUnitaryMatrixRep.character fundamentalRep g) ^ 2 := by
  rw [← su2WeylPolynomial_spinHalf_representation_bridge]
  simp only [su2WeylPolynomial_spinOne, su2WeylPolynomial_spinHalf]
  norm_cast
  ring

/-- Registered coefficient integral. -/
def alpha (characters : RealProbeFamily) (beta : ℝ) (j : TwiceSpin) : ℝ :=
  ∫ g : SU2,
    Real.exp ((beta / 2) * (chi g).re) * characters j g
      ∂haarSU2

private theorem chi_re_continuous : Continuous (fun g : SU2 => (chi g).re) :=
  Complex.continuous_re.comp chi_continuous

private theorem exp_mul_chi_re_integrable (a : ℝ) :
    Integrable (fun g : SU2 => Real.exp (a * (chi g).re) * (chi g).re) haarSU2 := by
  exact ((Real.continuous_exp.comp (continuous_const.mul chi_re_continuous)).mul
    chi_re_continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Central Haar symmetry rewrites the spin-half coefficient as an integral
of `u * sinh ((beta / 2) * u)`, with `u = re (chi g)`. -/
theorem alpha_spinHalf_eq_integral_mul_sinh (beta : ℝ) :
    alpha su2WeylPolynomial beta 1 =
      ∫ g : SU2, (chi g).re * Real.sinh ((beta / 2) * (chi g).re) ∂haarSU2 := by
  let a : ℝ := beta / 2
  let f : SU2 → ℝ := fun g => Real.exp (a * (chi g).re) * (chi g).re
  let fneg : SU2 → ℝ := fun g => Real.exp (-a * (chi g).re) * (chi g).re
  have hf : Integrable f haarSU2 := by
    simpa [f] using exp_mul_chi_re_integrable a
  have hfneg : Integrable fneg haarSU2 := by
    simpa [fneg] using exp_mul_chi_re_integrable (-a)
  have hsym : (∫ g, f g ∂haarSU2) = -(∫ g, fneg g ∂haarSU2) := by
    calc
      (∫ g, f g ∂haarSU2) = ∫ g, f (negIdentitySU2 * g) ∂haarSU2 :=
        (integral_mul_left_eq_self (μ := haarSU2) f negIdentitySU2).symm
      _ = ∫ g, -fneg g ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun g => by
          simp [f, fneg]
      _ = -(∫ g, fneg g ∂haarSU2) := integral_neg _
  change (∫ g, f g ∂haarSU2) = _
  calc
    (∫ g, f g ∂haarSU2) =
        (1 / 2 : ℝ) * ((∫ g, f g ∂haarSU2) - ∫ g, fneg g ∂haarSU2) := by
      rw [hsym]
      ring
    _ = (1 / 2 : ℝ) * ∫ g, (f - fneg) g ∂haarSU2 := by
      have hsub : (∫ g, (f - fneg) g ∂haarSU2) =
          (∫ g, f g ∂haarSU2) - ∫ g, fneg g ∂haarSU2 := by
        simpa only [Pi.sub_apply] using integral_sub hf hfneg
      rw [hsub]
    _ = ∫ g, (1 / 2 : ℝ) * (f - fneg) g ∂haarSU2 := by
      rw [integral_const_mul]
    _ = ∫ g : SU2, (chi g).re * Real.sinh (a * (chi g).re) ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        change (1 / 2 : ℝ) * (f g - fneg g) =
          (chi g).re * Real.sinh (a * (chi g).re)
        simp only [f, fneg]
        rw [Real.sinh_eq]
        ring
    _ = ∫ g : SU2, (chi g).re *
        Real.sinh ((beta / 2) * (chi g).re) ∂haarSU2 := by rfl

private theorem scaled_sq_le_mul_sinh {a u : ℝ} (ha : 0 ≤ a) :
    a * u ^ 2 ≤ u * Real.sinh (a * u) := by
  by_cases hu : 0 ≤ u
  · have hsinh : a * u ≤ Real.sinh (a * u) :=
      Real.self_le_sinh_iff.mpr (mul_nonneg ha hu)
    nlinarith
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hsinh : Real.sinh (a * u) ≤ a * u :=
      Real.sinh_le_self_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha hu')
    nlinarith

/-- Direct spin-half coefficient bound.  It uses only central Haar symmetry,
the elementary `sinh` inequality, and the already proved Schur second moment;
no character series or Peter--Weyl completeness enters. -/
theorem alpha_spinHalf_lower {beta : ℝ} (hbeta : 0 ≤ beta) :
    beta / 2 ≤ alpha su2WeylPolynomial beta 1 := by
  rw [alpha_spinHalf_eq_integral_mul_sinh]
  have ha : 0 ≤ beta / 2 := div_nonneg hbeta (by norm_num)
  have hleft : Integrable (fun g : SU2 =>
      (beta / 2) * (chi g).re ^ 2) haarSU2 := by
    exact ((continuous_const.mul (chi_re_continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hright : Integrable (fun g : SU2 =>
      (chi g).re * Real.sinh ((beta / 2) * (chi g).re)) haarSU2 := by
    exact (chi_re_continuous.mul
      (Real.continuous_sinh.comp
        (continuous_const.mul chi_re_continuous))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  calc
    beta / 2 = (beta / 2) * ∫ g : SU2, (chi g).re ^ 2 ∂haarSU2 := by
      rw [chi_re_sq_integral_one, mul_one]
    _ = ∫ g : SU2, (beta / 2) * (chi g).re ^ 2 ∂haarSU2 := by
      rw [integral_const_mul]
    _ ≤ ∫ g : SU2, (chi g).re * Real.sinh ((beta / 2) * (chi g).re) ∂haarSU2 := by
      exact integral_mono_ae hleft hright
        (ae_of_all _ fun g => scaled_sq_le_mul_sinh ha)

/-- The spin-one coefficient obligation, discharged below by the signed
hyperbolic remainder estimate and the concrete second and fourth moments. -/
structure SpinOneCoefficientRemainderStep (beta : ℝ) : Prop where
  one_remainder_nonnegative :
    0 ≤ alpha su2WeylPolynomial beta 2 - beta ^ 2 / 8

/-- The even Taylor remainder used in the spin-one coefficient estimate. -/
def coshRemainder (t : ℝ) : ℝ :=
  Real.cosh t - 1 - t ^ 2 / 2

private theorem coshRemainder_hasDerivAt (t : ℝ) :
    HasDerivAt coshRemainder (Real.sinh t - t) t := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
    convert ((hasDerivAt_id t).pow 2).div_const 2 using 1 <;> ring
  have hraw := ((Real.hasDerivAt_cosh t).sub (hasDerivAt_const t 1)).sub hsq
  convert hraw using 1 <;> simp [coshRemainder, id]

/-- The hyperbolic Taylor remainder is increasing on the nonnegative axis.
This is a one-variable calculus fact: its derivative is `sinh t - t`. -/
theorem coshRemainder_monotoneOn_nonnegative :
    MonotoneOn coshRemainder (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0 : Convex ℝ (Set.Ici 0))
  · change ContinuousOn (fun t : ℝ => Real.cosh t - 1 - t ^ 2 / 2) (Set.Ici 0)
    fun_prop
  · change DifferentiableOn ℝ (fun t : ℝ => Real.cosh t - 1 - t ^ 2 / 2)
      (interior (Set.Ici 0))
    fun_prop
  · intro t ht
    rw [(coshRemainder_hasDerivAt t).deriv]
    have ht0 : 0 ≤ t := by
      have : 0 < t := by simpa using ht
      exact this.le
    exact sub_nonneg.mpr (Real.self_le_sinh_iff.mpr ht0)

private theorem coshRemainder_abs (t : ℝ) :
    coshRemainder |t| = coshRemainder t := by
  simp only [coshRemainder, Real.cosh_abs]
  rw [sq_abs]

/-- Signed remainder estimate.  When `u^2 - 1` is negative, monotonicity of
the even remainder reverses exactly the comparison needed after
multiplication; when it is positive, it gives the direct comparison. -/
theorem signed_coshRemainder_nonnegative {a u : ℝ} (ha : 0 ≤ a) :
    0 ≤ (coshRemainder (a * u) - coshRemainder a) * (u ^ 2 - 1) := by
  by_cases hu : 1 ≤ |u|
  · have hau : a ≤ |a * u| := by
      rw [abs_mul, abs_of_nonneg ha]
      exact le_mul_of_one_le_right ha hu
    have hr : coshRemainder a ≤ coshRemainder |a * u| :=
      coshRemainder_monotoneOn_nonnegative
        (show a ∈ Set.Ici 0 from ha)
        (show |a * u| ∈ Set.Ici 0 from abs_nonneg _)
        hau
    rw [coshRemainder_abs] at hr
    have hfactor : 0 ≤ u ^ 2 - 1 := by
      nlinarith [sq_abs u]
    exact mul_nonneg (sub_nonneg.mpr hr) hfactor
  · have hu' : |u| ≤ 1 := le_of_lt (lt_of_not_ge hu)
    have hau : |a * u| ≤ a := by
      rw [abs_mul, abs_of_nonneg ha]
      exact mul_le_of_le_one_right ha hu'
    have hr : coshRemainder |a * u| ≤ coshRemainder a :=
      coshRemainder_monotoneOn_nonnegative
        (show |a * u| ∈ Set.Ici 0 from abs_nonneg _)
        (show a ∈ Set.Ici 0 from ha)
        hau
    rw [coshRemainder_abs] at hr
    have hfactor : u ^ 2 - 1 ≤ 0 := by
      nlinarith [sq_abs u]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hr) hfactor

private theorem exp_mul_spinOne_integrable (a : ℝ) :
    Integrable (fun g : SU2 =>
      Real.exp (a * (chi g).re) * ((chi g).re ^ 2 - 1)) haarSU2 := by
  exact ((Real.continuous_exp.comp (continuous_const.mul chi_re_continuous)).mul
    ((chi_re_continuous.pow 2).sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Central Haar symmetry replaces the spin-one exponential by `cosh`.
The probe `chi^2 - 1` is even under multiplication by the central `-I`. -/
theorem alpha_spinOne_eq_integral_mul_cosh (beta : ℝ) :
    alpha su2WeylPolynomial beta 2 =
      ∫ g : SU2, Real.cosh ((beta / 2) * (chi g).re) *
        ((chi g).re ^ 2 - 1) ∂haarSU2 := by
  let a : ℝ := beta / 2
  let f : SU2 → ℝ := fun g =>
    Real.exp (a * (chi g).re) * ((chi g).re ^ 2 - 1)
  let fneg : SU2 → ℝ := fun g =>
    Real.exp (-a * (chi g).re) * ((chi g).re ^ 2 - 1)
  have hf : Integrable f haarSU2 := by
    simpa [f] using exp_mul_spinOne_integrable a
  have hfneg : Integrable fneg haarSU2 := by
    simpa [fneg] using exp_mul_spinOne_integrable (-a)
  have hsym : (∫ g, f g ∂haarSU2) = ∫ g, fneg g ∂haarSU2 := by
    calc
      (∫ g, f g ∂haarSU2) = ∫ g, f (negIdentitySU2 * g) ∂haarSU2 :=
        (integral_mul_left_eq_self (μ := haarSU2) f negIdentitySU2).symm
      _ = ∫ g, fneg g ∂haarSU2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun g => by simp [f, fneg]
  change (∫ g, f g ∂haarSU2) = _
  calc
    (∫ g, f g ∂haarSU2) =
        (1 / 2 : ℝ) * ((∫ g, f g ∂haarSU2) + ∫ g, fneg g ∂haarSU2) := by
      rw [hsym]
      ring
    _ = (1 / 2 : ℝ) * ∫ g, f g + fneg g ∂haarSU2 := by
      rw [integral_add hf hfneg]
    _ = ∫ g, (1 / 2 : ℝ) * (f g + fneg g) ∂haarSU2 := by
      rw [integral_const_mul]
    _ = ∫ g : SU2, Real.cosh (a * (chi g).re) *
        ((chi g).re ^ 2 - 1) ∂haarSU2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun g => by
        change (1 / 2 : ℝ) * (f g + fneg g) = _
        simp only [f, fneg]
        rw [Real.cosh_eq]
        ring
    _ = ∫ g : SU2, Real.cosh ((beta / 2) * (chi g).re) *
        ((chi g).re ^ 2 - 1) ∂haarSU2 := by rfl

private theorem chi_re_sq_sub_one_integral_zero :
    (∫ g : SU2, ((chi g).re ^ 2 - 1) ∂haarSU2) = 0 := by
  have hsq : Integrable (fun g : SU2 => (chi g).re ^ 2) haarSU2 :=
    (chi_re_continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hone : Integrable (fun _ : SU2 => (1 : ℝ)) haarSU2 := integrable_const 1
  rw [integral_sub hsq hone, chi_re_sq_integral_one]
  simp

private theorem chi_re_fourth_sub_sq_integral_one :
    (∫ g : SU2, ((chi g).re ^ 4 - (chi g).re ^ 2) ∂haarSU2) = 1 := by
  have hfour : Integrable (fun g : SU2 => (chi g).re ^ 4) haarSU2 :=
    (chi_re_continuous.pow 4).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsq : Integrable (fun g : SU2 => (chi g).re ^ 2) haarSU2 :=
    (chi_re_continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hfour hsq, chi_re_fourth_integral_two_quaternion,
    chi_re_sq_integral_one]
  norm_num

private theorem coshRemainder_mul_spinOne_integrable (a : ℝ) :
    Integrable (fun g : SU2 => coshRemainder (a * (chi g).re) *
      ((chi g).re ^ 2 - 1)) haarSU2 := by
  exact (((Real.continuous_cosh.comp (continuous_const.mul chi_re_continuous)).sub
      continuous_const |>.sub ((continuous_const.mul chi_re_continuous).pow 2 |>.div_const 2)).mul
    ((chi_re_continuous.pow 2).sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

private theorem spinOne_signed_remainder_integral_nonnegative {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ ∫ g : SU2, coshRemainder (a * (chi g).re) *
      ((chi g).re ^ 2 - 1) ∂haarSU2 := by
  let R : SU2 → ℝ := fun g => coshRemainder (a * (chi g).re) *
    ((chi g).re ^ 2 - 1)
  let C : SU2 → ℝ := fun g => coshRemainder a * ((chi g).re ^ 2 - 1)
  have hR : Integrable R haarSU2 := by
    simpa [R] using coshRemainder_mul_spinOne_integrable a
  have hC : Integrable C haarSU2 := by
    exact (continuous_const.mul ((chi_re_continuous.pow 2).sub continuous_const))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnonneg : 0 ≤ ∫ g : SU2, (R - C) g ∂haarSU2 := by
    refine integral_nonneg fun g => ?_
    simpa [R, C, sub_mul] using
      (signed_coshRemainder_nonnegative (u := (chi g).re) ha)
  have hzero : (∫ g : SU2, C g ∂haarSU2) = 0 := by
    rw [show C = fun g : SU2 => coshRemainder a * ((chi g).re ^ 2 - 1) by rfl,
      integral_const_mul, chi_re_sq_sub_one_integral_zero, mul_zero]
  have hsub : (∫ g : SU2, (R - C) g ∂haarSU2) =
      (∫ g : SU2, R g ∂haarSU2) - ∫ g : SU2, C g ∂haarSU2 := by
    simpa only [Pi.sub_apply] using integral_sub hR hC
  rw [hsub, hzero, sub_zero] at hnonneg
  simpa [R] using hnonneg

/-- The spin-one coefficient splits into its quadratic moment contribution
`beta^2/8` and the signed hyperbolic remainder. -/
theorem alpha_spinOne_eq_quadratic_add_remainder (beta : ℝ) :
    alpha su2WeylPolynomial beta 2 = beta ^ 2 / 8 +
      ∫ g : SU2, coshRemainder ((beta / 2) * (chi g).re) *
        ((chi g).re ^ 2 - 1) ∂haarSU2 := by
  rw [alpha_spinOne_eq_integral_mul_cosh]
  let a : ℝ := beta / 2
  let M : SU2 → ℝ := fun g => a ^ 2 / 2 *
    ((chi g).re ^ 4 - (chi g).re ^ 2)
  let Z : SU2 → ℝ := fun g => (chi g).re ^ 2 - 1
  let R : SU2 → ℝ := fun g => coshRemainder (a * (chi g).re) *
    ((chi g).re ^ 2 - 1)
  have hM : Integrable M haarSU2 := by
    exact (continuous_const.mul ((chi_re_continuous.pow 4).sub
      (chi_re_continuous.pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hZ : Integrable Z haarSU2 := by
    exact ((chi_re_continuous.pow 2).sub continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR : Integrable R haarSU2 := by
    simpa [R] using coshRemainder_mul_spinOne_integrable a
  have hpoint : ∀ g : SU2,
      Real.cosh (a * (chi g).re) * ((chi g).re ^ 2 - 1) =
        M g + Z g + R g := by
    intro g
    simp only [M, Z, R, coshRemainder]
    ring
  rw [integral_congr_ae (ae_of_all _ hpoint)]
  have hsum : (∫ g : SU2, M g + Z g + R g ∂haarSU2) =
      ((∫ g : SU2, M g ∂haarSU2) + ∫ g : SU2, Z g ∂haarSU2) +
        ∫ g : SU2, R g ∂haarSU2 := by
    calc
      (∫ g : SU2, M g + Z g + R g ∂haarSU2) =
          (∫ g : SU2, (M + Z) g ∂haarSU2) + ∫ g : SU2, R g ∂haarSU2 := by
        simpa only [Pi.add_apply] using integral_add (hM.add hZ) hR
      _ = ((∫ g : SU2, M g ∂haarSU2) + ∫ g : SU2, Z g ∂haarSU2) +
          ∫ g : SU2, R g ∂haarSU2 := by
        rw [integral_add hM hZ]
  rw [hsum]
  have hMint : (∫ g : SU2, M g ∂haarSU2) = beta ^ 2 / 8 := by
    rw [show M = fun g : SU2 => a ^ 2 / 2 *
      ((chi g).re ^ 4 - (chi g).re ^ 2) by rfl,
      integral_const_mul, chi_re_fourth_sub_sq_integral_one]
    simp only [mul_one, a]
    ring
  have hZint : (∫ g : SU2, Z g ∂haarSU2) = 0 := by
    simpa [Z] using chi_re_sq_sub_one_integral_zero
  rw [hMint, hZint, add_zero]
  rfl

/-- Concrete discharge of the last coefficient obligation for every
nonnegative beta. -/
def spinOneCoefficientRemainderStepConcrete {beta : ℝ} (hbeta : 0 ≤ beta) :
    SpinOneCoefficientRemainderStep beta where
  one_remainder_nonnegative := by
    rw [alpha_spinOne_eq_quadratic_add_remainder]
    have ha : 0 ≤ beta / 2 := div_nonneg hbeta (by norm_num)
    have hrem := spinOne_signed_remainder_integral_nonnegative ha
    linarith

/-- Central convolution multiplier `alpha_j/(2j+1)`, with the denominator
derived from the general representation dimension. -/
def centralMultiplier (a : TwiceSpin → ℝ) (j : TwiceSpin) : ℝ :=
  a j / representationDimension j

theorem centralMultiplier_spinHalf (a : TwiceSpin → ℝ) :
    centralMultiplier a 1 = a 1 / 2 := by
  norm_num [centralMultiplier, representationDimension]

theorem centralMultiplier_spinOne (a : TwiceSpin → ℝ) :
    centralMultiplier a 2 = a 2 / 3 := by
  norm_num [centralMultiplier, representationDimension]

/-- Pairing assembled from the witness norm and three central multipliers.
The rational factor is deliberately not part of this definition. -/
def thetaPairingFromMultipliers
    (witnessNormSq : ℝ) (a : TwiceSpin → ℝ) : ℝ :=
  witnessNormSq * centralMultiplier a 2 * (centralMultiplier a 1) ^ 2

/-- `1/16` follows from the independently derived norm and dimensions. -/
theorem thetaPairing_factor_sixteen (a : TwiceSpin → ℝ) :
    thetaPairingFromMultipliers (3 / 4) a = a 2 * (a 1) ^ 2 / 16 := by
  rw [thetaPairingFromMultipliers, centralMultiplier_spinOne,
    centralMultiplier_spinHalf]
  ring

/-- Technical series-remainder inputs on the pre-registered interval.  These
are coefficient lower steps, not the pairing or gate conclusion. -/
structure CoefficientRemainderSteps (a : TwiceSpin → ℝ) (beta : ℝ) : Prop where
  half_remainder_nonnegative : 0 ≤ a 1 - beta / 2
  one_remainder_nonnegative : 0 ≤ a 2 - beta ^ 2 / 8

/-- Reconstruct the internal two-coefficient record from the proved
spin-half bound and the sole remaining spin-one obligation. -/
def coefficientRemainderSteps_of_spinOne {beta : ℝ} (hbeta : 0 ≤ beta)
    (step : SpinOneCoefficientRemainderStep beta) :
    CoefficientRemainderSteps (fun j => alpha su2WeylPolynomial beta j) beta where
  half_remainder_nonnegative := by
    have hhalf := alpha_spinHalf_lower hbeta
    linarith
  one_remainder_nonnegative := step.one_remainder_nonnegative

theorem coefficient_half_lower {a : TwiceSpin → ℝ} {beta : ℝ}
    (steps : CoefficientRemainderSteps a beta) : beta / 2 ≤ a 1 := by
  linarith [steps.half_remainder_nonnegative]

theorem coefficient_one_lower {a : TwiceSpin → ℝ} {beta : ℝ}
    (steps : CoefficientRemainderSteps a beta) : beta ^ 2 / 8 ≤ a 2 := by
  linarith [steps.one_remainder_nonnegative]

/-- Fixed manufactured inequality.  It is local to this artefact and is not
programme Gate 7. -/
theorem thetaPairing_gate {a : TwiceSpin → ℝ} {beta : ℝ}
    (hbeta : BetaDomain beta) (steps : CoefficientRemainderSteps a beta) :
    beta ^ 4 / 512 ≤ thetaPairingFromMultipliers (3 / 4) a := by
  rw [thetaPairing_factor_sixteen]
  have hb0 : 0 ≤ beta / 2 := by linarith [hbeta.1]
  have ha1 : beta / 2 ≤ a 1 := coefficient_half_lower steps
  have ha10 : 0 ≤ a 1 := le_trans hb0 ha1
  have hsq : (beta / 2) ^ 2 ≤ (a 1) ^ 2 := by
    exact (sq_le_sq₀ hb0 ha10).2 ha1
  have hb20 : 0 ≤ beta ^ 2 / 8 := by positivity
  have ha2 : beta ^ 2 / 8 ≤ a 2 := coefficient_one_lower steps
  have ha20 : 0 ≤ a 2 := le_trans hb20 ha2
  have hmul := mul_le_mul ha2 hsq (sq_nonneg (beta / 2)) ha20
  nlinarith

end YangMills.SU2ThetaPrism
