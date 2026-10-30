import YangMills.RG.TorusPhysicalShift

/-! Actual two-component coexact fields and a volume-order Fourier subband.
Positive first frequency supplies injectivity; no annihilation or dimension
is assumed. This module does not yet transport the Hodge energy bound. -/
namespace YangMills.RG
open Module
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1200000

section Difference
variable {D n : ℕ} [NeZero n]

noncomputable def torusBackwardDifference (j : Fin D) :
    ((Fin D → ZMod n) → ℂ) →ₗ[ℂ] ((Fin D → ZMod n) → ℂ) where
  toFun f x := f x - f (x - Pi.single j (1 : ZMod n))
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' r f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem torusBackwardDifference_apply (j : Fin D)
    (f : (Fin D → ZMod n) → ℂ) (x : Fin D → ZMod n) :
    torusBackwardDifference j f x = f x - f (x - Pi.single j (1 : ZMod n)) := rfl

/-- The actual real action is checked directly; no CompatibleSMul input. -/
noncomputable def torusBackwardDifferenceReal (j : Fin D) :
    ((Fin D → ZMod n) → ℂ) →ₗ[ℝ] ((Fin D → ZMod n) → ℂ) where
  toFun f := torusBackwardDifference j f
  map_add' f g := (torusBackwardDifference j).map_add f g
  map_smul' r f := by
    funext x
    simp only [torusBackwardDifference_apply, Pi.smul_apply, RingHom.id_apply, smul_sub]

theorem torusBackwardDifference_commute (i j : Fin D)
    (f : (Fin D → ZMod n) → ℂ) (x : Fin D → ZMod n) :
    torusBackwardDifference i (torusBackwardDifference j f) x =
      torusBackwardDifference j (torusBackwardDifference i f) x := by
  let ei : Fin D → ZMod n := Pi.single i (1 : ZMod n)
  let ej : Fin D → ZMod n := Pi.single j (1 : ZMod n)
  have hxy : x - ei - ej = x - ej - ei := by abel
  change (f x - f (x - ej)) - (f (x - ei) - f (x - ei - ej)) =
    (f x - f (x - ei)) - (f (x - ej) - f (x - ej - ei))
  rw [hxy]
  ring
end Difference

section ActualPhysical
variable {D n Nc : ℕ} [NeZero D] [NeZero n] [NeZero Nc]

noncomputable def torusPhysicalEmbedLinear (hNc : 2 ≤ Nc) (j : Fin D) :
    ((Fin D → ZMod n) → ℂ) →ₗ[ℝ] PhysicalGaugeOneCochain D n Nc where
  toFun f := torusPhysicalEmbed hNc j f
  map_add' f g := torusPhysicalEmbed_add hNc j f g
  map_smul' r f := torusPhysicalEmbed_smul hNc j r f

noncomputable def coexactFlatMap (hNc : 2 ≤ Nc) (i j : Fin D) :
    ((Fin D → ZMod n) → ℂ) →ₗ[ℝ] PhysicalGaugeOneCochain D n Nc :=
  (torusPhysicalEmbedLinear hNc i).comp (torusBackwardDifferenceReal j) -
    (torusPhysicalEmbedLinear hNc j).comp (torusBackwardDifferenceReal i)

@[simp] theorem coexactFlatMap_apply (hNc : 2 ≤ Nc) (i j : Fin D)
    (f : (Fin D → ZMod n) → ℂ) :
    coexactFlatMap hNc i j f =
      torusPhysicalEmbed hNc i (torusBackwardDifference j f) -
        torusPhysicalEmbed hNc j (torusBackwardDifference i f) := rfl

theorem coexactFlatMap_div_zero (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (i j : Fin D) (f : (Fin D → ZMod n) → ℂ) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground D n Nc)
      (coexactFlatMap hNc i j f) = 0 := by
  rw [coexactFlatMap_apply, map_sub]
  apply PiLp.ext
  intro y
  change gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground D n Nc)
      (torusPhysicalEmbed hNc i (torusBackwardDifference j f)) y -
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground D n Nc)
      (torusPhysicalEmbed hNc j (torusBackwardDifference i f)) y = 0
  rw [torusPhysicalEmbed_flat_div_apply, torusPhysicalEmbed_flat_div_apply]
  have hcomm : torusBackwardDifference j f (finBoxZModEquiv D n y) -
      torusBackwardDifference j f (finBoxZModEquiv D n y - Pi.single i (1 : ZMod n)) =
    torusBackwardDifference i f (finBoxZModEquiv D n y) -
      torusBackwardDifference i f (finBoxZModEquiv D n y - Pi.single j (1 : ZMod n)) :=
    torusBackwardDifference_commute i j f _
  rw [hcomm, sub_self]

theorem coexactFlatMap_zero_backward (hNc : 2 ≤ Nc) (i j : Fin D) (hij : i ≠ j)
    (f : (Fin D → ZMod n) → ℂ) (hf : coexactFlatMap hNc i j f = 0) :
    torusBackwardDifference i f = 0 := by
  have heq : torusPhysicalEmbed hNc i (torusBackwardDifference j f) =
      torusPhysicalEmbed hNc j (torusBackwardDifference i f) :=
    sub_eq_zero.mp (by simpa only [coexactFlatMap_apply] using hf)
  funext x
  let y := (finBoxZModEquiv D n).symm x
  have hy : finBoxZModEquiv D n y = x := (finBoxZModEquiv D n).apply_symm_apply x
  have hpoint := congrArg (fun A : PhysicalGaugeOneCochain D n Nc => A (y, j)) heq
  have hp : sunComplexPlane hNc (torusBackwardDifference i f x) = 0 := by
    simpa [torusPhysicalEmbed, hy, Ne.symm hij] using hpoint.symm
  have hn := sunComplexPlane_norm_sq hNc (torusBackwardDifference i f x)
  have hzsq : ‖torusBackwardDifference i f x‖ ^ 2 = 0 := by
    rw [← hn, hp]
    simp
  have hz : ‖torusBackwardDifference i f x‖ = 0 := by nlinarith
  exact norm_eq_zero.mp hz
end ActualPhysical

section PositiveBand
variable {d n : ℕ} [NeZero n]

abbrev CoexactPositiveIndex (d R : ℕ) := Fin R × (Fin (d + 1) → Fin (2 * R + 1))

def coexactPositiveFourierIndex (R : ℕ) (k : CoexactPositiveIndex d R) :
    Fin (d + 2) → Fin (2 * R + 1) :=
  Fin.cons ⟨R + k.1.val + 1, by have := k.1.isLt; omega⟩ k.2

theorem coexactPositiveFourierIndex_injective (R : ℕ) :
    Function.Injective (coexactPositiveFourierIndex (d := d) R) := by
  intro k l h
  apply Prod.ext
  · apply Fin.ext
    have hh := congrArg Fin.val (congrFun h 0)
    change R + k.1.val + 1 = R + l.1.val + 1 at hh
    omega
  · funext i
    have hh := congrFun h i.succ
    simpa [coexactPositiveFourierIndex] using hh

noncomputable def coexactPositiveProfile (R : ℕ) (k : CoexactPositiveIndex d R) :
    (Fin (d + 2) → ZMod n) → ℂ :=
  centeredFourierProfile R (coexactPositiveFourierIndex R k)

theorem coexactPositiveProfiles_linearIndependent (R : ℕ) (hR : 2 * R < n) :
    LinearIndependent ℂ (coexactPositiveProfile (d := d) (n := n) R) :=
  (centeredFourierProfiles_linearIndependent (d := d + 2) R hR).comp _
    (coexactPositiveFourierIndex_injective R)

noncomputable def coexactPositiveScalarBand (d n R : ℕ) [NeZero n] :
    Submodule ℂ ((Fin (d + 2) → ZMod n) → ℂ) :=
  Submodule.span ℂ (Set.range (coexactPositiveProfile (d := d) (n := n) R))

theorem coexactPositiveScalarBand_finrank_complex (R : ℕ) (hR : 2 * R < n) :
    finrank ℂ (coexactPositiveScalarBand d n R) = R * (2 * R + 1) ^ (d + 1) := by
  rw [coexactPositiveScalarBand,
    finrank_span_eq_card (coexactPositiveProfiles_linearIndependent R hR)]
  simp [CoexactPositiveIndex]

theorem coexactPositiveScalarBand_finrank_real (R : ℕ) (hR : 2 * R < n) :
    finrank ℝ (coexactPositiveScalarBand d n R) = 2 * R * (2 * R + 1) ^ (d + 1) := by
  have h := Module.finrank_mul_finrank ℝ ℂ (coexactPositiveScalarBand d n R)
  have htwo : finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [htwo, coexactPositiveScalarBand_finrank_complex R hR] at h
  simpa only [Nat.mul_assoc] using h.symm

theorem coexactPositiveProfile_forward_difference (R : ℕ) (k : CoexactPositiveIndex d R)
    (a x : Fin (d + 2) → ZMod n) :
    coexactPositiveProfile R k (x + a) - coexactPositiveProfile R k x =
      (coexactPositiveProfile R k a - 1) * coexactPositiveProfile R k x :=
  character_forward_difference
    (torusFourierCharacter (centeredFourierFrequency R (coexactPositiveFourierIndex R k))) a x

theorem coexactPositiveProfile_first_multiplier_ne (R : ℕ) (hR : 2 * R < n)
    (k : CoexactPositiveIndex d R) :
    coexactPositiveProfile (n := n) R k (Pi.single 0 (1 : ZMod n)) - 1 ≠ 0 := by
  classical
  have heval : coexactPositiveProfile (n := n) R k (Pi.single 0 (1 : ZMod n)) =
      ZMod.stdAddChar (centeredFourierFrequency (n := n) R
        (coexactPositiveFourierIndex R k) (0 : Fin (d + 2))) := by
    simp [coexactPositiveProfile, centeredFourierProfile, torusFourierCharacter, Pi.single_apply]
  have hfreq : centeredFourierFrequency (n := n) R
      (coexactPositiveFourierIndex R k) (0 : Fin (d + 2)) =
      ((k.1.val + 1 : ℕ) : ZMod n) := by
    change (((R + k.1.val + 1 : ℕ) : ZMod n) - (R : ZMod n)) = _
    push_cast
    ring
  intro hz
  have hchar := sub_eq_zero.mp hz
  rw [heval, hfreq] at hchar
  have hzero : ((k.1.val + 1 : ℕ) : ZMod n) = 0 := by
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using hchar
  have hk : k.1.val + 1 < n := by have := k.1.isLt; omega
  have hh := congrArg ZMod.val hzero
  simp only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hk] at hh
  omega

theorem coexactPositiveScalarBand_backward_kernel (R : ℕ) (hR : 2 * R < n)
    (f : (Fin (d + 2) → ZMod n) → ℂ) (hf : f ∈ coexactPositiveScalarBand d n R)
    (hzero : torusBackwardDifference (0 : Fin (d + 2)) f = 0) : f = 0 := by
  classical
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf with ⟨c, hc⟩
  have hs : f = fun x => ∑ k, c k * coexactPositiveProfile R k x := by
    rw [← hc]
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let a : Fin (d + 2) → ZMod n := Pi.single 0 (1 : ZMod n)
  have hsum : (∑ k, (c k * (coexactPositiveProfile R k a - 1)) •
      coexactPositiveProfile (n := n) R k) = 0 := by
    funext x
    have hshift : f (x + a) - f x = 0 := by
      have hh := congrFun hzero (x + a)
      simpa [torusBackwardDifference_apply, a] using hh
    rw [hs] at hshift
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    calc
      _ = ∑ k, c k * (coexactPositiveProfile R k (x + a) - coexactPositiveProfile R k x) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [coexactPositiveProfile_forward_difference]
        ring
      _ = (∑ k, c k * coexactPositiveProfile R k (x + a)) -
          ∑ k, c k * coexactPositiveProfile R k x := by
        simp only [mul_sub, Finset.sum_sub_distrib]
      _ = 0 := hshift
  have hcoef := (Fintype.linearIndependent_iff.mp
    (coexactPositiveProfiles_linearIndependent (d := d) R hR)) _ hsum
  have hc0 : ∀ k, c k = 0 := by
    intro k
    exact (mul_eq_zero.mp (hcoef k)).resolve_right
      (coexactPositiveProfile_first_multiplier_ne R hR k)
  rw [hs]
  funext x
  simp [hc0]
end PositiveBand

section PhysicalBand
variable {d n Nc : ℕ} [NeZero n] [NeZero Nc]

noncomputable def coexactPositivePhysicalBandMap (hNc : 2 ≤ Nc) (R : ℕ) :
    coexactPositiveScalarBand d n R →ₗ[ℝ] PhysicalGaugeOneCochain (d + 2) n Nc where
  toFun f := coexactFlatMap hNc (0 : Fin (d + 2)) (Fin.succ (0 : Fin (d + 1))) f.val
  map_add' f g := (coexactFlatMap hNc (0 : Fin (d + 2))
    (Fin.succ (0 : Fin (d + 1)))).map_add f.val g.val
  map_smul' r f := (coexactFlatMap hNc (0 : Fin (d + 2))
    (Fin.succ (0 : Fin (d + 1)))).map_smul r f.val

theorem coexactPositivePhysicalBandMap_injective (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n) :
    Function.Injective (coexactPositivePhysicalBandMap (d := d) (n := n) hNc R) := by
  intro f g hfg
  have hsub : coexactFlatMap hNc (0 : Fin (d + 2)) (Fin.succ (0 : Fin (d + 1)))
      (f.val - g.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hfg
  have hback := coexactFlatMap_zero_backward hNc (0 : Fin (d + 2))
    (Fin.succ (0 : Fin (d + 1))) (by simp) (f.val - g.val) hsub
  have hz := coexactPositiveScalarBand_backward_kernel R hR (f.val - g.val)
    ((coexactPositiveScalarBand d n R).sub_mem f.property g.property) hback
  exact Subtype.ext (sub_eq_zero.mp hz)

noncomputable def coexactPositivePhysicalBand (hNc : 2 ≤ Nc) (R : ℕ) :
    Submodule ℝ (PhysicalGaugeOneCochain (d + 2) n Nc) :=
  LinearMap.range (coexactPositivePhysicalBandMap hNc R)

theorem coexactPositivePhysicalBand_finrank (hNc : 2 ≤ Nc) (R : ℕ) (hR : 2 * R < n) :
    finrank ℝ (coexactPositivePhysicalBand (d := d) (n := n) hNc R) =
      2 * R * (2 * R + 1) ^ (d + 1) := by
  rw [coexactPositivePhysicalBand,
    LinearMap.finrank_range_of_inj (coexactPositivePhysicalBandMap_injective hNc R hR),
    coexactPositiveScalarBand_finrank_real R hR]

theorem coexactPositivePhysicalBand_div_zero (hNc : 2 ≤ Nc) (rho : SUNAdjointModel Nc)
    (R : ℕ) (x : PhysicalGaugeOneCochain (d + 2) n Nc)
    (hx : x ∈ coexactPositivePhysicalBand hNc R) :
    gaugeConstraintQCLM rho (trivialPhysicalGaugeBackground (d + 2) n Nc) x = 0 := by
  rcases hx with ⟨f, rfl⟩
  exact coexactFlatMap_div_zero hNc rho _ _ f.val
end PhysicalBand
end YangMills.RG
