/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import YangMills.OS.SU2HeatTransport

/-!
# An exact two-mode intertwining for SU(2) heat transport

This module upgrades equality of one decay rate to a commuting operator
diagram.  The common coefficient space is the real span of the vacuum and
fundamental modes.  Its continuous lift is an injective Haar-isometric map
into actual functions on bundled `SU(2)`.  Its finite lift is a bijection onto
the Euclidean space of the two-state, genuinely `SU(2)`-inhabited witness.

For positive heat time, actual normalized-Haar convolution and the finite
Dobrushin transfer matrix both intertwine these lifts with the same diagonal
map `diag(1, exp (-3t/4))`.  No eigenvalue or intertwining identity is assumed.

Scope: this is an exact invariant two-mode class sector, not a claim about the
completed full `L²(SU(2))` spectrum.
-/

noncomputable section

namespace YangMills.OS.SU2HeatIntertwining

open Finset Matrix MeasureTheory
open scoped RealInnerProductSpace

abbrev SU2 := Lean2dYangMills.SU2
abbrev Carrier := Dobrushin.SU2Transport.Carrier

/-- The common real coefficient model: vacuum coefficient, then fundamental
coefficient. -/
abbrev Mode2 := ℝ × ℝ

/-- The exact two-mode diagonal heat step. -/
def spectralStep (t : ℝ) (a : Mode2) : Mode2 :=
  (a.1, Dobrushin.SU2Transport.heatRate t * a.2)

/-- Lift two real coefficients to an actual complex-valued class function on
bundled `SU(2)`. -/
def continuousLift (a : Mode2) (g : SU2) : ℂ :=
  (a.1 : ℂ) * Lean2dYangMills.su2CharacterChebyshev 0 g +
    (a.2 : ℂ) * Lean2dYangMills.su2CharacterChebyshev 1 g

/-- Actual normalized-Haar convolution by the infinite SU(2) heat kernel. -/
def heatOperator (t : ℝ) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  Lean2dYangMills.su2Convolution (Lean2dYangMills.su2HeatKernel t) f g

/-- The sign coordinate of the finite carrier. -/
def carrierSign (x : Carrier) : ℝ := if x.1 = 0 then 1 else -1

/-- Lift the same coefficients to the finite Euclidean transfer space. -/
def finiteLift (a : Mode2) : EuclideanSpace ℝ Carrier :=
  WithLp.toLp 2 fun x => a.1 + a.2 * carrierSign x

@[simp] theorem character_zero (g : SU2) :
    Lean2dYangMills.su2CharacterChebyshev 0 g = 1 := by
  simp [Lean2dYangMills.su2CharacterChebyshev]

@[simp] theorem fundamental_at_phase :
    Lean2dYangMills.su2CharacterChebyshev 1
      Dobrushin.SU2Transport.phaseHolonomy = 0 := by
  rw [Lean2dYangMills.su2FundamentalCharacter_eq_two_mul_re]
  simp [Dobrushin.SU2Transport.phaseHolonomy,
    YangMills.ClayCore.twoSiteSU_val, YangMills.ClayCore.twoSitePhase,
    YangMills.ClayCore.twoSiteVec]

@[simp] theorem continuousLift_at_one (a : Mode2) :
    continuousLift a (1 : SU2) = (a.1 : ℂ) + 2 * (a.2 : ℂ) := by
  simp [continuousLift, SU2HeatTransport.fundamental_character_at_one]
  ring

@[simp] theorem continuousLift_at_phase (a : Mode2) :
    continuousLift a Dobrushin.SU2Transport.phaseHolonomy = (a.1 : ℂ) := by
  simp [continuousLift]

/-- Exact non-vacuity of the continuous embedding. -/
theorem continuousLift_injective : Function.Injective continuousLift := by
  intro a b hab
  have hp := congrFun hab Dobrushin.SU2Transport.phaseHolonomy
  have h1 := congrFun hab (1 : SU2)
  simp only [continuousLift_at_phase] at hp
  simp only [continuousLift_at_one] at h1
  have ha0 : a.1 = b.1 := by exact_mod_cast hp
  have ha1 : a.2 = b.2 := by
    rw [ha0] at h1
    norm_num at h1
    exact_mod_cast h1
  exact Prod.ext ha0 ha1

@[simp] theorem finiteLift_zero (a : Mode2) :
    finiteLift a (Dobrushin.SU2Transport.carrierEquiv 0) = a.1 + a.2 := by
  simp [finiteLift, carrierSign]

@[simp] theorem finiteLift_one (a : Mode2) :
    finiteLift a (Dobrushin.SU2Transport.carrierEquiv 1) = a.1 - a.2 := by
  simp [finiteLift, carrierSign]
  ring

theorem finiteLift_injective : Function.Injective finiteLift := by
  intro a b hab
  have h0 := congrArg
    (fun v : EuclideanSpace ℝ Carrier =>
      v (Dobrushin.SU2Transport.carrierEquiv 0)) hab
  have h1 := congrArg
    (fun v : EuclideanSpace ℝ Carrier =>
      v (Dobrushin.SU2Transport.carrierEquiv 1)) hab
  simp only [finiteLift_zero] at h0
  simp only [finiteLift_one] at h1
  apply Prod.ext <;> dsimp
  · linarith
  · linarith

theorem finiteLift_surjective : Function.Surjective finiteLift := by
  intro v
  let a : Mode2 :=
    ((v (Dobrushin.SU2Transport.carrierEquiv 0) +
        v (Dobrushin.SU2Transport.carrierEquiv 1)) / 2,
      (v (Dobrushin.SU2Transport.carrierEquiv 0) -
        v (Dobrushin.SU2Transport.carrierEquiv 1)) / 2)
  refine ⟨a, PiLp.ext fun x => ?_⟩
  have hx : x = Dobrushin.SU2Transport.carrierEquiv x.1 := by
    apply Dobrushin.SU2Transport.Carrier.ext
    simp
  have hi : x.1 = 0 ∨ x.1 = 1 := by omega
  rcases hi with hi | hi
  · have hx0 : x = Dobrushin.SU2Transport.carrierEquiv 0 := by
      apply Dobrushin.SU2Transport.Carrier.ext
      simpa using hi
    subst x
    simp [a]
    ring
  · have hx1 : x = Dobrushin.SU2Transport.carrierEquiv 1 := by
      apply Dobrushin.SU2Transport.Carrier.ext
      simpa using hi
    subst x
    simp [a]
    ring

theorem finiteLift_bijective : Function.Bijective finiteLift :=
  ⟨finiteLift_injective, finiteLift_surjective⟩

@[simp] theorem finiteLift_fundamental :
    finiteLift (0, 1) = Dobrushin.SU2Transport.signVector := by
  apply PiLp.ext
  intro x
  simp [finiteLift, carrierSign, Dobrushin.SU2Transport.signVector]

/-- Exact Haar pairing on the continuous two-mode sector.  Thus the lift is
an isometry for the real coefficient inner product, expressed in `ℂ`. -/
theorem continuousLift_haar_pairing (a b : Mode2) :
    (∫ g : SU2, continuousLift a g * continuousLift b g
      ∂Lean2dYangMills.su2HaarProb) =
      ((a.1 * b.1 + a.2 * b.2 : ℝ) : ℂ) := by
  have hint (n m : ℕ) : Integrable
      (fun g : SU2 =>
        Lean2dYangMills.su2CharacterChebyshev n g *
          Lean2dYangMills.su2CharacterChebyshev m g)
      Lean2dYangMills.su2HaarProb := by
    apply Lean2dYangMills.integrable_continuous_su2Haar
    exact (Lean2dYangMills.continuous_su2CharacterChebyshev n).mul
      (Lean2dYangMills.continuous_su2CharacterChebyshev m)
  let f00 : SU2 → ℂ := fun g => ((a.1 * b.1 : ℝ) : ℂ) *
    (Lean2dYangMills.su2CharacterChebyshev 0 g *
      Lean2dYangMills.su2CharacterChebyshev 0 g)
  let f01 : SU2 → ℂ := fun g => ((a.1 * b.2 : ℝ) : ℂ) *
    (Lean2dYangMills.su2CharacterChebyshev 0 g *
      Lean2dYangMills.su2CharacterChebyshev 1 g)
  let f10 : SU2 → ℂ := fun g => ((a.2 * b.1 : ℝ) : ℂ) *
    (Lean2dYangMills.su2CharacterChebyshev 1 g *
      Lean2dYangMills.su2CharacterChebyshev 0 g)
  let f11 : SU2 → ℂ := fun g => ((a.2 * b.2 : ℝ) : ℂ) *
    (Lean2dYangMills.su2CharacterChebyshev 1 g *
      Lean2dYangMills.su2CharacterChebyshev 1 g)
  have hf00 : Integrable f00 Lean2dYangMills.su2HaarProb :=
    (hint 0 0).const_mul _
  have hf01 : Integrable f01 Lean2dYangMills.su2HaarProb :=
    (hint 0 1).const_mul _
  have hf10 : Integrable f10 Lean2dYangMills.su2HaarProb :=
    (hint 1 0).const_mul _
  have hf11 : Integrable f11 Lean2dYangMills.su2HaarProb :=
    (hint 1 1).const_mul _
  have hI00 :
      (∫ g : SU2, f00 g ∂Lean2dYangMills.su2HaarProb) =
        ((a.1 * b.1 : ℝ) : ℂ) *
          (∫ g : SU2,
            Lean2dYangMills.su2CharacterChebyshev 0 g *
              Lean2dYangMills.su2CharacterChebyshev 0 g
            ∂Lean2dYangMills.su2HaarProb) := by
    dsimp [f00]
    exact MeasureTheory.integral_const_mul _ _
  have hI01 :
      (∫ g : SU2, f01 g ∂Lean2dYangMills.su2HaarProb) =
        ((a.1 * b.2 : ℝ) : ℂ) *
          (∫ g : SU2,
            Lean2dYangMills.su2CharacterChebyshev 0 g *
              Lean2dYangMills.su2CharacterChebyshev 1 g
            ∂Lean2dYangMills.su2HaarProb) := by
    dsimp [f01]
    exact MeasureTheory.integral_const_mul _ _
  have hI10 :
      (∫ g : SU2, f10 g ∂Lean2dYangMills.su2HaarProb) =
        ((a.2 * b.1 : ℝ) : ℂ) *
          (∫ g : SU2,
            Lean2dYangMills.su2CharacterChebyshev 1 g *
              Lean2dYangMills.su2CharacterChebyshev 0 g
            ∂Lean2dYangMills.su2HaarProb) := by
    dsimp [f10]
    exact MeasureTheory.integral_const_mul _ _
  have hI11 :
      (∫ g : SU2, f11 g ∂Lean2dYangMills.su2HaarProb) =
        ((a.2 * b.2 : ℝ) : ℂ) *
          (∫ g : SU2,
            Lean2dYangMills.su2CharacterChebyshev 1 g *
              Lean2dYangMills.su2CharacterChebyshev 1 g
            ∂Lean2dYangMills.su2HaarProb) := by
    dsimp [f11]
    exact MeasureTheory.integral_const_mul _ _
  rw [show (fun g : SU2 => continuousLift a g * continuousLift b g) =
      fun g => ((f00 g + f01 g) + f10 g) + f11 g by
        funext g
        simp [continuousLift, f00, f01, f10, f11]
        ring]
  calc
    (∫ g : SU2, ((f00 g + f01 g) + f10 g) + f11 g
        ∂Lean2dYangMills.su2HaarProb) =
        (∫ g : SU2, (f00 g + f01 g) + f10 g
          ∂Lean2dYangMills.su2HaarProb) +
        (∫ g : SU2, f11 g ∂Lean2dYangMills.su2HaarProb) :=
      MeasureTheory.integral_add ((hf00.add hf01).add hf10) hf11
    _ = ((∫ g : SU2, f00 g ∂Lean2dYangMills.su2HaarProb) +
          (∫ g : SU2, f01 g ∂Lean2dYangMills.su2HaarProb) +
          (∫ g : SU2, f10 g ∂Lean2dYangMills.su2HaarProb)) +
        (∫ g : SU2, f11 g ∂Lean2dYangMills.su2HaarProb) := by
      have htri :
          (∫ g : SU2, (f00 g + f01 g) + f10 g
            ∂Lean2dYangMills.su2HaarProb) =
            (∫ g : SU2, f00 g ∂Lean2dYangMills.su2HaarProb) +
            (∫ g : SU2, f01 g ∂Lean2dYangMills.su2HaarProb) +
            (∫ g : SU2, f10 g ∂Lean2dYangMills.su2HaarProb) := by
        calc
          (∫ g : SU2, (f00 g + f01 g) + f10 g
              ∂Lean2dYangMills.su2HaarProb) =
              (∫ g : SU2, f00 g + f01 g
                ∂Lean2dYangMills.su2HaarProb) +
              (∫ g : SU2, f10 g ∂Lean2dYangMills.su2HaarProb) :=
            MeasureTheory.integral_add (hf00.add hf01) hf10
          _ = _ := by
            rw [MeasureTheory.integral_add hf00 hf01]
      exact congrArg
        (fun z : ℂ => z +
          (∫ g : SU2, f11 g ∂Lean2dYangMills.su2HaarProb)) htri
    _ = _ := by
      rw [hI00, hI01, hI10, hI11]
      rw [Lean2dYangMills.integral_su2CharacterChebyshev_mul,
        Lean2dYangMills.integral_su2CharacterChebyshev_mul,
        Lean2dYangMills.integral_su2CharacterChebyshev_mul,
        Lean2dYangMills.integral_su2CharacterChebyshev_mul]
      norm_num

/-- Integrability of the actual infinite heat kernel against a translated
character.  It is proved by the same finite-partial dominated convergence
used for the infinite eigenmode theorem. -/
theorem integrable_heatKernel_mul_character {t : ℝ} (ht : 0 < t)
    (m : ℕ) (g : SU2) : Integrable
      (fun x : SU2 => Lean2dYangMills.su2HeatKernel t x *
        Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g))
      Lean2dYangMills.su2HaarProb := by
  let M : ℝ := ∑' n, Lean2dYangMills.su2HeatKernelMajorant t n
  let F : ℕ → SU2 → ℂ := fun N x =>
    Lean2dYangMills.su2HeatKernelPartial N t x *
      Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g)
  have hmeas (N : ℕ) : AEStronglyMeasurable (F N)
      Lean2dYangMills.su2HaarProb := by
    exact ((Lean2dYangMills.continuous_su2HeatKernelPartial N t).mul
      ((Lean2dYangMills.continuous_su2CharacterChebyshev m).comp <| by
        fun_prop)).aestronglyMeasurable
  have hM : 0 ≤ M := tsum_nonneg fun _ => by
    unfold Lean2dYangMills.su2HeatKernelMajorant
    positivity
  have hbound (N : ℕ) (x : SU2) :
      ‖F N x‖ ≤ M * ((m : ℝ) + 1) := by
    dsimp [F]
    rw [norm_mul]
    exact mul_le_mul
      (Lean2dYangMills.norm_su2HeatKernelPartial_le_tsum_majorant ht N x)
      (Lean2dYangMills.abs_su2CharacterChebyshev_le m (x⁻¹ * g))
      (norm_nonneg _) hM
  have hlim (x : SU2) :
      Filter.Tendsto (fun N => F N x) Filter.atTop
        (nhds (Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g))) := by
    exact (Lean2dYangMills.tendsto_su2HeatKernelPartial ht x).mul
      tendsto_const_nhds
  have hlimitmeas : AEStronglyMeasurable
      (fun x : SU2 => Lean2dYangMills.su2HeatKernel t x *
        Lean2dYangMills.su2CharacterChebyshev m (x⁻¹ * g))
      Lean2dYangMills.su2HaarProb := by
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hmeas
      (ae_of_all _ hlim)
  apply Integrable.of_bound hlimitmeas (M * ((m : ℝ) + 1))
  exact ae_of_all _ fun x =>
    le_of_tendsto (hlim x).norm (Filter.Eventually.of_forall fun N => hbound N x)

/-- The continuous side of the commuting diagram: actual Haar heat
convolution restricts to the two-mode sector and is conjugate to
`spectralStep` through the injective lift. -/
theorem heatOperator_continuousLift {t : ℝ} (ht : 0 < t) (a : Mode2) :
    heatOperator t (continuousLift a) = continuousLift (spectralStep t a) := by
  funext g
  rw [heatOperator, Lean2dYangMills.su2Convolution]
  change (∫ x : SU2,
    Lean2dYangMills.su2HeatKernel t x *
      ((a.1 : ℂ) * Lean2dYangMills.su2CharacterChebyshev 0 (x⁻¹ * g) +
       (a.2 : ℂ) * Lean2dYangMills.su2CharacterChebyshev 1 (x⁻¹ * g))
    ∂Lean2dYangMills.su2HaarProb) = _
  rw [show (fun x : SU2 =>
      Lean2dYangMills.su2HeatKernel t x *
        ((a.1 : ℂ) * Lean2dYangMills.su2CharacterChebyshev 0 (x⁻¹ * g) +
         (a.2 : ℂ) * Lean2dYangMills.su2CharacterChebyshev 1 (x⁻¹ * g))) =
      fun x =>
        (a.1 : ℂ) * (Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev 0 (x⁻¹ * g)) +
        (a.2 : ℂ) * (Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev 1 (x⁻¹ * g)) by
        funext x
        ring]
  rw [MeasureTheory.integral_add
      ((integrable_heatKernel_mul_character ht 0 g).const_mul _)
      ((integrable_heatKernel_mul_character ht 1 g).const_mul _)]
  have hmul0 :
      (∫ x : SU2, (a.1 : ℂ) *
        (Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev 0 (x⁻¹ * g))
        ∂Lean2dYangMills.su2HaarProb) =
      (a.1 : ℂ) * (∫ x : SU2,
        Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev 0 (x⁻¹ * g)
        ∂Lean2dYangMills.su2HaarProb) :=
    MeasureTheory.integral_const_mul _ _
  have hmul1 :
      (∫ x : SU2, (a.2 : ℂ) *
        (Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev 1 (x⁻¹ * g))
        ∂Lean2dYangMills.su2HaarProb) =
      (a.2 : ℂ) * (∫ x : SU2,
        Lean2dYangMills.su2HeatKernel t x *
          Lean2dYangMills.su2CharacterChebyshev 1 (x⁻¹ * g)
        ∂Lean2dYangMills.su2HaarProb) :=
    MeasureTheory.integral_const_mul _ _
  rw [hmul0, hmul1]
  change (a.1 : ℂ) *
      Lean2dYangMills.su2Convolution (Lean2dYangMills.su2HeatKernel t)
        (Lean2dYangMills.su2CharacterChebyshev 0) g +
    (a.2 : ℂ) *
      Lean2dYangMills.su2Convolution (Lean2dYangMills.su2HeatKernel t)
        (Lean2dYangMills.su2CharacterChebyshev 1) g = _
  rw [SU2HeatTransport.heatKernel_character_eigen ht 0 g,
    SU2HeatTransport.heatKernel_character_eigen ht 1 g,
    SU2HeatTransport.classHeatWeight_eq_modeRate,
    SU2HeatTransport.classHeatWeight_eq_modeRate,
    SU2HeatTransport.modeRate_zero, SU2HeatTransport.modeRate_one]
  simp [continuousLift, spectralStep, Dobrushin.SU2Transport.heatRate]
  ring

/-- The finite side of the commuting diagram: the exact witness transfer
matrix is conjugate to the same diagonal step through a bijective lift. -/
theorem finiteOperator_finiteLift (t : ℝ) (a : Mode2) :
    Dobrushin.opOf
        (Dobrushin.SU2Transport.kernel
          (Dobrushin.SU2Transport.heatRate t)) (finiteLift a) =
      finiteLift (spectralStep t a) := by
  apply PiLp.ext
  intro x
  rw [Dobrushin.opOf_apply, Dobrushin.SU2Transport.sum_carrier]
  have hx : x = Dobrushin.SU2Transport.carrierEquiv x.1 := by
    apply Dobrushin.SU2Transport.Carrier.ext
    simp
  have hi : x.1 = 0 ∨ x.1 = 1 := by omega
  rcases hi with hi | hi
  · have hx0 : x = Dobrushin.SU2Transport.carrierEquiv 0 := by
      apply Dobrushin.SU2Transport.Carrier.ext
      simpa using hi
    subst x
    simp [Dobrushin.SU2Transport.kernel, Dobrushin.wKernel,
      spectralStep]
    ring
  · have hx1 : x = Dobrushin.SU2Transport.carrierEquiv 1 := by
      apply Dobrushin.SU2Transport.Carrier.ext
      simpa using hi
    subst x
    simp [Dobrushin.SU2Transport.kernel, Dobrushin.wKernel,
      spectralStep]
    ring

/-- Published endpoint of the upgrade: a genuine injective continuous
restriction, a full finite conjugacy, and both exact commuting identities. -/
theorem exact_two_mode_intertwining {t : ℝ} (ht : 0 < t) :
    Function.Injective continuousLift ∧
    Function.Bijective finiteLift ∧
    (∀ a : Mode2,
      heatOperator t (continuousLift a) = continuousLift (spectralStep t a)) ∧
    (∀ a : Mode2,
      Dobrushin.opOf
          (Dobrushin.SU2Transport.kernel
            (Dobrushin.SU2Transport.heatRate t)) (finiteLift a) =
        finiteLift (spectralStep t a)) := by
  exact ⟨continuousLift_injective, finiteLift_bijective,
    heatOperator_continuousLift ht, finiteOperator_finiteLift t⟩

end YangMills.OS.SU2HeatIntertwining

end
