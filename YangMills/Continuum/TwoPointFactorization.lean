/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.Continuum.Example
import YangMills.L1_GibbsMeasure.ThermodynamicCorrelation
import YangMills.RG.ConcreteGaugeRGFidelity

/-!
# A genuine scale-varying two-plaquette sector

The thermodynamic-volume index and the lattice-spacing index are kept
strictly separate here.  For a fixed scale index `m`, the second plaquette is
at the fixed integer coordinate `2m`.  The volume is then sent to infinity
inside `infiniteLocalGibbsStateValue`; only after that constructed state
exists is `m → ∞` taken.

The canonical pair has exact touch-graph distance `2m` once the thermodynamic
torus is large enough.  Thus the repository's infinite-volume exponential
clustering theorem applies with `k = m`.  This file does not identify the
result with continuum Yang--Mills; it proves that the accessible fixed
strong-coupling two-point sector factorizes.
-/

namespace YangMills.Continuum

open Filter MeasureTheory Topology
open YangMills WindowPolymer GaugeConfig

universe u

variable {d : ℕ} [NeZero d]
variable {G : Type u} [Group G] [MeasurableSpace G]

private abbrev axisDir0 (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩
private abbrev axisDir1 (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

private abbrev axisSite (hd : 2 ≤ d) (τ : ℕ) : Fin d → ℕ :=
  fun j => if j = axisDir0 hd then τ else 0

private def axisPlaquetteCoord
    (hd : 2 ≤ d) (τ : ℕ) : Fin 4 → (Fin d → ℕ) × Fin d
  | ⟨0, _⟩ => ⟨axisSite hd τ, axisDir0 hd⟩
  | ⟨1, _⟩ =>
      ⟨fun j => axisSite hd τ j + if j = axisDir0 hd then 1 else 0,
        axisDir1 hd⟩
  | ⟨2, _⟩ =>
      ⟨fun j => axisSite hd τ j + if j = axisDir1 hd then 1 else 0,
        axisDir0 hd⟩
  | ⟨3, _⟩ => ⟨axisSite hd τ, axisDir1 hd⟩

private theorem axisPlaquetteCoord_injective
    (hd : 2 ≤ d) (τ : ℕ) :
    Function.Injective (axisPlaquetteCoord hd τ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [axisPlaquetteCoord] at hij ⊢
  all_goals
    exfalso
    have hcode := congrArg (fun c =>
      (c.2.val, c.1 (axisDir0 hd), c.1 (axisDir1 hd))) hij
    norm_num [axisDir0, axisDir1, axisSite] at hcode

/-- The bounded plaquette function at the natural-coordinate axis site
`τ e₀`. -/
noncomputable def axisPlaquetteObservable
    [MeasurableMul₂ G] [MeasurableInv G]
    (hd : 2 ≤ d) (τ : ℕ)
    (f : G → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ g, |f g| ≤ C) :
    CompatibleLocalObservable d G where
  Support := Fin 4
  coord := axisPlaquetteCoord hd τ
  coord_injective := axisPlaquetteCoord_injective hd τ
  minVolume := τ + 1
  coord_lt := by
    intro s j
    fin_cases s <;>
      simp only [axisPlaquetteCoord, axisSite]
    all_goals
      split_ifs <;> omega
  kernel := fun x => f (x 0 * x 1 * (x 2)⁻¹ * (x 3)⁻¹)
  kernel_measurable := by fun_prop
  bound := C
  bound_nonneg := hC
  kernel_bound := fun x => hfC _

/-- Declared physical separation of the canonical pair at scale `k`. -/
noncomputable def axisPairPhysicalSeparation
    (scale : ScaleSequence) (k : ℕ) : ℝ :=
  scale.spacing k * (2 * k : ℕ)

/-- With the explicit reciprocal spacing, the offset `2k` represents a
macroscopic separation tending to `2`.  This is a C0 scale convention only;
it is not identified with the repository's RG spacing convention. -/
theorem tendsto_axisPairPhysicalSeparation_reciprocal :
    Tendsto
      (axisPairPhysicalSeparation reciprocalScale)
      atTop (𝓝 2) := by
  have hzero :
      Tendsto (fun k => 2 * reciprocalScale.spacing k)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using reciprocalScale.tendsToZero.const_mul 2
  have h :=
    (tendsto_const_nhds.sub hzero :
      Tendsto (fun k => 2 - 2 * reciprocalScale.spacing k)
        atTop (𝓝 (2 - 0)))
  have heq :
      (fun k => 2 - 2 * reciprocalScale.spacing k) =ᶠ[atTop]
        axisPairPhysicalSeparation reciprocalScale :=
    Eventually.of_forall fun k => by
      simp only [axisPairPhysicalSeparation, reciprocalScale,
        Nat.cast_mul, Nat.cast_ofNat]
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hk]
      ring
  simpa only [sub_zero] using h.congr' heq

set_option maxRecDepth 10000

/-- The four positive edges used by the abstract axis observable are exactly
the positive representatives of the canonical concrete plaquette edges. -/
theorem axisPlaquetteObservable_edgeAt
    [MeasurableMul₂ G] [MeasurableInv G]
    (hd : 2 ≤ d) (τ n : ℕ)
    (f : G → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ g, |f g| ≤ C)
    (hn : τ + 1 ≤ n) (s : Fin 4) :
    ((axisPlaquetteObservable hd τ f hf C hC hfC).edgeAt n hn s).1 =
      { ((RG.canonicalPlaquette d (n + 1) hd τ).edges s) with
        sign := true } := by
  simp only [CompatibleLocalObservable.edgeAt,
    axisPlaquetteObservable, axisPlaquetteCoord, axisSite]
  simp only [ConcreteEdge.mk.injEq]
  constructor
  · funext j
    apply Fin.ext
    fin_cases s <;>
      simp only [ConcretePlaquette.edges, RG.canonicalPlaquette,
        FinBox.shift]
    all_goals
      by_cases hj0 : j = axisDir0 hd
      · rw [hj0]
        simp [axisDir0, axisDir1, axisSite]
      · by_cases hj1 : j = axisDir1 hd
        · rw [hj1]
          simp [axisDir0, axisDir1, axisSite]
        · simp only [axisDir0, axisDir1] at hj0 hj1 ⊢
          simp only [axisSite, if_neg hj0, if_neg hj1]
          simp
  · constructor
    · fin_cases s <;>
        simp [RG.canonicalPlaquette, ConcretePlaquette.edges,
          axisDir0, axisDir1]
    · simp

set_option maxRecDepth 1000

/-- At every admissible thermodynamic volume, the axis observable literally
reads the canonical plaquette at offset `τ`. -/
theorem axisPlaquetteObservable_realize
    [MeasurableMul₂ G] [MeasurableInv G]
    (hd : 2 ≤ d) (τ n : ℕ)
    (f : G → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ g, |f g| ≤ C)
    (hn : τ + 1 ≤ n)
    (A : GaugeConfig d (n + 1) G) :
    (axisPlaquetteObservable hd τ f hf C hC hfC).realize n A =
      f (plaquetteHolonomy A
        (RG.canonicalPlaquette d (n + 1) hd τ)) := by
  let O := axisPlaquetteObservable hd τ f hf C hC hfC
  let p := RG.canonicalPlaquette d (n + 1) hd τ
  change O.realize n A = f (plaquetteHolonomy A p)
  have hnO : O.minVolume ≤ n := by
    simpa [O, axisPlaquetteObservable] using hn
  rw [CompatibleLocalObservable.realize, dif_pos hnO]
  dsimp only [O, axisPlaquetteObservable]
  change f (
      configToPos A
          ((axisPlaquetteObservable hd τ f hf C hC hfC).edgeAt n hn
            (show (axisPlaquetteObservable hd τ f hf C hC hfC).Support
              from (0 : Fin 4))) *
      configToPos A
          ((axisPlaquetteObservable hd τ f hf C hC hfC).edgeAt n hn
            (show (axisPlaquetteObservable hd τ f hf C hC hfC).Support
              from (1 : Fin 4))) *
      (configToPos A
          ((axisPlaquetteObservable hd τ f hf C hC hfC).edgeAt n hn
            (show (axisPlaquetteObservable hd τ f hf C hC hfC).Support
              from (2 : Fin 4))))⁻¹ *
      (configToPos A
          ((axisPlaquetteObservable hd τ f hf C hC hfC).edgeAt n hn
            (show (axisPlaquetteObservable hd τ f hf C hC hfC).Support
              from (3 : Fin 4))))⁻¹) =
    f (plaquetteHolonomy A p)
  simp only [configToPos]
  rw [axisPlaquetteObservable_edgeAt hd τ n f hf C hC hfC hn 0,
    axisPlaquetteObservable_edgeAt hd τ n f hf C hC hfC hn 1,
    axisPlaquetteObservable_edgeAt hd τ n f hf C hC hfC hn 2,
    axisPlaquetteObservable_edgeAt hd τ n f hf C hC hfC hn 3]
  unfold GaugeConfig.plaquetteHolonomy
  change _ =
    f (A (p.edges 0) * A (p.edges 1) *
      A (p.edges 2) * A (p.edges 3))
  rw [config_apply_neg A (p.edges 2) rfl,
    config_apply_neg A (p.edges 3) rfl]
  rfl

/-- Fixed-scale application of the repository's infinite-volume clustering
bound to the canonical pair at offsets `0` and `2k`.  The volume limit is
entirely internal to the two `CompatibleLocalObservable`s. -/
theorem abs_infiniteTruncatedCorrelation_axisPair_le
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (hd : 2 ≤ d)
    (f : G → ℝ) (hfm : Measurable f) (hf : ∀ x, |f x| ≤ 1)
    {s : ℝ} (hs0 : 0 < s)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ t)
    (k : ℕ) (hk : 1 ≤ k)
    (hone : 4 * Real.exp (-(ε * k)) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ 1) :
    |infiniteLocalGibbsTruncatedCorrelation μ hpe_meas hpe κ
        (axisPlaquetteObservable hd 0 f hfm 1 (by norm_num) hf)
        (axisPlaquetteObservable hd (2 * k) f hfm 1 (by norm_num) hf)|
      ≤ (8 * ((((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (((Real.exp (|β| * B) - 1) + s +
              (Real.exp (|β| * B) - 1) * s) *
              Real.exp (t + ε + 1)))) *
          (1 + s) ^ 2 / s ^ 2) *
        Real.exp (-(ε * k)) := by
  apply abs_infiniteLocalGibbsTruncatedCorrelation_le_twoPlaquette
    μ hpe_meas hpe κ _ _ hfm hf hs0 t ε ht0 hε0 hr hsmall k hone
  filter_upwards
    [eventually_ge_atTop (2 * k + 1),
      eventually_ge_atTop (4 * k)] with n hn htorus
  let p := RG.canonicalPlaquette d (n + 1) hd 0
  let q := RG.canonicalPlaquette d (n + 1) hd (2 * k)
  refine ⟨p, q, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [p, q]
    apply RG.canonicalPlaquette_ne hd
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  · dsimp only [p, q]
    rw [RG.canonicalPlaquette_dist_eq hd (by omega)]
  · simp [axisPlaquetteObservable]
    omega
  · intro A
    exact axisPlaquetteObservable_realize hd 0 n f hfm 1
      (by norm_num) hf (by omega) A
  · intro A
    exact axisPlaquetteObservable_realize hd (2 * k) n f hfm 1
      (by norm_num) hf hn A

/-- The separation-indexed connected two-point function tends to zero.  The
second observable moves from lattice offset `2k`.  The separate theorem
`tendsto_axisPairPhysicalSeparation_reciprocal` proves that this offset has
limiting physical separation `2` for C0's reciprocal spacing; no RG
scale-convention compatibility is inferred. -/
theorem tendsto_infiniteTruncatedCorrelation_axisPair_zero
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (hd : 2 ≤ d)
    (f : G → ℝ) (hfm : Measurable f) (hf : ∀ x, |f x| ≤ 1)
    {s : ℝ} (hs0 : 0 < s)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε : 0 < ε)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) < 1)
    (hsmall : ((16 * d : ℕ) : ℝ) *
      ((((Real.exp (|β| * B) - 1) + s +
        (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|β| * B) - 1) + s +
            (Real.exp (|β| * B) - 1) * s) *
            Real.exp (t + ε + 1)))) ≤ t) :
    Tendsto
      (fun k : ℕ =>
        infiniteLocalGibbsTruncatedCorrelation μ hpe_meas hpe κ
          (axisPlaquetteObservable hd 0 f hfm 1 (by norm_num) hf)
          (axisPlaquetteObservable hd (2 * k) f hfm 1 (by norm_num) hf))
      atTop (𝓝 0) := by
  let Q : ℝ :=
    (((Real.exp (|β| * B) - 1) + s +
      (Real.exp (|β| * B) - 1) * s) * Real.exp (t + ε + 1)) /
      (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
        (((Real.exp (|β| * B) - 1) + s +
          (Real.exp (|β| * B) - 1) * s) *
          Real.exp (t + ε + 1)))
  let C : ℝ := 8 * Q * (1 + s) ^ 2 / s ^ 2
  have hExp :
      Tendsto (fun k : ℕ => Real.exp (-(ε * (k : ℝ))))
        atTop (𝓝 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
  have hExpC :
      Tendsto (fun k : ℕ => C * Real.exp (-(ε * (k : ℝ))))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using hExp.const_mul C
  have hExpQ :
      Tendsto (fun k : ℕ => 4 * Real.exp (-(ε * (k : ℝ))) * Q)
        atTop (𝓝 0) := by
    have hh :
        Tendsto (fun k : ℕ => (4 * Q) * Real.exp (-(ε * (k : ℝ))))
          atTop (𝓝 0) := by
      simpa only [mul_zero] using hExp.const_mul (4 * Q)
    exact hh.congr' (Eventually.of_forall fun k => by ring)
  have hhone :
      ∀ᶠ k : ℕ in atTop,
        4 * Real.exp (-(ε * (k : ℝ))) * Q ≤ 1 := by
    exact ((tendsto_order.1 hExpQ).2 1 (by norm_num)).mono
      fun _ hk => hk.le
  have hbound :
      ∀ᶠ k : ℕ in atTop,
        |infiniteLocalGibbsTruncatedCorrelation μ hpe_meas hpe κ
          (axisPlaquetteObservable hd 0 f hfm 1 (by norm_num) hf)
          (axisPlaquetteObservable hd (2 * k) f hfm 1 (by norm_num) hf)|
          ≤ C * Real.exp (-(ε * (k : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1, hhone] with k hk hkone
    simpa [Q, C] using
      abs_infiniteTruncatedCorrelation_axisPair_le
        μ hpe_meas hpe κ hd f hfm hf hs0 t ε ht0 hε.le
        hr hsmall k hk (by simpa [Q] using hkone)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hExpC

/-! ## Fully discharged four-dimensional SU(2) example -/

/-- The physical plaquette energy normalized to the unit bound required by
the two-plaquette correlation theorem. -/
noncomputable def normalizedSU2PlaquetteEnergy (g : SU2GaugeGroup) : ℝ :=
  su2FundamentalPlaquetteEnergy g / 2

theorem measurable_normalizedSU2PlaquetteEnergy :
    Measurable normalizedSU2PlaquetteEnergy := by
  exact measurable_su2FundamentalPlaquetteEnergy.div_const 2

theorem normalizedSU2PlaquetteEnergy_abs_le_one
    (g : SU2GaugeGroup) :
    |normalizedSU2PlaquetteEnergy g| ≤ 1 := by
  rw [normalizedSU2PlaquetteEnergy, abs_div]
  norm_num
  nlinarith [su2FundamentalPlaquetteEnergy_bounded g]

private theorem exp_fifty_one_fiftieth_le_nine :
    Real.exp (51 / 50 : ℝ) ≤ 9 := by
  calc
    Real.exp (51 / 50 : ℝ) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (by norm_num)
    _ = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    _ ≤ 3 * 3 := by
      exact mul_le_mul Real.exp_one_lt_three.le
        Real.exp_one_lt_three.le (Real.exp_pos _).le (by norm_num)
    _ = 9 := by norm_num

private theorem exampleD4_activity_le_four :
    Real.exp (|exampleD4Coupling| * 2) - 1 ≤
      4 * exampleD4Coupling := by
  have hβ0 : 0 ≤ exampleD4Coupling := exampleD4Coupling_pos.le
  have hx0 : 0 ≤ |exampleD4Coupling| * 2 := by positivity
  have hx1 : |(|exampleD4Coupling| * 2)| ≤ 1 := by
    rw [abs_of_nonneg hx0, abs_of_nonneg hβ0]
    norm_num [exampleD4Coupling, explicitStrongCouplingRadiusD4]
  have hy0 : 0 ≤ Real.exp (|exampleD4Coupling| * 2) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hx0
  have h := Real.abs_exp_sub_one_le
    (x := |exampleD4Coupling| * 2) hx1
  rw [abs_of_nonneg hy0, abs_of_nonneg hx0,
    abs_of_nonneg hβ0] at h
  rw [abs_of_pos exampleD4Coupling_pos]
  nlinarith

private theorem exampleD4_activity_nonneg :
    0 ≤ Real.exp (|exampleD4Coupling| * 2) - 1 := by
  rw [sub_nonneg, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr
    (mul_nonneg (abs_nonneg _) (by norm_num))

private theorem positiveCoupling_axis_radius :
    ((16 * 4 + 1 : ℕ) : ℝ) ^ 2 *
      (((Real.exp (|exampleD4Coupling| * 2) - 1) +
        (1 / 1000000 : ℝ) +
        (Real.exp (|exampleD4Coupling| * 2) - 1) *
          (1 / 1000000 : ℝ)) *
        Real.exp ((1 / 100 : ℝ) + 1 / 100 + 1)) < 1 := by
  let a : ℝ := Real.exp (|exampleD4Coupling| * 2) - 1
  let z : ℝ :=
    (a + (1 / 1000000 : ℝ) + a * (1 / 1000000 : ℝ)) *
      Real.exp (51 / 50 : ℝ)
  have he := exp_fifty_one_fiftieth_le_nine
  have ha : a ≤ 4 / 1000000 := by
    have h := exampleD4_activity_le_four
    rw [abs_of_pos exampleD4Coupling_pos] at h
    norm_num [a, exampleD4Coupling,
      explicitStrongCouplingRadiusD4] at h ⊢
    exact h
  have ha0 : 0 ≤ a := by
    exact exampleD4_activity_nonneg
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz9 : z ≤ 46 / 1000000 := by
    dsimp [z]
    nlinarith
  norm_num
  change 4225 * z < 1
  nlinarith

private theorem positiveCoupling_axis_small :
    ((16 * 4 : ℕ) : ℝ) *
      ((((Real.exp (|exampleD4Coupling| * 2) - 1) +
        (1 / 1000000 : ℝ) +
        (Real.exp (|exampleD4Coupling| * 2) - 1) *
          (1 / 1000000 : ℝ)) *
        Real.exp ((1 / 100 : ℝ) + 1 / 100 + 1)) /
        (1 - ((16 * 4 + 1 : ℕ) : ℝ) ^ 2 *
          (((Real.exp (|exampleD4Coupling| * 2) - 1) +
            (1 / 1000000 : ℝ) +
            (Real.exp (|exampleD4Coupling| * 2) - 1) *
              (1 / 1000000 : ℝ)) *
            Real.exp ((1 / 100 : ℝ) + 1 / 100 + 1)))) ≤
      (1 / 100 : ℝ) := by
  let a : ℝ := Real.exp (|exampleD4Coupling| * 2) - 1
  let z : ℝ :=
    (a + (1 / 1000000 : ℝ) + a * (1 / 1000000 : ℝ)) *
      Real.exp (51 / 50 : ℝ)
  have he := exp_fifty_one_fiftieth_le_nine
  have ha : a ≤ 4 / 1000000 := by
    have h := exampleD4_activity_le_four
    rw [abs_of_pos exampleD4Coupling_pos] at h
    norm_num [a, exampleD4Coupling,
      explicitStrongCouplingRadiusD4] at h ⊢
    exact h
  have ha0 : 0 ≤ a := by
    exact exampleD4_activity_nonneg
  have hz0 : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz9 : z ≤ 46 / 1000000 := by
    dsimp [z]
    nlinarith
  have hden : 0 < 1 - 4225 * z := by
    nlinarith
  norm_num [a]
  change 64 * (z / (1 - 4225 * z)) ≤ (1 / 100 : ℝ)
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

/-- Uniform marked-pair weight for every coupling in the proved `d=4`
strong-coupling window. -/
private noncomputable def d4AxisWeight (β : ℝ) : ℝ :=
  ((Real.exp (|β| * 2) - 1) + (1 / 1000000 : ℝ) +
    (Real.exp (|β| * 2) - 1) * (1 / 1000000 : ℝ)) *
      Real.exp (51 / 50 : ℝ)

private noncomputable def d4AxisRatio (β : ℝ) : ℝ :=
  d4AxisWeight β / (1 - 4225 * d4AxisWeight β)

private theorem d4Window_activity_nonneg (β : ℝ) :
    0 ≤ Real.exp (|β| * 2) - 1 := by
  rw [sub_nonneg, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr
    (mul_nonneg (abs_nonneg _) (by norm_num))

private theorem d4Window_activity_le
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadiusD4) :
    Real.exp (|β| * 2) - 1 ≤ 4 / 1000000 := by
  have hx0 : 0 ≤ |β| * 2 := by positivity
  have hx1 : |(|β| * 2)| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    have hr :
        explicitStrongCouplingRadiusD4 = (1 / 1000000 : ℝ) := by
      norm_num [explicitStrongCouplingRadiusD4]
    rw [hr] at hβ
    nlinarith [abs_nonneg β]
  have ha0 := d4Window_activity_nonneg β
  have h := Real.abs_exp_sub_one_le (x := |β| * 2) hx1
  rw [abs_of_nonneg ha0, abs_of_nonneg hx0] at h
  have hr :
      explicitStrongCouplingRadiusD4 = (1 / 1000000 : ℝ) := by
    norm_num [explicitStrongCouplingRadiusD4]
  rw [hr] at hβ
  nlinarith

private theorem d4AxisWeight_nonneg
    (β : ℝ) :
    0 ≤ d4AxisWeight β := by
  unfold d4AxisWeight
  exact mul_nonneg
    (add_nonneg
      (add_nonneg (d4Window_activity_nonneg β) (by norm_num))
      (mul_nonneg (d4Window_activity_nonneg β) (by norm_num)))
    (Real.exp_pos _).le

private theorem d4AxisWeight_le
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadiusD4) :
    d4AxisWeight β ≤ 46 / 1000000 := by
  have ha := d4Window_activity_le β hβ
  have ha0 := d4Window_activity_nonneg β
  have he := exp_fifty_one_fiftieth_le_nine
  unfold d4AxisWeight
  nlinarith

private theorem d4Window_axis_radius
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadiusD4) :
    4225 * d4AxisWeight β < 1 := by
  have hz := d4AxisWeight_le β hβ
  nlinarith

private theorem d4AxisRatio_nonneg
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadiusD4) :
    0 ≤ d4AxisRatio β := by
  have hden : 0 < 1 - 4225 * d4AxisWeight β := by
    linarith [d4Window_axis_radius β hβ]
  exact div_nonneg (d4AxisWeight_nonneg β) hden.le

private theorem d4AxisRatio_le_one
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadiusD4) :
    d4AxisRatio β ≤ 1 := by
  have hz := d4AxisWeight_le β hβ
  have hz0 := d4AxisWeight_nonneg β
  have hden : 0 < 1 - 4225 * d4AxisWeight β := by
    linarith [d4Window_axis_radius β hβ]
  unfold d4AxisRatio
  rw [div_le_iff₀ hden]
  nlinarith

private theorem d4Window_axis_small
    (β : ℝ) (hβ : |β| ≤ explicitStrongCouplingRadiusD4) :
    64 * d4AxisRatio β ≤ (1 / 100 : ℝ) := by
  have hz := d4AxisWeight_le β hβ
  have hden : 0 < 1 - 4225 * d4AxisWeight β := by
    linarith [d4Window_axis_radius β hβ]
  unfold d4AxisRatio
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

/-- The actual infinite-volume connected correlation at scale index `k`.
Both the state (`β k`) and the second observable (`2k`) vary with the same
index. -/
noncomputable def d4ScaleIndexedTruncatedCorrelation
    (β : ℕ → ℝ)
    (hβ : ∀ k, |β k| ≤ explicitStrongCouplingRadiusD4)
    (k : ℕ) : ℝ :=
  infiniteLocalGibbsTruncatedCorrelation
    (sunHaarProb 2)
    measurable_su2FundamentalPlaquetteEnergy
    su2FundamentalPlaquetteEnergy_bounded
    (su2D4UniformLocalKPRegimeOfBound (β k) (hβ k))
    (axisPlaquetteObservable (d := 4) (G := SU2GaugeGroup)
      (by omega) 0 normalizedSU2PlaquetteEnergy
      measurable_normalizedSU2PlaquetteEnergy 1 (by norm_num)
      normalizedSU2PlaquetteEnergy_abs_le_one)
    (axisPlaquetteObservable (d := 4) (G := SU2GaugeGroup)
      (by omega) (2 * k) normalizedSU2PlaquetteEnergy
      measurable_normalizedSU2PlaquetteEnergy 1 (by norm_num)
      normalizedSU2PlaquetteEnergy_abs_le_one)

/-- Uniform clustering for a genuinely scale-indexed family of constructed
states. No relation among the values `β k` is assumed beyond membership in
the proved KP window. -/
theorem tendsto_d4ScaleIndexedTruncatedCorrelation_zero
    (β : ℕ → ℝ)
    (hβ : ∀ k, |β k| ≤ explicitStrongCouplingRadiusD4) :
    Tendsto
      (d4ScaleIndexedTruncatedCorrelation β hβ)
      atTop (𝓝 0) := by
  let C : ℝ := 32000000000000
  have hExp :
      Tendsto
        (fun k : ℕ => Real.exp (-((1 / 100 : ℝ) * (k : ℝ))))
        atTop (𝓝 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hFour :
      ∀ᶠ k : ℕ in atTop,
        4 * Real.exp (-((1 / 100 : ℝ) * (k : ℝ))) ≤ 1 := by
    have ht :
        Tendsto
          (fun k : ℕ =>
            4 * Real.exp (-((1 / 100 : ℝ) * (k : ℝ))))
          atTop (𝓝 0) := by
      simpa only [mul_zero] using hExp.const_mul 4
    exact ((tendsto_order.1 ht).2 1 (by norm_num)).mono
      fun _ hk => hk.le
  have hbound :
      ∀ᶠ k : ℕ in atTop,
        |d4ScaleIndexedTruncatedCorrelation β hβ k| ≤
          C * Real.exp (-((1 / 100 : ℝ) * (k : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1, hFour] with k hk hfour
    have hq0 := d4AxisRatio_nonneg (β k) (hβ k)
    have hq1 := d4AxisRatio_le_one (β k) (hβ k)
    have hone :
        4 * Real.exp (-((1 / 100 : ℝ) * (k : ℝ))) *
            d4AxisRatio (β k) ≤ 1 := by
      calc
        4 * Real.exp (-((1 / 100 : ℝ) * (k : ℝ))) *
              d4AxisRatio (β k)
            ≤ 4 * Real.exp (-((1 / 100 : ℝ) * (k : ℝ))) * 1 := by
              gcongr
        _ ≤ 1 := by simpa using hfour
    have hraw :=
      abs_infiniteTruncatedCorrelation_axisPair_le
        (sunHaarProb 2)
        measurable_su2FundamentalPlaquetteEnergy
        su2FundamentalPlaquetteEnergy_bounded
        (su2D4UniformLocalKPRegimeOfBound (β k) (hβ k))
        (by omega)
        normalizedSU2PlaquetteEnergy
        measurable_normalizedSU2PlaquetteEnergy
        normalizedSU2PlaquetteEnergy_abs_le_one
        (s := 1 / 1000000) (by norm_num)
        (1 / 100) (1 / 100) (by norm_num) (by norm_num)
        (by
          convert d4Window_axis_radius (β k) (hβ k) using 1 <;>
            norm_num [d4AxisWeight])
        (by
          convert d4Window_axis_small (β k) (hβ k) using 1 <;>
            norm_num [d4AxisWeight, d4AxisRatio])
        k hk (by
          convert hone using 1 <;>
            norm_num [d4AxisWeight, d4AxisRatio])
    have hcoef :
        (8 * d4AxisRatio (β k) *
            (1 + (1 / 1000000 : ℝ)) ^ 2 /
              (1 / 1000000 : ℝ) ^ 2) ≤ C := by
      dsimp [C]
      norm_num
      nlinarith
    have hexp0 :
        0 ≤ Real.exp (-((1 / 100 : ℝ) * (k : ℝ))) :=
      (Real.exp_pos _).le
    have hraw' :
        |d4ScaleIndexedTruncatedCorrelation β hβ k| ≤
          (8 * d4AxisRatio (β k) *
              (1 + (1 / 1000000 : ℝ)) ^ 2 /
                (1 / 1000000 : ℝ) ^ 2) *
            Real.exp (-((1 / 100 : ℝ) * (k : ℝ))) := by
      convert hraw using 1 <;>
        norm_num [d4ScaleIndexedTruncatedCorrelation,
          d4AxisWeight, d4AxisRatio]
    exact hraw'.trans (mul_le_mul_of_nonneg_right hcoef hexp0)
  have hExpC :
      Tendsto
        (fun k : ℕ =>
          C * Real.exp (-((1 / 100 : ℝ) * (k : ℝ))))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using hExp.const_mul C
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero'
    (Eventually.of_forall fun _ => abs_nonneg _) hbound hExpC

/-- A bookkeeping pair in which the declared physical separation and the
actual state correlation share the same scale index.  Its limit theorem is
the conjunction of two independent limit statements in the product
topology; C0 proves no dependence relation between the two components. -/
noncomputable def d4ScaleIndexedTwoPointData
    (β : ℕ → ℝ)
    (hβ : ∀ k, |β k| ≤ explicitStrongCouplingRadiusD4)
    (k : ℕ) : ℝ × ℝ :=
  (axisPairPhysicalSeparation reciprocalScale k,
    d4ScaleIndexedTruncatedCorrelation β hβ k)

theorem tendsto_d4ScaleIndexedTwoPointData
    (β : ℕ → ℝ)
    (hβ : ∀ k, |β k| ≤ explicitStrongCouplingRadiusD4) :
    Tendsto
      (d4ScaleIndexedTwoPointData β hβ)
      atTop (𝓝 (2, 0)) := by
  have h :=
    tendsto_axisPairPhysicalSeparation_reciprocal.prodMk
      (tendsto_d4ScaleIndexedTruncatedCorrelation_zero β hβ)
  simpa [d4ScaleIndexedTwoPointData, nhds_prod_eq] using h

/-- A compiled, separation-varying fixed-coupling example.  The first
plaquette stays at the origin, the second is at lattice offset `2k`, and
their connected correlation in the actual constructed SU(2) infinite-volume
Gibbs state tends to zero.  Scale-indexed states are handled by
`tendsto_d4ScaleIndexedTruncatedCorrelation_zero` above. -/
theorem exampleD4_twoPoint_connected_tendsto_zero :
    Tendsto
      (fun k : ℕ =>
        infiniteLocalGibbsTruncatedCorrelation
          (sunHaarProb 2)
          measurable_su2FundamentalPlaquetteEnergy
          su2FundamentalPlaquetteEnergy_bounded
          (su2D4UniformLocalKPRegimeOfBound exampleD4Coupling (by
            rw [abs_of_pos exampleD4Coupling_pos]
            exact le_rfl))
          (axisPlaquetteObservable (d := 4) (G := SU2GaugeGroup)
            (by omega) 0 normalizedSU2PlaquetteEnergy
            measurable_normalizedSU2PlaquetteEnergy 1 (by norm_num)
            normalizedSU2PlaquetteEnergy_abs_le_one)
          (axisPlaquetteObservable (d := 4) (G := SU2GaugeGroup)
            (by omega) (2 * k) normalizedSU2PlaquetteEnergy
            measurable_normalizedSU2PlaquetteEnergy 1 (by norm_num)
            normalizedSU2PlaquetteEnergy_abs_le_one))
      atTop (𝓝 0) := by
  exact tendsto_infiniteTruncatedCorrelation_axisPair_zero
    (sunHaarProb 2)
    measurable_su2FundamentalPlaquetteEnergy
    su2FundamentalPlaquetteEnergy_bounded
    (su2D4UniformLocalKPRegimeOfBound exampleD4Coupling (by
      rw [abs_of_pos exampleD4Coupling_pos]
      exact le_rfl))
    (by omega)
    normalizedSU2PlaquetteEnergy
    measurable_normalizedSU2PlaquetteEnergy
    normalizedSU2PlaquetteEnergy_abs_le_one
    (s := 1 / 1000000) (by norm_num)
    (1 / 100) (1 / 100) (by norm_num) (by norm_num)
    positiveCoupling_axis_radius positiveCoupling_axis_small

end YangMills.Continuum
