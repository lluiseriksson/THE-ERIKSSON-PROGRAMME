/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.IntegerTranslation
import YangMills.L1_GibbsMeasure.FreeBoundaryThermodynamicLimit

/-!
# A translation-invariant thermodynamic state on `ℤ^d`

This module transfers the whole-sequence uniform-KP limit to the intrinsic
integer-coordinate observable algebra.  The transfer is eventual equality of
genuine finite Gibbs expectations:

* one fixed finite integer translation moves the support into `ℕ^d`;
* exact finite-volume Gibbs invariance removes that translation;
* beyond the explicit coordinate bound, the integer realization and the
  existing compatible realization agree pointwise.

The resulting `TranslationInvariantLocalState` is real linear, positive,
normalized, and invariant under the genuine `AddAction (Fin d → ℤ)`.  Since
the acting object is an additive group, inverse translations are included
with no volume-dependent word or guard.

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no axioms.
-/

namespace YangMills

open Filter MeasureTheory GaugeConfig
open WindowPolymer
open scoped BigOperators Topology

namespace IntegerLocalObservable

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

omit [NeZero d] [Group G] in
theorem natMod_eq_toNat_mod
    (a : ℤ) (N : ℕ) (hN : 0 < N) (ha : 0 ≤ a) :
    a.natMod N = a.toNat % N := by
  apply Int.ofNat_injective
  change
    (((a.natMod N : ℕ) : ℤ)) =
      (((a.toNat % N : ℕ) : ℤ))
  rw [natCast_natMod a N hN, Int.natCast_mod,
    Int.toNat_of_nonneg ha]

theorem edgeAt_lowerShiftVector
    (O : IntegerLocalObservable d G) (n : ℕ)
    (h : O.toCompatible.minVolume ≤ n) (s : O.Support) :
    (O.lowerShiftVector +ᵥ O).edgeAt n s =
      O.toCompatible.edgeAt n h s := by
  apply Subtype.ext
  change ConcreteEdge.mk _ _ true = ConcreteEdge.mk _ _ true
  congr 1
  · funext j
    apply Fin.ext
    change
      (((O.coord s).1 j + (O.lowerShift j : ℤ)).natMod (n + 1)) =
        O.natCoord s j % (n + 1)
    exact natMod_eq_toNat_mod
      ((O.coord s).1 j + (O.lowerShift j : ℤ))
      (n + 1) (by omega) (O.coord_add_lowerShift_nonneg s j)

theorem realize_lowerShiftVector
    (O : IntegerLocalObservable d G) (n : ℕ)
    (h : O.toCompatible.minVolume ≤ n)
    (A : GaugeConfig d (n + 1) G) :
    (O.lowerShiftVector +ᵥ O).realize n A =
      O.toCompatible.realize n A := by
  rw [CompatibleLocalObservable.realize, dif_pos h]
  apply congrArg O.kernel
  funext s
  exact congrArg A
    (congrArg Subtype.val (O.edgeAt_lowerShiftVector n h s))

/-- Embed a natural-coordinate compatible observable into the intrinsic
integer-coordinate algebra. -/
noncomputable def ofCompatible
    (O : CompatibleLocalObservable d G) :
    IntegerLocalObservable d G where
  Support := O.Support
  coord := fun s =>
    ⟨fun j => (O.coord s).1 j, (O.coord s).2⟩
  coord_injective := by
    intro s t hst
    apply O.coord_injective
    apply Prod.ext
    · funext j
      have hj := congrArg (fun c => c.1 j) hst
      exact Int.ofNat_injective hj
    · have hdir := congrArg Prod.snd hst
      simpa using hdir
  kernel := O.kernel
  kernel_measurable := O.kernel_measurable
  bound := O.bound
  bound_nonneg := O.bound_nonneg
  kernel_bound := O.kernel_bound

theorem edgeAt_ofCompatible
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) (s : O.Support) :
    (ofCompatible O).edgeAt n s = O.edgeAt n h s := by
  apply Subtype.ext
  change ConcreteEdge.mk _ _ true = ConcreteEdge.mk _ _ true
  congr 1

theorem realize_ofCompatible
    (O : CompatibleLocalObservable d G) (n : ℕ)
    (h : O.minVolume ≤ n) (A : GaugeConfig d (n + 1) G) :
    (ofCompatible O).realize n A = O.realize n A := by
  rw [CompatibleLocalObservable.realize, dif_pos h]
  apply congrArg O.kernel
  funext s
  exact congrArg A
    (congrArg Subtype.val (edgeAt_ofCompatible O n h s))

end IntegerLocalObservable

section IntegerThermodynamicLimit

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [MeasurableMul₂ G] [MeasurableInv G]

theorem integerLocalGibbsExpectation_lowerShiftVector
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (n : ℕ)
    (h : O.toCompatible.minVolume ≤ n) :
    integerLocalGibbsExpectation μ pe β
        (O.lowerShiftVector +ᵥ O) n =
      localGibbsExpectation μ pe β O.toCompatible n := by
  unfold integerLocalGibbsExpectation localGibbsExpectation expectation
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun A =>
    IntegerLocalObservable.realize_lowerShiftVector O n h A

/-- Eventual literal equality between an integer-coordinate Gibbs expectation
and the already-controlled natural-coordinate chart. -/
theorem eventually_integerLocalGibbsExpectation_eq_compatible
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) :
    ∀ᶠ n in atTop,
      integerLocalGibbsExpectation μ pe β O n =
        localGibbsExpectation μ pe β O.toCompatible n := by
  filter_upwards
    [eventually_ge_atTop O.toCompatible.minVolume] with n hn
  calc
    integerLocalGibbsExpectation μ pe β O n =
        integerLocalGibbsExpectation μ pe β
          (O.lowerShiftVector +ᵥ O) n :=
      (integerLocalGibbsExpectation_vadd
        μ pe β O O.lowerShiftVector n).symm
    _ = localGibbsExpectation μ pe β O.toCompatible n :=
      integerLocalGibbsExpectation_lowerShiftVector
        μ pe β O n hn

/-- The infinite value on the integer-coordinate algebra.  Its definition
reuses the already-constructed complete-sequence limit of one canonical
natural chart; the next theorem proves that the genuine integer realizations
converge to it. -/
noncomputable def integerInfiniteLocalGibbsStateValue
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : IntegerLocalObservable d G) : ℝ :=
  infiniteLocalGibbsStateValue μ hpe_meas hpe κ O.toCompatible

/-- The complete sequence of genuine integer-coordinate Gibbs expectations
converges to the integer local state value. -/
theorem tendsto_integerInfiniteLocalGibbsStateValue
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : IntegerLocalObservable d G) :
    Tendsto
      (fun n => integerLocalGibbsExpectation μ pe β O n)
      atTop
      (𝓝 (integerInfiniteLocalGibbsStateValue
        μ hpe_meas hpe κ O)) := by
  have hlocal :=
    tendsto_infiniteLocalGibbsStateValue
      μ hpe_meas hpe κ O.toCompatible
  have heq :=
    eventually_integerLocalGibbsExpectation_eq_compatible
      μ pe β O
  exact hlocal.congr' (heq.mono fun _ hn => hn.symm)

/-- Explicit Cauchy theorem for the complete sequence of genuine
integer-coordinate Gibbs expectations. -/
theorem cauchySeq_integerLocalGibbsExpectation
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : IntegerLocalObservable d G) :
    CauchySeq
      (fun n => integerLocalGibbsExpectation μ pe β O n) :=
  (tendsto_integerInfiniteLocalGibbsStateValue
    μ hpe_meas hpe κ O).cauchySeq

/-- Every cofinal volume schedule has the same integer-coordinate state
limit. -/
theorem tendsto_integerInfiniteLocalGibbsStateValue_comp
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : IntegerLocalObservable d G)
    (volume : ℕ → ℕ) (hvolume : Tendsto volume atTop atTop) :
    Tendsto
      (fun k => integerLocalGibbsExpectation
        μ pe β O (volume k))
      atTop
      (𝓝 (integerInfiniteLocalGibbsStateValue
        μ hpe_meas hpe κ O)) :=
  (tendsto_integerInfiniteLocalGibbsStateValue
    μ hpe_meas hpe κ O).comp hvolume

/-- The integer-coordinate limit extends the original compatible-observable
state; no result is discarded by changing charts. -/
theorem integerInfiniteLocalGibbsStateValue_ofCompatible
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : CompatibleLocalObservable d G) :
    integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ
        (IntegerLocalObservable.ofCompatible O) =
      infiniteLocalGibbsStateValue μ hpe_meas hpe κ O := by
  have hI :=
    tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ (IntegerLocalObservable.ofCompatible O)
  have hO :=
    tendsto_infiniteLocalGibbsStateValue μ hpe_meas hpe κ O
  have heq :
      ∀ᶠ n in atTop,
        integerLocalGibbsExpectation μ pe β
            (IntegerLocalObservable.ofCompatible O) n =
          localGibbsExpectation μ pe β O n := by
    filter_upwards [eventually_ge_atTop O.minVolume] with n hn
    unfold integerLocalGibbsExpectation localGibbsExpectation expectation
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun A =>
      IntegerLocalObservable.realize_ofCompatible O n hn A
  exact tendsto_nhds_unique hI
    (hO.congr' (heq.mono fun _ hn => hn.symm))

theorem integerInfiniteLocalGibbsStateValue_add
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : IntegerLocalObservable d G) :
    integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ
        (IntegerLocalObservable.add O P) =
      integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ O +
        integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ P := by
  have hAdd :=
    tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ (IntegerLocalObservable.add O P)
  have hSum :=
    (tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ O).add
      (tendsto_integerInfiniteLocalGibbsStateValue
        μ hpe_meas hpe κ P)
  have heq :
      ∀ᶠ n in atTop,
        integerLocalGibbsExpectation μ pe β O n +
            integerLocalGibbsExpectation μ pe β P n =
          integerLocalGibbsExpectation μ pe β
            (IntegerLocalObservable.add O P) n := by
    exact Filter.Eventually.of_forall fun n =>
      (integerLocalGibbsExpectation_add
        μ hpe_meas hpe β O P n).symm
  exact tendsto_nhds_unique hAdd (hSum.congr' heq)

theorem integerInfiniteLocalGibbsStateValue_smul
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (c : ℝ) (O : IntegerLocalObservable d G) :
    integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ
        (IntegerLocalObservable.smul c O) =
      c * integerInfiniteLocalGibbsStateValue
        μ hpe_meas hpe κ O := by
  have hScalar :=
    tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ (IntegerLocalObservable.smul c O)
  have hMul :=
    (tendsto_const_nhds.mul
      (tendsto_integerInfiniteLocalGibbsStateValue
        μ hpe_meas hpe κ O) :
      Tendsto
        (fun n : ℕ =>
          c * integerLocalGibbsExpectation μ pe β O n)
        atTop
        (𝓝 (c * integerInfiniteLocalGibbsStateValue
          μ hpe_meas hpe κ O)))
  have heq :
      ∀ᶠ n in atTop,
        c * integerLocalGibbsExpectation μ pe β O n =
          integerLocalGibbsExpectation μ pe β
            (IntegerLocalObservable.smul c O) n := by
    exact Filter.Eventually.of_forall fun n =>
      (integerLocalGibbsExpectation_smul μ pe β c O n).symm
  exact tendsto_nhds_unique hScalar (hMul.congr' heq)

theorem integerInfiniteLocalGibbsStateValue_one
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β) :
    integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (IntegerLocalObservable.const (d := d) (G := G) 1) = 1 := by
  apply tendsto_nhds_unique
    (tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ
        (IntegerLocalObservable.const (d := d) (G := G) 1))
  simpa [integerLocalGibbsExpectation_const
      μ hpe_meas hpe β] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

theorem integerInfiniteLocalGibbsStateValue_nonneg
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : IntegerLocalObservable d G)
    (hO : ∀ x, 0 ≤ O.kernel x) :
    0 ≤ integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ O := by
  apply ge_of_tendsto'
    (tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ O)
  intro n
  exact integerLocalGibbsExpectation_nonneg μ pe β O n hO

/-- **Invariance under every element of the full translation group
`ℤ^d`, including inverse translations.** -/
theorem integerInfiniteLocalGibbsStateValue_vadd
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (z : Fin d → ℤ) (O : IntegerLocalObservable d G) :
    integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ (z +ᵥ O) =
      integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ O := by
  have hT :=
    tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ (z +ᵥ O)
  have hO :=
    tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ O
  have heq :
      ∀ᶠ n in atTop,
        integerLocalGibbsExpectation μ pe β O n =
          integerLocalGibbsExpectation μ pe β (z +ᵥ O) n := by
    exact Filter.Eventually.of_forall fun n =>
      (integerLocalGibbsExpectation_vadd μ pe β O z n).symm
  exact tendsto_nhds_unique hT (hO.congr' heq)

/-- A positive normalized real local state carrying a literal action of the
full integer translation group. -/
structure TranslationInvariantLocalState
    (d : ℕ) [NeZero d]
    (G : Type*) [Group G] [MeasurableSpace G] where
  value : IntegerLocalObservable d G → ℝ
  map_add : ∀ O P,
    value (IntegerLocalObservable.add O P) = value O + value P
  map_smul : ∀ c O,
    value (IntegerLocalObservable.smul c O) = c * value O
  map_one :
    value (IntegerLocalObservable.const (d := d) (G := G) 1) = 1
  nonneg : ∀ O, (∀ x, 0 ≤ O.kernel x) → 0 ≤ value O
  vadd_invariant : ∀ (z : Fin d → ℤ) O, value (z +ᵥ O) = value O

instance :
    CoeFun (TranslationInvariantLocalState d G)
      (fun _ => IntegerLocalObservable d G → ℝ) :=
  ⟨TranslationInvariantLocalState.value⟩

/-- **The infinite-volume positive, normalized, fully translation-invariant
local Gibbs state.** -/
noncomputable def integerInfiniteLocalGibbsState
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β) :
    TranslationInvariantLocalState d G where
  value := integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ
  map_add :=
    integerInfiniteLocalGibbsStateValue_add μ hpe_meas hpe κ
  map_smul :=
    integerInfiniteLocalGibbsStateValue_smul μ hpe_meas hpe κ
  map_one :=
    integerInfiniteLocalGibbsStateValue_one μ hpe_meas hpe κ
  nonneg :=
    integerInfiniteLocalGibbsStateValue_nonneg μ hpe_meas hpe κ
  vadd_invariant :=
    integerInfiniteLocalGibbsStateValue_vadd μ hpe_meas hpe κ

/-- The genuine centered free-boundary exhaustion attached to the canonical
natural chart of an integer-coordinate observable. -/
noncomputable def integerFreeBoundaryThermodynamicExpectation
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : IntegerLocalObservable d G) (q : ℕ) : ℂ :=
  freeBoundaryThermodynamicExpectation μ pe β O.toCompatible q

/-- The complete genuine centered free-boundary sequence converges to the
same fully translation-invariant integer state as periodic boundary
conditions. -/
theorem tendsto_integerFreeBoundaryThermodynamicExpectation
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O : IntegerLocalObservable d G) :
    Tendsto
      (integerFreeBoundaryThermodynamicExpectation μ pe β O)
      atTop
      (𝓝 (integerInfiniteLocalGibbsStateValue
        μ hpe_meas hpe κ O : ℂ)) := by
  have hfree :=
    tendsto_freeBoundaryThermodynamicExpectation
      μ hpe_meas hpe κ O.toCompatible
  have hvalue :
      infiniteLocalGibbsExpectation
          μ hpe_meas hpe κ O.toCompatible =
        (integerInfiniteLocalGibbsStateValue
          μ hpe_meas hpe κ O : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using infiniteLocalGibbsExpectation_im
        μ hpe_meas hpe κ O.toCompatible
  simpa [integerFreeBoundaryThermodynamicExpectation, hvalue] using hfree

/-! ## Truncated correlations on the integer-coordinate algebra -/

noncomputable def integerLocalGibbsTruncatedCorrelation
    (μ : Measure G) [IsProbabilityMeasure μ]
    (pe : G → ℝ) (β : ℝ)
    (O P : IntegerLocalObservable d G) (n : ℕ) : ℝ :=
  integerLocalGibbsExpectation μ pe β
      (IntegerLocalObservable.mul O P) n -
    integerLocalGibbsExpectation μ pe β O n *
      integerLocalGibbsExpectation μ pe β P n

noncomputable def integerInfiniteLocalGibbsTruncatedCorrelation
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : IntegerLocalObservable d G) : ℝ :=
  integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ
      (IntegerLocalObservable.mul O P) -
    integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ O *
      integerInfiniteLocalGibbsStateValue μ hpe_meas hpe κ P

theorem tendsto_integerInfiniteLocalGibbsTruncatedCorrelation
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : IntegerLocalObservable d G) :
    Tendsto
      (integerLocalGibbsTruncatedCorrelation μ pe β O P)
      atTop
      (𝓝 (integerInfiniteLocalGibbsTruncatedCorrelation
        μ hpe_meas hpe κ O P)) := by
  exact
    (tendsto_integerInfiniteLocalGibbsStateValue
      μ hpe_meas hpe κ (IntegerLocalObservable.mul O P)).sub
      ((tendsto_integerInfiniteLocalGibbsStateValue
        μ hpe_meas hpe κ O).mul
        (tendsto_integerInfiniteLocalGibbsStateValue
          μ hpe_meas hpe κ P))

/-- Every eventual volume-uniform bound on genuine integer-coordinate
truncated correlations passes unchanged to the fully translation-invariant
state. -/
theorem abs_integerInfiniteLocalGibbsTruncatedCorrelation_le_of_eventually
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B β : ℝ} (hpe : ∀ g, |pe g| ≤ B)
    (κ : UniformLocalKPRegime d B β)
    (O P : IntegerLocalObservable d G) (C : ℝ)
    (hC : ∀ᶠ n in atTop,
      |integerLocalGibbsTruncatedCorrelation μ pe β O P n| ≤ C) :
    |integerInfiniteLocalGibbsTruncatedCorrelation
      μ hpe_meas hpe κ O P| ≤ C := by
  exact le_of_tendsto
    ((tendsto_integerInfiniteLocalGibbsTruncatedCorrelation
      μ hpe_meas hpe κ O P).abs) hC

end IntegerThermodynamicLimit

end YangMills
