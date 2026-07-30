/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalMarkedCorrectionCauchy

/-!
# Cauchy transport of the below-cutoff normalized marked sum

This layer combines exact transport of the marked integral with the
quantitative two-volume bound for its normalization correction.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

@[simp]
theorem CompatibleLocalObservable.bound_translateList
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (is : List (Fin d)) :
    (O.translateList is).bound = O.bound := by
  induction is generalizing O with
  | nil => rfl
  | cons i is ih =>
      simpa [CompatibleLocalObservable.translateList,
        CompatibleLocalObservable.translate] using ih (O := O.translate i)

@[simp]
theorem CompatibleLocalObservable.bound_center
    {d : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G) (r : ℕ) :
    (O.center r).bound = O.bound := by
  exact CompatibleLocalObservable.bound_translateList O
    (CompatibleLocalObservable.centeringWord d r)

/-- Complete centered marked sets with the actual outer cutoff `K`.  The
larger radius `R` is reserved for the joint marked/correction geometry. -/
def CenteredMarkedSetBelow
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (R K : ℕ)
    (hn : MarkedWindowAdmissible O R n) :=
  {S₀ : Finset (ConcretePlaquette d (n + 1)) //
    localNear
        ((O.center (R + 2)).realizedSupport n hn.center_le) S₀
      = S₀ ∧
    S₀.card < K}

noncomputable instance centeredMarkedSetBelowFintype
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (R K : ℕ)
    (hn : MarkedWindowAdmissible O R n) :
    Fintype (CenteredMarkedSetBelow O R K hn) := by
  classical
  unfold CenteredMarkedSetBelow
  infer_instance

/-- Transport of a below-cutoff marked set. -/
noncomputable def transportCenteredMarkedSetBelow
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (R K : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m) :
    CenteredMarkedSetBelow O R K hn →
      CenteredMarkedSetBelow O R K hm :=
  fun S₀ =>
    let hcardR : S₀.1.card ≤ R :=
      (Nat.le_of_lt S₀.2.2).trans hKR
    ⟨transportMarkedSet
      O R hn.center_le hn.room hm.room S₀.2.1 hcardR,
     localNear_transportMarkedSet
      O R hn.center_le hm.center_le hn.room hm.room
        S₀.2.1 hcardR,
     by
       rw [card_transportMarkedSet]
       exact S₀.2.2⟩

/-- Transporting a below-cutoff marked set in both directions recovers it
literally. -/
theorem transportCenteredMarkedSetBelow_leftInverse
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (R K : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (S₀ : CenteredMarkedSetBelow O R K hn) :
    transportCenteredMarkedSetBelow O R K hKR hm hn
        (transportCenteredMarkedSetBelow O R K hKR hn hm S₀)
      =
    S₀ := by
  apply Subtype.ext
  let S₁ :=
    transportCenteredMarkedSetBelow O R K hKR hn hm S₀
  let hcardR : S₀.1.card ≤ R :=
    (Nat.le_of_lt S₀.2.2).trans hKR
  change
    WindowPlaquette.realizedFinset
        (decodedMarkedSet S₁.1)
        (decodedMarkedSet_fits_target
          O R hm.center_le hm.room hn.room
            S₁.2.1
            ((Nat.le_of_lt S₁.2.2).trans hKR))
      =
    S₀.1
  have hdecode :
      decodedMarkedSet S₁.1 = decodedMarkedSet S₀.1 :=
    decodedMarkedSet_transportMarkedSet
      O R hn.center_le hn.room hm.room S₀.2.1 hcardR
  have hsource :=
    realizedFinset_decodedMarkedSet_source
      O R hn.center_le hn.room S₀.2.1 hcardR
  ext q
  constructor
  · intro hq
    obtain ⟨p, hpq⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hq
    rw [← hsource]
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    refine ⟨⟨p.1, ?_⟩, ?_⟩
    · rw [← hdecode]
      exact p.2
    · exact hpq
  · intro hq
    rw [← hsource] at hq
    obtain ⟨p, hpq⟩ :=
      WindowPlaquette.mem_realizedFinset_iff.mp hq
    apply WindowPlaquette.mem_realizedFinset_iff.mpr
    refine ⟨⟨p.1, ?_⟩, ?_⟩
    · rw [hdecode]
      exact p.2
    · exact hpq

/-- Explicit equivalence of the outer below-cutoff marked indices. -/
noncomputable def centeredMarkedSetBelowEquiv
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (R K : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m) :
    CenteredMarkedSetBelow O R K hn ≃
      CenteredMarkedSetBelow O R K hm where
  toFun := transportCenteredMarkedSetBelow
    O R K hKR hn hm
  invFun := transportCenteredMarkedSetBelow
    O R K hKR hm hn
  left_inv := transportCenteredMarkedSetBelow_leftInverse
    O R K hKR hn hm
  right_inv := transportCenteredMarkedSetBelow_leftInverse
    O R K hKR hm hn

/-- The correction exponent in a normalized marked term is the negative of
the exact local correction series. -/
theorem localMarkedClusterTerm_eq_integral_mul_exp_neg_correctionSeries
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    localMarkedClusterTerm μ pe β O SF S₀
      =
    (∫ A, (O.realize n A : ℂ) *
        ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
    Complex.exp (-
      ∑' q, localCorrectionSeriesTerm μ pe β
        (SF ∪ S₀.biUnion plaquetteSupport) 0 q) := by
  unfold localMarkedClusterTerm
  rw [show
      KP.clusterSum
          ((connectedLatticePolymerSystem
            (d := d) (N := n + 1) μ pe β).restrict
            (Finset.univ.filter
              (fun c => c.1 ⊆ localFarRegion SF S₀)))
        -
        KP.clusterSum
          (connectedLatticePolymerSystem
            (d := d) (N := n + 1) μ pe β)
      =
      -(
        KP.clusterSum
          (connectedLatticePolymerSystem
            (d := d) (N := n + 1) μ pe β)
        -
        KP.clusterSum
          ((connectedLatticePolymerSystem
            (d := d) (N := n + 1) μ pe β).restrict
            (Finset.univ.filter
              (fun c => c.1 ⊆ localFarRegion SF S₀)))) by ring,
    clusterSum_sub_localFarRegion_eq_localCorrectionSeries
      μ pe β SF S₀ hkp]

/-- The explicit two-volume bound for a marked normalization correction. -/
noncomputable def markedCorrectionCauchyBound
    {d : ℕ} {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (t ε : ℝ) (K L : ℕ) : ℝ :=
  2 * (Real.exp (-(ε * L)) *
    ((2 * t) *
      (((Fintype.card O.Support + 4 * K : ℕ) : ℝ) *
        (4 * (d : ℝ)))))

/-- One normalized marked summand changes by at most its usual
volume-uniform majorant times twice the correction Cauchy bound. -/
theorem norm_localMarkedClusterTerm_transport_sub_le_volumeUniform
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (hres : (2 * L + 1) + K ≤ R)
    (S₀ : CenteredMarkedSetBelow O R K hn)
    {aN : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    {aM : (connectedLatticePolymerSystem
      (d := d) (N := m + 1) μ pe β).Polymer → ℝ}
    (hkpN : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) aN)
    (hkpM : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β) aM)
    (hboundOne : markedCorrectionCauchyBound
      O t ε K L ≤ 1) :
    let S₀m :=
      transportCenteredMarkedSetBelow O R K hKR hn hm S₀
    ‖localMarkedClusterTerm μ pe β
          (O.center (R + 2))
          ((O.center (R + 2)).realizedSupport n hn.center_le)
          S₀.1
        -
      localMarkedClusterTerm μ pe β
          (O.center (R + 2))
          ((O.center (R + 2)).realizedSupport m hm.center_le)
          S₀m.1‖
      ≤
    ((O.center (R + 2)).bound *
      Real.exp (
        (2 * t) *
          ((((O.center (R + 2)).realizedSupport
            m hm.center_le).card : ℝ) *
            (4 * (d : ℝ)))) *
      (localMarkedEffectiveWeight d B β t) ^ S₀m.1.card) *
    (2 * markedCorrectionCauchyBound O t ε K L) := by
  dsimp only
  let C := O.center (R + 2)
  let hcardR : S₀.1.card ≤ R :=
    (Nat.le_of_lt S₀.2.2).trans hKR
  let S₀m :=
    transportCenteredMarkedSetBelow O R K hKR hn hm S₀
  let S := decodedMarkedSet S₀.1
  let hSn := decodedMarkedSet_fits_source
    O R hn.center_le hn.room S₀.2.1 hcardR
  let hSm := decodedMarkedSet_fits_target
    O R hn.center_le hn.room hm.room S₀.2.1 hcardR
  let corrn := ∑' q, localCorrectionSeriesTerm μ pe β
    (C.realizedSupport n hn.center_le ∪
      (WindowPlaquette.realizedFinset S hSn).biUnion
        plaquetteSupport) 0 q
  let corrm := ∑' q, localCorrectionSeriesTerm μ pe β
    (C.realizedSupport m hm.center_le ∪
      (WindowPlaquette.realizedFinset S hSm).biUnion
        plaquetteSupport) 0 q
  have hcorr :
      ‖corrn - corrm‖ ≤
        markedCorrectionCauchyBound O t ε K L := by
    exact
      norm_localCorrectionSeries_commonCombined_sub_le_volumeUniform
        μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
          O R K L hn.center_le hm.center_le hn.room hm.room
          S hSn hSm
          (by
            rw [realizedFinset_decodedMarkedSet_source
              O R hn.center_le hn.room S₀.2.1 hcardR]
            exact S₀.2.1)
          (by
            rw [card_decodedMarkedSet]
            exact Nat.le_of_lt S₀.2.2)
          hres
  have hcorrOne : ‖-(corrn - corrm)‖ ≤ 1 := by
    rw [norm_neg]
    exact hcorr.trans hboundOne
  have hExpDiff :
      ‖Complex.exp (-corrn) - Complex.exp (-corrm)‖
        ≤
      ‖Complex.exp (-corrm)‖ *
        (2 * markedCorrectionCauchyBound O t ε K L) := by
    have hfactor :
        Complex.exp (-corrn) - Complex.exp (-corrm)
          =
        Complex.exp (-corrm) *
          (Complex.exp (-(corrn - corrm)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      ring
    rw [hfactor, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖Complex.exp (-(corrn - corrm)) - 1‖
          ≤ 2 * ‖-(corrn - corrm)‖ :=
        Complex.norm_exp_sub_one_le hcorrOne
      _ = 2 * ‖corrn - corrm‖ := by rw [norm_neg]
      _ ≤ 2 * markedCorrectionCauchyBound O t ε K L :=
        mul_le_mul_of_nonneg_left hcorr (by positivity)
  have hInt :=
    integral_center_realize_mul_transportMarkedSet_eq
      μ pe β O R hn.center_le hm.center_le hn.room hm.room
        S₀.2.1 hcardR
  have htermN :=
    localMarkedClusterTerm_eq_integral_mul_exp_neg_correctionSeries
      μ pe β C
        (C.realizedSupport n hn.center_le) S₀.1 hkpN
  have htermM :=
    localMarkedClusterTerm_eq_integral_mul_exp_neg_correctionSeries
      μ pe β C
        (C.realizedSupport m hm.center_le) S₀m.1 hkpM
  have hcorrN :
      (∑' q, localCorrectionSeriesTerm μ pe β
        (C.realizedSupport n hn.center_le ∪
          S₀.1.biUnion plaquetteSupport) 0 q) = corrn := by
    unfold corrn
    rw [realizedFinset_decodedMarkedSet_source
      O R hn.center_le hn.room S₀.2.1 hcardR]
  have hcorrM :
      (∑' q, localCorrectionSeriesTerm μ pe β
        (C.realizedSupport m hm.center_le ∪
          S₀m.1.biUnion plaquetteSupport) 0 q) = corrm := by
    rfl
  rw [htermN, htermM, hcorrN, hcorrM]
  rw [hInt]
  have hfactorTerm :
      (∫ A, (C.realize m A : ℂ) *
          ∏ p ∈ S₀m.1, (plaquetteWeight pe β A p : ℂ)
        ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ)) *
          Complex.exp (-corrn)
        -
      (∫ A, (C.realize m A : ℂ) *
          ∏ p ∈ S₀m.1, (plaquetteWeight pe β A p : ℂ)
        ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ)) *
          Complex.exp (-corrm)
      =
      (∫ A, (C.realize m A : ℂ) *
          ∏ p ∈ S₀m.1, (plaquetteWeight pe β A p : ℂ)
        ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ)) *
        (Complex.exp (-corrn) - Complex.exp (-corrm)) := by
    ring
  change
    ‖(∫ A, (C.realize m A : ℂ) *
          ∏ p ∈ S₀m.1, (plaquetteWeight pe β A p : ℂ)
        ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ)) *
          Complex.exp (-corrn)
        -
      (∫ A, (C.realize m A : ℂ) *
          ∏ p ∈ S₀m.1, (plaquetteWeight pe β A p : ℂ)
        ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ)) *
          Complex.exp (-corrm)‖
      ≤
    ((O.center (R + 2)).bound *
      Real.exp (
        (2 * t) *
          ((((O.center (R + 2)).realizedSupport
            m hm.center_le).card : ℝ) *
            (4 * (d : ℝ)))) *
      (localMarkedEffectiveWeight d B β t) ^ S₀m.1.card) *
    (2 * markedCorrectionCauchyBound O t ε K L)
  rw [hfactorTerm, norm_mul]
  calc
    _ ≤ ‖(∫ A, (C.realize m A : ℂ) *
          ∏ p ∈ S₀m.1, (plaquetteWeight pe β A p : ℂ)
        ∂(gaugeMeasureFrom (d := d) (N := m + 1) μ))‖ *
        (‖Complex.exp (-corrm)‖ *
          (2 * markedCorrectionCauchyBound O t ε K L)) :=
      mul_le_mul_of_nonneg_left hExpDiff (norm_nonneg _)
    _ = ‖localMarkedClusterTerm μ pe β C
          (C.realizedSupport m hm.center_le) S₀m.1‖ *
        (2 * markedCorrectionCauchyBound O t ε K L) := by
      rw [htermM, hcorrM, norm_mul]
      ring
    _ ≤
        (C.bound *
          Real.exp (
            (2 * t) *
              (((C.realizedSupport m hm.center_le).card : ℝ) *
                (4 * (d : ℝ)))) *
          (localMarkedEffectiveWeight d B β t) ^ S₀m.1.card) *
        (2 * markedCorrectionCauchyBound O t ε K L) := by
      apply mul_le_mul_of_nonneg_right
      · exact norm_localMarkedClusterTerm_le_volumeUniform
          μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
            C (C.realizedSupport m hm.center_le) S₀m.1 hkpM
      · unfold markedCorrectionCauchyBound
        positivity

/-- The centered below-cutoff normalized marked sum, indexed by its explicit
finite subtype. -/
noncomputable def centeredMarkedClusterSmallLayer
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K : ℕ)
    (hn : MarkedWindowAdmissible O R n) : ℂ :=
  ∑ S₀ : CenteredMarkedSetBelow O R K hn,
    localMarkedClusterTerm μ pe β
      (O.center (R + 2))
      ((O.center (R + 2)).realizedSupport n hn.center_le)
      S₀.1

/-- The filtered finite sum used by the marked expansion is exactly the
explicit centered marked-set layer. -/
theorem localMarkedClusterSmallSum_eq_centeredMarkedLayer
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (R K : ℕ)
    (hn : MarkedWindowAdmissible O R n) :
    localMarkedClusterSmallSum μ pe β
        (O.center (R + 2))
        ((O.center (R + 2)).realizedSupport n hn.center_le)
        K
      =
    centeredMarkedClusterSmallLayer μ pe β O R K hn := by
  classical
  let f : Finset (ConcretePlaquette d (n + 1)) → ℂ :=
    fun S₀ => localMarkedClusterTerm μ pe β
      (O.center (R + 2))
      ((O.center (R + 2)).realizedSupport n hn.center_le)
      S₀
  have hsub :=
    Finset.sum_subtype_eq_sum_filter
      (p := fun S₀ : Finset (ConcretePlaquette d (n + 1)) =>
        localNear
            ((O.center (R + 2)).realizedSupport n hn.center_le)
            S₀
          = S₀ ∧
        S₀.card < K)
      (s := Finset.univ) f
  unfold localMarkedClusterSmallSum
    centeredMarkedClusterSmallLayer
  simpa [CenteredMarkedSetBelow, f] using hsub.symm

/-- Difference of the two finite marked layers, reduced to the sum of the
single-term Cauchy majorants. -/
theorem norm_centeredMarkedClusterSmallLayer_sub_le_sum
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (hres : (2 * L + 1) + K ≤ R)
    {aN : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    {aM : (connectedLatticePolymerSystem
      (d := d) (N := m + 1) μ pe β).Polymer → ℝ}
    (hkpN : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) aN)
    (hkpM : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β) aM)
    (hboundOne : markedCorrectionCauchyBound
      O t ε K L ≤ 1) :
    ‖centeredMarkedClusterSmallLayer μ pe β O R K hn -
      centeredMarkedClusterSmallLayer μ pe β O R K hm‖
      ≤
    ∑ S₀ : CenteredMarkedSetBelow O R K hn,
      ((O.center (R + 2)).bound *
        Real.exp (
          (2 * t) *
            ((((O.center (R + 2)).realizedSupport
              m hm.center_le).card : ℝ) *
              (4 * (d : ℝ)))) *
        (localMarkedEffectiveWeight d B β t) ^ S₀.1.card) *
      (2 * markedCorrectionCauchyBound O t ε K L) := by
  let e := centeredMarkedSetBelowEquiv
    O R K hKR hn hm
  let fn : CenteredMarkedSetBelow O R K hn → ℂ :=
    fun S₀ => localMarkedClusterTerm μ pe β
      (O.center (R + 2))
      ((O.center (R + 2)).realizedSupport n hn.center_le)
      S₀.1
  let fm : CenteredMarkedSetBelow O R K hm → ℂ :=
    fun S₀ => localMarkedClusterTerm μ pe β
      (O.center (R + 2))
      ((O.center (R + 2)).realizedSupport m hm.center_le)
      S₀.1
  have hreindex :
      (∑ S₀, fm S₀) = ∑ S₀, fm (e S₀) := by
    exact (Fintype.sum_equiv e
      (fun S₀ => fm (e S₀)) fm (fun _ => rfl)).symm
  unfold centeredMarkedClusterSmallLayer
  change ‖(∑ S₀, fn S₀) - ∑ S₀, fm S₀‖ ≤ _
  rw [hreindex, ← Finset.sum_sub_distrib]
  calc
    ‖∑ S₀, (fn S₀ - fm (e S₀))‖
        ≤ ∑ S₀, ‖fn S₀ - fm (e S₀)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ S₀ : CenteredMarkedSetBelow O R K hn,
        ((O.center (R + 2)).bound *
          Real.exp (
            (2 * t) *
              ((((O.center (R + 2)).realizedSupport
                m hm.center_le).card : ℝ) *
                (4 * (d : ℝ)))) *
          (localMarkedEffectiveWeight d B β t) ^ S₀.1.card) *
        (2 * markedCorrectionCauchyBound O t ε K L) := by
      apply Finset.sum_le_sum
      intro S₀ _
      simpa [fn, fm, e,
        centeredMarkedSetBelowEquiv,
        transportCenteredMarkedSetBelow,
        card_transportMarkedSet] using
        (norm_localMarkedClusterTerm_transport_sub_le_volumeUniform
          μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
            O R K L hKR hn hm hres S₀ hkpN hkpM hboundOne)

/-- Uniform elementary resummation of the outer below-cutoff marked
indices. -/
theorem sum_centeredMarkedSetBelow_pow_le_exp_volumeUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (R K : ℕ)
    (hn : MarkedWindowAdmissible O R n)
    (σ η : ℝ) (hσ : 0 ≤ σ) (hη : 0 ≤ η)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (σ * Real.exp η) < 1) :
    (∑ S₀ : CenteredMarkedSetBelow O R K hn,
      σ ^ S₀.1.card)
      ≤
    Real.exp (
      ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
        ((σ * Real.exp η) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (σ * Real.exp η)))) := by
  classical
  let SF :=
    (O.center (R + 2)).realizedSupport n hn.center_le
  let small :=
    (Finset.univ :
      Finset (Finset (ConcretePlaquette d (n + 1)))).filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ S₀.card < K)
  let all :=
    (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ 0 ≤ S₀.card)
  have hsubtype :
      (∑ S₀ : CenteredMarkedSetBelow O R K hn,
        σ ^ S₀.1.card)
        =
      ∑ S₀ ∈ small, σ ^ S₀.card := by
    simpa [CenteredMarkedSetBelow, small, SF] using
      (Finset.sum_subtype_eq_sum_filter
        (p := fun S₀ : Finset (ConcretePlaquette d (n + 1)) =>
          localNear SF S₀ = S₀ ∧ S₀.card < K)
        (s := Finset.univ)
        (fun S₀ => σ ^ S₀.card))
  have hsubset : small ⊆ all := by
    intro S₀ hS₀
    change S₀ ∈ (Finset.univ :
      Finset (Finset (ConcretePlaquette d (n + 1)))).filter
        (fun T => localNear SF T = T ∧ T.card < K) at hS₀
    rw [Finset.mem_filter] at hS₀
    change S₀ ∈ (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
        (fun T => localNear SF T = T ∧ 0 ≤ T.card)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hS₀.2.1, Nat.zero_le _⟩
  have hsmallAll :
      (∑ S₀ ∈ small, σ ^ S₀.card)
        ≤
      ∑ S₀ ∈ all, σ ^ S₀.card :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun S₀ _ _ => pow_nonneg hσ _)
  have htail :=
    localPinnedSetTailWeight_le_exp_volumeUniform
      SF σ η hσ hη 0 hr
  rw [hsubtype]
  calc
    (∑ S₀ ∈ small, σ ^ S₀.card)
        ≤ ∑ S₀ ∈ all, σ ^ S₀.card := hsmallAll
    _ = localPinnedSetTailWeight SF σ 0 := by
      rfl
    _ ≤ Real.exp (-(η * (0 : ℝ))) *
        Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            ((σ * Real.exp η) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (σ * Real.exp η)))) := by
      simpa using htail
    _ = Real.exp (
        ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
          ((σ * Real.exp η) /
            (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
              (σ * Real.exp η)))) := by
      rw [CompatibleLocalObservable.card_realizedSupport,
        CompatibleLocalObservable.card_support_center]
      simp

/-- **Quantitative two-volume bound for the complete below-cutoff normalized
marked sum.** -/
theorem norm_centeredMarkedClusterSmallLayer_sub_le_volumeUniform
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ)
    (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (hres : (2 * L + 1) + K ≤ R)
    {aN : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    {aM : (connectedLatticePolymerSystem
      (d := d) (N := m + 1) μ pe β).Polymer → ℝ}
    (hkpN : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) aN)
    (hkpM : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β) aM)
    (hboundOne : markedCorrectionCauchyBound
      O t ε K L ≤ 1)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    ‖centeredMarkedClusterSmallLayer μ pe β O R K hn -
      centeredMarkedClusterSmallLayer μ pe β O R K hm‖
      ≤
    (((O.center (R + 2)).bound *
      Real.exp (
        (2 * t) *
          ((((O.center (R + 2)).realizedSupport
            m hm.center_le).card : ℝ) *
            (4 * (d : ℝ))))) *
      (2 * markedCorrectionCauchyBound O t ε K L)) *
    Real.exp (
      ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
        ((localMarkedEffectiveWeight d B β t * Real.exp η) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (localMarkedEffectiveWeight d B β t *
              Real.exp η)))) := by
  let σ := localMarkedEffectiveWeight d B β t
  let A := (O.center (R + 2)).bound *
    Real.exp (
      (2 * t) *
        ((((O.center (R + 2)).realizedSupport
          m hm.center_le).card : ℝ) *
          (4 * (d : ℝ))))
  let D := markedCorrectionCauchyBound O t ε K L
  let E := Real.exp (
    ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
      ((σ * Real.exp η) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (σ * Real.exp η))))
  have hB : 0 ≤ B :=
    le_trans (abs_nonneg _) (hpe 1)
  have hδ : 0 ≤ Real.exp (|β| * B) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonneg (abs_nonneg β) hB)
  have hσ : 0 ≤ σ := by
    dsimp only [σ, localMarkedEffectiveWeight]
    exact mul_nonneg hδ (Real.exp_pos _).le
  have hD : 0 ≤ D := by
    dsimp only [D, markedCorrectionCauchyBound]
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (O.center (R + 2)).bound_nonneg
      (Real.exp_pos _).le
  have hlayer :=
    norm_centeredMarkedClusterSmallLayer_sub_le_sum
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
        O R K L hKR hn hm hres hkpN hkpM hboundOne
  have hsum :
      (∑ S₀ : CenteredMarkedSetBelow O R K hn,
        σ ^ S₀.1.card) ≤ E := by
    exact sum_centeredMarkedSetBelow_pow_le_exp_volumeUniform
      O R K hn σ η hσ hη0
        (by simpa [σ] using hrMarked)
  calc
    ‖centeredMarkedClusterSmallLayer μ pe β O R K hn -
        centeredMarkedClusterSmallLayer μ pe β O R K hm‖
        ≤
      ∑ S₀ : CenteredMarkedSetBelow O R K hn,
        ((A * σ ^ S₀.1.card) * (2 * D)) := by
          simpa [A, D, σ] using hlayer
    _ = (A * (2 * D)) *
        ∑ S₀ : CenteredMarkedSetBelow O R K hn,
          σ ^ S₀.1.card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S₀ _
      ring
    _ ≤ (A * (2 * D)) * E :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hA (mul_nonneg (by positivity) hD))
    _ = (((O.center (R + 2)).bound *
        Real.exp (
          (2 * t) *
            ((((O.center (R + 2)).realizedSupport
              m hm.center_le).card : ℝ) *
              (4 * (d : ℝ))))) *
        (2 * markedCorrectionCauchyBound O t ε K L)) *
      Real.exp (
        ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
          ((localMarkedEffectiveWeight d B β t * Real.exp η) /
            (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
              (localMarkedEffectiveWeight d B β t *
                Real.exp η)))) := by rfl

/-- Outer marked-set truncation error used in the final Gibbs Cauchy
estimate. -/
noncomputable def markedOuterTailBound
    {d : ℕ} {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (B β t η : ℝ) (K : ℕ) : ℝ :=
  (O.bound *
    Real.exp (
      (2 * t) *
        ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))))) *
  (Real.exp (-(η * K)) *
    Real.exp (
      ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
        ((localMarkedEffectiveWeight d B β t * Real.exp η) /
          (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
            (localMarkedEffectiveWeight d B β t *
              Real.exp η)))))

/-- Error caused by changing the normalization correction inside the
below-cutoff marked layer. -/
noncomputable def markedSmallLayerCauchyBound
    {d : ℕ} {G : Type*} [Group G] [MeasurableSpace G]
    (O : CompatibleLocalObservable d G)
    (B β t ε η : ℝ) (K L : ℕ) : ℝ :=
  ((O.bound *
    Real.exp (
      (2 * t) *
        ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ)))) *
    (2 * markedCorrectionCauchyBound O t ε K L)) *
  Real.exp (
    ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
      ((localMarkedEffectiveWeight d B β t * Real.exp η) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          (localMarkedEffectiveWeight d B β t *
            Real.exp η)))))

/-- Simplified, radius-independent form of the finite marked-layer Cauchy
bound. -/
theorem norm_centeredMarkedClusterSmallLayer_sub_le_explicit
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ}
    (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ)
    (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (hres : (2 * L + 1) + K ≤ R)
    {aN : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    {aM : (connectedLatticePolymerSystem
      (d := d) (N := m + 1) μ pe β).Polymer → ℝ}
    (hkpN : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) aN)
    (hkpM : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β) aM)
    (hboundOne : markedCorrectionCauchyBound
      O t ε K L ≤ 1)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    ‖centeredMarkedClusterSmallLayer μ pe β O R K hn -
      centeredMarkedClusterSmallLayer μ pe β O R K hm‖
      ≤
    markedSmallLayerCauchyBound O B β t ε η K L := by
  have h :=
    norm_centeredMarkedClusterSmallLayer_sub_le_volumeUniform
      μ hpe β t ε η ht0 hε0 hη0 hr₀ hsmall₀ hr₁ hsmall₁
        O R K L hKR hn hm hres hkpN hkpM hboundOne hrMarked
  simpa [markedSmallLayerCauchyBound,
    CompatibleLocalObservable.card_realizedSupport] using h

/-- **Direct two-volume Cauchy estimate for genuine local Gibbs
expectations.**  The first and last terms are the marked-set tails; the
middle term is the transported below-cutoff layer.  No subsequence or
compactness argument enters this estimate. -/
theorem norm_localGibbsExpectation_sub_le_volumeUniform
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ)
    (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (hres : (2 * L + 1) + K ≤ R)
    {aN : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    {aM : (connectedLatticePolymerSystem
      (d := d) (N := m + 1) μ pe β).Polymer → ℝ}
    (hkpN : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) aN)
    (hkpM : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := m + 1) μ pe β) aM)
    (hboundOne : markedCorrectionCauchyBound
      O t ε K L ≤ 1)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    ‖(localGibbsExpectation μ pe β O n : ℂ) -
        (localGibbsExpectation μ pe β O m : ℂ)‖
      ≤
    2 * markedOuterTailBound O B β t η K +
      markedSmallLayerCauchyBound O B β t ε η K L := by
  let C := O.center (R + 2)
  let Sn : ℂ :=
    centeredMarkedClusterSmallLayer μ pe β O R K hn
  let Sm : ℂ :=
    centeredMarkedClusterSmallLayer μ pe β O R K hm
  have hnTail₀ :=
    norm_localGibbsExpectation_sub_localMarkedClusterSmallSum_le_volumeUniform
      μ hpe_meas hpe β t ε η ht0 hε0 hη0
        hr₀ hsmall₀ hr₁ hsmall₁ C hn.center_le K hkpN hrMarked
  have hmTail₀ :=
    norm_localGibbsExpectation_sub_localMarkedClusterSmallSum_le_volumeUniform
      μ hpe_meas hpe β t ε η ht0 hε0 hη0
        hr₀ hsmall₀ hr₁ hsmall₁ C hm.center_le K hkpM hrMarked
  have hnTail :
      ‖(localGibbsExpectation μ pe β C n : ℂ) - Sn‖
        ≤ markedOuterTailBound O B β t η K := by
    rw [localMarkedClusterSmallSum_eq_centeredMarkedLayer
      μ pe β O R K hn] at hnTail₀
    simpa [C, Sn, markedOuterTailBound,
      CompatibleLocalObservable.card_support_center] using hnTail₀
  have hmTail :
      ‖(localGibbsExpectation μ pe β C m : ℂ) - Sm‖
        ≤ markedOuterTailBound O B β t η K := by
    rw [localMarkedClusterSmallSum_eq_centeredMarkedLayer
      μ pe β O R K hm] at hmTail₀
    simpa [C, Sm, markedOuterTailBound,
      CompatibleLocalObservable.card_support_center] using hmTail₀
  have hsmall :
      ‖Sn - Sm‖ ≤
        markedSmallLayerCauchyBound O B β t ε η K L := by
    simpa [Sn, Sm] using
      (norm_centeredMarkedClusterSmallLayer_sub_le_explicit
        μ hpe β t ε η ht0 hε0 hη0
          hr₀ hsmall₀ hr₁ hsmall₁ O R K L hKR hn hm hres
          hkpN hkpM hboundOne hrMarked)
  have hnCenter :
      localGibbsExpectation μ pe β C n =
        localGibbsExpectation μ pe β O n := by
    simpa [C] using
      (localGibbsExpectation_center μ pe β O (R + 2) n hn.center_le)
  have hmCenter :
      localGibbsExpectation μ pe β C m =
        localGibbsExpectation μ pe β O m := by
    simpa [C] using
      (localGibbsExpectation_center μ pe β O (R + 2) m hm.center_le)
  rw [← hnCenter, ← hmCenter]
  calc
    ‖(localGibbsExpectation μ pe β C n : ℂ) -
        (localGibbsExpectation μ pe β C m : ℂ)‖
        =
      ‖((localGibbsExpectation μ pe β C n : ℂ) - Sn) +
        (Sn - Sm) +
        (Sm - (localGibbsExpectation μ pe β C m : ℂ))‖ := by
          congr 1
          ring
    _ ≤
        ‖(localGibbsExpectation μ pe β C n : ℂ) - Sn‖ +
          ‖Sn - Sm‖ +
          ‖Sm - (localGibbsExpectation μ pe β C m : ℂ)‖ := by
      calc
        ‖((localGibbsExpectation μ pe β C n : ℂ) - Sn) +
            (Sn - Sm) +
            (Sm - (localGibbsExpectation μ pe β C m : ℂ))‖
            ≤
          ‖((localGibbsExpectation μ pe β C n : ℂ) - Sn) +
            (Sn - Sm)‖ +
          ‖Sm - (localGibbsExpectation μ pe β C m : ℂ)‖ :=
            norm_add_le _ _
        _ ≤
          (‖(localGibbsExpectation μ pe β C n : ℂ) - Sn‖ +
            ‖Sn - Sm‖) +
          ‖Sm - (localGibbsExpectation μ pe β C m : ℂ)‖ :=
            add_le_add (norm_add_le _ _) le_rfl
    _ ≤
        markedOuterTailBound O B β t η K +
          markedSmallLayerCauchyBound O B β t ε η K L +
          markedOuterTailBound O B β t η K := by
      exact add_le_add
        (add_le_add hnTail hsmall)
        (by simpa [norm_sub_rev] using hmTail)
    _ =
        2 * markedOuterTailBound O B β t η K +
          markedSmallLayerCauchyBound O B β t ε η K L := by
      ring

/-- The direct Cauchy estimate with the finite-volume KP witnesses supplied
canonically by the volume-uniform connected-lattice criterion. -/
theorem norm_localGibbsExpectation_sub_le_kpUniform
    {d n m : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ)
    (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) *
        Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) *
          Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) *
            Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (R K L : ℕ) (hKR : K ≤ R)
    (hn : MarkedWindowAdmissible O R n)
    (hm : MarkedWindowAdmissible O R m)
    (hres : (2 * L + 1) + K ≤ R)
    (hboundOne : markedCorrectionCauchyBound
      O t ε K L ≤ 1)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    ‖(localGibbsExpectation μ pe β O n : ℂ) -
        (localGibbsExpectation μ pe β O m : ℂ)‖
      ≤
    2 * markedOuterTailBound O B β t η K +
      markedSmallLayerCauchyBound O B β t ε η K L := by
  have hkpN :=
    connectedLatticePolymerSystem_kpCriterion_volumeUniform
      (d := d) (N := n + 1) μ hpe β (t + ε)
        (add_nonneg ht0 hε0) hr₀
        (hsmall₀.trans (le_add_of_nonneg_right hε0))
  have hkpM :=
    connectedLatticePolymerSystem_kpCriterion_volumeUniform
      (d := d) (N := m + 1) μ hpe β (t + ε)
        (add_nonneg ht0 hε0) hr₀
        (hsmall₀.trans (le_add_of_nonneg_right hε0))
  exact norm_localGibbsExpectation_sub_le_volumeUniform
    μ hpe_meas hpe β t ε η ht0 hε0 hη0
      hr₀ hsmall₀ hr₁ hsmall₁ O R K L hKR hn hm hres
      hkpN hkpM hboundOne hrMarked

end WindowPolymer

end YangMills
