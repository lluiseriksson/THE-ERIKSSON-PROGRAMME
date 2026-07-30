/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalMarkedCorrectionTransport

/-!
# Quantitative Cauchy bound for marked normalization corrections

The below-cutoff correction series agrees exactly by joint common-window
transport.  Both remaining tails are bounded by the same rooted KP tail,
with a volume-free pinning-support cardinality.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- **Direct two-volume bound for the normalization correction attached to
one transported marked window.** -/
theorem norm_localCorrectionSeries_commonCombined_sub_le_volumeUniform
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
    (R K L : ℕ)
    (hCn : (O.center (R + 2)).minVolume ≤ n)
    (hCm : (O.center (R + 2)).minVolume ≤ m)
    (hroomN :
      O.minVolume + (R + 2) + 1 + R + 1 < n + 1)
    (hroomM :
      O.minVolume + (R + 2) + 1 + R + 1 < m + 1)
    (S : Finset (WindowPlaquette d))
    (hSn : ∀ p ∈ S, p.Fits (n + 1))
    (hSm : ∀ p ∈ S, p.Fits (m + 1))
    (hnearN : localNear
      ((O.center (R + 2)).realizedSupport n hCn)
      (WindowPlaquette.realizedFinset S hSn)
        =
      WindowPlaquette.realizedFinset S hSn)
    (hcardS : S.card ≤ K)
    (hres : (2 * L + 1) + K ≤ R) :
    ‖(∑' q, localCorrectionSeriesTerm μ pe β
          (((O.center (R + 2)).realizedSupport n hCn) ∪
            (WindowPlaquette.realizedFinset S hSn).biUnion
              plaquetteSupport)
          0 q)
        -
      ∑' q, localCorrectionSeriesTerm μ pe β
          (((O.center (R + 2)).realizedSupport m hCm) ∪
            (WindowPlaquette.realizedFinset S hSm).biUnion
              plaquetteSupport)
          0 q‖
      ≤
    2 * (Real.exp (-(ε * L)) *
      ((2 * t) *
        (((Fintype.card O.Support + 4 * K : ℕ) : ℝ) *
          (4 * (d : ℝ))))) := by
  let SFn :=
    ((O.center (R + 2)).realizedSupport n hCn) ∪
      (WindowPlaquette.realizedFinset S hSn).biUnion
        plaquetteSupport
  let SFm :=
    ((O.center (R + 2)).realizedSupport m hCm) ∪
      (WindowPlaquette.realizedFinset S hSm).biUnion
        plaquetteSupport
  let fulln := ∑' q,
    localCorrectionSeriesTerm μ pe β SFn 0 q
  let fullm := ∑' q,
    localCorrectionSeriesTerm μ pe β SFm 0 q
  let smalln := ∑' q,
    localCorrectionSmallSeriesTerm μ pe β SFn L q
  let smallm := ∑' q,
    localCorrectionSmallSeriesTerm μ pe β SFm L q
  let C := Real.exp (-(ε * L)) *
    ((2 * t) *
      (((Fintype.card O.Support + 4 * K : ℕ) : ℝ) *
        (4 * (d : ℝ))))
  have hsmall : smalln = smallm := by
    exact localCorrectionSmallSeries_commonCombined_eq
      μ pe β O R K L hCn hCm hroomN hroomM
        S hSn hSm hnearN hcardS hres
  have hcardn :
      SFn.card ≤ Fintype.card O.Support + 4 * K := by
    calc
      SFn.card
          ≤ ((O.center (R + 2)).realizedSupport
                n hCn).card +
              4 * (WindowPlaquette.realizedFinset S hSn).card :=
        card_union_biUnion_plaquetteSupport_le _ _
      _ = Fintype.card O.Support + 4 * S.card := by
        rw [CompatibleLocalObservable.card_realizedSupport,
          CompatibleLocalObservable.card_support_center,
          WindowPlaquette.card_realizedFinset]
      _ ≤ Fintype.card O.Support + 4 * K := by omega
  have hcardm :
      SFm.card ≤ Fintype.card O.Support + 4 * K := by
    calc
      SFm.card
          ≤ ((O.center (R + 2)).realizedSupport
                m hCm).card +
              4 * (WindowPlaquette.realizedFinset S hSm).card :=
        card_union_biUnion_plaquetteSupport_le _ _
      _ = Fintype.card O.Support + 4 * S.card := by
        rw [CompatibleLocalObservable.card_realizedSupport,
          CompatibleLocalObservable.card_support_center,
          WindowPlaquette.card_realizedFinset]
      _ ≤ Fintype.card O.Support + 4 * K := by omega
  have hcoef :
      0 ≤ Real.exp (-(ε * L)) *
        ((2 * t) * (4 * (d : ℝ))) := by positivity
  have hnTail : ‖fulln - smalln‖ ≤ C := by
    have htail :=
      norm_localCorrectionSeries_sub_small_le_volumeUniform
        μ hpe β t ε ht0 hε0 hr₀ hsmall₀
          hr₁ hsmall₁ SFn L
    change ‖(∑' q, localCorrectionSeriesTerm μ pe β SFn 0 q)
        - ∑' q,
          localCorrectionSmallSeriesTerm μ pe β SFn L q‖ ≤ C
    calc
      _ ≤ Real.exp (-(ε * L)) *
          ((2 * t) * ((SFn.card : ℝ) *
            (4 * (d : ℝ)))) := htail
      _ = (SFn.card : ℝ) *
          (Real.exp (-(ε * L)) *
            ((2 * t) * (4 * (d : ℝ)))) := by ring
      _ ≤ ((Fintype.card O.Support + 4 * K : ℕ) : ℝ) *
          (Real.exp (-(ε * L)) *
            ((2 * t) * (4 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcardn) hcoef
      _ = C := by ring
  have hmTail : ‖fullm - smallm‖ ≤ C := by
    have htail :=
      norm_localCorrectionSeries_sub_small_le_volumeUniform
        μ hpe β t ε ht0 hε0 hr₀ hsmall₀
          hr₁ hsmall₁ SFm L
    change ‖(∑' q, localCorrectionSeriesTerm μ pe β SFm 0 q)
        - ∑' q,
          localCorrectionSmallSeriesTerm μ pe β SFm L q‖ ≤ C
    calc
      _ ≤ Real.exp (-(ε * L)) *
          ((2 * t) * ((SFm.card : ℝ) *
            (4 * (d : ℝ)))) := htail
      _ = (SFm.card : ℝ) *
          (Real.exp (-(ε * L)) *
            ((2 * t) * (4 * (d : ℝ)))) := by ring
      _ ≤ ((Fintype.card O.Support + 4 * K : ℕ) : ℝ) *
          (Real.exp (-(ε * L)) *
            ((2 * t) * (4 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast hcardm) hcoef
      _ = C := by ring
  change ‖fulln - fullm‖ ≤ 2 * C
  calc
    ‖fulln - fullm‖
        = ‖(fulln - smalln) - (fullm - smallm)‖ := by
          rw [hsmall]
          congr 1
          ring
    _ ≤ ‖fulln - smalln‖ + ‖fullm - smallm‖ :=
      norm_sub_le _ _
    _ ≤ C + C := add_le_add hnTail hmTail
    _ = 2 * C := by ring

end WindowPolymer

end YangMills
