/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalSmallCorrectionCauchy

/-!
# Volume-uniform summation of the outer marked sets

The exact Gibbs formula still contains a finite sum over plaquette sets every
connected component of which meets the local observable support.  This module
majorizes that outer sum without introducing an Ursell tuple: components are
resummed as an elementary pinned polymer gas and the lattice-animal estimate
controls every rooted connected component uniformly in the torus volume.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- The sum of bare `σ^|c|` weights over connected plaquette sets which meet
the positive-edge support `SF`. -/
noncomputable def localConnectedMarkedWeight
    {d N : ℕ} [NeZero d] [NeZero N]
    (SF : Finset (PosEdge d N)) (σ : ℝ) : ℝ :=
  ∑ c ∈ (Finset.univ :
      Finset (Finset (ConcretePlaquette d N))).filter
      (fun c => (c.Nonempty ∧ IsConnectedPolymer c) ∧
        ∃ p ∈ c, ¬ Disjoint SF (plaquetteSupport p)),
    σ ^ c.card

open Classical in
/-- The connected marked-component weight is bounded by the number of local
root plaquettes times the volume-uniform rooted animal series. -/
theorem localConnectedMarkedWeight_le_volumeUniform
    {d N : ℕ} [NeZero d] [NeZero N]
    (SF : Finset (PosEdge d N)) (σ : ℝ) (hσ : 0 ≤ σ)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ < 1) :
    localConnectedMarkedWeight SF σ
      ≤ ((supportPlaquettes SF).card : ℝ) *
          (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ)) := by
  classical
  let Conn :=
    {c : Finset (ConcretePlaquette d N) //
      c.Nonempty ∧ IsConnectedPolymer c}
  let R := supportPlaquettes SF
  let S := σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ)
  let conn : Finset (ConcretePlaquette d N) → Prop :=
    fun c => c.Nonempty ∧ IsConnectedPolymer c
  let marked : Finset (ConcretePlaquette d N) → Prop :=
    fun c => conn c ∧ ∃ p ∈ c, ¬ Disjoint SF (plaquetteSupport p)
  let g : Finset (ConcretePlaquette d N) → ℝ := fun c =>
    ∑ p ∈ R, if p ∈ c then σ ^ c.card else 0
  have hg0 : ∀ c, 0 ≤ g c := by
    intro c
    exact Finset.sum_nonneg fun p _ => by
      split_ifs
      · positivity
      · exact le_rfl
  have hterm : ∀ c, marked c → σ ^ c.card ≤ g c := by
    intro c hc
    obtain ⟨_, q, hqc, hqSF⟩ := hc
    have hqR : q ∈ R := by
      obtain ⟨e, heSF, heq⟩ :=
        Finset.not_disjoint_iff.mp hqSF
      exact ConcreteSupport.mem_supportPlaquettes_iff.mpr
        ⟨e, heSF, heq⟩
    have hsingle := Finset.single_le_sum
      (f := fun p => if p ∈ c then σ ^ c.card else 0)
      (fun p _ => by
        change 0 ≤ if p ∈ c then σ ^ c.card else 0
        split_ifs
        · positivity
        · exact le_rfl)
      hqR
    simpa [g, hqc] using hsingle
  have hsubset :
      (Finset.univ.filter marked :
        Finset (Finset (ConcretePlaquette d N)))
        ⊆ Finset.univ.filter conn := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, hc.2.1⟩
  have hreindex :
      (∑ c ∈ (Finset.univ :
          Finset (Finset (ConcretePlaquette d N))).filter conn, g c)
        =
      ∑ c : Conn, g c.1 := by
    simpa [Conn, conn] using
      (Finset.sum_subtype_eq_sum_filter
        (p := conn)
        (s := (Finset.univ :
          Finset (Finset (ConcretePlaquette d N))))
        g).symm
  have hroot : ∀ p : ConcretePlaquette d N,
      (∑ c ∈ (Finset.univ : Finset Conn).filter
          (fun c => p ∈ c.1), σ ^ c.1.card) ≤ S := by
    intro p
    simpa [Conn, S] using
      (sum_connectedPolymers_through_le
        (d := d) (N := N) p σ hσ hr)
  unfold localConnectedMarkedWeight
  change (∑ c ∈ (Finset.univ :
      Finset (Finset (ConcretePlaquette d N))).filter marked,
        σ ^ c.card) ≤ _
  calc
    (∑ c ∈ (Finset.univ :
        Finset (Finset (ConcretePlaquette d N))).filter marked,
          σ ^ c.card)
        ≤ ∑ c ∈ (Finset.univ :
            Finset (Finset (ConcretePlaquette d N))).filter marked,
            g c := Finset.sum_le_sum fun c hc =>
              hterm c (Finset.mem_filter.mp hc).2
    _ ≤ ∑ c ∈ (Finset.univ :
          Finset (Finset (ConcretePlaquette d N))).filter conn,
          g c :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun c _ _ => hg0 c)
    _ = ∑ c : Conn, g c.1 := hreindex
    _ = ∑ p ∈ R, ∑ c : Conn,
          if p ∈ c.1 then σ ^ c.1.card else 0 := by
      simp only [g]
      rw [Finset.sum_comm]
    _ = ∑ p ∈ R, ∑ c ∈ (Finset.univ : Finset Conn).filter
          (fun c => p ∈ c.1), σ ^ c.1.card := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_filter]
    _ ≤ ∑ _p ∈ R, S :=
      Finset.sum_le_sum fun p _ => hroot p
    _ = ((R.card : ℕ) : ℝ) * S := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((supportPlaquettes SF).card : ℝ) *
          (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ)) := rfl

open Classical in
/-- **Uniform elementary resummation of every marked plaquette set.**

There is no Ursell rooting factor here: connected components of the marked
set are resummed directly, and each component is charged to one plaquette
incident to the finite edge support. -/
theorem localPinnedSetWeight_le_exp_volumeUniform
    {d N : ℕ} [NeZero d] [NeZero N]
    (SF : Finset (PosEdge d N)) (σ : ℝ) (hσ : 0 ≤ σ)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ < 1) :
    (∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d N)).powerset.filter
        (fun S₀ => localNear SF S₀ = S₀),
      σ ^ S₀.card)
      ≤ Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ))) := by
  classical
  let C : ℝ := ((16 * d + 1 : ℕ) : ℝ) ^ 2
  let S : ℝ := σ / (1 - C * σ)
  let comps :=
    (Finset.univ :
      Finset (Finset (ConcretePlaquette d N))).filter
      (fun c => (c.Nonempty ∧ IsConnectedPolymer c) ∧
        ∃ p ∈ c, ¬ Disjoint SF (plaquetteSupport p))
  have hS0 : 0 ≤ S := by
    have hden : 0 < 1 - C * σ := by
      dsimp only [C]
      linarith
    exact div_nonneg hσ hden.le
  have hpinned := sum_pinned_pow_le_prod
    (d := d) (N := N) (supportEdgeList SF) σ hσ
  have hprod :
      (∏ c ∈ comps, (1 + σ ^ c.card))
        ≤ Real.exp (localConnectedMarkedWeight SF σ) := by
    have h := prod_one_add_le_exp_sum comps
      (fun c => σ ^ c.card)
      (fun c _ => pow_nonneg hσ _)
    simpa [comps, localConnectedMarkedWeight] using h
  have hcomp := localConnectedMarkedWeight_le_volumeUniform
    SF σ hσ hr
  have hroot :
      ((supportPlaquettes SF).card : ℝ) * S
        ≤ ((SF.card : ℝ) * (4 * (d : ℝ))) * S := by
    exact mul_le_mul_of_nonneg_right
      (card_supportPlaquettes_le SF) hS0
  calc
    (∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d N)).powerset.filter
        (fun S₀ => localNear SF S₀ = S₀),
      σ ^ S₀.card)
        ≤ ∏ c ∈ comps, (1 + σ ^ c.card) := by
          simpa [localNear, comps, edgeSupport_supportEdgeList] using
            hpinned
    _ ≤ Real.exp (localConnectedMarkedWeight SF σ) := hprod
    _ ≤ Real.exp (((SF.card : ℝ) * (4 * (d : ℝ))) * S) := by
      apply Real.exp_le_exp.mpr
      exact hcomp.trans hroot
    _ = Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            (σ / (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * σ))) := rfl

/-- Marked sets of plaquette cardinality at least `L`, with their bare
geometric weight. -/
noncomputable def localPinnedSetTailWeight
    {d N : ℕ} [NeZero d] [NeZero N]
    (SF : Finset (PosEdge d N)) (σ : ℝ) (L : ℕ) : ℝ :=
  ∑ S₀ ∈ (Finset.univ :
      Finset (ConcretePlaquette d N)).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
    σ ^ S₀.card

open Classical in
/-- **Exponential cardinality tail for the outer marked-set sum.**

The factor `exp (-ε L)` is extracted by tilting the elementary component
weight from `σ` to `σ * exp ε`.  No tuple-coordinate symmetrization occurs. -/
theorem localPinnedSetTailWeight_le_exp_volumeUniform
    {d N : ℕ} [NeZero d] [NeZero N]
    (SF : Finset (PosEdge d N)) (σ ε : ℝ)
    (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (L : ℕ)
    (hr : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (σ * Real.exp ε) < 1) :
    localPinnedSetTailWeight SF σ L
      ≤ Real.exp (-(ε * L)) *
          Real.exp (
            ((SF.card : ℝ) * (4 * (d : ℝ))) *
              ((σ * Real.exp ε) /
                (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                  (σ * Real.exp ε)))) := by
  classical
  let T :=
    (Finset.univ :
      Finset (ConcretePlaquette d N)).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card)
  let F :=
    (Finset.univ :
      Finset (ConcretePlaquette d N)).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀)
  let στ := σ * Real.exp ε
  have hστ : 0 ≤ στ := mul_nonneg hσ (Real.exp_pos ε).le
  have hpow : ∀ S₀ ∈ T,
      σ ^ S₀.card
        ≤ Real.exp (-(ε * L)) * στ ^ S₀.card := by
    intro S₀ hS₀
    have hcard : L ≤ S₀.card :=
      (Finset.mem_filter.mp hS₀).2.2
    have hcast : (L : ℝ) ≤ (S₀.card : ℝ) := by
      exact_mod_cast hcard
    have hexp :
        Real.exp (ε * (L : ℝ))
          ≤ Real.exp (ε * (S₀.card : ℝ)) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hcast hε)
    have hcancel :
        Real.exp (-(ε * (L : ℝ))) *
            Real.exp (ε * (L : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      σ ^ S₀.card
          = Real.exp (-(ε * L)) *
              (Real.exp (ε * L) * σ ^ S₀.card) := by
            rw [show ε * (L : ℝ) = ε * L by norm_num,
              ← mul_assoc, hcancel, one_mul]
      _ ≤ Real.exp (-(ε * L)) *
            (Real.exp (ε * (S₀.card : ℝ)) * σ ^ S₀.card) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hexp
              (pow_nonneg hσ _))
            (Real.exp_pos _).le
      _ = Real.exp (-(ε * L)) * στ ^ S₀.card := by
          congr 1
          dsimp only [στ]
          rw [mul_pow, ← Real.exp_nat_mul]
          rw [show (S₀.card : ℝ) * ε =
              ε * (S₀.card : ℝ) by ring]
          ring
  have hsub : T ⊆ F := by
    intro S₀ hS₀
    rw [Finset.mem_filter] at hS₀ ⊢
    exact ⟨hS₀.1, hS₀.2.1⟩
  have hfull := localPinnedSetWeight_le_exp_volumeUniform
    SF στ hστ hr
  unfold localPinnedSetTailWeight
  change (∑ S₀ ∈ T, σ ^ S₀.card) ≤ _
  calc
    (∑ S₀ ∈ T, σ ^ S₀.card)
        ≤ ∑ S₀ ∈ T,
            Real.exp (-(ε * L)) * στ ^ S₀.card :=
      Finset.sum_le_sum fun S₀ hS₀ => hpow S₀ hS₀
    _ = Real.exp (-(ε * L)) * ∑ S₀ ∈ T, στ ^ S₀.card := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-(ε * L)) * ∑ S₀ ∈ F, στ ^ S₀.card := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun S₀ _ _ => pow_nonneg hστ _)
    _ ≤ Real.exp (-(ε * L)) *
        Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            (στ /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 * στ))) := by
      exact mul_le_mul_of_nonneg_left hfull (Real.exp_pos _).le
    _ = Real.exp (-(ε * L)) *
          Real.exp (
            ((SF.card : ℝ) * (4 * (d : ℝ))) *
              ((σ * Real.exp ε) /
                (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                  (σ * Real.exp ε)))) := rfl

/-- The arbitrary local observable contributes only its uniform sup norm to
the marked integral; every selected plaquette contributes one Mayer-weight
factor. -/
theorem norm_integral_realize_mul_prod_plaquetteWeight_le
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (S₀ : Finset (ConcretePlaquette d (n + 1))) :
    ‖∫ A, (O.realize n A : ℂ) *
        ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
      ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)‖
      ≤ O.bound * (Real.exp (|β| * B) - 1) ^ S₀.card := by
  let δ := Real.exp (|β| * B) - 1
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hpe 1)
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonneg (abs_nonneg β) hB)
  have hbound := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := gaugeMeasureFrom (d := d) (N := n + 1) μ)
    (f := fun A : GaugeConfig d (n + 1) G =>
      (O.realize n A : ℂ) *
        ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ))
    (C := O.bound * δ ^ S₀.card) ?_
  · simpa [measure_univ, δ] using hbound
  · refine MeasureTheory.ae_of_all _ fun A => ?_
    rw [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul (O.abs_realize_le n A) ?_
      (Finset.prod_nonneg fun p _ => norm_nonneg _)
      O.bound_nonneg
    calc
      (∏ p ∈ S₀, ‖(plaquetteWeight pe β A p : ℂ)‖)
          ≤ ∏ _p ∈ S₀, δ := by
            refine Finset.prod_le_prod
              (fun p _ => norm_nonneg _)
              (fun p _ => ?_)
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact abs_plaquetteWeight_le pe β A p hpe
      _ = δ ^ S₀.card := by
        rw [Finset.prod_const]

/-- The normalized far-gas correction attached to one marked set grows at
most exponentially in the size of that marked set, with a volume-free
coefficient.  The extensive cluster sums are first replaced by their exact
local correction series. -/
theorem norm_exp_localFarClusterDiff_le_volumeUniform
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)))) ≤ t)
    (SF : Finset (PosEdge d N))
    (S₀ : Finset (ConcretePlaquette d N))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := N) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := N) μ pe β) a) :
    ‖Complex.exp (
        KP.clusterSum
          ((connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).restrict
            (Finset.univ.filter
              (fun c => c.1 ⊆ localFarRegion SF S₀)))
        -
        KP.clusterSum
          (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β))‖
      ≤ Real.exp (
          (2 * t) *
            (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
              (4 * (d : ℝ)))) := by
  let U := SF ∪ S₀.biUnion plaquetteSupport
  let corr := ∑' q, localCorrectionSeriesTerm μ pe β U 0 q
  have hcorr := clusterSum_sub_localFarRegion_eq_localCorrectionSeries
    μ pe β SF S₀ hkp
  have hexponent :
      KP.clusterSum
          ((connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).restrict
            (Finset.univ.filter
              (fun c => c.1 ⊆ localFarRegion SF S₀)))
        -
        KP.clusterSum
          (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β)
        = -corr := by
    dsimp only [corr]
    rw [← hcorr]
    ring
  have hseries := (localCorrectionSeries_summable_volumeUniform
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ U 0).2
  have hcard :
      (U.card : ℝ) ≤ ((SF.card + 4 * S₀.card : ℕ) : ℝ) := by
    exact_mod_cast card_union_biUnion_plaquetteSupport_le SF S₀
  have hseries' :
      ‖corr‖ ≤
        (2 * t) *
          (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
            (4 * (d : ℝ))) := by
    have hfactor : 0 ≤ (2 * t) * (4 * (d : ℝ)) := by positivity
    calc
      ‖corr‖
          ≤ Real.exp (-(ε * 0)) *
              ((2 * t) * ((U.card : ℝ) * (4 * (d : ℝ)))) := by
            simpa [corr] using hseries
      _ = ((U.card : ℝ)) * ((2 * t) * (4 * (d : ℝ))) := by
        simp [Real.exp_zero]
        ring
      _ ≤ (((SF.card + 4 * S₀.card : ℕ) : ℝ)) *
            ((2 * t) * (4 * (d : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard hfactor
      _ = (2 * t) *
            (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
              (4 * (d : ℝ))) := by ring
  rw [hexponent]
  calc
    ‖Complex.exp (-corr)‖
        ≤ Real.exp ‖-corr‖ := Complex.norm_exp_le_exp_norm _
    _ = Real.exp ‖corr‖ := by rw [norm_neg]
    _ ≤ Real.exp (
          (2 * t) *
            (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
              (4 * (d : ℝ)))) :=
      Real.exp_le_exp.mpr hseries'

/-- One summand of the exact normalized marked expansion, with the local
edge support exposed independently of the observable realization. -/
noncomputable def localMarkedClusterTerm
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1))) : ℂ :=
  (∫ A, (O.realize n A : ℂ) *
      ∏ p ∈ S₀, (plaquetteWeight pe β A p : ℂ)
    ∂(gaugeMeasureFrom (d := d) (N := n + 1) μ)) *
  Complex.exp (
    KP.clusterSum
      ((connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β).restrict
        (Finset.univ.filter
          (fun c => c.1 ⊆ localFarRegion SF S₀)))
    -
    KP.clusterSum
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β))

/-- The genuine finite-volume Gibbs expectation is exactly the sum of the
normalized local marked terms used by this module. -/
theorem localGibbsExpectation_eq_localMarkedClusterSum
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (hvol : O.minVolume ≤ n)
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    (localGibbsExpectation μ pe β O n : ℂ)
      =
    ∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d (n + 1))).powerset.filter
        (fun S₀ => localNear (O.realizedSupport n hvol) S₀ = S₀),
      localMarkedClusterTerm μ pe β O
        (O.realizedSupport n hvol) S₀ := by
  simpa [localMarkedClusterTerm,
    weightedLatticePolymerSystem_plaquetteWeight] using
    (localGibbsExpectation_eq_markedClusterSum
      μ hpe_meas hpe β O n hvol hkp)

/-- The below-cutoff part of the exact normalized marked sum. -/
noncomputable def localMarkedClusterSmallSum
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1))) (L : ℕ) : ℂ :=
  ∑ S₀ ∈ (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ S₀.card < L),
    localMarkedClusterTerm μ pe β O SF S₀

/-- Effective single-plaquette marked weight after absorbing the linear
growth of the normalized far-gas correction. -/
noncomputable def localMarkedEffectiveWeight
    (d : ℕ) (B β t : ℝ) : ℝ :=
  (Real.exp (|β| * B) - 1) *
    Real.exp ((2 * t) * (4 * (4 * (d : ℝ))))

/-- Each normalized marked summand is majorized by a volume-free constant
times the effective marked weight to `|S₀|`. -/
theorem norm_localMarkedClusterTerm_le_volumeUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1)))
    (S₀ : Finset (ConcretePlaquette d (n + 1)))
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    ‖localMarkedClusterTerm μ pe β O SF S₀‖
      ≤ O.bound *
          Real.exp (
            (2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) *
        (localMarkedEffectiveWeight d B β t) ^ S₀.card := by
  let δ := Real.exp (|β| * B) - 1
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hpe 1)
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonneg (abs_nonneg β) hB)
  have hInt :=
    norm_integral_realize_mul_prod_plaquetteWeight_le
      μ hpe β O S₀
  have hExp := norm_exp_localFarClusterDiff_le_volumeUniform
    μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF S₀ hkp
  unfold localMarkedClusterTerm
  rw [norm_mul]
  calc
    _ ≤ (O.bound * δ ^ S₀.card) *
          Real.exp (
            (2 * t) *
              (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
                (4 * (d : ℝ)))) := by
      exact mul_le_mul hInt hExp (norm_nonneg _)
        (mul_nonneg O.bound_nonneg (pow_nonneg hδ _))
    _ = O.bound *
          Real.exp (
            (2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) *
        (localMarkedEffectiveWeight d B β t) ^ S₀.card := by
      have hexp :
          Real.exp (
              (2 * t) *
                (((SF.card + 4 * S₀.card : ℕ) : ℝ) *
                  (4 * (d : ℝ))))
            =
          Real.exp (
              (2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) *
            Real.exp (
              (S₀.card : ℝ) *
                ((2 * t) * (4 * (4 * (d : ℝ))))) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      unfold localMarkedEffectiveWeight
      dsimp only [δ]
      rw [mul_pow, ← Real.exp_nat_mul]
      ring

/-- The sum of norms of normalized marked terms whose marked plaquette set
has cardinality at least `L`. -/
noncomputable def localMarkedClusterTailNorm
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1))) (L : ℕ) : ℝ :=
  ∑ S₀ ∈ (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
    ‖localMarkedClusterTerm μ pe β O SF S₀‖

/-- The genuine Gibbs expectation differs from its below-cutoff normalized
marked sum by at most the sum of norms of the discarded marked terms. -/
theorem norm_localGibbsExpectation_sub_localMarkedClusterSmallSum_le
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (O : CompatibleLocalObservable d G)
    (hvol : O.minVolume ≤ n) (L : ℕ)
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a) :
    ‖(localGibbsExpectation μ pe β O n : ℂ) -
        localMarkedClusterSmallSum μ pe β O
          (O.realizedSupport n hvol) L‖
      ≤ localMarkedClusterTailNorm μ pe β O
          (O.realizedSupport n hvol) L := by
  classical
  let SF := O.realizedSupport n hvol
  let U :=
    (Finset.univ :
      Finset (ConcretePlaquette d (n + 1))).powerset.filter
      (fun S₀ => localNear SF S₀ = S₀)
  let small : Finset (ConcretePlaquette d (n + 1)) → Prop :=
    fun S₀ => S₀.card < L
  let f : Finset (ConcretePlaquette d (n + 1)) → ℂ :=
    fun S₀ => localMarkedClusterTerm μ pe β O SF S₀
  have hfull := localGibbsExpectation_eq_localMarkedClusterSum
    μ hpe_meas hpe β O hvol hkp
  have hpart := Finset.sum_filter_add_sum_filter_not U small f
  have hsplit :
      (∑ S₀ ∈ U, f S₀)
        =
      localMarkedClusterSmallSum μ pe β O SF L +
        ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
          f S₀ := by
    simpa [U, small, f, localMarkedClusterSmallSum,
      Finset.filter_filter, Nat.not_lt, and_assoc] using hpart.symm
  change ‖(localGibbsExpectation μ pe β O n : ℂ) -
      localMarkedClusterSmallSum μ pe β O SF L‖ ≤ _
  rw [show (localGibbsExpectation μ pe β O n : ℂ) =
      ∑ S₀ ∈ U, f S₀ by
        simpa [SF, U, f] using hfull,
    hsplit]
  rw [add_sub_cancel_left]
  unfold localMarkedClusterTailNorm
  exact norm_sum_le _ _

/-- **Uniform tail for the complete normalized outer marked sum.**

This combines the arbitrary-observable integral bound, the exact local
normalization correction, and the elementary component resummation. -/
theorem localMarkedClusterTailNorm_le_volumeUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (SF : Finset (PosEdge d (n + 1))) (L : ℕ)
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    localMarkedClusterTailNorm μ pe β O SF L
      ≤
    (O.bound *
      Real.exp ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ))))) *
      (Real.exp (-(η * L)) *
        Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            ((localMarkedEffectiveWeight d B β t * Real.exp η) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (localMarkedEffectiveWeight d B β t *
                  Real.exp η))))) := by
  let σ := localMarkedEffectiveWeight d B β t
  let C₀ := O.bound *
    Real.exp ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ))))
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hpe 1)
  have hδ : 0 ≤ Real.exp (|β| * B) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (mul_nonneg (abs_nonneg β) hB)
  have hσ : 0 ≤ σ := by
    dsimp only [σ, localMarkedEffectiveWeight]
    exact mul_nonneg hδ (Real.exp_pos _).le
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact mul_nonneg O.bound_nonneg (Real.exp_pos _).le
  have hterm : ∀ S₀,
      ‖localMarkedClusterTerm μ pe β O SF S₀‖
        ≤ C₀ * σ ^ S₀.card := by
    intro S₀
    simpa [C₀, σ] using
      (norm_localMarkedClusterTerm_le_volumeUniform
        μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁
        O SF S₀ hkp)
  have htail := localPinnedSetTailWeight_le_exp_volumeUniform
    SF σ η hσ hη0 L (by simpa [σ] using hrMarked)
  unfold localMarkedClusterTailNorm
  calc
    (∑ S₀ ∈ (Finset.univ :
        Finset (ConcretePlaquette d (n + 1))).powerset.filter
        (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
      ‖localMarkedClusterTerm μ pe β O SF S₀‖)
        ≤ ∑ S₀ ∈ (Finset.univ :
            Finset (ConcretePlaquette d (n + 1))).powerset.filter
            (fun S₀ => localNear SF S₀ = S₀ ∧ L ≤ S₀.card),
          C₀ * σ ^ S₀.card :=
      Finset.sum_le_sum fun S₀ _ => hterm S₀
    _ = C₀ * localPinnedSetTailWeight SF σ L := by
      unfold localPinnedSetTailWeight
      rw [Finset.mul_sum]
    _ ≤ C₀ * (Real.exp (-(η * L)) *
        Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            ((σ * Real.exp η) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (σ * Real.exp η))))) :=
      mul_le_mul_of_nonneg_left htail hC₀
    _ = (O.bound *
      Real.exp ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ))))) *
      (Real.exp (-(η * L)) *
        Real.exp (
          ((SF.card : ℝ) * (4 * (d : ℝ))) *
            ((localMarkedEffectiveWeight d B β t * Real.exp η) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (localMarkedEffectiveWeight d B β t *
                  Real.exp η))))) := rfl

/-- **The genuine finite-volume Gibbs expectation is uniformly close to its
below-cutoff normalized marked sum.** -/
theorem norm_localGibbsExpectation_sub_localMarkedClusterSmallSum_le_volumeUniform
    {d n : ℕ} [NeZero d]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {pe : G → ℝ} (hpe_meas : Measurable pe)
    {B : ℝ} (hpe : ∀ g, |pe g| ≤ B) (β : ℝ)
    (t ε η : ℝ) (ht0 : 0 ≤ t) (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hr₀ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) < 1)
    (hsmall₀ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε)))) ≤ t)
    (hr₁ : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) < 1)
    (hsmall₁ : ((16 * d : ℕ) : ℝ) *
      (((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)) /
        (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
          ((Real.exp (|β| * B) - 1) * Real.exp (t + ε + 1)))) ≤ t)
    (O : CompatibleLocalObservable d G)
    (hvol : O.minVolume ≤ n) (L : ℕ)
    {a : (connectedLatticePolymerSystem
      (d := d) (N := n + 1) μ pe β).Polymer → ℝ}
    (hkp : KP.KPCriterion
      (connectedLatticePolymerSystem
        (d := d) (N := n + 1) μ pe β) a)
    (hrMarked : ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
      (localMarkedEffectiveWeight d B β t * Real.exp η) < 1) :
    ‖(localGibbsExpectation μ pe β O n : ℂ) -
        localMarkedClusterSmallSum μ pe β O
          (O.realizedSupport n hvol) L‖
      ≤
    (O.bound *
      Real.exp (
        (2 * t) *
          ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))))) *
      (Real.exp (-(η * L)) *
        Real.exp (
          ((Fintype.card O.Support : ℝ) * (4 * (d : ℝ))) *
            ((localMarkedEffectiveWeight d B β t * Real.exp η) /
              (1 - ((16 * d + 1 : ℕ) : ℝ) ^ 2 *
                (localMarkedEffectiveWeight d B β t *
                  Real.exp η))))) := by
  have hfirst :=
    norm_localGibbsExpectation_sub_localMarkedClusterSmallSum_le
      μ hpe_meas hpe β O hvol L hkp
  have htail := localMarkedClusterTailNorm_le_volumeUniform
    μ hpe β t ε η ht0 hε0 hη0
    hr₀ hsmall₀ hr₁ hsmall₁ O (O.realizedSupport n hvol) L
    hkp hrMarked
  exact hfirst.trans (by
    simpa [CompatibleLocalObservable.card_realizedSupport] using htail)

end WindowPolymer

end YangMills
