/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalWindowCauchy

/-!
# Rooted volume-uniform tails for local Gibbs corrections

The exact local cluster correction is an unrooted tuple sum meeting a marked
region.  Choosing a marked tuple coordinate costs the genuine factor `n + 1`.
This module records that factor explicitly.  It is absorbed by a unit
plaquette-cardinality tilt; it is not silently dropped.

The final estimate deliberately retains the original
`connectedLattice_pinned_tail_volumeUniform` contribution and adds the
unit-tilted contribution required by the rooting factor.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

/-- The rooting factor `n + 1` is bounded by the sum of the original pinned
size layer and its unit-cardinality tilt.  This is the precise extra cost
incurred when a symmetric unrooted cluster is pinned at a coordinate meeting
the local marked region. -/
lemma weighted_rootFactor_pinnedClusterWeightGE_le
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem
      (d := d) (N := N) μ w).Polymer)
    (L n : ℕ) :
    ((n : ℝ) + 1) *
        KP.pinnedClusterWeightGE
          (weightedLatticePolymerSystem (d := d) (N := N) μ w)
          (fun c' => c'.1.card) c L n
      ≤
        KP.pinnedClusterWeightGE
          (weightedLatticePolymerSystem (d := d) (N := N) μ w)
          (fun c' => c'.1.card) c L n
        +
        KP.pinnedClusterWeightGE
          ((weightedLatticePolymerSystem
            (d := d) (N := N) μ w).tilt
              (fun c' => (c'.1.card : ℝ)))
          (fun c' => c'.1.card) c L n := by
  classical
  let P := weightedLatticePolymerSystem (d := d) (N := N) μ w
  let F : Finset (Fin (n + 1) → P.Polymer) :=
    (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X => X 0 = c ∧ L ≤ ∑ i, (X i).1.card)
  let f : (Fin (n + 1) → P.Polymer) → ℝ :=
    fun X => |((KP.ursell P X : ℤ) : ℝ)| *
      ∏ i, ‖P.activity (X i)‖
  let f₁ : (Fin (n + 1) → P.Polymer) → ℝ :=
    fun X => |((KP.ursell
      (P.tilt fun c' => (c'.1.card : ℝ)) X : ℤ) : ℝ)| *
      ∏ i, ‖(P.tilt fun c' => (c'.1.card : ℝ)).activity (X i)‖
  have hterm : ∀ X, ((n : ℝ) + 1) * f X ≤ f X + f₁ X := by
    intro X
    have hone : ∀ i : Fin (n + 1), 1 ≤ (X i).1.card :=
      fun i => Finset.card_pos.mpr (X i).2.1
    have hsum1 : ((n : ℝ) + 1) ≤
        ∑ i, ((X i).1.card : ℝ) := by
      calc
        ((n : ℝ) + 1) =
            ∑ _i : Fin (n + 1), (1 : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
        _ ≤ ∑ i, ((X i).1.card : ℝ) :=
          Finset.sum_le_sum fun i _ => by exact_mod_cast hone i
    have hexp : (∑ i, ((X i).1.card : ℝ)) ≤
        Real.exp (∑ i, ((X i).1.card : ℝ)) := by
      have h := Real.add_one_le_exp
        (∑ i, ((X i).1.card : ℝ))
      linarith
    have hroot : ((n : ℝ) + 1) ≤
        1 + Real.exp (∑ i, ((X i).1.card : ℝ)) := by
      linarith
    have hprod :
        (∏ i, ‖(P.tilt fun c' => (c'.1.card : ℝ)).activity (X i)‖)
          =
        Real.exp (∑ i, ((X i).1.card : ℝ)) *
          ∏ i, ‖P.activity (X i)‖ := by
      calc
        (∏ i, ‖(P.tilt fun c' =>
            (c'.1.card : ℝ)).activity (X i)‖)
            =
          ∏ i, (Real.exp (((X i).1.card : ℝ)) *
            ‖P.activity (X i)‖) :=
              Finset.prod_congr rfl fun i _ =>
                KP.tilt_norm_activity _ _ _
        _ = (∏ i, Real.exp (((X i).1.card : ℝ))) *
            ∏ i, ‖P.activity (X i)‖ :=
              Finset.prod_mul_distrib
        _ = Real.exp (∑ i, ((X i).1.card : ℝ)) *
            ∏ i, ‖P.activity (X i)‖ := by
              rw [← Real.exp_sum]
    have hnonneg : 0 ≤ f X := by
      exact mul_nonneg (abs_nonneg _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
    calc
      ((n : ℝ) + 1) * f X
          ≤ (1 + Real.exp (∑ i, ((X i).1.card : ℝ))) * f X :=
            mul_le_mul_of_nonneg_right hroot hnonneg
      _ = f X + f₁ X := by
        simp only [f, f₁, KP.tilt_ursell, hprod]
        ring
  unfold KP.pinnedClusterWeightGE
  change ((n : ℝ) + 1) *
      ((((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ F, f X) ≤
    ((((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ F, f X) +
      (((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ F, f₁ X
  calc
    ((n : ℝ) + 1) *
        ((((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ F, f X)
        =
      (((n + 1).factorial : ℝ))⁻¹ *
        (((n : ℝ) + 1) * ∑ X ∈ F, f X) := by
          ring
    _ =
      (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ F, ((n : ℝ) + 1) * f X := by
          rw [Finset.mul_sum]
    _ ≤ (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ F, (f X + f₁ X) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum fun X _ => hterm X
    _ = ((((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ F, f X) +
        (((n + 1).factorial : ℝ))⁻¹ * ∑ X ∈ F, f₁ X := by
          rw [Finset.sum_add_distrib]
          ring

/-- The finite rooted pinned tail.  The factor `n + 1` is the exact cost of
turning an unrooted symmetric cluster layer into a layer pinned at a tuple
coordinate meeting the marked region. -/
noncomputable def rootedPinnedClusterTail
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    (μ : Measure G)
    (w : GaugeConfig d N G → ConcretePlaquette d N → ℝ)
    (c : (weightedLatticePolymerSystem
      (d := d) (N := N) μ w).Polymer)
    (L K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1), ((n : ℝ) + 1) *
    KP.pinnedClusterWeightGE
      (weightedLatticePolymerSystem (d := d) (N := N) μ w)
      (fun c' => c'.1.card) c L n

/-- **Volume-uniform rooted size tail.**

The first summand is bounded by the literal
`connectedLattice_pinned_tail_volumeUniform`.  The second is the unavoidable
unit-cardinality tilt which absorbs the rooting factor.  Consequently the
honest uniform KP window for a local cluster correction contains
`t + ε + 1`; the extra `+1` is explicit in `hr₁` and `hsmall₁`. -/
theorem connectedLattice_rootedPinnedTail_volumeUniform
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
    (c : (connectedLatticePolymerSystem (d := d) (N := N)
      μ pe β).Polymer) (L K : ℕ) :
    rootedPinnedClusterTail μ
        (fun A p => plaquetteWeight pe β A p) c L K
      ≤ Real.exp (-(ε * L)) *
        ((Real.exp (ε * (c.1.card : ℝ)) *
            ‖(connectedLatticePolymerSystem (d := d) (N := N)
              μ pe β).activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) +
          (Real.exp (ε * (c.1.card : ℝ)) *
            (Real.exp ((c.1.card : ℝ)) *
              ‖(connectedLatticePolymerSystem (d := d) (N := N)
                μ pe β).activity c‖) *
            Real.exp (t * (c.1.card : ℝ)))) := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  let P₁ := P.tilt fun c' => (c'.1.card : ℝ)
  have hB0 : (0 : ℝ) ≤ B :=
    le_trans (abs_nonneg (pe 1)) (hpe 1)
  have hδ0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (abs_nonneg β) hB0)
  have hbd : ∀ (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
      |plaquetteWeight pe β A p| ≤ Real.exp (|β| * B) - 1 :=
    fun A p => abs_plaquetteWeight_le pe β A p hpe
  have hbase :
      ∑ n ∈ Finset.range (K + 1),
          KP.pinnedClusterWeightGE P (fun c' => c'.1.card) c L n
        ≤ Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) * ‖P.activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) :=
    connectedLattice_pinned_tail_volumeUniform
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ c L K
  have hcrit₁ : KP.KPCriterion
      (P₁.tilt fun c' => ε * (c'.1.card : ℝ))
      (fun c' => t * (c'.1.card : ℝ)) := by
    simpa [P, P₁, weightedLatticePolymerSystem_plaquetteWeight] using
      (weighted_unitTilt_kpCriterion_volumeUniform
        (d := d) (N := N) μ hδ0 hbd t ε ht0 hr₁ hsmall₁)
  have hunit :
      ∑ n ∈ Finset.range (K + 1),
          KP.pinnedClusterWeightGE P₁ (fun c' => c'.1.card) c L n
        ≤ Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) *
            ‖P₁.activity c‖ * Real.exp (t * (c.1.card : ℝ))) :=
    KP.kp_pinned_cluster_tail_bound P₁
      (fun c' => c'.1.card) hε0 hcrit₁ c L K
  unfold rootedPinnedClusterTail
  change (∑ n ∈ Finset.range (K + 1), ((n : ℝ) + 1) *
      KP.pinnedClusterWeightGE P (fun c' => c'.1.card) c L n) ≤ _
  calc
    (∑ n ∈ Finset.range (K + 1), ((n : ℝ) + 1) *
        KP.pinnedClusterWeightGE P (fun c' => c'.1.card) c L n)
        ≤ ∑ n ∈ Finset.range (K + 1),
          (KP.pinnedClusterWeightGE P
              (fun c' => c'.1.card) c L n +
            KP.pinnedClusterWeightGE P₁
              (fun c' => c'.1.card) c L n) := by
          refine Finset.sum_le_sum fun n _ => ?_
          simpa [P, P₁, weightedLatticePolymerSystem_plaquetteWeight] using
            (weighted_rootFactor_pinnedClusterWeightGE_le
              μ (fun A p => plaquetteWeight pe β A p) c L n)
    _ = (∑ n ∈ Finset.range (K + 1),
          KP.pinnedClusterWeightGE P
            (fun c' => c'.1.card) c L n) +
        ∑ n ∈ Finset.range (K + 1),
          KP.pinnedClusterWeightGE P₁
            (fun c' => c'.1.card) c L n := by
          rw [Finset.sum_add_distrib]
    _ ≤ Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) * ‖P.activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) +
        Real.exp (-(ε * L)) *
          (Real.exp (ε * (c.1.card : ℝ)) *
            ‖P₁.activity c‖ * Real.exp (t * (c.1.card : ℝ))) :=
          add_le_add hbase hunit
    _ = Real.exp (-(ε * L)) *
        ((Real.exp (ε * (c.1.card : ℝ)) * ‖P.activity c‖ *
            Real.exp (t * (c.1.card : ℝ))) +
          (Real.exp (ε * (c.1.card : ℝ)) *
            (Real.exp ((c.1.card : ℝ)) * ‖P.activity c‖) *
            Real.exp (t * (c.1.card : ℝ)))) := by
          rw [KP.tilt_norm_activity]
          ring

/-- Rooted cluster tails summed over every polymer touching a plaquette
incident to the finite observable support. -/
noncomputable def supportRootedBoundaryRemainder
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L K : ℕ) : ℝ :=
  ∑ p ∈ supportPlaquettes SF,
    ∑ c ∈ (Finset.univ :
        Finset (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).Polymer).filter
        (fun c => (connectedLatticePolymerSystem
          (d := d) (N := N) μ pe β).incomp
          (singletonConnectedPolymer μ pe β p) c),
      rootedPinnedClusterTail μ
        (fun A q => plaquetteWeight pe β A q) c L K

/-- **Uniform rooted boundary estimate for a local edge support.**

The only geometric prefactor is the support incidence bound `4d·|SF|`.
The factor two records, rather than hides, the ordinary pinned tail plus the
unit-tilted tail needed to root an unrooted local correction. -/
theorem supportRootedBoundaryRemainder_le_volumeUniform
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
    (SF : Finset (PosEdge d N)) (L K : ℕ) :
    supportRootedBoundaryRemainder μ pe β SF L K
      ≤ Real.exp (-(ε * L)) *
        ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  let P₁ := P.tilt fun c' => (c'.1.card : ℝ)
  let b₀ : P.Polymer → ℝ := fun c =>
    Real.exp (ε * (c.1.card : ℝ)) * ‖P.activity c‖ *
      Real.exp (t * (c.1.card : ℝ))
  let b₁ : P.Polymer → ℝ := fun c =>
    Real.exp (ε * (c.1.card : ℝ)) *
      (Real.exp ((c.1.card : ℝ)) * ‖P.activity c‖) *
      Real.exp (t * (c.1.card : ℝ))
  have hB0 : (0 : ℝ) ≤ B :=
    le_trans (abs_nonneg (pe 1)) (hpe 1)
  have hδ0 : (0 : ℝ) ≤ Real.exp (|β| * B) - 1 := by
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (abs_nonneg β) hB0)
  have hbd : ∀ (A : GaugeConfig d N G) (p : ConcretePlaquette d N),
      |plaquetteWeight pe β A p| ≤ Real.exp (|β| * B) - 1 :=
    fun A p => abs_plaquetteWeight_le pe β A p hpe
  have hcrit₀ : KP.KPCriterion
      (P.tilt fun c' => ε * (c'.1.card : ℝ))
      (fun c' => t * (c'.1.card : ℝ)) := by
    simpa [P] using
      (connectedLatticePolymerSystem_tilt_kpCriterion_volumeUniform
        (d := d) (N := N) μ hpe β t ε ht0 hr₀ hsmall₀)
  have hcrit₁ : KP.KPCriterion
      (P₁.tilt fun c' => ε * (c'.1.card : ℝ))
      (fun c' => t * (c'.1.card : ℝ)) := by
    simpa [P, P₁, weightedLatticePolymerSystem_plaquetteWeight] using
      (weighted_unitTilt_kpCriterion_volumeUniform
        (d := d) (N := N) μ hδ0 hbd t ε ht0 hr₁ hsmall₁)
  have hroot : ∀ c : P.Polymer,
      rootedPinnedClusterTail μ
          (fun A q => plaquetteWeight pe β A q) c L K
        ≤ Real.exp (-(ε * L)) * (b₀ c + b₁ c) := by
    intro c
    simpa [P, b₀, b₁] using
      (connectedLattice_rootedPinnedTail_volumeUniform
        μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ c L K)
  have hpinned : ∀ p ∈ supportPlaquettes SF,
      (∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c => P.incomp (singletonConnectedPolymer μ pe β p) c),
          rootedPinnedClusterTail μ
            (fun A q => plaquetteWeight pe β A q) c L K)
        ≤ Real.exp (-(ε * L)) * (2 * t) := by
    intro p hp
    let anchor : P.Polymer := singletonConnectedPolymer μ pe β p
    have hsum₀ := hcrit₀.2 anchor
    have hsum₁ := hcrit₁.2 anchor
    have hb₀ :
        ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
            (fun c => P.incomp anchor c), b₀ c
          ≤ t := by
      simpa [b₀, anchor, singletonConnectedPolymer,
        KP.tilt_norm_activity, mul_assoc, mul_left_comm, mul_comm] using hsum₀
    have hb₁ :
        ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
            (fun c => P.incomp anchor c), b₁ c
          ≤ t := by
      simpa [P₁, b₁, anchor, singletonConnectedPolymer,
        KP.tilt_norm_activity, mul_assoc, mul_left_comm, mul_comm] using hsum₁
    calc
      (∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c => P.incomp anchor c),
          rootedPinnedClusterTail μ
            (fun A q => plaquetteWeight pe β A q) c L K)
          ≤ ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
              (fun c => P.incomp anchor c),
              Real.exp (-(ε * L)) * (b₀ c + b₁ c) :=
            Finset.sum_le_sum fun c _ => hroot c
      _ = Real.exp (-(ε * L)) *
          ((∑ c ∈ (Finset.univ : Finset P.Polymer).filter
              (fun c => P.incomp anchor c), b₀ c) +
            ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
              (fun c => P.incomp anchor c), b₁ c) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ Real.exp (-(ε * L)) * (t + t) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add hb₀ hb₁) (Real.exp_pos _).le
      _ = Real.exp (-(ε * L)) * (2 * t) := by ring
  unfold supportRootedBoundaryRemainder
  change (∑ p ∈ supportPlaquettes SF,
      ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
        (fun c => P.incomp (singletonConnectedPolymer μ pe β p) c),
        rootedPinnedClusterTail μ
          (fun A q => plaquetteWeight pe β A q) c L K) ≤ _
  calc
    (∑ p ∈ supportPlaquettes SF,
      ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
        (fun c => P.incomp (singletonConnectedPolymer μ pe β p) c),
        rootedPinnedClusterTail μ
          (fun A q => plaquetteWeight pe β A q) c L K)
        ≤ ∑ _p ∈ supportPlaquettes SF,
            Real.exp (-(ε * L)) * (2 * t) :=
          Finset.sum_le_sum fun p hp => hpinned p hp
    _ = ((supportPlaquettes SF).card : ℝ) *
        (Real.exp (-(ε * L)) * (2 * t)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((SF.card : ℝ) * (4 * (d : ℝ))) *
        (Real.exp (-(ε * L)) * (2 * t)) := by
          refine mul_le_mul_of_nonneg_right
            (card_supportPlaquettes_le SF) ?_
          exact mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (by positivity) ht0)
    _ = Real.exp (-(ε * L)) *
        ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) := by ring

end WindowPolymer

end YangMills
