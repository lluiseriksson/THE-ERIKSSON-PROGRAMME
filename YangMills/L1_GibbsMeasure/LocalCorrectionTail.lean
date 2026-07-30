/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L1_GibbsMeasure.LocalRootedTail

/-!
# The exact local correction is dominated by the rooted KP tail

This module supplies the combinatorial bridge between the unrooted correction
series produced by `KP.clusterSum_sub_restrict` and the rooted, volume-uniform
tail proved in `LocalRootedTail`.

The predicate saying that a tuple has total plaquette cardinality at least
`L` is invariant under coordinate permutations but is not a predicate of one
polymer.  We therefore keep it explicitly through the symmetrization.  Moving
an arbitrary marked coordinate to coordinate zero costs exactly `n + 1`.
That factor is retained all the way to `rootedPinnedClusterTail`, where the
unit-cardinality tilt absorbs it.
-/

namespace YangMills

open MeasureTheory GaugeConfig

namespace WindowPolymer

open Classical

set_option maxHeartbeats 1600000 in
/-- Symmetrization with a permutation-invariant predicate on the whole tuple.

This is the form needed for a local correction tail: `Q` says that one
polymer meets the marked region, while `H` says that the total polymer size is
at least the window cutoff. -/
lemma sum_marked_le_succ_mul_pinned_of_invariant
    (P : KP.PolymerSystem) [Fintype P.Polymer]
    (Q : P.Polymer → Prop) [DecidablePred Q]
    (n : ℕ) (H : (Fin (n + 1) → P.Polymer) → Prop) [DecidablePred H]
    (hH : ∀ (σ : Equiv.Perm (Fin (n + 1))) X,
      H (X ∘ σ) ↔ H X) :
    ∑ X ∈ (Finset.univ : Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => (∃ i, Q (X i)) ∧ H X),
      |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖
      ≤ ((n + 1 : ℕ) : ℝ) *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => Q (X 0) ∧ H X),
        |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖ := by
  classical
  let f : (Fin (n + 1) → P.Polymer) → ℝ := fun X =>
    |((KP.ursell P X : ℤ) : ℝ)| * ∏ k, ‖P.activity (X k)‖
  have hf0 : ∀ X, 0 ≤ f X := fun X =>
    mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun k _ => norm_nonneg _)
  have hswap : ∀ i : Fin (n + 1),
      (∑ X : Fin (n + 1) → P.Polymer,
        if Q (X i) ∧ H X then f X else 0)
      =
      ∑ X : Fin (n + 1) → P.Polymer,
        if Q (X 0) ∧ H X then f X else 0 := by
    intro i
    have hbij : Function.Bijective
        (fun X : Fin (n + 1) → P.Polymer => X ∘ Equiv.swap 0 i) := by
      have hinv : Function.Involutive
          (fun X : Fin (n + 1) → P.Polymer =>
            X ∘ Equiv.swap 0 i) := by
        intro X
        funext k
        simp [Function.comp, Equiv.swap_apply_self]
      exact hinv.bijective
    refine Fintype.sum_bijective _ hbij _ _ ?_
    intro X
    have hc0 : (X ∘ Equiv.swap 0 i) 0 = X i := by
      simp [Function.comp, Equiv.swap_apply_left]
    have hu : KP.ursell P (X ∘ Equiv.swap 0 i) = KP.ursell P X :=
      KP.ursell_comp_equiv P X (Equiv.swap 0 i)
    have hprod :
        (∏ k, ‖P.activity ((X ∘ Equiv.swap 0 i) k)‖)
          = ∏ k, ‖P.activity (X k)‖ :=
      Equiv.prod_comp (Equiv.swap 0 i)
        (fun k => ‖P.activity (X k)‖)
    have hpred :
        (Q ((X ∘ Equiv.swap 0 i) 0) ∧
            H (X ∘ Equiv.swap 0 i))
          ↔ Q (X i) ∧ H X := by
      rw [hc0, hH]
    refine (if_congr hpred ?_ rfl).symm
    simp only [f, hu, hprod]
  calc
    (∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
        (fun X => (∃ i, Q (X i)) ∧ H X), f X)
        ≤ ∑ X : Fin (n + 1) → P.Polymer,
            ∑ i : Fin (n + 1),
              if Q (X i) ∧ H X then f X else 0 := by
          rw [Finset.sum_filter]
          refine Finset.sum_le_sum fun X _ => ?_
          by_cases hX : (∃ i, Q (X i)) ∧ H X
          · rw [if_pos hX]
            obtain ⟨⟨i₀, hi₀⟩, hHX⟩ := hX
            have h := Finset.single_le_sum
              (f := fun i =>
                if Q (X i) ∧ H X then f X else 0)
              (fun i _ => by
                change 0 ≤ if Q (X i) ∧ H X then f X else 0
                by_cases hi : Q (X i) ∧ H X
                · rw [if_pos hi]
                  exact hf0 X
                · rw [if_neg hi])
              (Finset.mem_univ i₀)
            simpa [hi₀, hHX] using h
          · rw [if_neg hX]
            exact Finset.sum_nonneg fun i _ => by
              change 0 ≤ if Q (X i) ∧ H X then f X else 0
              by_cases hi : Q (X i) ∧ H X
              · rw [if_pos hi]
                exact hf0 X
              · rw [if_neg hi]
    _ = ∑ i : Fin (n + 1),
          ∑ X : Fin (n + 1) → P.Polymer,
            if Q (X i) ∧ H X then f X else 0 :=
      Finset.sum_comm
    _ = ∑ _i : Fin (n + 1),
          ∑ X : Fin (n + 1) → P.Polymer,
            if Q (X 0) ∧ H X then f X else 0 :=
      Finset.sum_congr rfl fun i _ => hswap i
    _ = ((n + 1 : ℕ) : ℝ) *
          ∑ X : Fin (n + 1) → P.Polymer,
            if Q (X 0) ∧ H X then f X else 0 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ = ((n + 1 : ℕ) : ℝ) *
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => Q (X 0) ∧ H X), f X := by
      rw [Finset.sum_filter]

/-- The norm majorant of the order-`n+1` local correction carried by
clusters which meet `supportPlaquettes SF` and whose total plaquette
cardinality is at least `L`. -/
noncomputable def localCorrectionTailLayer
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L n : ℕ) : ℝ :=
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  (((n + 1).factorial : ℝ))⁻¹ *
    ∑ X ∈ (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
      (fun X =>
        (∃ i, ¬ Disjoint (X i).1 (supportPlaquettes SF)) ∧
          L ≤ ∑ i, (X i).1.card),
      |((KP.ursell P X : ℤ) : ℝ)| *
        ∏ i, ‖P.activity (X i)‖

/-- Finite partial sum of the exact local correction majorant. -/
noncomputable def localCorrectionTailPartial
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    localCorrectionTailLayer μ pe β SF L n

set_option maxHeartbeats 2400000 in
/-- **Per-layer unrooted-to-rooted bridge.**

The left side is the exact norm majorant produced by the restriction
identity.  The right side is rooted at every plaquette incident to the
observable support.  No volume-cardinality factor occurs. -/
theorem localCorrectionTailLayer_le_rooted
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L n : ℕ) :
    localCorrectionTailLayer μ pe β SF L n
      ≤ ∑ p ∈ supportPlaquettes SF,
          ∑ c ∈ (Finset.univ :
              Finset (connectedLatticePolymerSystem
                (d := d) (N := N) μ pe β).Polymer).filter
            (fun c => (connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).incomp
                (singletonConnectedPolymer μ pe β p) c),
          ((n : ℝ) + 1) *
            KP.pinnedClusterWeightGE
              (connectedLatticePolymerSystem
                (d := d) (N := N) μ pe β)
              (fun c' => c'.1.card) c L n := by
  classical
  let P := connectedLatticePolymerSystem
    (d := d) (N := N) μ pe β
  let R := supportPlaquettes SF
  let H : (Fin (n + 1) → P.Polymer) → Prop :=
    fun X => L ≤ ∑ i, (X i).1.card
  let f : (Fin (n + 1) → P.Polymer) → ℝ := fun X =>
    |((KP.ursell P X : ℤ) : ℝ)| * ∏ i, ‖P.activity (X i)‖
  have hf0 : ∀ X, 0 ≤ f X := fun X =>
    mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hHperm : ∀ (σ : Equiv.Perm (Fin (n + 1))) X,
      H (X ∘ σ) ↔ H X := by
    intro σ X
    simp only [H, Function.comp_apply]
    rw [Equiv.sum_comp σ (fun i => (X i).1.card)]
  have hsym :
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => (∃ i, ¬ Disjoint (X i).1 R) ∧ H X), f X
        ≤ ((n + 1 : ℕ) : ℝ) *
          ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
            (fun X => ¬ Disjoint (X 0).1 R ∧ H X), f X := by
    simpa [f] using
      (sum_marked_le_succ_mul_pinned_of_invariant
        P (fun c => ¬ Disjoint c.1 R) n H hHperm)
  have hfiber :
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => ¬ Disjoint (X 0).1 R ∧ H X), f X
        =
      ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c => ¬ Disjoint c.1 R),
        ∑ X ∈ (Finset.univ :
            Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => X 0 = c ∧ H X), f X := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ :
        Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X => ¬ Disjoint (X 0).1 R ∧ H X))
      (t := (Finset.univ : Finset P.Polymer).filter
        (fun c => ¬ Disjoint c.1 R))
      (g := fun X : Fin (n + 1) → P.Polymer => X 0)
      (fun X hX => by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp hX).2.1⟩) f]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    refine Finset.filter_congr fun X _ => ?_
    have hQc : ¬ Disjoint c.1 R :=
      (Finset.mem_filter.mp hc).2
    constructor
    · rintro ⟨⟨_, hHX⟩, hEq⟩
      exact ⟨hEq, hHX⟩
    · rintro ⟨hEq, hHX⟩
      refine ⟨⟨?_, hHX⟩, hEq⟩
      rw [hEq]
      exact hQc
  have hregion :
      ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c => ¬ Disjoint c.1 R),
        KP.pinnedClusterWeightGE P (fun c' => c'.1.card) c L n
        ≤
      ∑ p ∈ R,
        ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c => p ∈ c.1),
          KP.pinnedClusterWeightGE P
            (fun c' => c'.1.card) c L n := by
    rw [Finset.sum_filter]
    calc
      (∑ c : P.Polymer,
          if ¬ Disjoint c.1 R then
            KP.pinnedClusterWeightGE P
              (fun c' => c'.1.card) c L n else 0)
          ≤ ∑ c : P.Polymer, ∑ p ∈ R,
              if p ∈ c.1 then
                KP.pinnedClusterWeightGE P
                  (fun c' => c'.1.card) c L n else 0 := by
            refine Finset.sum_le_sum fun c _ => ?_
            by_cases hc : ¬ Disjoint c.1 R
            · rw [if_pos hc]
              rw [Finset.not_disjoint_iff] at hc
              obtain ⟨p, hpc, hpR⟩ := hc
              have h := Finset.single_le_sum
                (f := fun p =>
                  if p ∈ c.1 then
                    KP.pinnedClusterWeightGE P
                      (fun c' => c'.1.card) c L n else 0)
                (fun p _ => by
                  change 0 ≤ if p ∈ c.1 then
                    KP.pinnedClusterWeightGE P
                      (fun c' => c'.1.card) c L n else 0
                  by_cases hp : p ∈ c.1
                  · rw [if_pos hp]
                    exact KP.pinnedClusterWeightGE_nonneg
                      P (fun c' => c'.1.card) c L n
                  · rw [if_neg hp])
                hpR
              simpa [hpc] using h
            · rw [if_neg hc]
              exact Finset.sum_nonneg fun p _ => by
                change 0 ≤ if p ∈ c.1 then
                  KP.pinnedClusterWeightGE P
                    (fun c' => c'.1.card) c L n else 0
                by_cases hp : p ∈ c.1
                · rw [if_pos hp]
                  exact KP.pinnedClusterWeightGE_nonneg
                    P (fun c' => c'.1.card) c L n
                · rw [if_neg hp]
      _ = ∑ p ∈ R, ∑ c : P.Polymer,
            if p ∈ c.1 then
              KP.pinnedClusterWeightGE P
                (fun c' => c'.1.card) c L n else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ p ∈ R,
          ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
            (fun c => p ∈ c.1),
            KP.pinnedClusterWeightGE P
              (fun c' => c'.1.card) c L n := by
          refine Finset.sum_congr rfl fun p _ => ?_
          exact (Finset.sum_filter _ _).symm
  have hmem_incomp : ∀ p (c : P.Polymer), p ∈ c.1 →
      P.incomp (singletonConnectedPolymer μ pe β p) c := by
    intro p c hpc hdisj
    have hp0 : (p.edges 0).pos ∈
        ({p} : Finset (ConcretePlaquette d N)).biUnion
          plaquetteSupport :=
      Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_singleton_self p, by simp [plaquetteSupport]⟩
    have hpc0 : (p.edges 0).pos ∈ c.1.biUnion plaquetteSupport :=
      Finset.mem_biUnion.mpr
        ⟨p, hpc, by simp [plaquetteSupport]⟩
    exact (Finset.disjoint_left.mp hdisj hp0) hpc0
  have hincomp :
      ∑ p ∈ R,
        ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c => p ∈ c.1),
          KP.pinnedClusterWeightGE P
            (fun c' => c'.1.card) c L n
        ≤
      ∑ p ∈ R,
        ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c =>
            P.incomp (singletonConnectedPolymer μ pe β p) c),
          KP.pinnedClusterWeightGE P
            (fun c' => c'.1.card) c L n := by
    refine Finset.sum_le_sum fun p _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ =>
      KP.pinnedClusterWeightGE_nonneg
        P (fun c' => c'.1.card) c L n
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨Finset.mem_univ _, hmem_incomp p c hc.2⟩
  unfold localCorrectionTailLayer
  change (((n + 1).factorial : ℝ))⁻¹ *
      ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X =>
            (∃ i, ¬ Disjoint (X i).1 R) ∧ H X), f X ≤ _
  calc
    (((n + 1).factorial : ℝ))⁻¹ *
        ∑ X ∈ (Finset.univ :
          Finset (Fin (n + 1) → P.Polymer)).filter
          (fun X =>
            (∃ i, ¬ Disjoint (X i).1 R) ∧ H X), f X
        ≤ (((n + 1).factorial : ℝ))⁻¹ *
          (((n + 1 : ℕ) : ℝ) *
            ∑ X ∈ (Finset.univ :
              Finset (Fin (n + 1) → P.Polymer)).filter
              (fun X => ¬ Disjoint (X 0).1 R ∧ H X), f X) :=
      mul_le_mul_of_nonneg_left hsym (by positivity)
    _ = ((n : ℝ) + 1) *
        ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c => ¬ Disjoint c.1 R),
          KP.pinnedClusterWeightGE
            P (fun c' => c'.1.card) c L n := by
      rw [hfiber]
      calc
        (((n + 1).factorial : ℝ))⁻¹ *
            (((n + 1 : ℕ) : ℝ) *
              ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
                (fun c => ¬ Disjoint c.1 R),
                ∑ X ∈ (Finset.univ :
                    Finset (Fin (n + 1) → P.Polymer)).filter
                  (fun X => X 0 = c ∧ H X), f X)
            =
          ((n : ℝ) + 1) *
            ((((n + 1).factorial : ℝ))⁻¹ *
              ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
                (fun c => ¬ Disjoint c.1 R),
                ∑ X ∈ (Finset.univ :
                    Finset (Fin (n + 1) → P.Polymer)).filter
                  (fun X => X 0 = c ∧ H X), f X) := by
            push_cast
            ring
        _ = ((n : ℝ) + 1) *
            ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
              (fun c => ¬ Disjoint c.1 R),
              KP.pinnedClusterWeightGE
                P (fun c' => c'.1.card) c L n := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          unfold KP.pinnedClusterWeightGE
          simp only [H, f]
    _ ≤ ((n : ℝ) + 1) *
        ∑ p ∈ R,
          ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
            (fun c => p ∈ c.1),
            KP.pinnedClusterWeightGE P
              (fun c' => c'.1.card) c L n :=
      mul_le_mul_of_nonneg_left hregion (by positivity)
    _ ≤ ((n : ℝ) + 1) *
        ∑ p ∈ R,
          ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
            (fun c =>
              P.incomp (singletonConnectedPolymer μ pe β p) c),
            KP.pinnedClusterWeightGE P
              (fun c' => c'.1.card) c L n :=
      mul_le_mul_of_nonneg_left hincomp (by positivity)
    _ = ∑ p ∈ R,
        ∑ c ∈ (Finset.univ : Finset P.Polymer).filter
          (fun c =>
            P.incomp (singletonConnectedPolymer μ pe β p) c),
          ((n : ℝ) + 1) *
            KP.pinnedClusterWeightGE P
              (fun c' => c'.1.card) c L n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]

/-- The finite local correction tail is bounded by the rooted boundary
remainder from `LocalRootedTail`. -/
theorem localCorrectionTailPartial_le_rooted
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L K : ℕ) :
    localCorrectionTailPartial μ pe β SF L K
      ≤ supportRootedBoundaryRemainder μ pe β SF L K := by
  classical
  unfold localCorrectionTailPartial supportRootedBoundaryRemainder
  calc
    (∑ n ∈ Finset.range (K + 1),
        localCorrectionTailLayer μ pe β SF L n)
        ≤ ∑ n ∈ Finset.range (K + 1),
          ∑ p ∈ supportPlaquettes SF,
            ∑ c ∈ (Finset.univ :
                Finset (connectedLatticePolymerSystem
                  (d := d) (N := N) μ pe β).Polymer).filter
              (fun c => (connectedLatticePolymerSystem
                (d := d) (N := N) μ pe β).incomp
                  (singletonConnectedPolymer μ pe β p) c),
            ((n : ℝ) + 1) *
              KP.pinnedClusterWeightGE
                (connectedLatticePolymerSystem
                  (d := d) (N := N) μ pe β)
                (fun c' => c'.1.card) c L n := by
          refine Finset.sum_le_sum fun n _ =>
            localCorrectionTailLayer_le_rooted μ pe β SF L n
    _ = ∑ p ∈ supportPlaquettes SF,
        ∑ c ∈ (Finset.univ :
            Finset (connectedLatticePolymerSystem
              (d := d) (N := N) μ pe β).Polymer).filter
          (fun c => (connectedLatticePolymerSystem
            (d := d) (N := N) μ pe β).incomp
              (singletonConnectedPolymer μ pe β p) c),
        rootedPinnedClusterTail μ
          (fun A q => plaquetteWeight pe β A q) c L K := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rfl

/-- **Uniform finite correction-tail estimate.**

This is the boundary estimate consumed by the Cauchy argument.  Its proof is
the exact unrooted-to-rooted bridge followed by
`supportRootedBoundaryRemainder_le_volumeUniform`, whose first contribution
is the literal `connectedLattice_pinned_tail_volumeUniform`. -/
theorem localCorrectionTailPartial_le_volumeUniform
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
    localCorrectionTailPartial μ pe β SF L K
      ≤ Real.exp (-(ε * L)) *
        ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) :=
  (localCorrectionTailPartial_le_rooted μ pe β SF L K).trans
    (supportRootedBoundaryRemainder_le_volumeUniform
      μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF L K)

/-- Every layer of the local correction norm majorant is nonnegative. -/
theorem localCorrectionTailLayer_nonneg
    {d N : ℕ} [NeZero d] [NeZero N]
    {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) (pe : G → ℝ) (β : ℝ)
    (SF : Finset (PosEdge d N)) (L n : ℕ) :
    0 ≤ localCorrectionTailLayer μ pe β SF L n := by
  classical
  unfold localCorrectionTailLayer
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg fun X _ => ?_
  exact mul_nonneg (abs_nonneg _)
    (Finset.prod_nonneg fun i _ => norm_nonneg _)

/-- **Summed local correction tail.**

The whole sequence of size layers is summable, and its `tsum` obeys the same
volume-uniform exponential boundary estimate as every finite partial sum. -/
theorem localCorrectionTail_summable_volumeUniform
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
    (SF : Finset (PosEdge d N)) (L : ℕ) :
    Summable (fun n => localCorrectionTailLayer μ pe β SF L n) ∧
      ∑' n, localCorrectionTailLayer μ pe β SF L n
        ≤ Real.exp (-(ε * L)) *
          ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ)))) := by
  classical
  let C : ℝ := Real.exp (-(ε * L)) *
    ((2 * t) * ((SF.card : ℝ) * (4 * (d : ℝ))))
  have hpartial : ∀ M : ℕ,
      ∑ n ∈ Finset.range M,
          localCorrectionTailLayer μ pe β SF L n ≤ C := by
    intro M
    cases M with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        dsimp [C]
        positivity
    | succ K =>
        exact localCorrectionTailPartial_le_volumeUniform
          μ hpe β t ε ht0 hε0 hr₀ hsmall₀ hr₁ hsmall₁ SF L K
  have hsum :
      Summable (fun n => localCorrectionTailLayer μ pe β SF L n) :=
    summable_of_sum_range_le
      (fun n => localCorrectionTailLayer_nonneg μ pe β SF L n)
      hpartial
  exact ⟨hsum, Real.tsum_le_of_sum_range_le
    (fun n => localCorrectionTailLayer_nonneg μ pe β SF L n)
    hpartial⟩

end WindowPolymer

end YangMills
