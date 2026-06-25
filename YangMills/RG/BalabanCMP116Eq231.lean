/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq229

/-!
# CMP116 equation (2.31) P-bond entropy boundary

This module isolates the literal finite bond-subset summation used in CMP116
equation (2.31).  Equation (2.30) is only the surrounding metric/cardinality
comparison; the actual finite `P`-family exponential sum is equation (2.31).

The theorem below does not construct the repository's `PIndex` from Balaban's
bond subsets.  Instead, a boundary record supplies an injective encoding of
each current `P` index as a finite bond set contained in an eligible bond
carrier, plus the source count bound by `4 M^4` times the gap mass.

Honest scope: this proves the finite subset-entropy estimate behind (2.31),
yielding the geometric premise consumed by the existing P-stage constructor
after a separate target bound `1 <= C_P * exp (5 * kappa)` is supplied.  It
does not identify `PIndex`, prove the pointwise P-residual estimate, prove
Eq. (2.29), prove any post-`P` estimate, or identify physical activities.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Source boundary for the literal bond-set `P` summation in CMP116 (2.31).

`gapMass` represents `M^{-4} |Z0 \ Y0|`.  No identification of the
repository's `PIndex` with Balaban's bond subsets is constructed here. -/
structure CMP116Eq231PBondBoundary
    {σ ιD ιP β : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (localizationScale : ℕ) where

  pBonds : σ → ιD → ιP → Finset β
  bondCarrier : σ → ιD → Finset β
  gapMass : σ → ιD → ℝ

  pBonds_injective :
    ∀ Z D, D ∈ DIndex Z →
      ∀ P₁, P₁ ∈ PIndex Z D →
      ∀ P₂, P₂ ∈ PIndex Z D →
        pBonds Z D P₁ = pBonds Z D P₂ → P₁ = P₂

  pBonds_subset :
    ∀ Z D, D ∈ DIndex Z →
      ∀ P, P ∈ PIndex Z D →
        pBonds Z D P ⊆ bondCarrier Z D

  gapMass_nonneg :
    ∀ Z D, D ∈ DIndex Z →
      0 ≤ gapMass Z D

  bondCarrier_card_le :
    ∀ Z D, D ∈ DIndex Z →
      ((bondCarrier Z D).card : ℝ) ≤
        4 * ((localizationScale : ℝ) ^ 4) * gapMass Z D

/-- The exact exponential shape summed in CMP116 equation (2.31).

For the source parameters,
`rate = (1 / 20) * gamma2 * epsilon1^2 / gk^2`. -/
noncomputable def cmp116Eq231PWeight
    {σ ιD ιP β : Type*}
    (rate : ℝ)
    (gapMass : σ → ιD → ℝ)
    (pBonds : σ → ιD → ιP → Finset β) :
    σ → ιD → ιP → ℝ :=
  fun Z D P =>
    Real.exp (-(rate * gapMass Z D)) *
      Real.exp (-(2 * rate *
        ((pBonds Z D P).card : ℝ)))

/-- CMP116 (2.31) supplies the finite geometric premise used by
`cmp116PStageSourceBound_of_pointwise_geometric`.

The final `htarget` is deliberately explicit: equation (2.31) proves the
stronger bound `<= 1`; it does not itself produce the later
`O(1) * exp (5 * kappa)` factor. -/
theorem cmp116PGeometricFamilySummation_of_eq231
    {σ ιD ιP β : Type*}
    (DIndex : σ → Finset ιD)
    (PIndex : σ → ιD → Finset ιP)
    (pGeometryWeight : σ → ιD → ιP → ℝ)
    (localizationScale : ℕ)
    (rate pEntropyConstant kappa : ℝ)
    (B :
      CMP116Eq231PBondBoundary
        (β := β) DIndex PIndex localizationScale)
    (hrate :
      4 * ((localizationScale : ℝ) ^ 4) *
          Real.exp (-(2 * rate)) ≤ rate)
    (hgeometry :
      ∀ Z D, D ∈ DIndex Z →
        ∀ P, P ∈ PIndex Z D →
          pGeometryWeight Z D P ≤
            cmp116Eq231PWeight
              rate B.gapMass B.pBonds Z D P)
    (htarget :
      1 ≤ pEntropyConstant * Real.exp (5 * kappa)) :
    ∀ Z D, D ∈ DIndex Z →
      Finset.sum (PIndex Z D)
          (fun P => pGeometryWeight Z D P) ≤
        pEntropyConstant * Real.exp (5 * kappa) := by
  classical
  intro Z D hD
  let carrier : Finset β := B.bondCarrier Z D
  let gap : ℝ := B.gapMass Z D
  let q : ℝ := Real.exp (-(2 * rate))
  let egap : ℝ := Real.exp (-(rate * gap))
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact Real.exp_nonneg _
  have heg_nonneg : 0 ≤ egap := by
    dsimp [egap]
    exact Real.exp_nonneg _
  have hgap_nonneg : 0 ≤ gap := by
    dsimp [gap]
    exact B.gapMass_nonneg Z D hD
  have hcard_gap :
      ((carrier.card : ℝ) ≤
        4 * ((localizationScale : ℝ) ^ 4) * gap) := by
    dsimp [carrier, gap]
    exact B.bondCarrier_card_le Z D hD
  have hexp_card : ∀ S : Finset β,
      Real.exp (-(2 * rate * (S.card : ℝ))) = q ^ S.card := by
    intro S
    dsimp [q]
    have harg :
        -(2 * rate * (S.card : ℝ)) =
          (S.card : ℝ) * (-(2 * rate)) := by
      ring
    rw [harg, Real.exp_nat_mul]
  have hinj : Set.InjOn (fun P => B.pBonds Z D P) (PIndex Z D) := by
    intro P₁ hP₁ P₂ hP₂ hEq
    exact B.pBonds_injective Z D hD P₁ hP₁ P₂ hP₂ hEq
  have hsum_image_eq :
      Finset.sum ((PIndex Z D).image (fun P => B.pBonds Z D P))
          (fun S => q ^ S.card) =
        Finset.sum (PIndex Z D)
          (fun P => q ^ (B.pBonds Z D P).card) := by
    simpa using
      (Finset.sum_image
        (s := PIndex Z D)
        (g := fun P => B.pBonds Z D P)
        (f := fun S => q ^ S.card)
        hinj)
  have himage_subset :
      (PIndex Z D).image (fun P => B.pBonds Z D P) ⊆
        carrier.powerset := by
    intro S hS
    rw [Finset.mem_image] at hS
    rcases hS with ⟨P, hP, rfl⟩
    rw [Finset.mem_powerset]
    dsimp [carrier]
    exact B.pBonds_subset Z D hD P hP
  have hsum_image_le_powerset :
      Finset.sum ((PIndex Z D).image (fun P => B.pBonds Z D P))
          (fun S => q ^ S.card) ≤
        Finset.sum carrier.powerset (fun S => q ^ S.card) := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        himage_subset
        (fun S _hS _hnot => pow_nonneg hq_nonneg S.card)
  have hpowerset_sum_eq :
      Finset.sum carrier.powerset (fun S => q ^ S.card) =
        (1 + q) ^ carrier.card := by
    calc
      Finset.sum carrier.powerset (fun S => q ^ S.card)
          =
        Finset.sum carrier.powerset
          (fun S => Finset.prod S (fun _b => q)) := by
            refine Finset.sum_congr rfl ?_
            intro S _hS
            rw [Finset.prod_const]
      _ = Finset.prod carrier (fun _b => (1 + q)) := by
            exact
              (Finset.prod_one_add
                (s := carrier) (f := fun _ : β => q)).symm
      _ = (1 + q) ^ carrier.card := by
            rw [Finset.prod_const]
  have hpowerset_le_exp :
      Finset.sum carrier.powerset (fun S => q ^ S.card) ≤
        Real.exp ((carrier.card : ℝ) * q) := by
    rw [hpowerset_sum_eq]
    have hbase_nonneg : 0 ≤ 1 + q := add_nonneg zero_le_one hq_nonneg
    have hbase_le_exp : 1 + q ≤ Real.exp q := by
      have h := Real.add_one_le_exp q
      linarith
    calc
      (1 + q) ^ carrier.card ≤ (Real.exp q) ^ carrier.card := by
        exact pow_le_pow_left₀ hbase_nonneg hbase_le_exp carrier.card
      _ = Real.exp ((carrier.card : ℝ) * q) := by
        exact (Real.exp_nat_mul q carrier.card).symm
  have hcard_q_le : (carrier.card : ℝ) * q ≤ rate * gap := by
    calc
      (carrier.card : ℝ) * q ≤
          (4 * ((localizationScale : ℝ) ^ 4) * gap) * q := by
            exact mul_le_mul_of_nonneg_right hcard_gap hq_nonneg
      _ = (4 * ((localizationScale : ℝ) ^ 4) * q) * gap := by
            ring
      _ ≤ rate * gap := by
            exact mul_le_mul_of_nonneg_right hrate hgap_nonneg
  have hsum_weight_le_one :
      Finset.sum (PIndex Z D)
          (fun P => cmp116Eq231PWeight rate B.gapMass B.pBonds Z D P) ≤
        1 := by
    calc
      Finset.sum (PIndex Z D)
          (fun P => cmp116Eq231PWeight rate B.gapMass B.pBonds Z D P)
          =
        egap * Finset.sum (PIndex Z D)
          (fun P => q ^ (B.pBonds Z D P).card) := by
            dsimp [cmp116Eq231PWeight, egap, gap]
            simp [hexp_card, Finset.mul_sum]
      _ =
        egap *
          Finset.sum ((PIndex Z D).image (fun P => B.pBonds Z D P))
            (fun S => q ^ S.card) := by
              rw [hsum_image_eq]
      _ ≤ egap * Finset.sum carrier.powerset (fun S => q ^ S.card) := by
            exact
              mul_le_mul_of_nonneg_left hsum_image_le_powerset heg_nonneg
      _ ≤ egap * Real.exp ((carrier.card : ℝ) * q) := by
            exact mul_le_mul_of_nonneg_left hpowerset_le_exp heg_nonneg
      _ ≤ egap * Real.exp (rate * gap) := by
            exact
              mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr hcard_q_le)
                heg_nonneg
      _ = 1 := by
            dsimp [egap]
            rw [← Real.exp_add]
            have hzero : -(rate * gap) + rate * gap = 0 := by
              ring
            rw [hzero, Real.exp_zero]
  calc
    Finset.sum (PIndex Z D) (fun P => pGeometryWeight Z D P)
        ≤
      Finset.sum (PIndex Z D)
        (fun P => cmp116Eq231PWeight rate B.gapMass B.pBonds Z D P) := by
          exact Finset.sum_le_sum fun P hP => hgeometry Z D hD P hP
    _ ≤ 1 := hsum_weight_le_one
    _ ≤ pEntropyConstant * Real.exp (5 * kappa) := htarget

end YangMills.RG
