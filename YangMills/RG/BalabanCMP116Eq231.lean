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

/-- Source-shaped finite `P` family for CMP116 (2.31), when `P` is represented
as the bond set itself and admissibility is a filter on the four-direction
carrier over the source gap. -/
def cmp116Eq231SourcePIndex
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool) :
    σ → ιD → Finset (Finset (Cube × Fin 4)) :=
  fun Z D =>
    ((gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4))).powerset).filter
      (fun P => admissible Z D P = true)

/-- Membership in the filtered source `P` family is exactly carrier
containment plus the declared admissibility predicate.

This is a source-neutral extensional fact about the Lean filtered family; it
does not identify Balaban's source `P` family with this representation. -/
theorem cmp116Eq231SourcePIndex_mem_iff
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (Z : σ) (D : ιD) (P : Finset (Cube × Fin 4)) :
    P ∈ cmp116Eq231SourcePIndex gapCubes admissible Z D ↔
      P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4)) ∧
        admissible Z D P = true := by
  simp [cmp116Eq231SourcePIndex, Finset.mem_powerset]

/-- A pointwise membership characterization of a `PIndex` family yields the
filtered source-family equality by finite extensionality.

The theorem is deliberately conditional.  The actual source theorem still has
to prove the `hmem` premise from Balaban's definition of the `P` family and the
chosen bond-orientation encoding. -/
theorem cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (PIndex :
      σ → ιD → Finset (Finset (Cube × Fin 4)))
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (hmem :
      ∀ Z D P,
        P ∈ PIndex Z D ↔
          P ⊆ gapCubes Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible Z D P = true) :
    PIndex =
      cmp116Eq231SourcePIndex gapCubes admissible := by
  funext Z D
  ext P
  exact
    (hmem Z D P).trans
      (cmp116Eq231SourcePIndex_mem_iff
        gapCubes admissible Z D P).symm

/-- CMP116/CMP109 source-side dictionary for Balaban's Eq. (2.31) `P` family.

The predicate `sourceAdmissible` is the transcribed source condition: the
page-12 `Y0^{c,*}`/`b0(c)` exclusion, interior/boundary requirements, and
minimal-`Z0` convention after transporting positive oriented bonds through
the CMP109 `Cube × Fin 4` encoding.  The package is deliberately not a
consumer constructor.  It records the source theorem needed by the existing
`of_sourcePIndexMemIff` route and keeps the source predicate explicit, so a
generic boolean `admissible` is not treated as source-defined by fiat. -/
structure CMP116Eq231BalabanPFamilySourcePackage
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (PIndex :
      σ → ιD → Finset (Finset (Cube × Fin 4)))
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (sourceAdmissible :
      σ → ιD → Finset (Cube × Fin 4) → Prop) : Prop where

  /-- CMP116 page 12 / Eq. (2.3): the actual Balaban `P` family is exactly the
  finite family satisfying the source admissibility condition. -/
  mem_iff_source :
    ∀ Z D P,
      P ∈ PIndex Z D ↔ sourceAdmissible Z D P

  /-- CMP109 positive-orientation dictionary plus the CMP116 carrier
  restriction: every source-admissible `P` uses only the four positive
  directions over the `Z0 \ Y0` gap represented by `gapCubes`. -/
  source_subset_gapCarrier :
    ∀ Z D P,
      sourceAdmissible Z D P →
        P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4))

  /-- The Lean boolean `admissible` is definitionally tied to the transcribed
  source condition, including the `b0(c)` exclusion, interior/boundary
  requirements, and minimal-domain convention. -/
  admissible_iff_source :
    ∀ Z D P,
      admissible Z D P = true ↔ sourceAdmissible Z D P

/-- The source dictionary gives the one-way carrier inclusion currently
supported by the CMP116/CMP109 extraction.

This is weaker than the full filtered-family iff; it is useful for the older
`of_sourceBondSets` route and records precisely which part of the source
package supplies carrier containment. -/
theorem cmp116Eq231_balabanPFamily_subset_gapCarrier
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (PIndex :
      σ → ιD → Finset (Finset (Cube × Fin 4)))
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (sourceAdmissible :
      σ → ιD → Finset (Cube × Fin 4) → Prop)
    (S :
      CMP116Eq231BalabanPFamilySourcePackage
        PIndex gapCubes admissible sourceAdmissible) :
    ∀ Z D P,
      P ∈ PIndex Z D →
        P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4)) := by
  intro Z D P hP
  exact S.source_subset_gapCarrier Z D P ((S.mem_iff_source Z D P).mp hP)

/-- Source-fed pointwise membership theorem for the CMP116 Eq. (2.31) `P`
family.

This is the exact `hmem` premise consumed by
`CMP116Eq231PBondBoundary.of_sourcePIndexMemIff`.  The proof uses the
source-side package, not the Lean filtered-family definition alone. -/
theorem cmp116Eq231_balabanPFamily_sourcePIndexMemIff
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (PIndex :
      σ → ιD → Finset (Finset (Cube × Fin 4)))
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (sourceAdmissible :
      σ → ιD → Finset (Cube × Fin 4) → Prop)
    (S :
      CMP116Eq231BalabanPFamilySourcePackage
        PIndex gapCubes admissible sourceAdmissible) :
    ∀ Z D P,
      P ∈ PIndex Z D ↔
        P ⊆ gapCubes Z D ×ˢ
            (Finset.univ : Finset (Fin 4)) ∧
          admissible Z D P = true := by
  intro Z D P
  constructor
  · intro hP
    have hsource : sourceAdmissible Z D P :=
      (S.mem_iff_source Z D P).mp hP
    exact
      ⟨S.source_subset_gapCarrier Z D P hsource,
        (S.admissible_iff_source Z D P).mpr hsource⟩
  · intro h
    have hsource : sourceAdmissible Z D P :=
      (S.admissible_iff_source Z D P).mp h.2
    exact (S.mem_iff_source Z D P).mpr hsource

/-- The CMP116/CMP109 source dictionary identifies Balaban's `P` family with
the repository filtered family once the source admissibility predicate has been
transcribed and tied to the Lean boolean. -/
theorem cmp116Eq231_balabanPFamily_eq_sourceFilteredBondSets
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (PIndex :
      σ → ιD → Finset (Finset (Cube × Fin 4)))
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (sourceAdmissible :
      σ → ιD → Finset (Cube × Fin 4) → Prop)
    (S :
      CMP116Eq231BalabanPFamilySourcePackage
        PIndex gapCubes admissible sourceAdmissible) :
    PIndex =
      cmp116Eq231SourcePIndex gapCubes admissible :=
  cmp116Eq231PIndex_eq_sourceFilteredBondSets_of_mem_iff
    PIndex gapCubes admissible
    (cmp116Eq231_balabanPFamily_sourcePIndexMemIff
      PIndex gapCubes admissible sourceAdmissible S)

/-- Membership in the filtered source `P` family automatically gives
containment in the four-direction carrier. -/
theorem cmp116Eq231SourcePIndex_subset_carrier
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (Z : σ) (D : ιD) :
    ∀ P, P ∈ cmp116Eq231SourcePIndex gapCubes admissible Z D →
      P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4)) := by
  intro P hP
  rw [cmp116Eq231SourcePIndex, Finset.mem_filter, Finset.mem_powerset] at hP
  exact hP.1

/-- Concrete CMP116 (2.31) boundary when the `P` index is the finite bond set
itself and the carrier is the four positive coordinate directions over the
microscopic gap.  The only source-specific input left here is containment of
each source `P` in that carrier. -/
noncomputable def CMP116Eq231PBondBoundary.of_sourceBondSets
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (DIndex : σ → Finset ιD)
    (PIndex :
      σ → ιD → Finset (Finset (Cube × Fin 4)))
    (gapCubes : σ → ιD → Finset Cube)
    (localizationScale : ℕ)
    (hlocalizationScale : 0 < localizationScale)
    (hPcarrier :
      ∀ Z D, D ∈ DIndex Z →
        ∀ P, P ∈ PIndex Z D →
          P ⊆ gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4))) :
    CMP116Eq231PBondBoundary
      (β := Cube × Fin 4) DIndex PIndex localizationScale := by
  refine
    { pBonds := fun _ _ P => P
      bondCarrier := fun Z D =>
        gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4))
      gapMass := fun Z D =>
        ((gapCubes Z D).card : ℝ) / ((localizationScale : ℝ) ^ 4)
      pBonds_injective := ?_
      pBonds_subset := hPcarrier
      gapMass_nonneg := ?_
      bondCarrier_card_le := ?_ }
  · intro Z D hD P₁ hP₁ P₂ hP₂ hEq
    exact hEq
  · intro Z D hD
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · intro Z D hD
    have hscale_ne : ((localizationScale : ℝ) ^ 4) ≠ 0 := by
      have hscale_real : (localizationScale : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hlocalizationScale)
      exact pow_ne_zero 4 hscale_real
    have hcard :
        (((gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4))).card : ℝ) =
          4 * ((gapCubes Z D).card : ℝ)) := by
      simp [Finset.card_product, mul_comm]
    exact le_of_eq <| by
      calc
        (((gapCubes Z D ×ˢ (Finset.univ : Finset (Fin 4))).card : ℝ) =
          4 * ((gapCubes Z D).card : ℝ)) := hcard
        _ =
          4 * ((localizationScale : ℝ) ^ 4) *
            (((gapCubes Z D).card : ℝ) /
              ((localizationScale : ℝ) ^ 4)) := by
              field_simp [hscale_ne]

/-- Concrete CMP116 (2.31) boundary for the filtered-powerset source family.
Here carrier containment is definitional from powerset membership. -/
noncomputable def CMP116Eq231PBondBoundary.of_sourceFilteredBondSets
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (DIndex : σ → Finset ιD)
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (localizationScale : ℕ)
    (hlocalizationScale : 0 < localizationScale) :
    CMP116Eq231PBondBoundary
      (β := Cube × Fin 4)
      DIndex
      (cmp116Eq231SourcePIndex gapCubes admissible)
      localizationScale := by
  exact
    CMP116Eq231PBondBoundary.of_sourceBondSets
      DIndex
      (cmp116Eq231SourcePIndex gapCubes admissible)
      gapCubes
      localizationScale
      hlocalizationScale
      (fun Z D hD =>
        cmp116Eq231SourcePIndex_subset_carrier gapCubes admissible Z D)

/-- Concrete CMP116 (2.31) boundary from the exact source-membership theorem.

This is the theorem-facing variant of `of_sourceFilteredBondSets`: it does not
require callers to rewrite their `PIndex` to the filtered family first.  A
future source proof of the pointwise iff immediately supplies the carrier
containment needed by the finite bond-subset summation. -/
noncomputable def CMP116Eq231PBondBoundary.of_sourcePIndexMemIff
    {σ ιD Cube : Type*}
    [DecidableEq Cube]
    (DIndex : σ → Finset ιD)
    (PIndex :
      σ → ιD → Finset (Finset (Cube × Fin 4)))
    (gapCubes : σ → ιD → Finset Cube)
    (admissible :
      σ → ιD → Finset (Cube × Fin 4) → Bool)
    (localizationScale : ℕ)
    (hlocalizationScale : 0 < localizationScale)
    (hmem :
      ∀ Z D P,
        P ∈ PIndex Z D ↔
          P ⊆ gapCubes Z D ×ˢ
              (Finset.univ : Finset (Fin 4)) ∧
            admissible Z D P = true) :
    CMP116Eq231PBondBoundary
      (β := Cube × Fin 4) DIndex PIndex localizationScale := by
  exact
    CMP116Eq231PBondBoundary.of_sourceBondSets
      DIndex PIndex gapCubes localizationScale hlocalizationScale
      (fun Z D _hD P hP => ((hmem Z D P).mp hP).1)

/-- The exact exponential shape summed in CMP116 equation (2.31).

For the source parameters in CMP116 (2.31),
`rate = (1 / 20) * gamma2 * epsilon1^2 / gk^2` and `gapMass`
abstracts `M^-4 * |Z0 \ Y0|`. -/
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

/-- A source-shaped sufficient scalar condition for the CMP116 (2.31)
geometric rate premise.

CMP116 (2.31) records the rate in this lane as
`gamma2 * epsilon1^2 / (20 * gk^2)`.  The displayed second inequality there is
the bracket condition
`4 * M^4 * exp (-(gamma2 * epsilon1^2 / (10 * gk^2)))
  <= gamma2 * epsilon1^2 / (20 * gk^2)`.

The small-coupling inequality below is a stronger formal sufficient condition
for that bracket condition; it is not claimed to be Balaban's verbatim
parameter-hierarchy hypothesis. -/
theorem cmp116Eq231_rate_condition_of_source_smallness
    (localizationScale : ℕ)
    (gamma2 epsilon1 gk : ℝ)
    (hgk : 0 < gk)
    (hsmall :
      80 * ((localizationScale : ℝ) ^ 4) * gk ^ 2 ≤
        gamma2 * epsilon1 ^ 2) :
    4 * ((localizationScale : ℝ) ^ 4) *
        Real.exp
          (-(2 *
            (gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2)))) ≤
      gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2) := by
  let rho : ℝ := gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2)
  have hgk_sq_pos : 0 < gk ^ 2 := sq_pos_of_pos hgk
  have hden_pos : 0 < 20 * gk ^ 2 := by positivity
  have hfour_le_rho :
      4 * ((localizationScale : ℝ) ^ 4) ≤ rho := by
    dsimp [rho]
    rw [le_div_iff₀ hden_pos]
    calc
      4 * ((localizationScale : ℝ) ^ 4) * (20 * gk ^ 2)
          = 80 * ((localizationScale : ℝ) ^ 4) * gk ^ 2 := by
            ring
      _ ≤ gamma2 * epsilon1 ^ 2 := hsmall
  have hrho_nonneg : 0 ≤ rho := by
    exact
      (mul_nonneg (by positivity : 0 ≤ (4 : ℝ))
          (by positivity : 0 ≤ ((localizationScale : ℝ) ^ 4))).trans
        hfour_le_rho
  have hexp_le_one : Real.exp (-(2 * rho)) ≤ 1 := by
    calc
      Real.exp (-(2 * rho)) ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = 1 := by rw [Real.exp_zero]
  have hscale_nonneg :
      0 ≤ 4 * ((localizationScale : ℝ) ^ 4) := by positivity
  calc
    4 * ((localizationScale : ℝ) ^ 4) *
        Real.exp (-(2 * rho)) ≤
      4 * ((localizationScale : ℝ) ^ 4) * 1 := by
        exact mul_le_mul_of_nonneg_left hexp_le_one hscale_nonneg
    _ = 4 * ((localizationScale : ℝ) ^ 4) := by ring
    _ ≤ rho := hfour_le_rho

/-- The exact bracket condition displayed in CMP116 (2.31), rewritten into the
generic geometric-rate premise used by the finite P-family theorem. -/
theorem cmp116Eq231_rate_condition_of_source_bracket
    (localizationScale : ℕ)
    (gamma2 epsilon1 gk : ℝ)
    (hbracket :
      4 * ((localizationScale : ℝ) ^ 4) *
          Real.exp (-(gamma2 * epsilon1 ^ 2 / (10 * gk ^ 2))) ≤
        gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2)) :
    4 * ((localizationScale : ℝ) ^ 4) *
        Real.exp
          (-(2 *
            (gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2)))) ≤
      gamma2 * epsilon1 ^ 2 / (20 * gk ^ 2) := by
  convert hbracket using 2
  ring_nf

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
