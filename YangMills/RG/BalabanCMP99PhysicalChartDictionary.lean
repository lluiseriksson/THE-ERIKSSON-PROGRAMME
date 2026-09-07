/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99PatchedParametrixPhysicalSummability

/-!
# Source dictionary for physical CMP99 charts

The sparse patched-walk theorem has four remaining geometric inputs: a finite
chart family with nested cores, an injective simple-domain realization, the
near-range-to-meeting implication, and a uniform active-carrier budget.  This
file packages exactly those inputs and exposes the physical summability
theorem through a single source certificate.

The structure does not manufacture the charts.  Constructing an instance from
the literal CMP99 partition and collar conventions is the remaining source
geometry task.
-/

namespace YangMills.RG

noncomputable section

universe u v

private abbrev PhysicalEndomorphism (d N Nc : ℕ) [NeZero N] :=
  PhysicalGaugeOneCochain d N Nc →L[ℝ]
    PhysicalGaugeOneCochain d N Nc

/-- Complete source-facing geometric certificate for the physical patched
chart walk. -/
structure CMP99PhysicalChartDictionary
    {ι : Type*} [DecidableEq ι]
    {V : Type u} [Fintype V] [DecidableEq V]
    {Cube : Type v} [DecidableEq Cube]
    {d N : ℕ} [NeZero N]
    (G : SimpleGraph V) (S B : ℕ)
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ) (Rrange : ℕ) where
  charts : Finset ι
  core : ι → Finset (PhysicalBond d N)
  enlarged : ι → Finset (PhysicalBond d N)
  domainOf : ↥charts → CMP99SimpleLocalizationDomain G S
  domainActive : ↥charts → Finset Cube
  core_subset_enlarged : ∀ i, i ∈ charts → core i ⊆ enlarged i
  domainOf_injective : Function.Injective domainOf
  near_implies_meets : ∀ (left right : ↥charts),
    CMP99PhysicalPatchCanFollow core enlarged dist Rrange left right →
      (domainOf left).Meets (domainOf right)
  active_card_le : ∀ X, (domainActive X).card ≤ B

namespace CMP99PhysicalChartDictionary

variable {ι : Type*} [DecidableEq ι]
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {Cube : Type v} [DecidableEq Cube]
variable {d N : ℕ} [NeZero N]
variable {G : SimpleGraph V} {S B Rrange : ℕ}
variable {dist : PhysicalBond d N → PhysicalBond d N → ℕ}

/-- The dictionary itself produces the explicit volume-uniform branching
bound for every physical chart. -/
theorem card_successorSteps_le
    [DecidableRel G.Adj]
    (Dict : CMP99PhysicalChartDictionary
      (Cube := Cube) G S B dist Rrange)
    (Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (left : ↥Dict.charts) :
    (cmp99PhysicalPatchSuccessorSteps
      (ι := ι) (d := d) (N := N)
      Dict.charts Dict.core Dict.enlarged dist Rrange left).card ≤
        S * (S + 1) * Δ ^ (2 * S) :=
  card_cmp99PhysicalPatchSuccessorSteps_le_simpleDomainBound
    G Dict.charts Dict.core Dict.enlarged dist Rrange S Δ hΔ hΔ1
    Dict.domainOf Dict.domainOf_injective Dict.near_implies_meets left

end CMP99PhysicalChartDictionary

section DictionarySummability

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {Cube : Type v} [DecidableEq Cube]

/-- Terminal corollary consuming one physical chart dictionary.  The public
interface no longer repeats the chart nesting, domain injection,
near-to-meeting, or active-cardinality proofs. -/
theorem CMP99PhysicalChartDictionary.summable_weakenedPhysicalPatchWalkSeries
    {ι : Type*} [DecidableEq ι]
    {d N Nc : ℕ} [NeZero N]
    {S B Rrange NR : ℕ}
    (dist : PhysicalBond d N → PhysicalBond d N → ℕ)
    (Dict : CMP99PhysicalChartDictionary
      (Cube := Cube) G S B dist Rrange)
    (K : PhysicalEndomorphism d N Nc)
    (hsymm : ∀ p q, dist p q = dist q p)
    (hself : ∀ p, dist p p = 0)
    (htri : ∀ x y z, dist x y ≤ dist x z + dist z y)
    {M c mass κ σ Ssum Sdef : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (hmass : 0 < mass)
    (hσ : 0 ≤ σ) (h3σκ : 3 * σ < κ)
    (hSsum : 0 ≤ Ssum) (hSdef : 0 ≤ Sdef)
    (hsum : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(σ * (dist x z : ℝ))) ≤ Ssum)
    (hsumDef : ∀ x,
      ∑ z : PhysicalBond d N,
        Real.exp (-(((((κ - σ) - σ) - σ) * (dist x z : ℝ)))) ≤ Sdef)
    (hrange : PhysicalCovarianceFiniteRange K dist Rrange)
    (hbound : PhysicalCovarianceKernelBound K (fun _ _ => M))
    (hK : IsCoerciveCLM K c)
    (hNR : ∀ x : PhysicalBond d N,
      (Finset.univ.filter (fun y => dist x y ≤ Rrange)).card ≤ NR)
    (htilt :
      (M + |mass|) *
          (Real.exp (κ * (Rrange : ℝ)) - 1) *
            (NR : ℝ) ≤
        min c mass / 2)
    (Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (left : ↥Dict.charts) (s : Cube → ℝ) (Rweak : ℝ)
    (hRweak : 1 ≤ Rweak)
    (hsmall :
      ((S * (S + 1) * Δ ^ (2 * S) : ℕ) : ℝ) *
          (cmp99SingleDefectDecayAmplitude
            M κ Rrange c mass Ssum * Sdef) * Rweak ^ B < 1)
    (hs : s ∈ cmp116WeakeningPolydisc Rweak) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99PhysicalPatchSuccessorSteps
          (ι := ι) (d := d) (N := N)
          Dict.charts Dict.core Dict.enlarged dist Rrange) left =>
      cmp116WeakeningMonomial (walk.active Dict.domainActive) s •
        walk.term
          (cmp99PhysicalPatchHead
            Dict.charts K Dict.enlarged Dict.core hc hmass hK)
          (fun _ => cmp99PhysicalPatchContinuation
            Dict.charts K Dict.enlarged Dict.core hc hmass hK) := by
  exact
    summable_cmp116WeakenedPhysicalPatchWalkSeries_of_simpleDomainDictionary
      G Dict.charts K Dict.enlarged Dict.core Dict.core_subset_enlarged
      dist hsymm hself htri hM hc hmass hσ h3σκ hSsum hSdef
      hsum hsumDef hrange hbound hK hNR htilt S Δ B hΔ hΔ1
      Dict.domainOf Dict.domainOf_injective Dict.near_implies_meets
      Dict.domainActive Dict.active_card_le left s Rweak hRweak hsmall hs

end DictionarySummability

end

end YangMills.RG
