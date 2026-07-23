/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP116Eq214PhysicalIndices
import YangMills.RG.BalabanCMP116Eq229
import YangMills.RG.AppendixFFiberEntropy

/-!
# CMP116 equation (2.29) on exact-union `D` fibers

CMP116 does not apply equation (2.29) to the whole outer `D` index at once.
It first fixes the union

`Y₀ = ⋃ Y ∈ D, Y`

and sums only the subfamilies with that exact union.  This distinction is
forced mathematically: the unrestricted powerset contains the empty family,
whose product is one, so a nontrivial nonnegative unrestricted sum cannot be
bounded by one.

This module records the exact finite regrouping needed by the source:

* `cmp116Eq229UnionIndex` is the finite set of unions which actually occur;
* `cmp116Eq229DIndexFiber` is the fixed-union fiber;
* the original `D` sum is exactly the iterated sum over unions and fibers;
* `CMP116Eq229FiberSummability` states (2.29) on those fibers;
* `cmp116_DStage_sum_le_of_eq229_fibers` consumes the fiberwise estimate
  without ever assuming an impossible bound on the unrestricted `D` sum.

For the literal physical index of equation (2.14), the generic fiber is proved
equal to the source family

`{D ⊆ domainFamily | cmp116Eq23Y0 D = Y₀}`.

Honest scope: this file corrects the summation architecture but does not yet
prove the small-`alpha6`/large-`kappa` estimate inside each exact-union fiber.
That next estimate must use (2.27), (2.30), and connected-domain counting.
-/

namespace YangMills.RG

open scoped BigOperators

/-- The finite set of union labels attained by an outer `D` index. -/
noncomputable def cmp116Eq229UnionIndex
    {σ ιD ιY0 : Type*}
    (DIndex : σ → Finset ιD)
    (unionOf : σ → ιD → ιY0)
    (Z : σ) : Finset ιY0 := by
  classical
  exact (DIndex Z).image (unionOf Z)

/-- The exact-union fiber inside one outer `D` index. -/
noncomputable def cmp116Eq229DIndexFiber
    {σ ιD ιY0 : Type*}
    (DIndex : σ → Finset ιD)
    (unionOf : σ → ιD → ιY0)
    (Z : σ) (Y0 : ιY0) : Finset ιD := by
  classical
  exact (DIndex Z).filter fun D => unionOf Z D = Y0

@[simp] theorem mem_cmp116Eq229UnionIndex_iff
    {σ ιD ιY0 : Type*}
    (DIndex : σ → Finset ιD)
    (unionOf : σ → ιD → ιY0)
    (Z : σ) (Y0 : ιY0) :
    Y0 ∈ cmp116Eq229UnionIndex DIndex unionOf Z ↔
      ∃ D ∈ DIndex Z, unionOf Z D = Y0 := by
  classical
  simp [cmp116Eq229UnionIndex]

@[simp] theorem mem_cmp116Eq229DIndexFiber_iff
    {σ ιD ιY0 : Type*}
    (DIndex : σ → Finset ιD)
    (unionOf : σ → ιD → ιY0)
    (Z : σ) (Y0 : ιY0) (D : ιD) :
    D ∈ cmp116Eq229DIndexFiber DIndex unionOf Z Y0 ↔
      D ∈ DIndex Z ∧ unionOf Z D = Y0 := by
  classical
  simp [cmp116Eq229DIndexFiber]

/-- Exact finite regrouping of an outer `D` sum by its union label. -/
theorem cmp116_DStage_sum_eq_sum_union_fibers
    {σ ιD ιY0 E : Type*} [AddCommMonoid E]
    (DIndex : σ → Finset ιD)
    (unionOf : σ → ιD → ιY0)
    (term : σ → ιD → E)
    (Z : σ) :
    (∑ D ∈ DIndex Z, term Z D) =
      ∑ Y0 ∈ cmp116Eq229UnionIndex DIndex unionOf Z,
        ∑ D ∈ cmp116Eq229DIndexFiber DIndex unionOf Z Y0,
          term Z D := by
  classical
  exact
    (Finset.sum_fiberwise_of_maps_to
      (s := DIndex Z)
      (t := cmp116Eq229UnionIndex DIndex unionOf Z)
      (g := unionOf Z)
      (f := term Z)
      (fun D hD => Finset.mem_image.mpr ⟨D, hD, rfl⟩)).symm

/-- The literal source family of subfamilies with exact union `Y₀`. -/
noncomputable def cmp116Eq229ExactUnionDIndex
    {β : Type*} [DecidableEq β]
    (domainFamily : Finset (Finset β))
    (Y0 : Finset β) :
    Finset (Finset (Finset β)) := by
  classical
  exact domainFamily.powerset.filter fun D => cmp116Eq23Y0 D = Y0

@[simp] theorem mem_cmp116Eq229ExactUnionDIndex_iff
    {β : Type*} [DecidableEq β]
    (domainFamily : Finset (Finset β))
    (Y0 : Finset β)
    (D : Finset (Finset β)) :
    D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0 ↔
      D ⊆ domainFamily ∧ cmp116Eq23Y0 D = Y0 := by
  classical
  simp [cmp116Eq229ExactUnionDIndex]

/-- On the physical equation-(2.14) index, a fixed-union fiber is literally
the source family of subfamilies of `domainFamily` whose union is `Y₀`. -/
theorem cmp116Eq229DIndexFiber_physical_eq_exactUnion
    {d N' : ℕ}
    (domainFamily : Finset (Finset (FinBox d N')))
    (Z Y0 : Finset (FinBox d N'))
    (hY0Z : Y0 ⊆ Z) :
    cmp116Eq229DIndexFiber
        (fun _Z => cmp116Eq214DIndex domainFamily _Z)
        (fun _Z D => cmp116Eq23Y0 D) Z Y0 =
      cmp116Eq229ExactUnionDIndex domainFamily Y0 := by
  classical
  ext D
  simp only [mem_cmp116Eq229DIndexFiber_iff,
    mem_cmp116Eq214DIndex_iff, mem_cmp116Eq229ExactUnionDIndex_iff]
  constructor
  · rintro ⟨⟨hD, _hUnionZ⟩, hUnion⟩
    exact ⟨hD, hUnion⟩
  · rintro ⟨hD, hUnion⟩
    refine ⟨⟨hD, ?_⟩, hUnion⟩
    rw [hUnion]
    exact hY0Z

/-- Every exact-union family over a nonempty target is a nonempty subfamily of
the source domains contained in that target. -/
theorem cmp116Eq229ExactUnionDIndex_subset_nonemptyPowerset
    {β : Type*} [DecidableEq β]
    (domainFamily : Finset (Finset β))
    (Y0 : Finset β) (hY0 : Y0.Nonempty) :
    cmp116Eq229ExactUnionDIndex domainFamily Y0 ⊆
      ((domainFamily.filter fun Y => Y ⊆ Y0).powerset.erase ∅) := by
  classical
  intro D hD
  rw [Finset.mem_erase, Finset.mem_powerset]
  have hsource :=
    (mem_cmp116Eq229ExactUnionDIndex_iff domainFamily Y0 D).mp hD
  constructor
  · intro hDempty
    subst D
    have hY0empty : Y0 = ∅ := by
      simpa [cmp116Eq23Y0] using hsource.2.symm
    exact hY0.ne_empty hY0empty
  · intro Y hYD
    rw [Finset.mem_filter]
    refine ⟨hsource.1 hYD, ?_⟩
    intro x hx
    rw [← hsource.2]
    exact Finset.mem_biUnion.mpr ⟨Y, hYD, hx⟩

/-- Finite Cammarota/Mayer overcount on one exact-union fiber.

The exact-union constraint is forgotten only after proving that every member
is a nonempty family of source domains contained in `Y₀`.  The resulting
nonempty powerset is evaluated by the standard product expansion and bounded
by `exp (sum weights) - 1`. -/
theorem cmp116Eq229ExactUnion_sum_prod_le_exp_sub_one
    {β : Type*} [DecidableEq β]
    (domainFamily : Finset (Finset β))
    (Y0 : Finset β) (hY0 : Y0.Nonempty)
    (w : Finset β → ℝ)
    (hw : ∀ Y ∈ domainFamily, 0 ≤ w Y) :
    (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
        ∏ Y ∈ D, w Y) ≤
      Real.exp
          (∑ Y ∈ domainFamily.filter (fun Y => Y ⊆ Y0), w Y) -
        1 := by
  classical
  let relevant := domainFamily.filter fun Y => Y ⊆ Y0
  have hsub :
      cmp116Eq229ExactUnionDIndex domainFamily Y0 ⊆
        relevant.powerset.erase ∅ := by
    simpa [relevant] using
      cmp116Eq229ExactUnionDIndex_subset_nonemptyPowerset
        domainFamily Y0 hY0
  have hnonneg :
      ∀ D ∈ relevant.powerset.erase ∅,
        D ∉ cmp116Eq229ExactUnionDIndex domainFamily Y0 →
          0 ≤ ∏ Y ∈ D, w Y := by
    intro D hD _hnot
    have hDsub : D ⊆ relevant := (Finset.mem_powerset.mp
      (Finset.mem_of_mem_erase hD))
    exact Finset.prod_nonneg fun Y hYD =>
      hw Y ((Finset.mem_filter.mp (hDsub hYD)).1)
  have hsum_le :
      (∑ D ∈ cmp116Eq229ExactUnionDIndex domainFamily Y0,
          ∏ Y ∈ D, w Y) ≤
        ∑ D ∈ relevant.powerset.erase ∅, ∏ Y ∈ D, w Y :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hrelevant_nonneg : ∀ Y ∈ relevant, 0 ≤ w Y := by
    intro Y hY
    exact hw Y (Finset.mem_filter.mp hY).1
  exact hsum_le.trans (by
    simpa [relevant] using
      sum_powerset_erase_empty_prod_le_exp_sub_one
        relevant w hrelevant_nonneg)

/-- Equation (2.29) in its source-correct form: summability is asserted on
each exact-union fiber, not on the unrestricted outer `D` index. -/
def CMP116Eq229FiberSummability
    {σ ιD ιY0 ιY : Type*}
    (DIndex : σ → Finset ιD)
    (unionOf : σ → ιD → ιY0)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ) : Prop :=
  ∀ Z Y0,
    Finset.sum
        (cmp116Eq229DIndexFiber DIndex unionOf Z Y0)
        (fun D =>
          cmp116Eq229Product DParts alpha6 delta kappa metric Z D) ≤
      1

/-- Source-correct first-stage consumer.

Each term is bounded by a base depending only on the fixed union `Y₀`, times
the equation-(2.29) product.  Fiber summability removes the `D` family, and the
outer result is the remaining finite sum over the union labels that actually
occur. -/
theorem cmp116_DStage_sum_le_of_eq229_fibers
    {σ ιD ιY0 ιY τ : Type*}
    (DIndex : σ → Finset ιD)
    (unionOf : σ → ιD → ιY0)
    (DParts : σ → ιD → Finset ιY)
    (alpha6 delta kappa : ℝ)
    (metric : σ → ιY → ℕ)
    (base : σ → ιY0 → τ → ℝ)
    (term : σ → ιD → τ → ℝ)
    (hEq229 :
      CMP116Eq229FiberSummability
        DIndex unionOf DParts alpha6 delta kappa metric)
    (hbase_nonneg : ∀ Z Y0 t, 0 ≤ base Z Y0 t)
    (hterm :
      ∀ Z D, D ∈ DIndex Z → ∀ t,
        term Z D t ≤
          base Z (unionOf Z D) t *
            cmp116Eq229Product
              DParts alpha6 delta kappa metric Z D) :
    ∀ Z t,
      Finset.sum (DIndex Z) (fun D => term Z D t) ≤
        Finset.sum (cmp116Eq229UnionIndex DIndex unionOf Z)
          (fun Y0 => base Z Y0 t) := by
  classical
  intro Z t
  rw [cmp116_DStage_sum_eq_sum_union_fibers
    DIndex unionOf (fun Z D => term Z D t) Z]
  refine Finset.sum_le_sum fun Y0 _hY0 => ?_
  calc
    (∑ D ∈ cmp116Eq229DIndexFiber DIndex unionOf Z Y0,
        term Z D t) ≤
      ∑ D ∈ cmp116Eq229DIndexFiber DIndex unionOf Z Y0,
        base Z Y0 t *
          cmp116Eq229Product DParts alpha6 delta kappa metric Z D := by
      refine Finset.sum_le_sum fun D hD => ?_
      have hmem :=
        (mem_cmp116Eq229DIndexFiber_iff DIndex unionOf Z Y0 D).mp hD
      simpa [hmem.2] using hterm Z D hmem.1 t
    _ =
      base Z Y0 t *
        ∑ D ∈ cmp116Eq229DIndexFiber DIndex unionOf Z Y0,
          cmp116Eq229Product DParts alpha6 delta kappa metric Z D := by
      rw [Finset.mul_sum]
    _ ≤ base Z Y0 t * 1 := by
      exact mul_le_mul_of_nonneg_left (hEq229 Z Y0)
        (hbase_nonneg Z Y0 t)
    _ = base Z Y0 t := by ring

end YangMills.RG
