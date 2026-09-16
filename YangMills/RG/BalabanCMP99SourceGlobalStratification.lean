/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceStratifiedGaugeMass

/-!
# The global `Omega_j` / `Lambda_j` stratification of CMP99

Printed CMP99 p. 393 uses a global nested sequence

`Omega_0 superset ... superset Omega_k superset Omega_{k+1} = empty`

and defines `Lambda_j = Omega_j \ Omega_{j+1}`.  This object is deliberately
separate from the local domains `Omega_n(Pi)` on printed p. 408.  Conflating
the two sequences would give the wrong restriction in the mass term
`Q'^* a Q'` of (3.24).

The parameter `n` is the number of strata.  Thus `regions` has `n+1`
entries, including the terminal empty region, while `stratum` has `n`
entries.  The theorems below prove that the strata are pairwise disjoint and
partition `Omega_0` exactly.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- A source-faithful global nested sequence
`Omega_0 superset ... superset Omega_n = empty`.

This is the geometry of CMP99 (3.18)--(3.24), not the local propagator
geometry `Omega_r(Pi)` used later in Section C. -/
structure CMP99SourceGlobalStratification
    (Site : Type*) [DecidableEq Site] (n : ℕ) where
  regions : Fin (n + 1) → Finset Site
  antitone_regions : Antitone regions
  final_empty : regions (Fin.last n) = ∅

namespace CMP99SourceGlobalStratification

variable {Site : Type*} [DecidableEq Site] {n : ℕ}

/-- `Lambda_r = Omega_r \ Omega_{r+1}`. -/
def stratum (S : CMP99SourceGlobalStratification Site n) (r : Fin n) :
    Finset Site :=
  S.regions r.castSucc \ S.regions r.succ

@[simp] theorem mem_stratum_iff
    (S : CMP99SourceGlobalStratification Site n) (r : Fin n) (x : Site) :
    x ∈ S.stratum r ↔
      x ∈ S.regions r.castSucc ∧ x ∉ S.regions r.succ := by
  simp [stratum]

/-- Every stratum is contained in its source region. -/
theorem stratum_subset_region
    (S : CMP99SourceGlobalStratification Site n) (r : Fin n) :
    S.stratum r ⊆ S.regions r.castSucc := by
  exact Finset.sdiff_subset

/-- Later regions are contained in earlier regions. -/
theorem regions_subset_of_le
    (S : CMP99SourceGlobalStratification Site n)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    S.regions j ⊆ S.regions i :=
  S.antitone_regions hij

/-- Distinct ordered strata are disjoint. -/
theorem disjoint_stratum_of_lt
    (S : CMP99SourceGlobalStratification Site n)
    {r s : Fin n} (hrs : r < s) :
    Disjoint (S.stratum r) (S.stratum s) := by
  rw [Finset.disjoint_left]
  intro x hxr hxs
  have hnot : x ∉ S.regions r.succ := (S.mem_stratum_iff r x).mp hxr |>.2
  have hs : x ∈ S.regions s.castSucc :=
    (S.mem_stratum_iff s x).mp hxs |>.1
  have hle : r.succ ≤ s.castSucc := by
    change r.val + 1 ≤ s.val
    omega
  exact hnot (S.antitone_regions hle hs)

/-- The source strata are pairwise disjoint. -/
theorem pairwise_disjoint_strata
    (S : CMP99SourceGlobalStratification Site n) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin n)) S.stratum := by
  intro r _hr s _hs hrs
  rcases lt_or_gt_of_ne hrs with hrs | hsr
  · exact S.disjoint_stratum_of_lt hrs
  · exact (S.disjoint_stratum_of_lt hsr).symm

/-- The disjoint source strata cover `Omega_0` exactly. -/
theorem biUnion_strata_eq_region_zero
    (S : CMP99SourceGlobalStratification Site n) :
    (Finset.univ : Finset (Fin n)).biUnion S.stratum = S.regions 0 := by
  ext x
  constructor
  · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    rintro ⟨r, hxr⟩
    have hr : x ∈ S.regions r.castSucc :=
      (S.mem_stratum_iff r x).mp hxr |>.1
    exact S.antitone_regions (Fin.zero_le r.castSucc) hr
  · intro hx0
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    by_contra hnone
    push_neg at hnone
    have hstep : ∀ r : Fin n,
        x ∈ S.regions r.castSucc → x ∈ S.regions r.succ := by
      intro r hr
      by_contra hn
      exact hnone r ((S.mem_stratum_iff r x).2 ⟨hr, hn⟩)
    have hall : ∀ m : ℕ, (hm : m ≤ n) →
        x ∈ S.regions ⟨m, Nat.lt_succ_iff.mpr hm⟩ := by
      intro m
      induction m with
      | zero =>
          intro _hm
          simpa using hx0
      | succ m ih =>
          intro hm
          have hm_lt : m < n := by omega
          let r : Fin n := ⟨m, hm_lt⟩
          have hprev : x ∈ S.regions r.castSucc := by
            simpa [r] using ih (by omega)
          simpa [r] using hstep r hprev
    have hlast : x ∈ S.regions (Fin.last n) := by
      simpa using hall n le_rfl
    simpa [S.final_empty] using hlast

/-- Membership in `Omega_0` has a unique stratum index. -/
theorem existsUnique_mem_stratum
    (S : CMP99SourceGlobalStratification Site n)
    {x : Site} (hx : x ∈ S.regions 0) :
    ∃! r : Fin n, x ∈ S.stratum r := by
  have hxUnion : x ∈ (Finset.univ : Finset (Fin n)).biUnion S.stratum := by
    rw [S.biUnion_strata_eq_region_zero]
    exact hx
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hxUnion
  rcases hxUnion with ⟨r, hr⟩
  refine ⟨r, hr, ?_⟩
  intro s hs
  by_contra hrs
  have hd := S.pairwise_disjoint_strata
    (Set.mem_univ r) (Set.mem_univ s) (Ne.symm hrs)
  exact (Finset.disjoint_left.mp hd) hr hs

end CMP99SourceGlobalStratification

end

end YangMills.RG
