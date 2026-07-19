/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceGlobalStratification

/-!
# Admissible source region sequences in CMP96 (2.1)--(2.4)

CMP96 (2.1)--(2.2) does not define a unique sequence of regions.  It asks
for a nested sequence and the strict separation

`(L^r eta)^{-1} dist(Omega_r^c, Omega_{r+1}) > R M`.

On a lattice already expressed in scale-`r` units this is the pointwise
condition `gap r < dist x y` for `x` outside `Omega_r` and `y` inside
`Omega_{r+1}`.  The source explicitly permits some initial regions to be the
whole torus.  Consequently the regions are physical boundary data subject to
an admissibility predicate, not a function of the scale index.

This file makes that distinction formal.  It also gives the minimal exact
non-uniqueness witness: the empty sequence and the sequence equal to the
whole finite carrier until its terminal empty member both satisfy every
strict separation budget.  Thus no source-faithful constructor may claim to
recover a unique global sequence from scalar constants alone.
-/

namespace YangMills.RG

noncomputable section

/-- Pointwise form of
`dist(outer^c, inner) > gap`.  The universal formulation gives the correct
vacuous value when `outer` is the whole carrier or `inner` is empty. -/
def CMP96SourceRegionSeparated
    {Site : Type*} [DecidableEq Site]
    (dist : Site → Site → ℕ) (gap : ℕ)
    (outer inner : Finset Site) : Prop :=
  ∀ x, x ∉ outer → ∀ y, y ∈ inner → gap < dist x y

/-- A global CMP96 sequence satisfying the printed strict gap at every
consecutive transition.  The scalar gap is a parameter, so it can later be
instantiated by the source value `R*M` at each dependent lattice scale. -/
structure CMP96SourceAdmissibleGlobalStratification
    (Site : Type*) [DecidableEq Site] (n : ℕ)
    (dist : Site → Site → ℕ) (gap : Fin n → ℕ)
    extends CMP99SourceGlobalStratification Site n where
  separated : ∀ r : Fin n,
    CMP96SourceRegionSeparated dist (gap r)
      (toCMP99SourceGlobalStratification.regions r.castSucc)
      (toCMP99SourceGlobalStratification.regions r.succ)

namespace CMP96SourceAdmissibleGlobalStratification

variable {Site : Type*} [DecidableEq Site] [Fintype Site]
variable {n : ℕ} {dist : Site → Site → ℕ} {gap : Fin n → ℕ}

/-- The identically empty sequence is admissible for every metric and every
strict gap budget. -/
noncomputable def empty :
    CMP96SourceAdmissibleGlobalStratification Site n dist gap where
  regions := fun _ => ∅
  antitone_regions := fun _ _ _ h => by simpa using h
  final_empty := rfl
  separated := by
    intro r x hx y hy
    simp at hy

/-- The source-permitted sequence that is the whole carrier at every
nonterminal level and empty at the terminal level. -/
noncomputable def fullUntilLast :
    CMP96SourceAdmissibleGlobalStratification Site n dist gap where
  regions := fun r => if r = Fin.last n then ∅ else Finset.univ
  antitone_regions := by
    intro r s hrs x hx
    by_cases hs : s = Fin.last n
    · simp [hs] at hx
    · have hr : r ≠ Fin.last n := by
        intro hr
        subst r
        have hslast : s = Fin.last n := by
          apply Fin.ext
          have hsle : n ≤ s.val := hrs
          exact Nat.le_antisymm (Nat.le_of_lt_succ s.isLt) hsle
        exact hs hslast
      simp [hr]
  final_empty := by simp
  separated := by
    intro r x hx y hy
    have hr : r.castSucc ≠ Fin.last n := by
      intro h
      have := congrArg Fin.val h
      simp at this
      exact (Nat.ne_of_lt r.isLt) this
    simp [hr] at hx

@[simp] theorem empty_regions (r : Fin (n + 1)) :
    (empty (Site := Site) (dist := dist) (gap := gap)).regions r = ∅ := rfl

@[simp] theorem fullUntilLast_regions_of_ne_last
    (r : Fin (n + 1)) (hr : r ≠ Fin.last n) :
    (fullUntilLast (Site := Site) (dist := dist) (gap := gap)).regions r =
      Finset.univ := by
  simp [fullUntilLast, hr]

/-- Exact non-uniqueness obstruction.  When there is at least one stratum
and at least one site, two different region sequences satisfy the same
metric and the same strict separation constants. -/
theorem empty_ne_fullUntilLast [Nonempty Site] (hn : 0 < n) :
    empty (Site := Site) (dist := dist) (gap := gap) ≠
      fullUntilLast (Site := Site) (dist := dist) (gap := gap) := by
  intro h
  have hregions := congrArg
    (fun S : CMP96SourceAdmissibleGlobalStratification Site n dist gap =>
      S.regions (0 : Fin (n + 1))) h
  have hzero_ne_last : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro hz
    have := congrArg Fin.val hz
    simp at this
    omega
  change (∅ : Finset Site) =
    (if (0 : Fin (n + 1)) = Fin.last n then ∅ else Finset.univ) at hregions
  rw [if_neg hzero_ne_last] at hregions
  let x : Site := Classical.choice (inferInstance : Nonempty Site)
  have hx : x ∈ (∅ : Finset Site) := by
    rw [hregions]
    exact Finset.mem_univ x
  simpa using hx

/-- Forgetting the source gap certificate recovers the global
`Omega`/`Lambda` stratification consumed by the CMP99 mass term. -/
def global
    (S : CMP96SourceAdmissibleGlobalStratification Site n dist gap) :
    CMP99SourceGlobalStratification Site n :=
  S.toCMP99SourceGlobalStratification

@[simp] theorem global_regions
    (S : CMP96SourceAdmissibleGlobalStratification Site n dist gap)
    (r : Fin (n + 1)) :
    S.global.regions r = S.regions r := rfl

end CMP96SourceAdmissibleGlobalStratification

end

end YangMills.RG
