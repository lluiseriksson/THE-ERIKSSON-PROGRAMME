/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import Mathlib
import YangMills.RG.ModifiedMetric
import YangMills.RG.CubeLattice
import YangMills.RG.LocalKP

/-!
# Bounded-hole cardinality compression (`hRpoly` campaign — P3.5 brick B2)

`docs/HRPOLY-CAMPAIGN-PLAN.md` §3bis.  Discharges the carried
cardinality-compression binder

`(X.val.card : ℝ) ≤ θ * ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ)`

of `appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric`,
`appendixFHoleMetricCoverWeight_mul_exp_card_le_shifted_of_source_card_le_metric`
and `appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric`
(`RG/AppendixFKsharpEstimate.lean`), with the explicit constant
`θ = 1 + 3^d · B` for hole families whose components have at most `B` cubes.

**The mathematics.**  A connected hole-respecting polymer `X` with nonempty
active skeleton decomposes as `X = skeleton ∪ (absorbed holes)`
(`eq_union_absorbed`, Dimock eq. (149)).  Every absorbed hole touches the
skeleton (`absorbed_subset_touching`), the king-adjacency degree is `≤ 3^d`
(`cubeAdj_degree_le`), and pairwise-disjoint holes inject into
skeleton-adjacent pairs (`touchingHoles_card_le`), so
`#(absorbed) ≤ 3^d · #(skeleton)`.  With `#(hole) ≤ B` and
`#(skeleton) ≤ d_M + 1` (`skeleton_card_le_discreteModifiedMetric_add_one`):

`#X ≤ #skel + 3^d · #skel · B = (1 + 3^d B) · #skel ≤ (1 + 3^d B)(d_M(X)+1)`.

**METHOD DEVIATION (recorded, plan §3bis Trap C).**  The unconditional
compression `#X ≤ θ·(d_M(X)+1)` is FALSE: absorbed holes inflate `#X` at
fixed skeleton.  Dimock II pays the hole volume analytically through the P4
Gaussian large-field factor `e^{−c|H₀|}`; this brick pays with the uniform
finite-stage bound `|H₀| ≤ B` instead.  When P4 lands, the `hB` hypothesis
must be revisited against the source's Gaussian payment.  The difference is
deliberate and on record — do not silently strengthen either side.

**Non-vacuity guards.**
* `discreteModifiedMetric_add_one_eq_card_of_no_holes`: with no holes the
  compression is exact (`θ = 1`, equality) — the bound is tight in the bulk.
* `holeCompression_strict_witness`: a genuine-hole instance (d = 1, L = 3,
  one hole, `B = 1`) satisfying EVERY hypothesis of the master theorem, with
  `#X = 2 < 4 = (1 + 3·1)·(d_M+1)` — strict content, not an equality
  artifact, on the same concrete family as
  `discreteModifiedMetric_d_one_concrete_hole`.

**Source.**  Dimock II (arXiv:1212.5562) §3.1.2 eq. (149)–(151) geometry;
strategy/framing Lluis Eriksson.  All bricks stay on the source-facing
`omegaHolePolymerSystem` side (plan §3bis Trap B).

Oracle target: `[propext, Classical.choice, Quot.sound]`.  No sorry, no axioms.
-/

open Finset

namespace YangMills.RG

open SimpleGraph

/-- The active skeleton is disjoint from every hole component: skeleton cubes
lie in no hole by definition. -/
lemma skeleton_disjoint_hole {d L : ℕ} (HF : HoleFamily d L)
    (X : Finset (Cube d L)) {H₀ : Finset (Cube d L)} (hH₀ : H₀ ∈ HF.holes) :
    Disjoint (skeleton HF X) H₀ := by
  rw [Finset.disjoint_left]
  intro z hz hzH₀
  rw [skeleton, Finset.mem_filter] at hz
  exact hz.2 ⟨H₀, hH₀, hzH₀⟩

/-- A hole-respecting polymer is covered by its skeleton and its absorbed
holes, so its cardinality is at most the skeleton's plus the absorbed hole
volumes (Dimock eq. (149) decomposition, counted). -/
lemma card_le_skeleton_card_add_absorbed_sum {d L : ℕ} (HF : HoleFamily d L)
    (X : Finset (Cube d L)) (hresp : polymerWithHoles HF X) :
    X.card ≤ (skeleton HF X).card + ∑ H₀ ∈ absorbedHoles HF.holes X, H₀.card := by
  classical
  have hdecomp : X = skeleton HF X ∪ (absorbedHoles HF.holes X).biUnion id :=
    eq_union_absorbed HF.holes X hresp
  calc X.card
      = (skeleton HF X ∪ (absorbedHoles HF.holes X).biUnion id).card := by
        conv_lhs => rw [hdecomp]
    _ ≤ (skeleton HF X).card + ((absorbedHoles HF.holes X).biUnion id).card :=
        Finset.card_union_le _ _
    _ ≤ (skeleton HF X).card + ∑ H₀ ∈ absorbedHoles HF.holes X, (id H₀).card := by
        exact Nat.add_le_add_left (Finset.card_biUnion_le) _
    _ = (skeleton HF X).card + ∑ H₀ ∈ absorbedHoles HF.holes X, H₀.card := rfl

/-- **Bounded-hole cardinality compression (P3.5 brick B2, master form).**
For a hole family with pairwise-disjoint, mutually non-adjacent, nonempty
components of at most `B` cubes each, every connected hole-respecting polymer
`X` with nonempty active skeleton satisfies

`#X ≤ (1 + 3^d · B) · (d_M(X, mod holes) + 1)`.

This is the finite-stage substitute for Dimock's Gaussian hole-volume payment
(method deviation recorded in the module docstring and plan §3bis). -/
theorem polymerWithHoles_card_le_of_bounded_holes {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) {B : ℕ}
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hB : ∀ H₀ ∈ HF.holes, H₀.card ≤ B)
    (X : Finset (Cube d L)) (hconn : cubeConnected X)
    (hresp : polymerWithHoles HF X) (hskel : (skeleton HF X).Nonempty) :
    X.card ≤ (1 + 3 ^ d * B) * (discreteModifiedMetric HF X + 1) := by
  classical
  have habs_sub : absorbedHoles HF.holes X ⊆
      touchingHoles (cubeAdj d L) (skeleton HF X) HF.holes :=
    absorbed_subset_touching (cubeAdj d L) (skeleton HF X) HF.holes X hresp rfl
      hnoedges (fun H₀ hH₀ => skeleton_disjoint_hole HF X hH₀) hskel hholes_ne hconn
  have htouch : (touchingHoles (cubeAdj d L) (skeleton HF X) HF.holes).card
      ≤ 3 ^ d * (skeleton HF X).card :=
    touchingHoles_card_le (cubeAdj d L) (skeleton HF X) HF.holes (3 ^ d)
      (fun v => cubeAdj_degree_le d L v) hdisj
  have habs_card : (absorbedHoles HF.holes X).card ≤ 3 ^ d * (skeleton HF X).card :=
    le_trans (Finset.card_le_card habs_sub) htouch
  have hsum : ∑ H₀ ∈ absorbedHoles HF.holes X, H₀.card
      ≤ (absorbedHoles HF.holes X).card * B := by
    have h := Finset.sum_le_card_nsmul (absorbedHoles HF.holes X)
      (fun H₀ => H₀.card) B
      (fun H₀ hH₀ => hB H₀ (Finset.mem_of_mem_filter H₀ hH₀))
    simpa [smul_eq_mul] using h
  have hskel_card : (skeleton HF X).card ≤ discreteModifiedMetric HF X + 1 :=
    skeleton_card_le_discreteModifiedMetric_add_one HF X hconn
  calc X.card
      ≤ (skeleton HF X).card + ∑ H₀ ∈ absorbedHoles HF.holes X, H₀.card :=
        card_le_skeleton_card_add_absorbed_sum HF X hresp
    _ ≤ (skeleton HF X).card + (absorbedHoles HF.holes X).card * B :=
        Nat.add_le_add_left hsum _
    _ ≤ (skeleton HF X).card + (3 ^ d * (skeleton HF X).card) * B := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ habs_card) _
    _ = (1 + 3 ^ d * B) * (skeleton HF X).card := by ring
    _ ≤ (1 + 3 ^ d * B) * (discreteModifiedMetric HF X + 1) :=
        Nat.mul_le_mul_left _ hskel_card

/-- **The (O3) binder, discharged verbatim.**  On the source-facing
`omegaHolePolymerSystem` polymer type, the bounded-hole compression yields
exactly the carried hypothesis shape of
`appendixFHoleTargetFiber_card_le_metricSum_of_source_card_le_metric`,
`appendixFHoleMetricCoverWeight_mul_exp_card_le_shifted_of_source_card_le_metric`
and `appendixFHoleExpWeight_tilted_profile_le_of_card_le_metric`, with
`θ = 1 + 3^d · B`. -/
theorem omegaPolymerType_card_le_of_bounded_holes {d L : ℕ} [NeZero L]
    (HF : HoleFamily d L) (z : Finset (Cube d L) → ℂ) {B : ℕ}
    (hdisj : ∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes, H₁ ≠ H₂ → Disjoint H₁ H₂)
    (hnoedges : noEdgesBetweenHoles (cubeAdj d L) HF.holes)
    (hholes_ne : ∀ H₀ ∈ HF.holes, H₀.Nonempty)
    (hB : ∀ H₀ ∈ HF.holes, H₀.card ≤ B)
    (X : OmegaPolymerType HF z) :
    (X.val.card : ℝ) ≤ (1 + (3 ^ d : ℝ) * (B : ℝ)) *
      ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ) := by
  have h := polymerWithHoles_card_le_of_bounded_holes HF hdisj hnoedges hholes_ne hB
    X.val X.property.2.1 X.property.2.2.1 X.property.2.2.2
  calc (X.val.card : ℝ)
      ≤ (((1 + 3 ^ d * B) * (discreteModifiedMetric HF X.val + 1) : ℕ) : ℝ) := by
        exact_mod_cast h
    _ = (1 + (3 ^ d : ℝ) * (B : ℝ)) *
        ((discreteModifiedMetric HF X.val + 1 : ℕ) : ℝ) := by
        push_cast
        ring

/-- **Non-vacuity guard (bulk exactness).**  With no holes the compression is
an equality at `θ = 1`: for nonempty connected `X`,
`d_M(X) + 1 = #X` exactly (upper half `discreteModifiedMetric_le_bulkTreeLength`,
lower half `skeleton_card_le_discreteModifiedMetric_add_one` with
`skeleton = X`).  The master bound therefore has NO slack in the hole-free
sector — it is not an artifact of a loose skeleton estimate. -/
theorem discreteModifiedMetric_add_one_eq_card_of_no_holes {d L : ℕ}
    (HF : HoleFamily d L) (hHF : HF.holes = ∅)
    (X : Finset (Cube d L)) (hne : X.Nonempty) (hconn : cubeConnected X) :
    discreteModifiedMetric HF X + 1 = X.card := by
  have hskel_eq : skeleton HF X = X := by
    rw [skeleton]
    refine Finset.filter_true_of_mem (fun z _ => ?_)
    rintro ⟨H₀, hH₀, -⟩
    rw [hHF] at hH₀
    exact absurd hH₀ (Finset.notMem_empty _)
  have h1 : (skeleton HF X).card ≤ discreteModifiedMetric HF X + 1 :=
    skeleton_card_le_discreteModifiedMetric_add_one HF X hconn
  have h2 : discreteModifiedMetric HF X ≤ X.card - 1 :=
    discreteModifiedMetric_le_bulkTreeLength HF X hconn
  have hpos : 1 ≤ X.card := Finset.card_pos.mpr hne
  rw [hskel_eq] at h1
  omega

namespace HoleCompressionWitness

/-- Witness cube `0` on the `d = 1`, `L = 3` torus. -/
def s₀ : Cube 1 3 := fun _ => 0

/-- Witness cube `1` on the `d = 1`, `L = 3` torus. -/
def s₁ : Cube 1 3 := fun _ => 1

lemma s₀_ne_s₁ : s₀ ≠ s₁ := by
  intro h
  have h0 := congrFun h 0
  rw [s₀, s₁] at h0
  exact absurd h0 (by decide)

lemma adj : (cubeAdj 1 3).Adj s₀ s₁ := by
  refine ⟨s₀_ne_s₁, fun i => ?_⟩
  right; left
  rw [s₀, s₁]
  decide

end HoleCompressionWitness

/-- **Non-vacuity guard (genuine-hole strict witness).**  There is a hole
family with a NONEMPTY hole set and a polymer satisfying EVERY hypothesis of
`polymerWithHoles_card_le_of_bounded_holes`, on which the compression bound
holds STRICTLY (`2 < 4`): the theorem's hypothesis set is jointly satisfiable
with genuine holes and its conclusion is not an equality artifact.  Same
concrete family as `discreteModifiedMetric_d_one_concrete_hole`. -/
theorem holeCompression_strict_witness :
    ∃ (HF : HoleFamily 1 3) (X : Finset (Cube 1 3)) (B : ℕ),
      (∀ H₁ ∈ HF.holes, ∀ H₂ ∈ HF.holes, H₁ ≠ H₂ → Disjoint H₁ H₂) ∧
      noEdgesBetweenHoles (cubeAdj 1 3) HF.holes ∧
      (∀ H₀ ∈ HF.holes, H₀.Nonempty) ∧
      (∀ H₀ ∈ HF.holes, H₀.card ≤ B) ∧
      cubeConnected X ∧ polymerWithHoles HF X ∧ (skeleton HF X).Nonempty ∧
      HF.holes.Nonempty ∧ X.card = 2 ∧ discreteModifiedMetric HF X = 0 ∧
      X.card < (1 + 3 ^ 1 * B) * (discreteModifiedMetric HF X + 1) := by
  classical
  open HoleCompressionWitness in
  refine ⟨⟨{{s₀}}⟩, {s₀, s₁}, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pairwise disjointness: a single hole, `H₁ = H₂` always
    intro H₁ h₁ H₂ h₂ hne
    have e₁ : H₁ = {s₀} := Finset.mem_singleton.mp h₁
    have e₂ : H₂ = {s₀} := Finset.mem_singleton.mp h₂
    exact absurd (e₁.trans e₂.symm) hne
  · -- no edges between holes: a single hole, vacuous
    intro H₁ h₁ H₂ h₂ hne
    have e₁ : H₁ = {s₀} := Finset.mem_singleton.mp h₁
    have e₂ : H₂ = {s₀} := Finset.mem_singleton.mp h₂
    exact absurd (e₁.trans e₂.symm) hne
  · -- holes nonempty
    intro H₀ hH₀
    rw [Finset.mem_singleton.mp hH₀]
    exact ⟨s₀, Finset.mem_singleton_self _⟩
  · -- hole volume bound `B = 1`
    intro H₀ hH₀
    rw [Finset.mem_singleton.mp hH₀]
    exact le_of_eq (Finset.card_singleton _)
  · -- connectivity of `{s₀, s₁}` via the explicit king-move edge
    intro x hx y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hmem : ∀ v, v = s₀ ∨ v = s₁ → v ∈ ({s₀, s₁} : Finset (Cube 1 3)) := by
      rintro v (rfl | rfl)
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨SimpleGraph.Walk.nil, by
        intro v hv
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
        exact hmem v (Or.inl hv)⟩
    · refine ⟨SimpleGraph.Walk.cons adj SimpleGraph.Walk.nil, ?_⟩
      intro v hv
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hmem s₀ (Or.inl rfl)
      · exact hmem s₁ (Or.inr rfl)
    · refine ⟨SimpleGraph.Walk.cons adj.symm SimpleGraph.Walk.nil, ?_⟩
      intro v hv
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hmem s₁ (Or.inr rfl)
      · exact hmem s₀ (Or.inl rfl)
    · exact ⟨SimpleGraph.Walk.nil, by
        intro v hv
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
        exact hmem v (Or.inr hv)⟩
  · -- the single hole is absorbed: `{s₀} ⊆ {s₀, s₁}`
    intro H₀ hH₀
    rw [Finset.mem_singleton.mp hH₀]
    left
    intro z hz
    rw [Finset.mem_singleton.mp hz]
    exact Finset.mem_insert_self _ _
  · -- nonempty skeleton: `s₁` is active
    refine ⟨s₁, ?_⟩
    rw [skeleton, Finset.mem_filter]
    constructor
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rintro ⟨H₀, hH₀, hs⟩
      rw [Finset.mem_singleton.mp hH₀] at hs
      exact s₀_ne_s₁ (Finset.mem_singleton.mp hs).symm
  · -- the hole set is genuinely nonempty
    exact ⟨{s₀}, Finset.mem_singleton_self _⟩
  · -- `#X = 2`
    have hnm : s₀ ∉ ({s₁} : Finset (Cube 1 3)) := by
      rw [Finset.mem_singleton]
      exact s₀_ne_s₁
    rw [Finset.card_insert_of_notMem hnm, Finset.card_singleton]
  · -- `d_M = 0` on this instance (existing concrete evaluation)
    simpa using discreteModifiedMetric_d_one_concrete_hole s₀ s₁ rfl rfl
  · -- strict: `2 < (1 + 3·1)·(d_M+1) = 4`
    have hdm : discreteModifiedMetric (⟨{{s₀}}⟩ : HoleFamily 1 3)
        ({s₀, s₁} : Finset (Cube 1 3)) = 0 := by
      simpa using discreteModifiedMetric_d_one_concrete_hole s₀ s₁ rfl rfl
    have hnm : s₀ ∉ ({s₁} : Finset (Cube 1 3)) := by
      rw [Finset.mem_singleton]
      exact s₀_ne_s₁
    have hcard : ({s₀, s₁} : Finset (Cube 1 3)).card = 2 := by
      rw [Finset.card_insert_of_notMem hnm, Finset.card_singleton]
    rw [hdm, hcard]
    norm_num

end YangMills.RG
