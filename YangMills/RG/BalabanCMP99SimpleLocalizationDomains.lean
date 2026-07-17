import YangMills.RG.AnimalTour
import YangMills.RG.BalabanCMP99GeneralizedRandomWalkSummability
import YangMills.RG.ModifiedMetric

/-!
# CMP99 simple localization domains and uniform successor branching

Section C of CMP99 describes a simple localization domain as a connected,
finite family of cubes, with a uniform bound on the number of cubes in the
family.  Consecutive generalized-walk domains have nonempty intersection.

This file turns those source statements into a volume-uniform branching
producer.  For a graph of maximum degree `Δ`, a simple domain of size at most
`S` that intersects a fixed domain `X` contains a root cube of `X`.  The
existing lattice-animal theorem counts the connected size-`n` domains through
that root by `Δ ^ (2 * (n - 1))`.  Summing over roots and `n ≤ S` gives the
explicit, deliberately conservative bound

`S * (S + 1) * Δ ^ (2 * S)`.

After adjoining a finite factor label type, the labelled successor branching
is bounded by

`card Label * S * (S + 1) * Δ ^ (2 * S)`.

This is independent of the number of cubes in the periodic volume.  It does
not yet identify the particular finite list of operator factor labels in CMP99
or prove the analytic estimate (3.108).
-/

open Finset SimpleGraph

namespace YangMills.RG

universe u v

variable {V : Type u} {Label : Type v}

/-- A CMP99 simple localization domain: a nonempty connected family of at
most `S` localization cubes. -/
structure CMP99SimpleLocalizationDomain
    [DecidableEq V] (G : SimpleGraph V) (S : ℕ) where
  blocks : Finset V
  nonempty : blocks.Nonempty
  connected : walkConnected G blocks
  card_le : blocks.card ≤ S

noncomputable instance cmp99SimpleLocalizationDomainDecidableEq
    [DecidableEq V] (G : SimpleGraph V) (S : ℕ) :
    DecidableEq (CMP99SimpleLocalizationDomain G S) :=
  Classical.decEq _

namespace CMP99SimpleLocalizationDomain

variable [DecidableEq V] {G : SimpleGraph V} {S : ℕ}

/-- Two source domains meet when their cube carriers have nonempty
intersection. -/
def Meets (X Y : CMP99SimpleLocalizationDomain G S) : Prop :=
  ¬Disjoint X.blocks Y.blocks

noncomputable instance meetsDecidable
    (X Y : CMP99SimpleLocalizationDomain G S) :
    Decidable (Meets X Y) := Classical.propDecidable _

end CMP99SimpleLocalizationDomain

section RootedFamilies

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The literal finite family counted by the rooted lattice-animal theorem. -/
noncomputable def cmp99RootedConnectedFamilies (root : V) (n : ℕ) :
    Finset (Finset V) := by
  classical
  exact Finset.univ.filter fun blocks =>
    root ∈ blocks ∧ blocks.card = n ∧
      ∀ x ∈ blocks, ∃ walk : G.Walk root x, IsSWalk blocks walk

/-- The existing lattice-animal count in the finite-family form consumed by
the successor estimate below. -/
theorem card_cmp99RootedConnectedFamilies_le
    (root : V) (n Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) :
    (cmp99RootedConnectedFamilies (G := G) root n).card ≤
      Δ ^ (2 * (n - 1)) := by
  classical
  apply animal_card_le (G := G) _ hΔ
  intro blocks hblocks
  simpa [cmp99RootedConnectedFamilies] using
    (Finset.mem_filter.mp hblocks).2

end RootedFamilies

section SimpleDomainCount

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable instance (S : ℕ) :
    Fintype (CMP99SimpleLocalizationDomain G S) := by
  classical
  exact Fintype.ofInjective
    (fun X : CMP99SimpleLocalizationDomain G S => X.blocks)
    (by
      intro X Y hxy
      cases X
      cases Y
      cases hxy
      rfl)

/-- All simple domains meeting `X`. -/
noncomputable def cmp99MeetingSimpleDomains
    (S : ℕ) (X : CMP99SimpleLocalizationDomain G S) :
    Finset (CMP99SimpleLocalizationDomain G S) :=
  Finset.univ.filter fun Y => X.Meets Y

private theorem blocks_injective (S : ℕ) :
    Function.Injective
      (fun X : CMP99SimpleLocalizationDomain G S => X.blocks) := by
  intro X Y hxy
  cases X
  cases Y
  cases hxy
  rfl

/-- Every simple domain meeting `X` lies in one of the rooted, size-graded
animal families indexed by a root cube of `X`. -/
theorem image_cmp99MeetingSimpleDomains_subset_rootedUnion
    (S : ℕ) (X : CMP99SimpleLocalizationDomain G S) :
    (cmp99MeetingSimpleDomains G S X).image
        (fun Y => Y.blocks) ⊆
      X.blocks.biUnion fun root =>
        (Finset.range (S + 1)).biUnion fun n =>
          cmp99RootedConnectedFamilies (G := G) root n := by
  classical
  intro blocks hblocks
  simp only [Finset.mem_image] at hblocks
  obtain ⟨Y, hYmeet, rfl⟩ := hblocks
  have hmeet : X.Meets Y := (Finset.mem_filter.mp hYmeet).2
  rw [CMP99SimpleLocalizationDomain.Meets, Finset.not_disjoint_iff] at hmeet
  obtain ⟨root, hrootX, hrootY⟩ := hmeet
  rw [Finset.mem_biUnion]
  refine ⟨root, hrootX, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨Y.blocks.card, Finset.mem_range.mpr (Nat.lt_succ_of_le Y.card_le), ?_⟩
  simp only [cmp99RootedConnectedFamilies, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine ⟨hrootY, ?_⟩
  intro y hy
  exact Y.connected root hrootY y hy

/-- Volume-uniform count of simple domains meeting a fixed simple domain. -/
theorem card_cmp99MeetingSimpleDomains_le
    (S Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X : CMP99SimpleLocalizationDomain G S) :
    (cmp99MeetingSimpleDomains G S X).card ≤
      S * (S + 1) * Δ ^ (2 * S) := by
  calc
    (cmp99MeetingSimpleDomains G S X).card =
        ((cmp99MeetingSimpleDomains G S X).image
          (fun Y => Y.blocks)).card := by
      symm
      exact Finset.card_image_of_injective _ (blocks_injective G S)
    _ ≤ (X.blocks.biUnion fun root =>
          (Finset.range (S + 1)).biUnion fun n =>
            cmp99RootedConnectedFamilies (G := G) root n).card :=
      Finset.card_le_card
        (image_cmp99MeetingSimpleDomains_subset_rootedUnion G S X)
    _ ≤ ∑ root ∈ X.blocks,
          ((Finset.range (S + 1)).biUnion fun n =>
            cmp99RootedConnectedFamilies (G := G) root n).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _root ∈ X.blocks,
          ∑ n ∈ Finset.range (S + 1),
            (cmp99RootedConnectedFamilies (G := G) _root n).card := by
      gcongr with root hroot
      exact Finset.card_biUnion_le
    _ ≤ ∑ _root ∈ X.blocks,
          ∑ _n ∈ Finset.range (S + 1), Δ ^ (2 * S) := by
      gcongr with root hroot n hn
      have hnS : n ≤ S := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      exact (card_cmp99RootedConnectedFamilies_le G root n Δ hΔ).trans
        (Nat.pow_le_pow_right hΔ1 (by omega))
    _ = X.blocks.card * (S + 1) * Δ ^ (2 * S) := by simp [Nat.mul_assoc]
    _ ≤ S * (S + 1) * Δ ^ (2 * S) := by
      exact Nat.mul_le_mul_right (Δ ^ (2 * S))
        (Nat.mul_le_mul_right (S + 1) X.card_le)

/-- The complete overcounting successor family: every factor label paired with
every simple domain meeting the current domain.  Later source-specific scale
compatibility may filter this family further without increasing its cardinal. -/
noncomputable def cmp99SimpleDomainSuccessors
    [Fintype Label] [DecidableEq Label]
    (S : ℕ) (X : CMP99SimpleLocalizationDomain G S) :
    Finset (CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S)) :=
  ((Finset.univ : Finset Label).product (cmp99MeetingSimpleDomains G S X)).image
    fun pair => ⟨pair.1, pair.2⟩

/-- Explicit volume-uniform labelled branching constant for the source walk. -/
theorem card_cmp99SimpleDomainSuccessors_le
    [Fintype Label] [DecidableEq Label]
    (S Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X : CMP99SimpleLocalizationDomain G S) :
    (cmp99SimpleDomainSuccessors (Label := Label) G S X).card ≤
      Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S)) := by
  rw [cmp99SimpleDomainSuccessors, Finset.card_image_of_injective]
  · simpa using Nat.mul_le_mul_left (Fintype.card Label)
      (card_cmp99MeetingSimpleDomains_le G S Δ hΔ hΔ1 X)
  · intro a b hab
    cases a
    cases b
    cases hab
    rfl

/-- Every generated successor meets its source domain, so the abstract
admissible-tail generator produces literal CMP99 overlap chains. -/
theorem mem_cmp99SimpleDomainSuccessors_meets
    [Fintype Label] [DecidableEq Label]
    (S : ℕ) (X : CMP99SimpleLocalizationDomain G S)
    (step : CMP99WalkStep Label (CMP99SimpleLocalizationDomain G S))
    (hstep : step ∈ cmp99SimpleDomainSuccessors (Label := Label) G S X) :
    X.Meets step.domain := by
  simp only [cmp99SimpleDomainSuccessors, Finset.mem_image] at hstep
  obtain ⟨pair, hpair, rfl⟩ := hstep
  exact (Finset.mem_product.mp hpair).2 |> Finset.mem_filter.mp |>.2

end SimpleDomainCount

section SummabilityProducer

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype Label] [DecidableEq Label]
variable {Cube : Type*} [DecidableEq Cube]
variable {E : Type*} [NormedRing E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The explicit uniform branching constant produced by the simple-domain
geometry and the lattice-animal count. -/
def cmp99SimpleDomainBranchingBound (S Δ : ℕ) : ℕ :=
  Fintype.card Label * (S * (S + 1) * Δ ^ (2 * S))

/-- Source-simple-domain specialization of the radial majorant theorem.  The
abstract successor family and its cardinal bound have disappeared; the only
remaining analytic input is the printed whole-term decay (3.108), while
`domainActive` still exposes the separate CMP116 thickening geometry. -/
theorem summable_cmp99SimpleDomainWalk_radialMajorant
    (S Δ B : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X0 : CMP99SimpleLocalizationDomain G S)
    (domainActive : CMP99SimpleLocalizationDomain G S → Finset Cube)
    (R0 : CMP99SimpleLocalizationDomain G S → E)
    (Rop : Label → CMP99SimpleLocalizationDomain G S → E)
    (A ρ R : ℝ)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (cmp99SimpleDomainBranchingBound (Label := Label) S Δ : ℝ) *
      ρ * R ^ B < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0 =>
      R ^ (walk.active domainActive).card * ‖walk.term R0 Rop‖ := by
  classical
  exact summable_cmp99AnchoredWalk_radialMajorant
    (cmp99SimpleDomainSuccessors (Label := Label) G S) X0
    domainActive R0 Rop
    (cmp99SimpleDomainBranchingBound (Label := Label) S Δ) B A ρ R
    (fun X => card_cmp99SimpleDomainSuccessors_le G S Δ hΔ hΔ1 X)
    hB hA hρ hR hsmall hterm

/-- The same source producers instantiate the actual countable weakened series
at every point of the CMP116 polydisc. -/
theorem summable_cmp116WeakenedCMP99SimpleDomainWalkSeries
    (S Δ B : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X0 : CMP99SimpleLocalizationDomain G S)
    (domainActive : CMP99SimpleLocalizationDomain G S → Finset Cube)
    (R0 : CMP99SimpleLocalizationDomain G S → E)
    (Rop : Label → CMP99SimpleLocalizationDomain G S → E)
    (s : Cube → ℝ) (A ρ R : ℝ)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (cmp99SimpleDomainBranchingBound (Label := Label) S Δ : ℝ) *
      ρ * R ^ B < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0 =>
      cmp116WeakeningMonomial (walk.active domainActive) s •
        walk.term R0 Rop := by
  classical
  exact summable_cmp116WeakenedCMP99WalkSeries
    (cmp99SimpleDomainSuccessors (Label := Label) G S) X0
    domainActive R0 Rop s
    (cmp99SimpleDomainBranchingBound (Label := Label) S Δ) B A ρ R
    (fun X => card_cmp99SimpleDomainSuccessors_le G S Δ hΔ hΔ1 X)
    hB hA hρ hR hsmall hterm hs

end SummabilityProducer

end YangMills.RG
