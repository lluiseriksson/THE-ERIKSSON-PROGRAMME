import YangMills.RG.BalabanCMP99SimpleLocalizationDomains

/-!
# CMP99/CMP116 active weakening carriers for simple domains

CMP116 weakens a generalized-walk term by every regular-partition cube which
intersects its localization domains.  The preceding summability theorem kept
the resulting per-domain cardinal budget `B` explicit.  This file constructs
that carrier from a block-level incidence map.

If every localization block meets at most `T` weakening cubes and a simple
domain contains at most `S` blocks, its active carrier has cardinal at most
`T * S`.  Consequently the radial smallness condition becomes the explicit

`K * rho * R ^ (T * S) < 1`.

For the same-partition specialization, in which a localization block activates
itself, `T` disappears and the exponent is exactly `S`.

Honest scope: the source-specific incidence between the multiscale CMP99
localization blocks and the CMP116 weakening partition is not identified here.
The same-partition specialization is exact only where those two partitions
coincide.
-/

open Finset SimpleGraph

namespace YangMills.RG

universe u v w z

variable {V : Type u} {Label : Type v} {Cube : Type w} {E : Type z}

section ActiveCarrier

variable [DecidableEq V] [DecidableEq Cube]
variable {G : SimpleGraph V} {S : ℕ}

/-- Weakening cubes meeting at least one block of a simple localization
domain. -/
def cmp99SimpleDomainActive
    (blockActive : V → Finset Cube)
    (X : CMP99SimpleLocalizationDomain G S) : Finset Cube :=
  X.blocks.biUnion blockActive

/-- A per-block incidence budget `T` gives the explicit per-domain budget
`T * S`. -/
theorem card_cmp99SimpleDomainActive_le
    (blockActive : V → Finset Cube) (T : ℕ)
    (hT : ∀ v, (blockActive v).card ≤ T)
    (X : CMP99SimpleLocalizationDomain G S) :
    (cmp99SimpleDomainActive blockActive X).card ≤ T * S := by
  calc
    (cmp99SimpleDomainActive blockActive X).card ≤
        ∑ v ∈ X.blocks, (blockActive v).card := by
      simpa [cmp99SimpleDomainActive] using
        (Finset.card_biUnion_le (s := X.blocks) (t := blockActive))
    _ ≤ ∑ _v ∈ X.blocks, T :=
      Finset.sum_le_sum fun v _hv => hT v
    _ = X.blocks.card * T := by simp
    _ ≤ S * T := Nat.mul_le_mul_right T X.card_le
    _ = T * S := Nat.mul_comm _ _

/-- Same-partition carrier: the weakening cubes are literally the domain
blocks. -/
def cmp99SamePartitionActive
    (X : CMP99SimpleLocalizationDomain G S) : Finset V :=
  X.blocks

theorem card_cmp99SamePartitionActive_le
    (X : CMP99SimpleLocalizationDomain G S) :
    (cmp99SamePartitionActive X).card ≤ S :=
  X.card_le

end ActiveCarrier

section Summability

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype Label] [DecidableEq Label]
variable [DecidableEq Cube]
variable [NormedRing E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Radial majorant with the whole-domain `hB` binder replaced by a local
block-incidence estimate. -/
theorem summable_cmp99SimpleDomainWalk_radialMajorant_of_blockActive
    (S Δ T : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X0 : CMP99SimpleLocalizationDomain G S)
    (blockActive : V → Finset Cube)
    (R0 : CMP99SimpleLocalizationDomain G S → E)
    (Rop : Label → CMP99SimpleLocalizationDomain G S → E)
    (A ρ R : ℝ)
    (hT : ∀ v, (blockActive v).card ≤ T)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (cmp99SimpleDomainBranchingBound (Label := Label) S Δ : ℝ) *
      ρ * R ^ (T * S) < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0 =>
      R ^ (walk.active (cmp99SimpleDomainActive blockActive)).card *
        ‖walk.term R0 Rop‖ := by
  exact summable_cmp99SimpleDomainWalk_radialMajorant G S Δ (T * S)
    hΔ hΔ1 X0 (cmp99SimpleDomainActive blockActive) R0 Rop A ρ R
    (fun X => card_cmp99SimpleDomainActive_le blockActive T hT X)
    hA hρ hR hsmall hterm

/-- Countable weakened-series specialization with the explicit local
incidence budget `T * S`. -/
theorem summable_cmp116WeakenedCMP99SimpleDomainWalkSeries_of_blockActive
    (S Δ T : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X0 : CMP99SimpleLocalizationDomain G S)
    (blockActive : V → Finset Cube)
    (R0 : CMP99SimpleLocalizationDomain G S → E)
    (Rop : Label → CMP99SimpleLocalizationDomain G S → E)
    (s : Cube → ℝ) (A ρ R : ℝ)
    (hT : ∀ v, (blockActive v).card ≤ T)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (cmp99SimpleDomainBranchingBound (Label := Label) S Δ : ℝ) *
      ρ * R ^ (T * S) < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0 =>
      cmp116WeakeningMonomial
          (walk.active (cmp99SimpleDomainActive blockActive)) s •
        walk.term R0 Rop := by
  exact summable_cmp116WeakenedCMP99SimpleDomainWalkSeries G S Δ (T * S)
    hΔ hΔ1 X0 (cmp99SimpleDomainActive blockActive) R0 Rop s A ρ R
    (fun X => card_cmp99SimpleDomainActive_le blockActive T hT X)
    hA hρ hR hsmall hterm hs

/-- Same-partition radial majorant.  The active-cardinality exponent is the
source domain-size cutoff `S`, with no geometric binder remaining. -/
theorem summable_cmp99SamePartitionWalk_radialMajorant
    (S Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X0 : CMP99SimpleLocalizationDomain G S)
    (R0 : CMP99SimpleLocalizationDomain G S → E)
    (Rop : Label → CMP99SimpleLocalizationDomain G S → E)
    (A ρ R : ℝ)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (cmp99SimpleDomainBranchingBound (Label := Label) S Δ : ℝ) *
      ρ * R ^ S < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0 =>
      R ^ (walk.active cmp99SamePartitionActive).card *
        ‖walk.term R0 Rop‖ := by
  exact summable_cmp99SimpleDomainWalk_radialMajorant G S Δ S
    hΔ hΔ1 X0 cmp99SamePartitionActive R0 Rop A ρ R
    card_cmp99SamePartitionActive_le hA hρ hR hsmall hterm

/-- Same-partition countable weakened series. -/
theorem summable_cmp116WeakenedCMP99SamePartitionWalkSeries
    (S Δ : ℕ) (hΔ : ∀ x, G.degree x ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (X0 : CMP99SimpleLocalizationDomain G S)
    (R0 : CMP99SimpleLocalizationDomain G S → E)
    (Rop : Label → CMP99SimpleLocalizationDomain G S → E)
    (s : V → ℝ) (A ρ R : ℝ)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (cmp99SimpleDomainBranchingBound (Label := Label) S Δ : ℝ) *
      ρ * R ^ S < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    Summable fun walk : CMP99AnchoredWalk
        (cmp99SimpleDomainSuccessors (Label := Label) G S) X0 =>
      cmp116WeakeningMonomial (walk.active cmp99SamePartitionActive) s •
        walk.term R0 Rop := by
  exact summable_cmp116WeakenedCMP99SimpleDomainWalkSeries G S Δ S
    hΔ hΔ1 X0 cmp99SamePartitionActive R0 Rop s A ρ R
    card_cmp99SamePartitionActive_le hA hρ hR hsmall hterm hs

end Summability

end YangMills.RG
