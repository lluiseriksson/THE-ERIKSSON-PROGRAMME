import YangMills.RG.BalabanCMP99GeneralizedRandomWalk

/-!
# Uniform summability for source-faithful CMP99 generalized walks

This module turns the structural walk layer into the exact radial majorant used
by the countable CMP116 weakening series.  The head domain `X₀` is fixed.  A
finite successor family enumerates the possible labelled continuations from
each current domain, and its cardinal is bounded uniformly by `K`.

If every source domain activates at most `B` weakening cubes and the physical
ordered term satisfies the explicit CMP99-type estimate

`‖term ω‖ ≤ A * ρ ^ |ω|`,

then

`K * ρ * R ^ B < 1`

produces summability of

`R ^ card(active ω) * ‖term ω‖`.

The result is uniform in the total number of localization domains: it counts
only the bounded branching of admissible continuations.  The hypothesis on the
ordered term is deliberately visible.  Its source-specific proof from the
operators `R₀(X₀), R_α(X)` and the kernel estimate (3.108) remains the next
analytic producer.
-/

open scoped BigOperators

namespace YangMills.RG

universe u v w z

variable {Label : Type u} {Domain : Type v} {Cube : Type w} {E : Type z}
variable [DecidableEq Label] [DecidableEq Domain] [DecidableEq Cube]

namespace CMP99AnchoredWalk

variable {successors : Domain → Finset (CMP99WalkStep Label Domain)}
variable {X0 : Domain}

/-- The active weakening carrier of an anchored source walk. -/
def active (domainActive : Domain → Finset Cube)
    (walk : CMP99AnchoredWalk successors X0) : Finset Cube :=
  walk.toGeneralizedWalk.active domainActive

/-- The literal ordered operator term of an anchored source walk. -/
def term [Monoid E]
    (R0 : Domain → E) (Rop : Label → Domain → E)
    (walk : CMP99AnchoredWalk successors X0) : E :=
  walk.toGeneralizedWalk.term R0 Rop

/-- The source active-carrier estimate specialized to a generated walk of
length `n`. -/
theorem card_active_le_mul_length_add_one
    (domainActive : Domain → Finset Cube) (B : ℕ)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (walk : CMP99AnchoredWalk successors X0) :
    (walk.active domainActive).card ≤ B * (walk.1 + 1) := by
  simpa [active, CMP99AnchoredWalk.toGeneralizedWalk_length] using
    walk.toGeneralizedWalk.card_active_le_mul_length_add_one domainActive B hB

end CMP99AnchoredWalk

section Majorant

variable [NormedRing E]

/-- Bounded branching, bounded active support, and the visible physical term
estimate produce the load-bearing radial majorant for the countable walk
series.  No cardinal of the full domain alphabet occurs. -/
theorem summable_cmp99AnchoredWalk_radialMajorant
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (X0 : Domain) (domainActive : Domain → Finset Cube)
    (R0 : Domain → E) (Rop : Label → Domain → E)
    (K B : ℕ) (A ρ R : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (K : ℝ) * ρ * R ^ B < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk successors X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1) :
    Summable fun walk : CMP99AnchoredWalk successors X0 =>
      R ^ (walk.active domainActive).card * ‖walk.term R0 Rop‖ := by
  let q : ℝ := (K : ℝ) * ρ * R ^ B
  have hq_nonneg : 0 ≤ q :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg K) hρ) (pow_nonneg (by linarith) B)
  have hgeom : Summable fun n : ℕ => A * R ^ B * q ^ n := by
    have hs : Summable fun n : ℕ => q ^ n :=
      summable_geometric_of_norm_lt_one (by
        rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
        exact hsmall)
    exact hs.mul_left (A * R ^ B)
  rw [summable_sigma_of_nonneg (fun walk =>
    mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _))]
  constructor
  · intro n
    exact Summable.of_finite
  · refine Summable.of_nonneg_of_le
      (fun n => tsum_nonneg fun _ =>
        mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)) ?_ hgeom
    intro n
    rw [tsum_fintype]
    calc
        ∑ walk : ↥(cmp99AdmissibleTails successors X0 n),
            R ^ (CMP99AnchoredWalk.active domainActive
              (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)).card *
              ‖CMP99AnchoredWalk.term R0 Rop
                (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)‖ ≤
            ∑ _walk : ↥(cmp99AdmissibleTails successors X0 n),
              R ^ (B * (n + 1)) * (A * ρ ^ n) := by
          apply Finset.sum_le_sum
          intro walk _hwalk
          exact mul_le_mul
            (pow_le_pow_right₀ hR
              (CMP99AnchoredWalk.card_active_le_mul_length_add_one
                domainActive B hB
                (⟨n, walk⟩ : CMP99AnchoredWalk successors X0)))
            (hterm ⟨n, walk⟩) (norm_nonneg _)
            (pow_nonneg (by linarith) _)
        _ = ((cmp99AdmissibleTails successors X0 n).card : ℝ) *
              (R ^ (B * (n + 1)) * (A * ρ ^ n)) := by simp
        _ ≤ ((K ^ n : ℕ) : ℝ) *
              (R ^ (B * (n + 1)) * (A * ρ ^ n)) := by
          gcongr
          exact_mod_cast card_cmp99AdmissibleTails_le_pow successors K hK n X0
        _ = A * R ^ B * q ^ n := by
          dsimp [q]
          push_cast
          rw [pow_mul, pow_succ]
          ring

end Majorant

section SeriesConsequences

variable [NormedRing E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The source-faithful walk estimate directly instantiates the countable
CMP116 weakened series throughout its polydisc. -/
theorem summable_cmp116WeakenedCMP99WalkSeries
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (X0 : Domain) (domainActive : Domain → Finset Cube)
    (R0 : Domain → E) (Rop : Label → Domain → E)
    (s : Cube → ℝ) (K B : ℕ) (A ρ R : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (K : ℝ) * ρ * R ^ B < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk successors X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    Summable fun walk : CMP99AnchoredWalk successors X0 =>
      cmp116WeakeningMonomial (walk.active domainActive) s •
        walk.term R0 Rop := by
  exact summable_cmp116WeakenedRandomWalkSeries
    (CMP99AnchoredWalk.active domainActive) (CMP99AnchoredWalk.term R0 Rop)
    s R (by linarith) hs
    (summable_cmp99AnchoredWalk_radialMajorant
      successors X0 domainActive R0 Rop K B A ρ R
      hK hB hA hρ hR hsmall hterm)

/-- The same physical inputs discharge the infinite one-coordinate FTC step. -/
theorem cmp116WeakenedCMP99WalkSeries_ftcStep
    (successors : Domain → Finset (CMP99WalkStep Label Domain))
    (X0 : Domain) (domainActive : Domain → Finset Cube)
    (R0 : Domain → E) (Rop : Label → Domain → E)
    (s : Cube → ℝ) (d : Cube) (K B : ℕ) (A ρ R : ℝ)
    (hK : ∀ X, (successors X).card ≤ K)
    (hB : ∀ X, (domainActive X).card ≤ B)
    (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hsmall : (K : ℝ) * ρ * R ^ B < 1)
    (hterm : ∀ walk : CMP99AnchoredWalk successors X0,
      ‖walk.term R0 Rop‖ ≤ A * ρ ^ walk.1)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    cmp116WeakenedRandomWalkSeries
        (fun walk : CMP99AnchoredWalk successors X0 => walk.active domainActive)
        (fun walk : CMP99AnchoredWalk successors X0 => walk.term R0 Rop)
        (Function.update s d 0) +
      ∫ _t in (0 : ℝ)..1,
        cmp116WeakenedRandomWalkSeriesDerivative
          (fun walk : CMP99AnchoredWalk successors X0 => walk.active domainActive)
          (fun walk : CMP99AnchoredWalk successors X0 => walk.term R0 Rop) s d =
      cmp116WeakenedRandomWalkSeries
        (fun walk : CMP99AnchoredWalk successors X0 => walk.active domainActive)
        (fun walk : CMP99AnchoredWalk successors X0 => walk.term R0 Rop)
        (Function.update s d 1) := by
  exact cmp116WeakenedRandomWalkSeries_ftcStep
    (fun walk : CMP99AnchoredWalk successors X0 => walk.active domainActive)
    (fun walk : CMP99AnchoredWalk successors X0 => walk.term R0 Rop)
    s d R hR hs
    (summable_cmp99AnchoredWalk_radialMajorant
      successors X0 domainActive R0 Rop K B A ρ R
      hK hB hA hρ hR hsmall hterm)

end SeriesConsequences

end YangMills.RG
