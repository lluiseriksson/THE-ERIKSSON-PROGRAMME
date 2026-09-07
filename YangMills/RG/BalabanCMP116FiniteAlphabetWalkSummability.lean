import YangMills.RG.BalabanCMP116WeakenedRandomWalkSeries
import Mathlib.Data.List.OfFn

/-!
# A finite-alphabet summability producer for CMP116 walk series

The previous module identifies the exact radial majorant required by the
countable weakened walk series.  This file produces that majorant for a concrete
and standard walk substrate: finite lists over a finite local step alphabet.

A map `cube : σ → Δ` attaches each local step to its active weakening cube.
The active carrier is the deduplicated image of the walk, so its cardinality is
at most the walk length.  If the operator term has geometric decay

`‖term walk‖ ≤ A * ρ ^ walk.length`

and

`card σ * (R * ρ) < 1`,

then the radial majorant is summable.  The proof counts all length-`n` words
exactly as the finite type `Fin n → σ`, producing the geometric ratio
`card σ * R * ρ`.  This is a real producer of `hmajor`, not a renamed
summability hypothesis.

Honest scope: CMP116's concrete generalized walks still need an encoding into
this finite local alphabet, and their ordered operator products still need the
stated geometric norm bound.  This module does not claim those source-specific
constructions.
-/

open scoped BigOperators

namespace YangMills.RG

universe u v w

variable {σ : Type u} {Δ : Type v} {E : Type w}

section ActiveCarrier

variable [DecidableEq Δ]

/-- The active weakening cubes visited by a list walk. -/
def cmp116ListWalkActive (cube : σ → Δ) (walk : List σ) : Finset Δ :=
  (walk.map cube).toFinset

/-- Deduplication can only decrease the number of active cubes. -/
theorem card_cmp116ListWalkActive_le_length
    (cube : σ → Δ) (walk : List σ) :
    (cmp116ListWalkActive cube walk).card ≤ walk.length := by
  simpa using List.toFinset_card_le (walk.map cube)

end ActiveCarrier

section FiniteAlphabet

variable [Fintype σ]

/-- Summability of the geometric length weight on all words over a finite
alphabet.  The exact word count at length `n` is `(card σ)^n`. -/
theorem summable_listWalk_pow_length
    (q : ℝ) (hq : 0 ≤ q)
    (hsmall : (Fintype.card σ : ℝ) * q < 1) :
    Summable fun walk : List σ => q ^ walk.length := by
  rw [← List.equivSigmaTuple.symm.summable_iff]
  rw [show ((fun walk : List σ => q ^ walk.length) ∘
      (List.equivSigmaTuple.symm : (Σ n, Fin n → σ) → List σ)) =
        (fun p : Σ n, Fin n → σ => q ^ p.1) by
    funext p
    rcases p with ⟨n, f⟩
    simp [List.equivSigmaTuple]]
  rw [summable_sigma_of_nonneg (fun p => pow_nonneg hq p.1)]
  constructor
  · intro n
    exact Summable.of_finite
  · have hgeom := summable_geometric_of_norm_lt_one
      (show ‖(Fintype.card σ : ℝ) * q‖ < 1 by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hq)]
        exact hsmall)
    simpa [Fintype.card_fun, mul_pow] using hgeom

section NormedTerms

variable [DecidableEq Δ] [NormedAddCommGroup E]

/-- Geometric decay per local step produces the exact radial majorant required
by the countable weakening series. -/
theorem summable_cmp116ListWalk_radialMajorant
    (cube : σ → Δ) (term : List σ → E) (R ρ A : ℝ)
    (hR : 1 ≤ R) (hρ : 0 ≤ ρ)
    (hsmall : (Fintype.card σ : ℝ) * (R * ρ) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * ρ ^ walk.length) :
    Summable fun walk : List σ =>
      R ^ (cmp116ListWalkActive cube walk).card * ‖term walk‖ := by
  have hgeom : Summable fun walk : List σ => (R * ρ) ^ walk.length :=
    summable_listWalk_pow_length (R * ρ)
      (mul_nonneg (zero_le_one.trans hR) hρ) hsmall
  have hupper : Summable fun walk : List σ =>
      A * (R * ρ) ^ walk.length := hgeom.mul_left A
  apply Summable.of_nonneg_of_le
  · intro walk
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) (norm_nonneg _)
  · intro walk
    calc
      R ^ (cmp116ListWalkActive cube walk).card * ‖term walk‖ ≤
          R ^ walk.length * (A * ρ ^ walk.length) :=
        mul_le_mul
          (pow_le_pow_right₀ hR
            (card_cmp116ListWalkActive_le_length cube walk))
          (hterm walk) (norm_nonneg _)
          (pow_nonneg (zero_le_one.trans hR) _)
      _ = A * (R * ρ) ^ walk.length := by
        rw [mul_pow]
        ring
  · exact hupper

section CompleteTerms

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The geometric walk estimate directly produces summability of the weakened
operator series at every point of the polydisc. -/
theorem summable_cmp116WeakenedListWalkSeries_of_geometricDecay
    (cube : σ → Δ) (term : List σ → E)
    (s : Δ → ℝ) (R ρ A : ℝ)
    (hR : 1 ≤ R) (hρ : 0 ≤ ρ)
    (hsmall : (Fintype.card σ : ℝ) * (R * ρ) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * ρ ^ walk.length)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    Summable fun walk : List σ =>
      cmp116WeakeningMonomial (cmp116ListWalkActive cube walk) s • term walk := by
  exact summable_cmp116WeakenedRandomWalkSeries
    (cmp116ListWalkActive cube) term s R (zero_le_one.trans hR) hs
    (summable_cmp116ListWalk_radialMajorant
      cube term R ρ A hR hρ hsmall hterm)

/-- Finite truncations of the list-walk expansion converge uniformly throughout
the weakening polydisc under the scalar geometric smallness condition. -/
theorem tendstoUniformlyOn_cmp116WeakenedListWalkSeries_of_geometricDecay
    (cube : σ → Δ) (term : List σ → E)
    (R ρ A : ℝ)
    (hR : 1 ≤ R) (hρ : 0 ≤ ρ)
    (hsmall : (Fintype.card σ : ℝ) * (R * ρ) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * ρ ^ walk.length) :
    TendstoUniformlyOn
      (fun walks : Finset (List σ) => fun s =>
        ∑ walk ∈ walks,
          cmp116WeakeningMonomial (cmp116ListWalkActive cube walk) s • term walk)
      (cmp116WeakenedRandomWalkSeries (cmp116ListWalkActive cube) term)
      Filter.atTop (cmp116WeakeningPolydisc R) := by
  exact tendstoUniformlyOn_cmp116WeakenedRandomWalkSeries
    (cmp116ListWalkActive cube) term R (zero_le_one.trans hR)
    (summable_cmp116ListWalk_radialMajorant
      cube term R ρ A hR hρ hsmall hterm)

/-- The geometric decay and finite-alphabet counting hypotheses also discharge
the one-coordinate FTC endpoint of the infinite walk series. -/
theorem cmp116WeakenedListWalkSeries_ftcStep_of_geometricDecay
    (cube : σ → Δ) (term : List σ → E)
    (s : Δ → ℝ) (d : Δ) (R ρ A : ℝ)
    (hR : 1 ≤ R) (hρ : 0 ≤ ρ)
    (hsmall : (Fintype.card σ : ℝ) * (R * ρ) < 1)
    (hterm : ∀ walk, ‖term walk‖ ≤ A * ρ ^ walk.length)
    (hs : s ∈ cmp116WeakeningPolydisc R) :
    cmp116WeakenedRandomWalkSeries (cmp116ListWalkActive cube) term
        (Function.update s d 0) +
      ∫ _t in (0 : ℝ)..1,
        cmp116WeakenedRandomWalkSeriesDerivative
          (cmp116ListWalkActive cube) term s d =
      cmp116WeakenedRandomWalkSeries (cmp116ListWalkActive cube) term
        (Function.update s d 1) := by
  exact cmp116WeakenedRandomWalkSeries_ftcStep
    (cmp116ListWalkActive cube) term s d R hR hs
    (summable_cmp116ListWalk_radialMajorant
      cube term R ρ A hR hρ hsmall hterm)

end CompleteTerms
end NormedTerms
end FiniteAlphabet

end YangMills.RG
