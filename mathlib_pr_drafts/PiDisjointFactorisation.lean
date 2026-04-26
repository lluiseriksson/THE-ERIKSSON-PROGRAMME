/-
Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Disjoint-coordinate factorisation for product measures

For a product measure `Measure.pi μ` on `(i : ι) → α i` with
`Fintype ι` and probability factors `μ i`, this file shows that an
integrand depending only on coordinates in a sub-`Finset S` is
independent of an integrand depending only on coordinates in a
sub-`Finset T` whenever `S` and `T` are disjoint.

## Main results

* `MeasureTheory.Measure.pi_integral_factorise_disjoint` :
  `∫ x, f x · g x ∂(pi μ) = (∫ y, f' y ∂(pi (μ ∘ S))) · (∫ z, g' z ∂(pi (μ ∘ T)))`
  whenever `f` factors through `restrict S` as `f'`, `g` factors
  through `restrict T` as `g'`, and `S ∩ T = ∅`.

## Why this matters

In statistical mechanics, gauge-link products that touch disjoint
edges of a finite lattice are independent under a product Haar
measure. The classical Fubini factorisation is provided by Mathlib's
`integral_prod`, but the general "disjoint subset" rearrangement that
arises in cluster expansions and polymer models requires a small
specialisation that this file provides.

## Tags

product measure, Fubini, disjoint factorisation, cluster expansion

-/

namespace MeasureTheory

open Measure Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]

section DisjointFactorisation

variable (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- The restriction of a function `((i : ι) → α i) → ℝ` along the
inclusion `S → ι` for `S : Finset ι`. We use the explicit "extend by
default-on-complement" form rather than the abstract sigma-coproduct
to keep the proof close to existing Mathlib API. -/
def restrictDomain (S : Finset ι) (f : ((i : ι) → α i) → ℝ) :
    ((i : { i // i ∈ S }) → α i.val) → ℝ :=
  fun y => f (fun i => if h : i ∈ S then y ⟨i, h⟩ else
    Classical.arbitrary _)

/-- A function on `(i : ι) → α i` is **supported on `S`** if its value
depends only on coordinates with index in `S`. Equivalently: it
factors through `restrictDomain S`. -/
def SupportedOn (S : Finset ι) (f : ((i : ι) → α i) → ℝ) : Prop :=
  ∃ f' : ((i : { i // i ∈ S }) → α i.val) → ℝ,
    ∀ x, f x = f' (fun i => x i.val)

/-- The restriction of the pi-measure to a sub-`Finset S`. -/
noncomputable def piRestrict (S : Finset ι) :
    Measure ((i : { i // i ∈ S }) → α i.val) :=
  Measure.pi (fun i : { i // i ∈ S } => μ i.val)

instance piRestrict_isProbabilityMeasure (S : Finset ι) :
    IsProbabilityMeasure (piRestrict μ S) := by
  unfold piRestrict
  infer_instance

/-- **Disjoint-coordinate factorisation of a product-measure integral.**

If `f` and `g` are supported on disjoint sub-`Finset`s `S` and `T` of
`ι`, then their integral against `Measure.pi μ` factorises as the
product of independent integrals against the restricted pi-measures. -/
theorem pi_integral_factorise_disjoint
    {S T : Finset ι} (h_disj : Disjoint S T)
    {f g : ((i : ι) → α i) → ℝ}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hf_int : Integrable f (Measure.pi μ))
    (hg_int : Integrable g (Measure.pi μ)) :
    ∫ x, f x * g x ∂(Measure.pi μ) =
    (∫ y, (Classical.choose hf) y ∂(piRestrict μ S)) *
    (∫ z, (Classical.choose hg) z ∂(piRestrict μ T)) := by
  -- Proof outline:
  --
  -- 1. Reorder the index set ι as S ⊕ T ⊕ (ι \ (S ∪ T)) using
  --    `Finset.disjUnion h_disj` and the complement.
  -- 2. Apply `Measure.pi_pi` to factor the pi-measure over the three
  --    blocks, giving
  --    `pi μ = (pi μ_S) ⊗ (pi μ_T) ⊗ (pi μ_rest)`.
  -- 3. Apply `MeasureTheory.integral_prod` (Fubini) twice to extract
  --    the rest-block integral as a probability-measure integral over
  --    a constant (since both f and g are independent of those
  --    coordinates), which evaluates to f's value times g's value
  --    integrated against the appropriate measure.
  -- 4. Apply `MeasureTheory.integral_prod` once more on the (S, T)
  --    factor to separate the two product factors, using independence
  --    via Tonelli.
  --
  -- Key lemmas:
  -- - `MeasureTheory.Measure.pi_pi`
  -- - `MeasureTheory.integral_prod`
  -- - `IsProbabilityMeasure.integral_const` (probability measure of
  --   the rest block integrates a constant to 1)
  -- - `MeasureTheory.Integrable.integral_prod_left`
  --
  sorry  -- TODO: fill in proof

end DisjointFactorisation

/-! ## Common consumer-side specialisation

For applications in statistical mechanics, the most useful form of the
above takes a single function expressed as a product of factors, each
supported on a single coordinate or a small block. -/

section ProductFactorisation

variable (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Helper: a single-coordinate product `∏ i ∈ S, f_i (x i)` is
supported on `S`. -/
theorem supportedOn_prod_singleCoord {S : Finset ι}
    (f : ∀ i, α i → ℝ) :
    SupportedOn S (fun x => ∏ i ∈ S, f i (x i)) := by
  refine ⟨fun y => ∏ i ∈ S.attach, f i.val (y i), ?_⟩
  intro x
  rw [Finset.prod_attach]

/-- **Disjoint-coordinate product factorisation (Mayer-friendly form).**

If `S` and `T` are disjoint sub-`Finset`s of `ι`, and the integrand
factors as a product of single-coordinate functions over `S ∪ T`,
then the integral against `Measure.pi μ` factorises as the product
of two independent product integrals. -/
theorem pi_integral_prod_factorise_disjoint
    {S T : Finset ι} (h_disj : Disjoint S T)
    (f g : ∀ i, α i → ℝ)
    (hf_int : ∀ i ∈ S, Integrable (f i) (μ i))
    (hg_int : ∀ i ∈ T, Integrable (g i) (μ i)) :
    ∫ x, (∏ i ∈ S, f i (x i)) * (∏ i ∈ T, g i (x i)) ∂(Measure.pi μ) =
    (∫ y, (∏ i ∈ S.attach, f i.val (y i)) ∂(piRestrict μ S)) *
    (∫ z, (∏ i ∈ T.attach, g i.val (z i)) ∂(piRestrict μ T)) := by
  -- This is the application form that cluster expansions actually use.
  -- The proof is direct from `pi_integral_factorise_disjoint` with
  -- the supportedness witness from `supportedOn_prod_singleCoord`,
  -- plus a routine integrability check.
  sorry  -- TODO: fill in proof

end ProductFactorisation

end MeasureTheory
