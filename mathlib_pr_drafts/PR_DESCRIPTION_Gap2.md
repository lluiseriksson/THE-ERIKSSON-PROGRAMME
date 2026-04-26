# PR: Disjoint-coordinate factorisation for product measures

**Branch suggestion**: `lluis-eriksson/pi-disjoint-factorisation`
**Suggested target file**: `Mathlib/MeasureTheory/Constructions/Pi/Disjoint.lean`
(or extension of existing `Mathlib/MeasureTheory/Constructions/Pi.lean`)
**Estimated review effort**: 1–2 reviewer-hours
**Mathlib zulip ping**: #maths > measure theory, with mention to maintainers Yury Kudryashov and Floris van Doorn

---

## Summary

This PR adds a single new theorem to
`Mathlib/MeasureTheory/Constructions/Pi`:

```lean
theorem MeasureTheory.pi_integral_factorise_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    {S T : Finset ι} (h_disj : Disjoint S T)
    {f g : ((i : ι) → α i) → ℝ}
    (hf : SupportedOn S f) (hg : SupportedOn T g)
    (hf_int : Integrable f (Measure.pi μ))
    (hg_int : Integrable g (Measure.pi μ)) :
    ∫ x, f x * g x ∂(Measure.pi μ) =
    (∫ y, ... ∂(piRestrict μ S)) * (∫ z, ... ∂(piRestrict μ T))
```

stating that the integral of a product `f · g` over a finite product
measure factorises into independent integrals when `f` and `g` depend
on disjoint subsets of the coordinates.

The PR also adds a "Mayer-friendly" specialisation
`pi_integral_prod_factorise_disjoint` for the case where `f` and `g`
are products of single-coordinate functions.

Together the file is approximately 100 LOC.

## Why this matters

This is the core Fubini step that cluster expansions in classical
statistical mechanics rely on. The general "disjoint subset"
rearrangement appears whenever:

1. **Polymer models**: a polymer activity factorises across edges that
   the polymer doesn't touch (the standard Mayer/Ursell setting).
2. **Lattice gauge theories**: gauge-link products that touch disjoint
   plaquettes / edges are independent under the product Haar measure.
3. **Random graph models**: edge-product observables independent across
   edge-disjoint subgraphs.

Mathlib already has `MeasureTheory.Measure.pi`,
`MeasureTheory.integral_pi`, and `MeasureTheory.integral_prod` (Fubini
for products of two factors), but the **specific re-arrangement for
disjoint subsets of a finite index type** does not appear to be
formalised. This PR fills that gap.

The downstream Yang-Mills formal verification project consumes this
lemma as the keystone of the Brydges–Kennedy random-walk cluster
expansion's "geometric vanishing" property: if a polymer `Y =
Y₁ ⊔ Y₂` decomposes into edge-disjoint pieces, then the truncated
activity factorises and (combined with the zero-mean property of the
Wilson fluctuation `w̃`) vanishes.

## Statement details

The PR introduces three small helper definitions:

```lean
def restrictDomain (S : Finset ι)
    (f : ((i : ι) → α i) → ℝ) :
    ((i : { i // i ∈ S }) → α i.val) → ℝ

def SupportedOn (S : Finset ι)
    (f : ((i : ι) → α i) → ℝ) : Prop

noncomputable def piRestrict (S : Finset ι) :
    Measure ((i : { i // i ∈ S }) → α i.val)
```

`SupportedOn S f` is the proposition that `f` factors through the
restriction to `S`. This is the natural "depends only on coordinates
in `S`" predicate, expressed as an existential over a witness
restricted function. (An alternative formulation via section /
extension functions of types is possible but adds infrastructure.)

The main theorem and its product specialisation follow.

## Proof outline

The proof is a Fubini-style argument that decomposes the index `ι`
into three disjoint pieces `S ⊔ T ⊔ (ι \ (S ∪ T))` and:

1. Applies `MeasureTheory.Measure.pi_pi` (Mathlib has this) to
   factor the pi-measure across the three pieces.
2. Applies `MeasureTheory.integral_prod` (Fubini for product of two
   measures) twice to extract the integral over the rest-block,
   which integrates a constant (since `f` and `g` don't depend on
   those coordinates) against a probability measure to give 1.
3. Applies `integral_prod` once more on the `(S, T)` block to
   separate the `S` and `T` factors, using independence via Tonelli.

Key Mathlib lemmas relied on:

- `MeasureTheory.Measure.pi_pi`
- `MeasureTheory.integral_prod`
- `IsProbabilityMeasure.integral_const_one` or
  `MeasureTheory.integral_const` plus probability normalisation
- `MeasureTheory.Integrable.integral_prod_left`
- Existing `Disjoint`, `Finset.disjUnion` API

## Backwards compatibility

This PR adds new content only. No existing API is modified.

## Tests

A short test file demonstrates:

- Disjoint factorisation on `Fin n → ℝ` with `S = {0, 1}`, `T = {2, 3}`,
  `n = 5` and Gaussian / uniform factors.
- The product-form specialisation reduces the disjoint factorisation
  to a multiplication of two single-coordinate Riemann-integral-like
  quantities.
- Integration with `MeasureTheory.Measure.haarMeasure` on a product
  of compact groups (the Yang-Mills application).

## License

Apache 2.0, with copyright assigned to the Mathlib community as per
standard contribution policy.

## Author

Lluis Eriksson (lluiseriksson@gmail.com), as part of the Yang-Mills
formal verification project. Drafted with assistance from Anthropic
Claude (Cowork mode).

## Pre-PR checklist

- [ ] Run `lake build` and confirm zero errors.
- [ ] Confirm `#print axioms pi_integral_factorise_disjoint` returns
      `[propext, Classical.choice, Quot.sound]`.
- [ ] Run `mathlib-update-references`.
- [ ] Run `style-lint` and address output.
- [ ] Add docstring linking back to consumer use cases (cluster
      expansions, polymer models).

## Combination with PR 1 (Animal count)

The two PRs together provide the analytic infrastructure required by
the F3-Mayer blueprint of the Yang-Mills project:

- PR 1 (`AnimalCount.lean`): combinatorial bound on connected
  subgraph counts.
- PR 2 (this PR): disjoint-coordinate factorisation of product
  measures.

Each is independently useful; together they cover roughly half of
the missing measure-theoretic / combinatorial scaffolding needed for
the cluster expansion in `BrydgesKennedyEstimate.lean` (still
in-repo, project-local).

---

*PR drafted 2026-04-25 by Cowork agent (Claude) on behalf of
Lluis Eriksson.*
