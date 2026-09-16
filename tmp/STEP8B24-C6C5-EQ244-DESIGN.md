# Step 8b.24 C6c.5 — CMP96 (2.44) local defect

Status: static source/tree audit only.  No new Lean declaration, `.olean`,
focal or axiom verdict exists.

## Primary-source contract

CMP96 printed pp. 229--230 fixes the operator and its sign before the bound:

```text
Delta'_a G'_0 = I - sum_box K(h_box) G'(box) h_box              (2.38)

K(h) lambda
  = linkDerivative(h, lambda)
    - (Delta h) lambda
    - a_j Q'-massDerivative(h, lambda).                         (2.39)
```

After rescaling, (2.40) retains the same three signs.  Combining it with the
two local Green actions in (2.43) gives the one-cell estimate

```text
|(K(h_box) G'(box) h_box lambda)(x)|
  <= O(M^-1) exp(-delta0 |x-y|) |lambda|.                        (2.44)
```

This is a single-cell action estimate.  It precedes every overlap, layer,
walk, Neumann-series or contraction argument.

## Sign dictionary proved by the existing tree

The source uses a positive Laplacian: CMP96 printed p. 225 defines
`Delta'_a = Delta + Q'^* a Q'` and explicitly says that `Delta` is positive.
The tracked positive-`D^*D` product rule proves

```text
Delta_U(h phi) = h Delta_U(phi) - linkDerivative + correction.
```

Therefore

```text
h Delta_U(phi) - Delta_U(h phi) = linkDerivative - correction.
```

This is not merely a reading convention.  The sealed theorem
`cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_apply_eq` states the
full generated-precision commutator as

```text
linkDerivative - cutoffLaplacianCorrection + generatedMassCommutator.
```

Consequently the source middle species inside `K(h)` is the negative of the
positive tree correction, exactly as frozen by the C6c.3 sign gate.

## Measured defect in the current downstream assembly

The tracked definition
`cmp99Eq389SourceLocalizedThreeSpeciesRegionalCorrection` currently adds

```text
first + positiveCutoffCorrection + third.
```

It does not identify this sum with the full physical commutator, and its norm
majorant remains algebraically valid.  But the operator itself is not the
literal `K(h)` from (2.39)/(2.40): the physical sum is

```text
first - positiveCutoffCorrection + third.
```

C6c.5 must therefore not reuse the existing three-species operator definition
unchanged.  It may reuse all three component bounds and the displayed budget,
because negation preserves norms, but it must construct a sign-correct literal
operator and prove its equality to the generated-precision commutator before
claiming (2.44).

This is a semantic source gate, not a request to retract the sealed component
bounds.  No tracked file is changed by this note.

## Minimal analytic dependency on C6c.4

The existing source-localized component theorems over-request the four-field
`CMP99Eq342SourceLocalizedGreenCertificate`.  A field-use audit gives the
actual dependencies:

* the first/link species uses only `left_derivative_bound` plus common
  positivity of `B0` and `delta0`;
* the second/cutoff-Laplacian species uses only `value_bound` plus the same
  positivity;
* the third/generated-mass species uses only `value_bound` plus the same
  positivity.

Thus C6c.5 must consume the internally generated C6c.4 pair from (2.43), not
the right-adjoint-derivative or Laplacian fields that belong to C6c.7.  Passing
the full four-action certificate here would create a false dependency cycle
and would rename two later obligations as inputs.

The reusable component lemmas may expose their exact minimal predicates, but
the C6c.5 headline must obtain those predicates from the C6c.4 producer.  It
may not accept an arbitrary local Green, a free family of component bounds, or
the terminal certificate.

## Required construction

1. Define the sign-correct single-cell operator
   `first - positiveCutoffCorrection + third`, using the same generated local
   precision, regional Green and right signed cutoff.
2. Prove pointwise equality with
   `K(h_box) G'(box) h_box`, where `K(h) = h Delta'_a - Delta'_a h`, by the
   sealed generated-precision cutoff-commutator identity and the C6c.2/C6c.4
   local-precision dictionary.
3. Refactor or add componentwise localized-sup lemmas whose analytic inputs
   are exactly the C6c.4 value/left-derivative pair.
4. Combine the three component bounds by the triangle inequality.  Retain the
   separate budgets through the theorem statement:
   the first and third species are `K^-1`, while the middle species is
   `K^-2`.  A shared opaque constant is not accepted.
5. Conclude the single-cell (2.44) action at the source-owner distance and the
   common rate produced uniformly by C6c.4.

## Acceptance endpoint and exclusions

The first admissible C6c.5 endpoint is a theorem about the literal physical
single-cell defect, with exact operator equality and an explicit
`firstBudget + secondBudget + thirdBudget` majorant.  It proves the
`O(K^-1)` action before summation.

It does not claim a sum over cells, overlap `16`, layer counting, a random
walk, a Neumann inverse, contraction, or window-15 attainment.  Those begin
at C6c.6.

