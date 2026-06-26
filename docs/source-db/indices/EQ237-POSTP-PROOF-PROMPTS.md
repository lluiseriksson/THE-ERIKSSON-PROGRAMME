# Eq. (2.37) proof prompts

## Prompt A — fixed-Z0prime display

Open `cmp116.eq237.post-p-resummation` and inspect the rendered CMP116 pages 19-20. Extract a Lean-facing theorem statement for the fixed-`Z0'` estimate.

Required output:

```text
- exact source locator;
- summation domain before fixing Z0';
- definition of the fixed-Z0' fiber;
- all factors in the displayed bound;
- component product indexing convention;
- metric `d_{k+1}` convention;
- exact Lean theorem skeleton for CMP116Eq237MajorizationBoundary.
```

Do not claim closure if the `D/P/Z0/Z0'` dictionary is still a premise.

## Prompt B — post-(2.37) summation

Extract the paragraph following Eq. (2.37): the final sum over `Z0'` or `Z \ Z0'`.

Required output:

```text
- which part of exp(-(kappa1-1)*(LM)^-4*|Z\Z0'|) is reserved;
- where adapted Eq. (2.32) is invoked;
- exact form of `(1/2)*(kappa1-1) >= 2*L*kappa`;
- whether Eq. (2.34)-type estimate is cited;
- final normalized source-bound theorem statement.
```

## Prompt C — constants

Use `cmp116.constants.c3-alpha5` to write a constant hierarchy card.

Required output:

```text
- alpha5 definition;
- boundedness assumptions for (LM)^4*alpha0, alpha1, alpha4, gamma2;
- epsilon2 restrictions;
- C3 visual formula;
- common-majorant theorem target for O(1) constants.
```

## Prompt D — dictionary

Write only the source-to-Lean dictionary theorem for `cmp116Eq237Z0Fiber`.

Required output:

```lean
-- schematic only
theorem cmp116Eq237_sourceFiber_mem_iff ... :
  x ∈ SourceFiber Z Z0prime ↔ x ∈ cmp116Eq237Z0Fiber R Z Z0prime := ...
```

Do not combine this with analytic estimates.
