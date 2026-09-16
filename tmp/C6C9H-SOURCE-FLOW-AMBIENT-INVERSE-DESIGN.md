# C6c.9h--j source-flow ambient complex inverse design

Status: static scratch only.  No theorem below is claimed compiler-verified.

## Sealed inputs

- `cmp99SourceSeparatedSourceFlowFlatAmbientPrecision` and
  `cmp99SourceSeparatedSourceFlowFlatAmbientGreen`, with both real inverse
  laws.
- `cmp85LastPositivePrefix_sourceFlow_countingCoefficient_eq`.
- `cmp99SourceFlowCountingMass_complexFieldDictionary`.
- `CMP99SourceGeneratedTerminalComplexFieldData.
  sourceFlowPhysicalPrecision_complexification_eq_fullComplexAction`
  (pending the current Colab verdict before promotion).
- The separated Step-7b carrier and field equivalences.

## Brick H: canonical complex inverse pair

Promote the two definitions and inverse-law transports currently drafted in
`tmp/BalabanCMP99SourceSeparatedSourceFlowFlatAmbientGreenComplexification.draft.lean`.
The coefficient remains the literal input `a`; positivity `ha : 0 < a` is
used only to construct the real Green.

## Brick I: exact source-flow ambient precision dictionary

Define the transported full-box precision with

```text
fine side    = L^(depth+1)
coarse side  = 2*(K*Q)
bare mass    = 0
weighted a   = cmp99SourceFlowFlatFullComplexA a L depth.
```

The real bridge must be proved before complex linear extension:

```text
cmp99SourceSeparatedSourceFlowFlatAmbientPrecision ... phi x
  = cmp99SourceGaugePrecision
      activeFlatLaplacian
      regions.flatExplicitQprime
      (cmp99SourceFlowFlatCountingA 4 a L depth)
      D.activeField (eFull.symm x).
```

Its proof has exactly three non-definitional rewrites:

1. the retained tower at `cmp85LastPositivePrefix` is the terminal generated
   weighted-Qprime tower;
2. flat physical `Qprime` is `regions.flatExplicitQprime`;
3. the final-prefix counting coefficient is
   `cmp99SourceFlowFlatCountingA 4 a L depth`.

After that bridge, use the current pointwise physical theorem and the sealed
zero-extension/carrier dictionary exactly as in
`BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary`.
Extend from real inputs by real/imaginary decomposition; do not accept a
complex precision equality from the caller.

## Brick J: inverse uniqueness and stabilized field

Transport the internally constructed complex Green through the separated
Step-7b equivalence.  Prove it is a left inverse of the literal source-flow
full-box precision using Brick I and the complex inverse law from Brick H.
Then apply the existing full-complex inverse-uniqueness theorem.

The stabilized denominator proofs must use the literal positive coefficient
`cmp99SourceFlowFlatFullComplexA a L depth`, with `ha : 0 < a`; no generated
Poincare coefficient may re-enter.

## Delimitation

These bricks identify the literal source-flow ambient inverse with the
full-complex Fourier precision/Green.  They do not by themselves produce a
uniform regional `B0`/`delta0`, attain window 15, discharge rows 23--24, or
instantiate `TermSource`.  The hard counters stay `20/41`, `TermSource = 0`.
