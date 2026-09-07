# CMP89 Neumann reflection: scalar-convention gate

Static audit before the physical CMP89 (2.42) right-inverse producer.

## Measured mismatch

The retained regional precision and the literal full-lattice Fourier precision
do not consume the same scalar representation:

- `cmp89SourceRetainedNeumannPrefixGaugePrecision T r mass aSource` uses
  `cmp85SourcePrefixCountingCoefficient T aSource r`, because its `Qprime`
  adjoint is the counting-Hilbert adjoint.
- `cmp99SourceFlatFullComplexPrecisionCLM mass aFourier` and the normalized
  CMP89 (2.48) Green use `aFourier` in front of a coefficient-one *weighted*
  adjoint.

Therefore the source-faithful specialization is

```lean
aFourier := cmp85SourcePrefixWeightedCoefficient T aSource r
```

and not `aFourier := aSource`.  The exact weighted/counting bridge is already
recorded by `cmp85SourcePrefixCountingCoefficient` and
`cmp99SourceSpacingPairing_retainedNeumannPrefixGaugePrecision`.

## Spacing gate

The literal Eq. (2.48) endpoint with parameters `L = M` and
`j = steps + 1` uses fine spacing

```lean
cmp99SourceGeneratedFullComplexSpacing M (steps + 1)
```

so the regional precision compared with it must use that same canonical
spacing.  An arbitrary positive `spacing` is not a physical identification.

## Acceptance condition for the next producer

The next specialization must construct internally:

1. the retained tower `T` at canonical spacing;
2. the last positive prefix `r`;
3. `aFourier := cmp85SourcePrefixWeightedCoefficient T aSource r`;
4. the literal Eq. (2.48) real Green with `(L, j) = (M, steps + 1)`;
5. the regional counting coefficient only through the existing exact
   weighted/counting dictionary.

It must not reuse one free `a` or one free `spacing` on both sides by naming
coincidence.  The remaining analytic input is then the literal right-inverse
law for the internally constructed reflection operator, not a scalar
dictionary hidden inside that law.

This note does not claim CMP89 (2.42), a Green bound, or window 15.
