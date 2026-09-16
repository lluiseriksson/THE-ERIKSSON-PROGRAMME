# CMP89 (2.46): central fine-point-source component

Status: static design only.  This note is not compiler evidence and does not
move `20/41`.

## Exact branch

For the central alias `c`, the already constructed full solution is

```text
(moment - Σ_{n != c} row(n) *
  (source(n)/fine(n) - a*column(n)*moment/fine(n))) / row(c).
```

The cold target `BalabanCMP89Eq246CentralAverageRowReciprocalBound` supplies
the final reciprocal `1/row(c)`.  The numerator must not be bounded by first
forgetting the `row(n)` factor: doing that would incorrectly charge the
quadratic bare-diagonal alias budget to the central component.

## Three numerator pieces

1. `moment` is already bounded by
   `norm_cmp89Eq246StabilizedFinePointSourceSolutionMoment_le`.
2. `Σ row(n)*source(n)/fine(n)` is the named noncentral source moment.  Its
   existing producer is scale-uniform because `row/fine` carries the strict
   `alpha = -1` reciprocal-alias weight.
3. `Σ row(n)*a*column(n)*moment/fine(n)` factors as
   `a*moment*Σ row(n)*column(n)/fine(n)`.  The last sum must be bounded with
   the literal row/column product and the existing summable alias weights;
   it is not a new free family.

Thus the central component has a scale-uniform budget.  The visible
`O((L^j+1)^2)` loss belongs only to the noncentral bare diagonal sum.

## Acceptance gates

- cite the exact central-row reciprocal theorem, not merely nonvanishing;
- keep the three numerator pieces separately named through the last line;
- factor the correction moment before summation;
- use the existing finite alias carrier and erase the central index exactly;
- no cardinality bound and no assignment of the averaged quotient weight to
  the bare diagonal source term;
- the resulting theorem remains below the continuous Fourier synthesis and
  does not claim CMP89 (2.42), uniform physical `B0`/`delta0`, window 15,
  `20/41`, or a `TermSource`.
