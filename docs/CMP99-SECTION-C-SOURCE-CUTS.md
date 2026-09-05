# CMP99 Section C source lock: the cutoffs in (3.97)

Primary-source inspection was performed from rendered page images, not from
OCR alone.

## Source statements

- CMP99, printed p. 408: the cells `Pi` are cubes made from `2^d` large
  blocks.  The paper takes the partition of unity `{h_Pi}` from the end of
  Sect. A of the preceding propagator paper and states
  `sum_Pi h_Pi^2 = 1`.
- CMP99, printed p. 411, equation (3.95): the characteristic multiplier and
  the partition multiplier occur in different summands; they are not one
  interchangeable cutoff.
- CMP99, printed p. 412, equation (3.97): the operator order is

  `tildeChi * Q' * (G'_Pi0^2 - G'_Pi^2) * Q'^* * h_Pi * C_Pi * h_Pi`.

- Balaban, *Propagators and renormalization transformations for lattice gauge
  theories I*, printed p. 36, equation (1.118), gives the analogous explicit
  partition construction: a compactly supported smooth one-dimensional `h`
  is chosen with `h=1` on `[-1/3,1/3]` and
  `sum_n h(t-n)^2=1`; tensor products give `sum_z h_z(x)^2=1`.

## Lean convention now locked

- The characteristic is the literal source cell `Pi`, represented by
  `cmp99SourceTildePiLargeBlocks cell 0`; the equality `tilde Pi^0 = Pi` is
  already proved.
- The smooth functions are represented by one global
  `CMP99SourceSquarePartition`, not by arbitrary transition functions.
- `|h_Pi| <= 1` is derived from `sum_Pi h_Pi^2=1`.
- The characteristic bound is derived by case splitting on membership.
- The resulting `GeneratedSectionCTransitionCutData` is generated internally,
  and the full dependent tower no longer receives per-transition cutoff
  functions or norm certificates.

## Remaining source obligation

`CMP99SourceSquarePartition` is still the noncanonical smooth choice made by
the source.  A later source-dictionary module must construct it from the
printed smooth bump (or prove existence of an equivalent periodic square
partition with the required derivative estimates).  This is not claimed in
the present checkpoint; in particular, no hard cell indicator is substituted
for `h_Pi`.
