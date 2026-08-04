# Technical notes salvaged from the abandoned manuscript

## Base-point condition

For the Wilson word used in the candidate manuscript, the varying matrix
`gamma(t)` enters linearly in the relevant trace expression. Its first
derivative therefore depends only on `gamma'(0)`; the specialized statement
does not require `gamma(0) = I`. The more general theorem for an arbitrary
function still carries a base-point hypothesis because its derivative is
evaluated at `v * gamma(0)`. This explanatory distinction is not a new Lean
result and was not recompiled during the salvage.

## Render verification

Four escape failures motivated the discarded editorial revision: `alpha` to
BEL, `beta` to backspace, `texttt` to TAB, and `neq` to a legal newline followed
by `eq0`. The last class can compile cleanly and survive a control-byte scan.
Searching decompressed PDF streams is also insufficient because visible text
may be split across kerning arrays and font subsets. A future guard must use a
real text extractor with Unicode normalization and retain raster comparison or
human inspection for critical formulas.
