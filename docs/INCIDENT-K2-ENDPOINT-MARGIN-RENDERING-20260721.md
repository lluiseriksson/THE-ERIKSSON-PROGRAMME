# K2 endpoint margin-rendering incident

The first segmented endpoint transcripts printed only `arb.str(30)` for the
margin.  Flint's compact string representation can hide a positive midpoint
and display a symmetric hull (`[+/- ...]`), so those rows were not
machine-auditable from the transcript alone.  An independent validator
correctly refused to infer strict positivity from that rendering.

The underlying driver comparison has now been made explicit as
`margin.lower() > 0`, and the wrapper prints `margin_lower` and
`margin_upper` separately.  The old transcripts are quarantined; they carry
no evidence.  All production and replay rows must be regenerated with the
new wrapper hash and pass the strict lower-endpoint validator before the
endpoint brick can be accepted.
