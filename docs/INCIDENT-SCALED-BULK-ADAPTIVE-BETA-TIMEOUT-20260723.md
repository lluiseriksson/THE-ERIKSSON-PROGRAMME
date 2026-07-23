# Incident: adaptive beta/t cover timeout

Date: 2026-07-23
Status: candidate-only; no promotion to G2 or G6

An adaptive two-dimensional probe was attempted on the gap unit
\([3259/32,3261/32]\).  It used the existing scaled backend, order 35 in beta,
order 42 in `t`, 220 Arb bits, and split beta only after a `t` cell reached the
minimum width.  The local stress interval `t∈[3.12,3.13]` passed in four rows
with the original beta width `1/16`.

The same driver over `t∈[3/5,π-(3/2)/β_hi]` timed out after 600 seconds without
emitting a certificate.  This is an operational timeout, not a partial pass;
there is no production/replay transcript or manifest.

The relay audit remains unchanged (`beta_union_complete: false`,
`RELAY_LEMMA_UNPROVED`, `promotion: NONE`).  The local stress success is useful
for future partition design but cannot be promoted or used to alter G2/G6.
