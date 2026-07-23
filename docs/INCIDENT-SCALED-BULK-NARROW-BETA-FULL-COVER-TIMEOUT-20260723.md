# Incident: narrow beta slice full-cover timeout

Date: 2026-07-23
Status: candidate-only; no promotion to G2 or G6

## Probe

After the failed width-`1/16` unit, a higher-order, higher-precision probe was
tested on the narrow beta interval

\[
 [104319/1024,104321/1024]
   =[101.8740234375,101.8759765625].
\]

The local settings were order 35 in beta, order 42 in `t`, 220 Arb bits, and
the existing CWIN `3/2` scaled backend.  The problematic local interval
`t∈[3.124,3.127]` passed as a single strict-negative row, with upper endpoint
approximately `-4.8426990625e-109`.

The same adaptive cover over the complete domain
`t∈[3/5, π-(3/2)/β_hi]` did not finish within 600 seconds.  No transcript or
certificate was emitted, so this is a timeout, not a partial pass.

## Disposition

The local success shows that beta subdivision and higher precision can reduce
the interval overestimation near the stress point.  It does not establish a
cover: the full domain, production/replay identity, manifest, and independent
validator are all missing.  The relay audit therefore remains unchanged:
`beta_union_complete: false`, `RELAY_LEMMA_UNPROVED`, `promotion: NONE`.

Any continuation must either optimize and preregister a finite family of such
narrow slices, or pursue the absolute complex-majorant route.  This incident
must not be used to alter G2, G6, or the manuscript seal.
