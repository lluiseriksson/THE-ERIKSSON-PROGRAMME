# R7/R8 expression-engine nonterminal run (2026-07-28)

The production run of
`surface_remainder_delta0_seventh_eighth_coefficient.py` printed provenance
and then disappeared without a terminal line.  Its stderr transcript is
empty.  The last observed working set was approximately 6.3 GB, but no exit
status or operating-system diagnostic was recovered.

Therefore:

- the run is **nonterminal**, not failed mathematics and not a pass;
- its output is inadmissible as evidence for R7/R8;
- resource exhaustion is a plausible explanation, not a diagnosed fact;
- the identical expression-level replay and the over-order guard are not run
  through this implementation.

The replacement route uses the existing sparse coefficient-list derivation
against the already public immutable targets, with production/replay.  That
is one exact symbolic engine, not an independent second engine.  A separate
high-precision numerical extraction at the stress cell is required for
implementation-independent corroboration.

No K2, gate, or manuscript claim changes.
