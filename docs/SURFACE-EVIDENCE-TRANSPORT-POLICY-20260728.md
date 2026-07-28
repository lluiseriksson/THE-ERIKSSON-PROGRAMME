# Surface evidence-transport policy (2026-07-28)

This note records a repository-wide rule exposed by the weak-main v3
transcript incident.  It does not change or promote a mathematical gate.

## Literal implication, not digit count

A transcript is self-sufficient only when the enclosures printed in the
artifact, interpreted literally, imply every acceptance predicate consumed by
its validator.  A large number of printed digits is neither necessary nor
sufficient.  The relevant quantity is the outward radius relative to the
decision margin.

Whenever practical, a certifier must therefore print the actual decision
quantity — for example an outward `KD.lower()` or `XMAIN.lower()` — rather than
requiring a downstream parser to recover it from a diagnostic parent ball.

The weak-main v3 artifact exposed the distinction: `KD.str(18)` could collapse
to a wide zero-centred shorthand even though the internal lower endpoint was
positive.  The v4 format prints explicit lower endpoints.  Existing lambda-3
and lambda-4 aggregate enclosures have radii negligible relative to their
registered margins and therefore imply their predicates when read literally;
they are not affected by this incident.

## Failure taxonomy

Instrument defects must be triaged by the direction in which they can corrupt
the evidence:

1. **false-PASS capable** — a defect narrows an enclosure, shifts its centre, or
   changes the mathematical normalization.  Stop promotion and reconstruct the
   evidence from an independent anchor.
2. **false-FAIL only** — a defect only widens an enclosure and can make a judge
   return failure or `nan`, but cannot establish the target.  Preserve the
   failure and repair without treating it as evidence against the theorem.
3. **true PASS, non-transporting artifact** — the internal computation checks
   the true inequality, but the emitted transcript does not contain enough
   information for an independent validator to recover it.  Supersede the
   artifact and improve the emitter; never lower the validator.

When a validator rejects a transcript, the default hypothesis is that the
transcript is insufficient.  A threshold or parser requirement may be relaxed
only after an independent proof that the printed artifact still implies the
same preregistered predicate.

## Known aggregate/row asymmetry

The weak-main v4 architecture emits all 576 parameter rows per lane.  Its
validator can check the printed decision endpoint box by box.

The current lambda-3/lambda-4 high-beta inputs instead emit certified aggregate
maxima such as `rho`, `joint_adverse_upper`, `adverse_upper`, and
`relay_margin`.  Their validators rederive the registered inequalities from
those outward aggregate balls, and production/replay plus dependency hashes
protect reproducibility.  They do not, however, expose every underlying cell
inside the transcript.  Thus the aggregate value `0.852989...` cannot be
reconstructed from the transcript alone; reproducing it requires rerunning the
hashed certifier.

This is a documented evidence-granularity asymmetry, not a reason to invalidate
the existing gates.  Future certificate families should prefer per-cell rows
when storage and runtime permit.
