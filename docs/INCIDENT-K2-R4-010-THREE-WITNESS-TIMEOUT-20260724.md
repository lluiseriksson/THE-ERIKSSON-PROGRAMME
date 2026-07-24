# Incident: tenth-birth K2 three-witness probe timeout

**Scope:** design-only positive-delta K2 lane; no `(H_tail)`, G2, or G6 load.

The pre-existing exact-r4 tenth-birth probe
`scripts/surface_remainder_delta0_r4_extension_010_cover.py` was executed
with its registered three witnesses.  It initialized the six core boxes and
ten annulus boxes, then exceeded the 180-second command limit before emitting
any witness margin.  No pass/fail margin, transcript, replay, or manifest was
produced.  The timeout is therefore an execution/design result, not a sign
failure or certification.

The tenth birth remains outside the authoritative regular lane.  A future
retry must use a newly registered runtime/partition change and may not infer
coverage from this timeout.
