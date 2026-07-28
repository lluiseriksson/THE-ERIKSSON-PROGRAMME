# Surface candidate validation snapshot — 2026-07-24

This is a provenance record for candidate-only checks run against the current
worktree.  It does not change any gate, manifest status, or manuscript claim.

## Scaled finite-beta sign rows

The existing high-order CWIN=`3/2` units were independently replay-validated
for the adjacent intervals

```text
[78, 78.125], [78.125, 78.25],
[78.25, 79.625] (11-unit seam),
```

with strict negative Arb upper endpoints and byte-identical production/replay
transcripts.  The commands and outputs were:

```text
CWIN3P2 HIGH VALIDATION PASS cwin3p2_high_78_78p125 t_rows 189
CWIN3P2 HIGH VALIDATION PASS cwin3p2_high_78p125_78p25 t_rows 189
CWIN3P2 HIGH SEAM VALIDATION PASS units=11 t_rows 2107
```

These rows remain quarantined sign evidence.  They do not prove the analytic
sign-to-`(H_tail)` implication and do not promote G2 or G6.

The same rescue-300 protocol was then run on the frontier unit
`[102,1633/16]`.  Production and replay each contain 246 adjacent strict-
negative rows and are byte-identical; the independent validator passes.  The
owner is
`run-records/legacy/surface-scaled-bulk-cwin3p2-rescue300-102-102p0625-20260724.json`.
This is still candidate-only evidence: the normalized union now reaches
`1633/16`, while the gaps below `1000/9` and the sign-to-`(H_tail)` relay
remain open.

An adjacent rescue unit `[1633/16,817/8]` also passed the unchanged 300-bit
production/replay contract with 247 strict-negative rows and byte identity.
Its manifest is
`run-records/legacy/surface-scaled-bulk-cwin3p2-rescue300-102p0625-102p125-20260724.json`.
This extends candidate topology only and does not alter the relay or gate
state.

The next adjacent unit `[817/8,1635/16]` passed as well, with 247 strict-
negative rows and byte-identical production/replay.  It remains candidate-only
and leaves the relay and gate state unchanged; see its owner manifest
`run-records/legacy/surface-scaled-bulk-cwin3p2-rescue300-102p125-102p1875-20260724.json`.

## K4 candidate unions

The current regenerations were audited with byte-equality checks:

```text
K4 CURRENT-REGEN T-BOX AUDIT PASS
units 15 cells 34560 domain 3 31415927/10000000
K4 POSITIVE 0305-0500 UNION AUDIT PASS bands 39 cells 89856
K4 CENTERED LOWER UNION AUDIT PASS units 6 cells 55296
```

They remain local/candidate evidence.  The endpoint, overlap, global
`t`-union, and weighted `S1'''/S2'''` obligations are still open.

## Gate interpretation

The independent relay audit still reports `RELAY_LEMMA_UNPROVED` and a
non-complete beta union.  The final seal therefore remains blocked; this file
must not be cited as a theorem certificate.
