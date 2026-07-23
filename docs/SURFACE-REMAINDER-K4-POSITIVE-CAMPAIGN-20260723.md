# K4 positive-band campaign — candidate result (2026-07-23)

## Result

The preregistered positive-band campaign for `delta in [0.0305,0.0500]` was
regenerated with the current dependency tree for all 39 bands
`k4p_00` through `k4p_38`.  Each band passed both production and independent
replay.  The per-band validators then passed for all 39 bands, with 2,304
cells per band.  The aggregate audit passed with:

- 39 bands;
- 89,856 cells;
- byte-identical production/replay parsed records;
- worst reported budget fraction
  `0.501826306922 +/- 4.19e-13` (`k4p_00`, `nuD_main`).

The commands were:

```text
python scripts/validate_surface_remainder_k4_positive_0305_0500.py --unit k4p_XX
python scripts/audit_surface_remainder_k4_positive_0305_0500.py
```

The aggregate audit ended with:

```text
K4 POSITIVE 0305-0500 UNION AUDIT PASS bands 39 cells 89856
CANDIDATE ONLY; NO K4/G2/G6/S1'''/S2''' PROMOTION
```

## Scope and non-promotion

This is a coherent candidate result, not a terminal theorem certificate.  The
preregistration explicitly forbids promotion from this campaign alone.  It
covers one positive-delta interval and the local box budget; it does not prove
the regular endpoint patch, uniformity in `t`, a global weighted
`S1'''/S2'''` judge, or the relay implication needed by G2.  It therefore does
not change the closure board, G2, G6, the manuscript banner, or any `[SLOT]`.

The current final-seal and relay audits remain the authoritative independent
checks.  At this run they still report `G2 =
REGULAR_008_AND_HYBRID_009_CERTIFIED`, `G6 = BLOCKED`, and
`RELAY_LEMMA_UNPROVED`, with nonempty finite-beta relay gaps.

## Provenance note

The transcripts were regenerated against worktree head
`23663e7f3b726bf504d4ce31b52bcbd99a818a5c`.  They are intentionally left
outside the terminal promotion path until an owner manifest is produced,
committed, and audited under the separate-fabricator/reviewer rule.  In
particular, this note does not mutate the older preregistered manifest or
retroactively make it current.
