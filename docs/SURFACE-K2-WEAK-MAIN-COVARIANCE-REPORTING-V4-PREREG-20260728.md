# Weak-main covariance reporting v4 — preregistration (2026-07-28)

**Frozen before either v4 production run.**

This contract changes only the evidence representation necessitated by
`INCIDENT-WEAK-MAIN-TRANSCRIPT-LOSSY-ENDPOINTS-20260728.md`.  It does not alter
the parameter partitions, quadrature, precision, companion enclosure, tail
charges, grid ladders, or the strict target `X_main > -1/20`.

Every accepted row must have the form

```text
ROW ... grid G KD <diagnostic-ball> KDLOWER <50-digit-lower> XMAIN <diagnostic-ball> XMAINLOWER <50-digit-lower>
```

where `KDLOWER` is `arb(KD.lower()).str(50)` and `XMAINLOWER` is
`arb(XMAIN.lower()).str(50)` from the same judge call.  The independent decimal
validator must:

1. ignore the lossy diagnostic balls for acceptance;
2. require the explicit `KDLOWER` enclosure to be strictly positive;
3. require the explicit `XMAINLOWER` enclosure to be strictly greater than
   `-1/20`;
4. accept only the frozen lane ladder, including grid 96 only in the far lane;
5. retain byte equality, empty stderr, exact partitions, dependency hashes,
   row order, row count, and terminal-scope checks unchanged.

The v3 near transcripts remain diagnostic historical artifacts only.  Fresh
canonical v4 production and replay paths are required for both lanes.
