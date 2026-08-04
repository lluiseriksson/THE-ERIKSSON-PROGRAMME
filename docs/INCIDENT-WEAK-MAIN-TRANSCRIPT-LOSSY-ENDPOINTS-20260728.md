# Incident — lossy Arb endpoint printing in weak-main transcripts (2026-07-28)

The near v3 production and replay completed all 576 boxes, had empty stderr,
and were byte-identical.  The independent validator nevertheless rejected the
pair before promotion.

The runner printed the full `KD` and `XMAIN` Arb balls with `str(18)`.  Arb may
replace a wide ball by a short zero-centred enclosure such as

```text
[+/- 2.99]
```

even when the internally computed lower endpoint of `KD` is strictly positive.
Consequently the transcript did not contain enough decimal information for an
independent parser to prove the two inequalities that had actually been tested
inside the worker.  Accepting the worker's exit status would have weakened the
preregistered self-sufficiency contract, so the v3 pair is preserved under
`superseded-lossy` names and is not evidence.

This is a reporting defect, not a changed mathematical box or target.  The v4
repair prints, in addition to the diagnostic balls, the outward lower endpoints
`KDLOWER` and `XMAINLOWER` with 50 decimal digits.  The validator consumes only
those explicit endpoint fields for the strict tests.  It also recognizes grid
96 in the already preregistered far ladder; the earlier regular expression
listed only grids 24 and 48.

No production or replay run under the repaired format had started when this
incident and the v4 contract were written.
