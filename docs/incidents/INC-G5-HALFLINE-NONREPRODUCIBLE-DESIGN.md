# Incident: G5 half-line design did not reproduce autonomously

**Opened:** 2026-07-15
**Scope:** five-family right-edge design, `delta in [0,1/125]`
**Evidence status:** no G5 half-line result promoted

## Trigger

Before freezing production, row 74 was rerun in a fresh Python process by
calling only `surface_right_edge_five_family_cover_design`.  The advertised
positive design margin did not reproduce.  The autonomous result was

```text
resolution mixed
P0 [+/- 5.92e-3]
H  [+/- 0.611]
```

and the denominator family `B0` also crossed zero.  Repeating after making
the already proved `v>=3/4`, `1/z<=4/375`, and symmetric `q,-q` contracts
explicit produced the same indeterminate enclosure.  Row 63 and its Fourier
oracle regression remain green; this incident concerns the upper mixed rows.

The first successful repair split the full delta interval into the eight
exact adjacent boxes `[j/1000,(j+1)/1000]`, `j=0,...,7`.  On this partition,
all eight row-74 cells pass on the coarse grid.  Their strict `H` lower
margins range from `0.0538267940` to `0.0640558872`.  Thus the measured cause
is interval dependency across the former single delta box, not a failed
mathematical sign.

## Ruling

The earlier full-cover terminal line was design output without an immutable
transcript.  It is therefore non-authoritative and is withdrawn.  The new
600-cell partition is a fresh design and must complete independently; the
eight-cell adversarial pass does not retroactively validate the old line.
Static review of the identities does not substitute for execution.

## Repair contract

1. Keep the exact chart intersections and symmetric integration in the
   autonomous dependency graph, each with a regression test.
2. Use the eight-box delta partition; require `B0`, `P0`, and `H` to be
   strictly positive in every one of the 600 product cells.
3. Rerun all 600 cells from a committed source state.
4. Validate hashes, configuration, row coverage, and the worst margin.
5. Reproduce the frozen transcript in a separate execution role.

Until all five items pass, the half-line lane is `OPEN_REPAIR`, not a design
pass and not a certificate.
