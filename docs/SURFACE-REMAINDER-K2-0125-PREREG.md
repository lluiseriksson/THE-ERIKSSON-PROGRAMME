# Regular K2 extension to delta 1/80 — preregistration

**State:** `DESIGN`; no theorem load  
**Registered:** 2026-07-15, before any `delta>9/1000` result

## Objective and exact seam

The manifested regular/hybrid union already closes `0<=delta<=9/1000` on
`0<=t<=313/100`; G5 owns the complementary moving wedge.  The candidate
extends only the regular part to

```text
9/1000 <= delta <= 1/80.
```

The right seam stays `t=313/100`: its exact inclusion is controlled by the
old lower endpoint `9/1000`, so enlarging the upper delta endpoint does not
move or weaken the G5 overlap.

## Frozen delta partition and judge

The old core boxes through `9/1000` are retained.  Four new exact core boxes
are appended:

```text
[9/1000,1/100], [1/100,11/1000],
[11/1000,3/250], [3/250,1/80].
```

The annulus ledger uses unit-thousand bands through `12/1000` and the final
half band `[3/250,1/80]`.  The exact-r4 judge, companion coefficients,
moving-band value error and strict formula

```text
theta - |r3+r4 delta| - (|Y4|+C_value) delta^2 > 0
```

are unchanged.

Before a full cover, test born-t indices `0,50,157` at grids
`384,192,384` for the physical-inner ladder

```text
1181/1000, 1183/1000, 237/200, 1187/1000.
```

The first split passing all three witnesses fixes the complete cover.  If no
split passes, the extension is rejected.  Precision, grids, delta endpoint,
or witness set may not be changed in response.  A green three-witness result
is design evidence only; theorem load requires all 158 t units, frozen source
hashes, a union validator, and an independent rerun.

## Domain-contract repair before any witness run

The first copy of the probe imported the `v6` outer-domain helper, whose hard
cap is `9/1000`; it therefore failed mechanically when asked to inspect the
new boxes. This was caught before reading a witness result. The probe now
imports the byte-separate `surface_remainder_delta0_outer_domain_v8.py`
wrapper, which widens only the checked cap to `1/80` and has a regression test
accepting `[1/100,1/80]` while rejecting every larger box. No 0125 witness has
yet been run or promoted.

## First isolated probe outcomes

The first split was evaluated in a clean process with all three frozen
witnesses. Its outward-rounded margins were

```text
index 0: -33640.2619188618248743
index 50: -33695.0838539740038954
index 157: -14173.1865349198708999
```

and the split is therefore rejected at design level. The second split reaches
the first witness but returns `UNRESOLVED: leading term in denominator is not
nonzero`; this is a representation/domain failure, not a sign certificate.
The remaining two preregistered splits have not been promoted or silently
substituted. The probe now supports `--split-index`, so each future split is
run in a fresh process and a worker-pool shutdown cannot contaminate the next
split. No 0125 production cover or theorem load exists.
