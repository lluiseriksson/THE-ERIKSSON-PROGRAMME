# Weak-main covariance result and G2 promotion (2026-07-28)

## Canonical transcript pairs

The v4 self-sufficient near and far campaigns both pass their independent
decimal validators.

| lane | domain in `t` | rows | grid counts | pair SHA-256 (LF blob / CRLF checkout) |
|---|---:|---:|---:|---|
| near | `[21/10,31415927/10000000]` | 576 | `24:93, 48:483` | `C093BF9BE0BB9CD4FF45BD280772554CFB511E060FAF3720A9DAB6689786B734` / `54ECC1DC2987291E1EAFF7F179F8B6B626D44BDCF10C3EE17CD3F4A5BC9CBF52` |
| far | `[0,21/10]` | 576 | `24:64, 48:487, 96:25` | `4A032DC53E758E7332E208786E0E7AA84279232CC408F8FDDA799B27F1C7B863` / `F627FE80B3560CA72C686160F988F38D1147AF9E5894916B230A2E3AEC89F8D2` |

Both lanes use `delta in [0,9/1000]`, 18 delta boxes, 32 `t` boxes,
180-bit Arb arithmetic, 12 workers, the true order-four companion, the
certified exterior tail charges, and the strict target

```text
X_main > -1/20.
```

Production and replay stdout are byte-identical in each lane, both stderr
files are empty, every row carries explicit 50-digit `KDLOWER` and
`XMAINLOWER` fields, every printed `KDLOWER` is strictly positive, and every
printed `XMAINLOWER` is strictly greater than `-1/20`.  The validators check
the frozen head `150f439ba30ac1ee915fc92e93ec0b4d708f4349`, all dependency
hashes, exact rational partitions, row order, lane-specific grid ladders, and
terminal scope lines.

The dual hashes distinguish the LF repository blob from a Windows CRLF
checkout.  Git normalization changes representation, not transcript content;
the validator compares production and replay in the representation actually
checked out and parses the same UTF-8 lines on either platform.

## Evidence-margin interpretation

The adaptive runner stops at the first grid that clears the target.  Its
`GRID_COUNTS` and `WORST_LOWER` are properties of the recorded binary and
stopping rule, not mathematical constants or estimates of the analytic
distance to the target.

A preregistered floor-grid-48 diagnostic refined all 157 grid-24 rows at grid
48.  Every refinement improved its lower endpoint.  In particular,
`near:d2:t6` improved from `-0.04987979...` to `-0.01009533...`.  The
combined diagnostic worst then moved to the already-grid-48 row
`far:d17:t31`; a separate non-gate grid-96 check improved that row from
`-0.04989520...` to `-0.01502476...`.  These checks confirm the early-stop
effect but do not define a uniform analytic margin.  The manuscript must quote
the certified strict predicate, not the adaptive worst endpoint or grid
counts.

The inactive `X_main>-1/2` far fallback was never invoked.

## Terminal composition

After both transcript validators passed,
`scripts/audit_surface_g2_weak_terminal_cover.py` reconstructed:

1. the authoritative finite role on `20<=beta<=1000/9`;
2. all G5 lanes on `0<lambda<=3`;
3. `Q>19/20`;
4. both weak-main rectangles and their exact `t=21/10` seam;
5. the common-variable and fixed-gap mirror inputs;
6. the exact near and far relays and third-block remainder;
7. all beta, delta, lambda, and `p=101/200` seams.

It terminated with

```text
G2_WEAK_TERMINAL_COVER_PROVED
```

and did not import the superseded sharp-positive K2, R7/R8, K4, or
S1'''/S2''' route.  This promotes G2.  K4/S1'''/S2''' remain unsolved
research obligations only for the stronger sharp-positive statement; they
carry no load in the Surface Theorem through the weak-main route.

## Final seal

The manuscript rewrite now states and proves the unconditional Surface
Theorem through the weak-main route.  A fresh two-pass pdfTeX build produced
33 pages with zero fatal errors, undefined references, undefined citations,
or overfull boxes.  The build manifest freezes

```text
TeX  a74713d8ace7113422f9bd1d8c5c2ff9067675c3de3375b434ab6d43dbe69335
PDF  0bb2b5eddc41b257e34b8860474c843c8bfcb6923b345c631357b6d481759a42
```

The terminal-prerequisite audit, weak G2 composition, closed-form anchor
gate, and 26 focused tests pass.  The executable final audit terminates with

```text
FINAL-SEAL PASS: terminal gates, manuscript, and PDF are present
```

Thus `G6=SEALED` and the submission state is
`READY_FOR_CLAIM_AUDIT`.
