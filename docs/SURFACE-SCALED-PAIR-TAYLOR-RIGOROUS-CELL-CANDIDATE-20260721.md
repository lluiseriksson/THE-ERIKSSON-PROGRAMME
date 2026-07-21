# Rigorous-accounting pair-Taylor cell — candidate only (2026-07-21)

## Scope

`scripts/probe_surface_scaled_pair_taylor_rigorous_cell.py` evaluates the
cell

* beta: `[1629/16, 1629/16 + 1/16]`;
* t: `[1311/500, 1311/500 + 1/1000]`;
* beta Taylor order 24, t Taylor order 50, 350 Arb bits.

The finite pair polynomial is formed from

`W = 2 sum_{m<n} (a_m b_n-a_n b_m) K_{mn}(t)`.

Unlike the earlier design probe, every absolute remainder uses Arb
`abs_upper()` on the coefficient jets.  The beta remainder uses the certified
order-25 derivative majorant, the t remainder uses order 51, and the omitted
mode term is bounded by positive derivative tails with at least one index
outside the finite cutoff.  No signed `abs_center` sum is used as an absolute
bound.

Script SHA-256:

`5975344F0EF94B5F38049901C1AB3BA993EAEEC5D1059168D43ADACC06A821DF`

## Production output

```
POLY [-1.368453588099678762561289412756e-79 +/- 3.11e-110]
OMITTED_POLY [4.0224630259097055679130044557754204556020092141229943498363975613200198025145852e-191 +/- 3.90e-271]
T_REMAINDER [7.4748843113885338183612595304376310637761073568347502148435179301661778295533128e-101 +/- 4.93e-182]
BETA_REMAINDER [2.2425564799645936037542430148337198790745335659567015757084475109521885901684688e-93 +/- 4.00e-173]
ENCLOSURE [-1.3684535880997e-79 +/- 4.37e-93]
NEGATIVE True
PAIR TAYLOR RIGOROUS-ACCOUNTING CANDIDATE ONLY; NO G2/G6 PROMOTION
```

The independent replay produced the same lines and values byte-for-byte.
The frozen production and replay transcript files are both 534 bytes with
SHA-256 `8ED1CD109B77F3FD69D03F07B40F0A4CF99E1609AC4310521F9209F7121F9D07`;
`scripts/validate_surface_scaled_pair_taylor_rigorous_cell.py` checks this
identity and the negative enclosure.

## Why this is not yet a terminal gate

This closes one local cell only.  A terminal G2/G6 certificate still needs:

1. a preregistered exhaustive beta/t cover of the complete scaled-bulk seam;
2. a standalone proof and validator for the positive scaled-Bessel
   derivative-tail contract over the full beta box;
3. production/replay manifests containing environment hashes and cell rows;
4. the relay from this sign cover to the weighted `S1'''/S2'''` remainder and
   the final real-beta theorem.

Accordingly this document carries no gate load and leaves the manuscript
`DO_NOT_SUBMIT` banner untouched.

## Independent stress-cell witness

The same frozen script and parameters were run on the stress cell
`t=[23069/10000,23069/10000+1/1000]` at the same beta box, orders, and
precision.  The resulting enclosure was

`[-1.13912636450264370488479847567e-63 +/- 6.91e-93]`.

Production and replay files are frozen under
`outputs/surface-scaled-pair-taylor-rigorous-stress-20260721.*.txt`.
They are witnesses only; no union or gate promotion follows from this second
cell.
