# G2 pair-sum Taylor design (2026-07-20)

This note records a design experiment for the unresolved finite-beta seam. It
is deliberately **not** a certificate and does not change the closure gates.

## Exact object

After the common factor `exp(-8 beta)` is removed, the finite pair identity is

\[
 W_M(\beta,\lambda)=\sum_{1\le m<n\le M}
 (A_mB_n-A_nB_m)\,
 \bigl((m-n)\sin((m+n)\lambda/\beta)
 +(m+n)\sin((n-m)\lambda/\beta)\bigr)(-1)^{n-m+1}.
\]

The implementation keeps the minor `A_m B_n-A_n B_m` intact. This is
important: expanding the two products separately loses the cancellation at the
right edge. The beta jets use the exact scaled-Bessel recurrence, while the
phase is expanded jointly in beta and lambda.

## Reproducible design runs

For `beta in [1629/16,3259/32]`, `M=120`, precision 600, and Taylor orders
`(12,12)`, the finite-mode interval is strictly negative on both adaptive
lambda cells:

| lambda cell | finite Taylor enclosure |
|---|---|
| `[2.98,2.99]` | `[-9e-108 +/- 7.59e-109]` |
| `[2.99,3]` | `[-9e-108 +/- 9.11e-109]` |

The explicit mode-tail bound is about `1e-119` on these cells. The unsplit
cell `[2.98,3]` gives an interval containing zero, which is an interval
dependency failure, not evidence of a sign change.

The first narrow-cell stress test at the actual failed seam uses
`beta=[101.8125,101.81275]` and the point `lambda=1.501`. With 115 modes,
Taylor orders `(50,28)`, and 500-bit Arb, the finite enclosure is
`[-6.62e-109 +/- 2.97e-112]`; after the mode tail it remains strictly
negative. The independent beta/lambda remainder probe (115 modes, remainder
orders `(30,28)`) gives beta remainder about `2.44e-150` and lambda remainder
zero at this point. The production-shaped cell driver is
`scripts/certify_surface_scaled_pair_taylor_cell.py`; it records all four
components and still labels its output one-cell-only.

The first nonzero-width production band is now frozen and replayed:
`beta=[1629/16,407251/4000]`, `lambda=[3/2,151/100]`, 115 modes,
orders `(50,50)`, and 500-bit Arb. Its total upper endpoint is about
`-6.548e-109`; the paired transcript and byte-identical replay are owned by
`run-records/legacy/surface-scaled-pair-taylor-band-20260720.json`. This remains a
single beta/lambda band and is not a global finite-beta bridge.

The beta-dependence can be enclosed without micro-subdivision by a mean-value
form. On the full beta cell `[1629/16,3259/32]` and the same lambda band
`[3/2,151/100]`, the centre, slope, mode-tail derivative, and Taylor-remainder
charges give total upper endpoint `-5.9884206602e-109`. Production and replay
are byte-identical and owned by
`run-records/legacy/surface-scaled-pair-mean-value-cell-20260720.json`. The
mean-value route is still a single local band; it does not close the global
finite-beta bridge or alter G2.

## What remains open

The script converts the exact coefficient derivatives to factorial-divided
Taylor coefficients before multiplying the pair minors. It bounds the
truncated Taylor polynomial and the mode tail only. It
does **not** yet bound the beta/lambda Taylor remainder. Therefore these runs
cannot promote G2, alter `SURFACE-CLOSURE-GATES.md`, remove a `[SLOT]`, or be
quoted as proof of `W_M<0`. A valid promotion needs an independently checked
majorant for all omitted Taylor terms (or an exact derivative interval bound)
and a replay transcript with hashes and software versions. Until then this is
design evidence guiding the adaptive partition.

The companion remainder probe also makes the scale obstruction explicit: on a
20-mode smoke run with orders `(8,8)` it returned lambda and beta majorants of
approximately `4.34e-41` and `3.63e-31`, respectively, vastly above the
`1e-108` sign margin. Raising the orders is mathematically allowed but the
current interval-jet implementation did not finish within the two-minute
replay budget for a 40-mode `(12,28)` run. This is a performance/design issue,
not a certificate or a reason to relax the gate.
