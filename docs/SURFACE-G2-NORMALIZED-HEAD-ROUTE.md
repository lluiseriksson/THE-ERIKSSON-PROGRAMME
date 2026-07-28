# G2 normalized-head route (design proposal)

**State:** `DESIGN_ONLY`; no theorem load  
**Registered:** 2026-07-16

The scaled moving-bulk driver loses sign because it majorizes the unnormalised
sixth-order Wronskian remainder before quotient cancellation.  The regular
coordinate already exposes the cancelled carrier

\[
 Y(\delta,c)=T(c)+r_2(c)\delta+r_3(c)\delta^2+r_4(c)\delta^3+…,
 \qquad \delta=\beta^{-1},\quad c=\cos(t/4).
\]

The replacement judge must bound this normalized carrier directly.  It may
not infer a bound by dividing two independently enclosed moment intervals.

## Exact head and an a-priori sign margin

On the complete bulk domain, \(c\in[\sqrt2/2,1]\).  The exact first
coefficients are the registered \(T,r_2,\ldots,r_6\) in the manuscript.  A
new exact-series derivation also gives the design candidate

```text
r7(c) = (2085412 c^14 + 6775103 c^12 + 11636676 c^10
         - 52644752 c^8 + 1046587520 c^6 - 2880628992 c^4
         + 2254849024 c^2 - 513015808)/(33554432 c^21),
```

and the next candidate

```text
r8(c) = (19936 c^16 + 119595 c^14 + 323054 c^12 + 637408 c^10
         - 12653880 c^8 + 104539328 c^6 - 219463616 c^4
         + 153352416 c^2 - 33064504)/(524288 c^24).
```

These two expressions are candidates only until independently regenerated and
validated.  The algebraic sign and coefficient-sum audit is now executable in
`scripts/verify_surface_g2_normalized_head.py` (and its pytest wrapper); it
still carries no tail or theorem load.  The following sign facts are exact
and require no numerics:

* \(T(c)\ge \sqrt2/4\), since \(T'(c)=(3-4c^2)/(8c^4)\) and the two
  endpoints are \(\sqrt2/4\) and \(3/8\).
* \(r_2>0\): its numerator is the concave polynomial
  \(-8u^2+15u-4\), \(u=c^2\in[1/2,1]\), positive at both endpoints.
* \(r_3>0\): its numerator is concave on this interval and has endpoint
  values \(205/4\) and \(75\).

Absolute coefficient-sum bounds at \(c=\sqrt2/2\) give

```text
|r4| <= 243.063, |r5| <= 2215.05, |r6| <= 23674.5,
|r7| <= 292106, |r8| <= 4095108.
```

Consequently the charged head through \(r_8\) is below `0.060` at
\(\delta\le1/20\), while \(T\ge0.3535\).  This is a design margin, not a
certificate: the missing step is a uniform tail bound for \(r_9,r_{10},\ldots\).

## Required executable work

1. Regenerate `r7` and `r8` with a fresh exact-series script and independent
   symbolic-zero checks.
2. Prove a complex-\(\delta\) disk bound for the *compensated* regular carrier
   (root floor, Bessel companion denominator, and localized complement), e.g.
   radius `R=1/10`.  A Cauchy estimate on that disk must bound the tail after
   `r8`; no coefficient may be divided after independent interval formation.
3. Add an Arb validator with a strict inequality
   `T + r2*delta + ... + r8*delta^7 - tail_lower > 0` on every frozen
   `(delta,t)` birth.  Repeat the run from an independent implementation before
   promoting any G2 interval.

Until all three steps and the exhaustive adjacency/provenance audit pass, the
G2 slot remains open and the manuscript must retain `DO NOT SUBMIT`.

## Fresh algebraic replay (2026-07-17; no promotion)

The registered exact-series design engine was executed afresh under the
current dependency tree.  It reproduced the displayed `r7(c)` and
`r8(c)` expressions exactly; the transcript is
`scripts/surface_remainder_delta0_r7_design_transcript.txt` and records the
script hash.  The replay confirms only the algebraic head.  It does not close
the missing complex-disk/Cauchy tail, the positive-delta partition, K2, or G2,
so the status above is unchanged.

## Candidate frontier continuation (2026-07-21; no promotion)

The scaled pair mean-value driver was continued across two exact adjacent
beta cells,

```text
[6527/64,6529/64], [6529/64,6531/64]
```

with the frozen λ-domain `[3/2,19/10]`, 115 modes, order 50 in both
parameters, and 500 Arb bits. Production and independent replay are
byte-identical on both cells; the executable cover audit reports two cells
and strict negative `total_upper` on each. The manifest is
`run-records/legacy/surface-scaled-pair-mean-value-cover-beta6527p64-6531p64-lambda150-190-20260721.json`.
This extends only the candidate inventory. It supplies no complex-disk tail,
no exhaustive finite-β union, no scaled-tail splice, and no G2/G6 promotion.
