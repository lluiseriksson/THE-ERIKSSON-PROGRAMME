# Weak-main covariance — bounded independent audit (2026-07-28)

**Scope:** algebra and uniform tail inequalities only.  This is not a
production certificate and changes no closure gate.

## Model provenance and failed first attempt

The local bridge authenticated the explicitly selected profile
`masterythief` as `masterythief@gmail.com`.  A first read-enabled request
timed out after 300 seconds and supplied no usable result.

A narrower request returned with `verified_model: claude-fable-5`.  Its first
verdict was rejected because the prompt had not said explicitly that
`KD,KF,GDD,GDF` are four separately integrated moments; it therefore treated
them as pointwise products and claimed a spurious cancellation.

The corrected request also returned with
`verified_model: claude-fable-5`.  Under the correct integral semantics it
withdrew that objection and returned `PASS` for the bounded questions.

## Independently checked resolution

The implementation forms

```text
KD  = integral K D,       KF  = integral K F,
GDD = integral K D (R-r0),
GDF = integral K F (R-r0).
```

Consequently

```text
KD*GDF-KF*GDD
 = KD*(HDF-r0*KF)-KF*(HDD-r0*KD)
 = KD*HDF-KF*HDD.
```

The centering therefore changes the second moment row by a multiple of the
first and leaves the determinant exactly invariant.

For `a=delta*p`, `b=delta*q`, `0<=a,b<=u<1/3`, the bracket in `F` is

```text
B0 = cc*(2-2a-b) + (1-a)*(1-2b).
```

Since `|cc|<=1`, `2-2a-b` lies in `(1,2]`, and
`(1-a)(1-2b)` lies in `(2/9,1]`, one obtains

```text
|B0| <= 3 < 6.
```

Thus `p<=sigma^2/4` gives the implemented conservative bound
`|F|<=6*(sigma^2+tau^2)`.

The audit also reproduced:

```text
root >= sqrt(1-2u),
phase <= -(cmin/2)*(1-u)*sinc(3/5)^2*r^2,
```

and confirmed that independently enclosing the four omitted moment tails is
rigorous under interval evaluation of the determinant.  Ignoring correlations
can widen the enclosure but cannot invalidate inclusion.

## Status after the audit

No algebraic defect was found in the bounded material examined.  Static source
contracts pass.  The decisive Flint/Arb production and replay runs have not
been executed on this desk, so `X_main>=-1/20`, G2, G6, and the manuscript
remain open.
