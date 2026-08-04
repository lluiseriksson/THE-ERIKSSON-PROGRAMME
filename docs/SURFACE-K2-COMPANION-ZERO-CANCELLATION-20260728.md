# K2 companion zero cancellation

**State:** exact local lemma; no K2, K4, S1/S2, gate, or manuscript
promotion.

Every relative modified-Bessel companion polynomial used here has exact
constant term

```text
A_N(0)=B_N(0)=1.
```

For the full kernels,

```text
K/H = 8c * root * A_N/B_N,
R = (H/K)D = B_N*D/(8c*root*A_N).
```

At `delta=0`, `D=2` and `root=1`, hence

```text
R(0)=1/(4c)
```

for every truncation order.  Equivalently,

```text
B_N*D - 2*root*A_N
```

is exactly divisible by `delta`.  Therefore a joint companion analysis in
the pointwise coordinate

```text
G=(R-1/(4c))/delta
```

does not inherit an artificial `1/delta` singularity.  The executable checks
both companion families for truncation lengths 1 through 16 and verifies the
formal divisibility algebra.  It does not yet give a numerical bound for the
true companion remainder on a real or complex domain.

The green transcript SHA-256 is
`188A2E49FCDA6B1300179F1A60F2C8109D1EE70F74DAF8BE23211E2DE418C5BF`
raw CRLF and
`2593A62DD7FFF28429C1A6F0262C57E9245B81299360FEE413E8A9CDE1815D0A`
normalized LF.
