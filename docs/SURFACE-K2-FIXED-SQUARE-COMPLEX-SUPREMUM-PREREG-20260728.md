# K2 fixed-square complex supremum — preregistration

**Registered:** 2026-07-28, before any circle arc was evaluated.

**State:** nominal stress-cell design only; no K2, K4, S1/S2, gate, or
manuscript promotion.

Freeze:

```text
t = 29/10
rho = 17/2000
delta_max = 1/1000
fixed square = [0,12]^2
relative companion order = 5
p-over-delta entire-series terms = 18
(spatial grid, theta arcs) ladder = (12,16), (24,32), (48,64)
Arb/Acb precision = 140 bits
```

On every theta arc the probe integrates outward-rounded Acb boxes for

```text
weight, weight*A, weight*G, weight*A*G,
Y = 4*(E[A*G]-E[A]E[G]).
```

The entire `p/delta` series avoids a square-root branch in the complex
delta variable and carries an explicit geometric tail.  The exact heads
through `Y_5` determine the stress-cell available remainder and hence the
required circle supremum

```text
M_required = available / (q^6/(1-q)), q=delta_max/rho.
```

The first ladder level with a strictly positive complex KD modulus lower
bound and `M_sup < M_required` is a design pass.  Exhausting the ladder is a
design failure.  A pass still omits the true Bessel companion remainder, the
moving exterior, and every t-cell other than `29/10`; it cannot restore K2.

## Result

The ladder is exhausted.  Grid 48 resolves the complex KD denominator
strictly (`|KD|>=1.9948`) but the uncentered global covariance enclosure is

```text
M_sup <= 30.3687 > M_required = 0.654168.
```

The terminal verdict is
`K2 FIXED-SQUARE COMPLEX SUPREMUM DESIGN FAIL; EXTERIOR AND TRUE COMPANION OPEN`.
This retires blind refinement of the uncentered four-moment assembly, not the
fixed-square Cauchy strategy.  Transcript SHA-256:
`8DF1F70EFE09FF84ED15A60B9159A0BB03CB2C120C24B441D14C7086C5B8660E`
raw CRLF and
`C3536A7507DEB15EF1E2E3A8B9C6A3077191E09D0A7694177714CD868D6C6DBA`
normalized LF.
