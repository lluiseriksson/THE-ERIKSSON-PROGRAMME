# K4 real-axis remainder probe — pre-registration

**Status:** diagnostic only; no K4, S1'''/S2''', or G6 promotion.

This probe tests the non-complex alternative left open by the regular-ball
preregistration.  It evaluates the scaled carriers at fixed scaled
coordinates and encloses the real-axis combination

```text
2 D g(delta,sigma,tau) + delta D^2 g(delta,sigma,tau),
```

which is the integrand in `H'' = 2 integral Dg + delta integral D^2g`.
The delta interval, spatial boxes, and both main/mirror carriers are enclosed
with the existing fourth-order `TJet` backend.  The probe deliberately omits
the analytic delta=0 continuation and all spatial/phi tails; a finite result
is therefore only a go/no-go signal for the real-axis implementation.

Frozen configuration:

```text
t = 29/10
delta = [1/100, 1/15]
scaled square = [-4,4]^2
grid = 8 by 8
precision = 140 Arb bits
```

The required terminal line is `K4 REALAXIS FINITE`; failures are retained as
diagnostics and do not change any closure gate.
