# Incident — beta-shape transport candidate falsified (2026-07-26)

## Question tested

The residual authoritative beta gap is

```text
[3409/32, 1000/9] = [106.53125, 111.111...].
```

A possible way to transport the already-certified signs at the two ends was
to define

```text
Phi(beta,t) = E'(t) / exp(beta*cos(t))
```

and prove convexity in beta.  Since the divisor is strictly positive, this
would preserve the sign while reducing the gap to its endpoints.

## Reproducible falsification

The probe `scripts/probe_surface_g2_beta_shape.py` evaluates the defining
Bessel series at 80 decimal digits, with `modes=int(beta)+80`, and computes
the beta derivatives with `mpmath.diff`.  At beta=107 it reports a negative
second derivative at every tested point:

```text
t=0.6   d2 = -4.4385035e-40
t=1.5   d2 = -8.7304426e-7
t=2.5   d2 = -5.1170069e+36
t=3.0   d2 = -4.8932478e+45
```

The values are a falsification probe, not interval evidence.  A single
negative row is enough to reject the proposed global convexity lemma; the
four rows make it clear that the failure is not confined to the endpoint
layer.  No G2 or G6 status is changed.

## Disposition

The beta-shape transport route is closed as a candidate.  The residual gap
still needs either a new proof valid in its interior or a certified direct
cover with a separately proved sign-to-`H_tail` relay.  Existing scaled-bulk
timeouts and the killed-bridge TP2 obstruction remain the authoritative
negative evidence against the previously attempted shortcuts.
