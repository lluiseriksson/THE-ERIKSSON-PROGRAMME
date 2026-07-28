# K2 degree-eight complex geometry at rho=0.0085 — preregistration

A design reconnaissance, performed after noticing that the earlier geometry
certificate stopped at `rho=0.007`, found positive margins at the actual
degree-eight circle radius.  Before a certifying execution, freeze:

```text
rho = 17/2000
fixed square = [0,12]^2
c >= sqrt(2)/2
relative companion degree = 8
Arb precision = 180 bits
```

The certificate uses absolute Taylor-series bounds, not sampled complex
points.  Acceptance requires:

```text
|p| upper < 0.35
|D| lower > 0.64
|1-(1-delta*w)| upper < 0.92
|sqrt(1-delta*w)| lower > 0.30
|1+sqrt(1-delta*w)| lower > 1.30
|P_A| lower > 0.995
|P_B| lower > 0.98
```

Production and replay must agree.  This proves only pointwise branch and
polynomial zero-freeness on the fixed square.  It does not prove that the
integrated KD has no zeros in the disk; that requires a separate Rouché
certificate.  True companions and the exterior remain open.

## Result

Production and replay passed with byte-identical transcripts.  The decisive
outward bounds were:

```text
radicand deviation < 0.906211
root modulus        > 0.306250
1+root modulus      > 1.306250
P_A modulus         > 0.996308
P_B modulus         > 0.981521
```

Both transcript SHA-256 digests are
`EF4D5D1D84980B3F95E31BD5E8A58F8835E813913112D451FE2A4A96E1073BE6`.
The scope remains exactly the preregistered one: integrated KD, the true
companion, and the exterior are open.
