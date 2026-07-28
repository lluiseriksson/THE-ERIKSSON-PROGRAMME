# K2 fixed-square complex geometry — preregistration

**Registered:** 2026-07-28, before reading the Arb bounds.

**State:** local analytic input only; no K2, K4, S1/S2, gate, or manuscript
promotion.

Freeze

```text
|delta| <= rho = 7/1000
0 <= sigma,alpha <= 12
cos(t/4) >= 1/sqrt(2)
relative companion polynomial terms = 5
Arb precision = 180 bits
```

For `P=sin(sqrt(delta)*sigma/2)^2`, use the absolute Taylor inequality
`|sin z|<=sinh(|z|)`.  The executable must establish strict positive lower
bounds for:

1. `|D|=2|1-P-Q|`;
2. the square-root radicand modulus;
3. `|1+root|` on the branch connected to `root(0)=1`;
4. both finite relative-Bessel polynomials.

The frozen numerical gates are `|P|<0.28`, `|radicand-1|<0.75`,
`|D|>0.8`, `|root|>0.5`, `|1+root|>1.5`, and both polynomial moduli
above `0.99`.

A pass certifies holomorphy/zero-freeness only for the nominal fixed-square
integrand.  It does not supply the complex circle supremum, the true Bessel
companion remainder, or a holomorphic moving-exterior integral.

## Result

All frozen gates pass.  The stress bounds include

```text
|P| <= 0.273893
|D| >= 0.904431
|radicand| >= 0.302181
|root| >= 0.549710
|1+root| >= 1.549710
|A_polynomial| >= 0.998309
|B_polynomial| >= 0.991541
```

The transcript SHA-256 is
`741531976FF143BD29D71A4CF4A0F863B16F984D5A7A95315B243E6FD6036034`
for raw CRLF and
`4354C1859AE0BABEB44E0B76724036636C345FEC406F04955BA767709C0D265B`
after LF normalization.  This is the nominal fixed-square zero-freeness
input only; the two exclusions above remain binding.
