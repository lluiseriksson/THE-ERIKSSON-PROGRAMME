# Incident — K4 sector-aware modulus still fails the reach judge

Date: 2026-07-25. The preregistered polar cover used four radial sectors,
sixteen angular sectors, two-by-two spatial sectors, sixteen `phi` sectors,
and the frozen A1 stress parameters.

The calculation remained finite but did not recover decay:

```text
main   exponent_real_upper   122848.884190396...
mirror exponent_real_upper   101817.560330941...
best tail2                  ~8.8517e44199
headroom_half               0.3621
K4 BALL REACH POLAR REALPART FAIL
```

This rejects the registered polar interval implementation as a usable
regular-ball modulus. It is not a counterexample to K4 and carries no gate or
manuscript load. A successful route must exploit a sharper analytic sector
argument than interval evaluation of the full exponent, or use a different
endpoint representation.
