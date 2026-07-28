# Diagnostic: seam samples do not establish tangency (2026-07-23)

The proposed boundary-layer route was checked at three sample values using
the scaled Taylor backend (order 40, t-order 45, 220-bit Arb). The beta box
was widened by `10^-8` and each t evaluation used a width below `10^-10`.
The t centre was `pi - 3/(2 beta)` to the recorded decimal precision.

The interval midpoints for `W^J` were:

```text
beta=101.8125  -6.6078764033721027670807430774e-109
beta=105.0     -3.6610146424864376968914479838e-112
beta=111.0     -2.7212663023928106612685221121e-118
```

The three-point finite differences had a consistent positive slope at the
sampled curve. These are diagnostic centre values, not a proof: they do not
certify the exact irrational curve, its derivative, or the full beta union.
They do, however, provide no evidence that the timeout is caused by a proven
double tangency. The analytic boundary-layer lemma therefore remains
uninstantiated, and no gate is promoted from this experiment.
