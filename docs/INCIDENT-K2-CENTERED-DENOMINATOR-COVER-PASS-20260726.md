# K2 centered-denominator cover — favorable diagnostic (2026-07-26)

The preregistered centered carrier passed on the complete sealed t-partition.
Production and replay each contain exactly 158 rows, with no stderr, and are
byte-identical:

```text
production/replay SHA-256: EB34F475C4D5FEF74E655067DEB8AA53B1723EB3096FA2EF3C3B698CC581CC29
worst index: 0
worst uniform K_D floor: 1.1886689192002117770292475135217270040336 +/- 4.51e-41
terminal line: CENTERED DENOMINATOR COVER PASS rows 158 ... DIAGNOSTIC ONLY
python: 3.12.6
git head at run: bc05e23a81134eefe16bd74bf8e55299a46c2744
cover script SHA-256: 496441BBF70D46E4AA71BE96E52FD46BED62E4097546BCE2241417D3C59FAB15
preregistration SHA-256: 765FF8EC980874D2EDB0A5DFE8E2D09AAB3A584F6F73C9B6FF6A18A06703CCC0
```

The frozen parameters were `delta=[9/1000,1/100]`, midpoint `19/2000`,
half-width `1/2000`, spatial grid `192 x 192`, physical split `1181/1000`,
and Arb precision 140 bits. The rows charge the registered outer-domain
coefficient radii and all higher centered coefficients over the half-width.

This is still only a denominator-conditioning result. It does not certify the
R3 residual, the companion/outer-tail budget, `(H_tail)`, K2, G2, G6, or the
manuscript. The next proof-bearing step is to assemble and certify the full
S2-direct residual using this carrier, with an independent production/replay
cover and the role audit.
