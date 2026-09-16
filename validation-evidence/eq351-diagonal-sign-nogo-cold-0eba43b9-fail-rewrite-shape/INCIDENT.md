# Eq. (3.51) diagonal-sign no-go — cold FAIL 5

- Mathematical source: `0eba43b922020571637b09e5dd25e3cd89ecbffd`
- Runner checkpoint: `208beee5c4e8ee4750c8c32babc29e4bb7ef6a02`
- Notebook checkpoint: `4ce7aa9b8673ede960cab5d71ab0e5efba2505ac`
- Runtime: Colab Pro+ CPU/high RAM, `MemTotal = 53,467,192 KiB`
- Runner SHA-256: `DF92826FED19D66241565F6C224E951ED13E7A90DE1EFDD3ED53F62A4008473B`
- Evidence archive SHA-256: `14F182858608D829574B27A0B1FC83FCB25791BE8F0A0B0C7C71BCE9C3218D26`
- Executed notebook SHA-256: `D4D9744A5D119DD6A1642E4422F26E88A72E13A82A326098F489C020977732CF`
- Verdict: `FINAL_STATUS=FAIL STAGE=focal TOTAL_SECONDS=417.303`

First real error:

```text
BalabanCMP99Eq351DiagonalSignNoGo.lean:63:6:
Tactic `rewrite` failed: Did not find an occurrence of
  -(Dstar * phi) + phi * Dstar
in
  -(Complex.I • (-(Dstar * phi) - -(phi * Dstar))) =
    Complex.I • (Dstar * phi - phi * Dstar)
```

The explicit algebraic identity is correct, but `simp only` normalized the
left commutator as `-A - (-B)` rather than `-A + B`, so the subsequent rewrite
was shape-dependent. The next repair replaces this literal rewrite with the
module normalizer, treating the two noncommutative matrix products as atoms.
No statement, sign convention, witness, or constant changes.

No declaration in the module was compiler-verified. This incident does not
move `20/41`, prove Eq. (3.51)/(3.54), attain window 15, or create a
`TermSource` instance.
