# Eq. (3.51) diagonal-sign no-go — cold FAIL 4

- Mathematical source: `c1e3814bb70036a6d6b61f39e517aab017043a50`
- Runner checkpoint: `a52013246fd15aefb45d169df7fc05783680ddea`
- Notebook checkpoint: `3f7c88aed95a4b197bd814f4668b6327bb3b2ad4`
- Runtime: Colab Pro+ CPU/high RAM, `MemTotal = 53,467,192 KiB`
- Runner SHA-256: `0AE132411D6C8AF1784A1F639D6BD476F61C5DF476A628CDEBD1994C772FB7AF`
- Evidence archive SHA-256: `A45B027FAC93460A6EFD92E2455211A959E4AC5860D7715B9B042BDCB6D9630E`
- Executed notebook SHA-256: `7E4BB8374466522B51F9BAAE9E39AB03F6EFBE76BC6181B6B35EE0D9A4AABEBB`
- Verdict: `FINAL_STATUS=FAIL STAGE=focal TOTAL_SECONDS=318.008`

First real error:

```text
BalabanCMP99Eq351DiagonalSignNoGo.lean:58:42:
unsolved goals
Dstar phi : Matrix (Fin 2) (Fin 2) ℂ
⊢ -(Complex.I • (-(Dstar * phi) + phi * Dstar)) =
    Complex.I • (Dstar * phi - phi * Dstar)
```

The Frobenius instance import repair succeeded: Lean reached the algebraic
proof. The remaining first goal is a purely additive normalization after the
commutator has been expanded. The next repair may state the intermediate
identity `-A + B = -(A - B)` explicitly and rewrite it before simplifying the
outer negation. The later witness goal `Complex.I = -Complex.I ⊢ False` is the
same sign discrepancy projected to entry `(0,0)` and can be discharged by
applying `Complex.im`; it is not a separate mathematical obstruction.

No declaration in the module was compiler-verified. This incident does not
move `20/41`, prove Eq. (3.51)/(3.54), attain window 15, or create a
`TermSource` instance.
