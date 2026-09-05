# Eq. (3.51) diagonal-sign no-go — cold FAIL 2

- Mathematical source: `176c0d46ea91ae2325d2cf26a526d76198ed0fa8`
- Runner checkpoint: `4b53c109af3e4ad844ef04e17b8c6a9d652fd07b`
- Notebook checkpoint: `785eff173a9f8cb27549ea73c16993dffc6c7d2c`
- Runtime: Colab Pro+ CPU/high RAM, `MemTotal = 53,467,192 KiB`
- Runner SHA-256: `87C72BF50EED9DBA98D4AC03583C7D7E2BFC0A231C3CCF3B88C41FFB6E1FEA08`
- Evidence archive SHA-256: `6BDBCEF8E4BBFD66513F928862CA29F68DDE4DFAB9D2651242F9A58D389E1D02`
- Executed notebook SHA-256: `B15F3D8BA2FF4D3F7FBD0AAE6679009DEC12863DFA0E59BFCEC6B1B14E6F3C0F`
- Verdict: `FINAL_STATUS=FAIL STAGE=focal TOTAL_SECONDS=365.050`

First real error:

```text
BalabanCMP99Eq351DiagonalSignNoGo.lean:36:16:
failed to synthesize NormedRing (Matrix (Fin 2) (Fin 2) ℂ)
```

The import repair succeeded: Lean reached the declarations. The first missing
premise is the same local Frobenius matrix norm/ring instance already used by
the neighboring Eq. (3.51) matrix modules. Later diagnostics are downstream
of that missing instance and are not treated as independent mathematical
failures. The next source checkpoint may add only the local
`Matrix.frobeniusNormedRing` and `Matrix.frobeniusNormedAlgebra` instances,
then rerun the same focal/audit gate.

No declaration in the module was compiler-verified; the warnings mentioning
`sorry` are elaborator recovery after the failed instance synthesis, not
source `sorry`s. This incident does not move `20/41`, prove Eq. (3.51)/(3.54),
attain window 15, or create a `TermSource` instance.
