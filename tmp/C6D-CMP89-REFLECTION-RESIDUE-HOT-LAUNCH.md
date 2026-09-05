# C6d retained-runtime CMP89 reflection-residue diagnostic

Run only after the active cold C6d gate has reached `FINAL_STATUS=PASS` and
its evidence has been downloaded and verified. Execute once in the retained
runtime after the scale dictionary has been overlaid. This is hot diagnostic
evidence and cannot retire PRE-VALIDATION.

```text
runner object: 3ece7761e8c52afd0265f9374fa2feecfa00cdee
runner SHA-256: 99f22c996c8a0ae7707ca8de3e696ae1fbc21456ccb398a38322caa4d9e8bdab
source object: dd27cd6081b0e276d3059a7fdcfb36fb0f634178
success sentinel: HOT_C6D_CMP89_REFLECTION_RESIDUE_PASS
```

The gate checks the exact `2*m_mu` displacement decomposition and the
half-open-carrier distance comparison. It does not prove the Green image
representation, its absolute convergence, uniform `B0`/`delta0`, or window
15.
