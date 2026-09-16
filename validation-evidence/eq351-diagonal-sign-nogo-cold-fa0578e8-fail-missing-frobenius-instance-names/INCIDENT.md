# Eq. (3.51) diagonal-sign no-go — cold FAIL 3

- Mathematical source: `fa0578e8ab02c5edbee12427c37a01b38ebc32e1`
- Runner checkpoint: `c737f32a2d71a3bb3d86769cb55bb5eeb001f506`
- Notebook checkpoint: `59820256fa43fdea56abc90ca6fd085fbabf9d38`
- Runtime: Colab Pro+ CPU/high RAM, `MemTotal = 53,467,192 KiB`
- Runner SHA-256: `EF395BB2C9AD068C809971EFF43885ECFCBA0C8A7DE2DC3AE8EB2AB3EC8AE4F4`
- Evidence archive SHA-256: `A712B45139EC7E260655EB5EBC0D58A16127BD91F79714A9F04F3BFC9271E3B7`
- Executed notebook SHA-256: `75BC5AB897A9EDAB680DEFD9CA4BCD8C0AD13F131F1F43BB8DCBC808C7135A60`
- Verdict: `FINAL_STATUS=FAIL STAGE=focal TOTAL_SECONDS=224.128`

First real errors:

```text
BalabanCMP99Eq351DiagonalSignNoGo.lean:33:2:
Unknown constant `Matrix.frobeniusNormedRing`

BalabanCMP99Eq351DiagonalSignNoGo.lean:37:2:
Unknown constant `Matrix.frobeniusNormedAlgebra`
```

The previous missing-instance diagnosis was correct, but the repair used two
names that do not exist in the pinned Mathlib revision. Later proof failures
are downstream of these missing local instances and are not classified as
independent mathematical failures. The next repair must locate the actual
Frobenius matrix instances already used by neighboring project modules, or
define the required local instances from existing pinned declarations, before
touching the theorem statements.

No declaration in the module was compiler-verified. This incident does not
move `20/41`, prove Eq. (3.51)/(3.54), attain window 15, or create a
`TermSource` instance.
