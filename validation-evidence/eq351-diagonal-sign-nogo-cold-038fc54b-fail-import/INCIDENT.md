# Eq. (3.51) diagonal-sign no-go — cold FAIL

- Mathematical source: `038fc54bd1286f9a48ac6944d9b366569fe651bf`
- Runner checkpoint: `9780197a0af15d3fef5cd2c5d5f85174f4326846`
- Notebook checkpoint: `5127eadff28a074175924ce7d48d971d194fad0a`
- Runtime: Colab Pro+ CPU/high RAM, `MemTotal = 53,467,192 KiB`
- Runner SHA-256: `D16D882CC692CAA8E90F7F5090CE5291E6222F07DA4B56BDCF10D56A7AF868AB`
- Evidence archive SHA-256: `FDB22BECFDFAF96AC777C283133167A91ACAE87F38CDAF68F029F4D5EDFD00A7`
- Executed notebook SHA-256: `15009234291B13EDDB5E20D90D5FBC661B817A227AC884A0F17172E50D634D61`
- Verdict: `FINAL_STATUS=FAIL STAGE=focal TOTAL_SECONDS=297.397`

First real error:

```text
Mathlib.Data.Matrix.Notation: no such file or directory
YangMills/RG/BalabanCMP99Eq351DiagonalSignNoGo.lean: bad import
  'Mathlib.Data.Matrix.Notation'
```

No theorem in the sign-no-go module was compiler-verified. The failure is an
invalid import path, before elaboration of the mathematical declarations.
The only authorized repair is to remove that unnecessary import (matrix
notation is already available through the pinned project import closure) and
rerun the same focal/audit gate at a new exact source checkpoint. This
incident does not move `20/41`, prove Eq. (3.51)/(3.54), attain window 15, or
create a `TermSource` instance.
