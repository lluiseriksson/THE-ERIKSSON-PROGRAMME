# C6d ambient/compression cold gate — incomplete runtime loss, attempt 2

Classification: `INCOMPLETE-RUNTIME-LOSS`; this directory is diagnostic
evidence only and is not a compiler or axiom-oracle verdict.

- source checkpoint: `89cb81e0416e6a6fbc66540a8019471bbbcafed5`
- runner checkpoint: `d005bc1949d279864c00d5894d03a731f9fa5546`
- runner SHA-256:
  `4d402751fe0b0bca8ec7fd6ac9b84930841ca00b3a630a7aff3aa61f89eb3d7f`
- notebook checkpoint: `b4e2cf494d810425c94ac23f32a48c994383629d`
- runtime open: `2026-08-28T18:15:09.114774+00:00`
- runtime class reported by the notebook: CPU, 50.99 GiB RAM
- last emitted stage:
  `c6d_ambient_compression_01_balabancmp99regionaldirichletgaugeprecisioncompression_source`
- terminal sentinel: absent (`FINAL_STATUS=PASS` and `FINAL_STATUS=FAIL`
  were both absent)
- cell state when recovered: not running; Colab was reconnecting and the
  original runtime state was unavailable
- preserved notebook SHA-256:
  `2136D5118600A5C3414E86914C6CB3D0C9934A85AE600E77C6207CBEBF228D2E`

The hash gates, toolchain, Mathlib pin, overlay guards and eleven-pair/58
readout manifest gate all passed before the first focal started.  No focal
exit code was emitted.  Therefore no prefix is promoted to evidence and no
`PRE-VALIDATION` mark may be removed from this attempt.

This is the second independent Colab runtime loss at the same first cold
focal.  Repeating the identical Colab route is no longer informative; the
next terminal attempt must use a more durable sanctioned compute plane while
preserving the same source object, cold-checkout condition, manifest and
stop-on-first-error semantics.
