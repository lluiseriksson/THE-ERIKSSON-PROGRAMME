# CMP89 physical fine-kernel v2 infrastructure failure

- runner revision: `cmp89-eq246-directed-normalized-physical-fine-kernel-cold-v2`
- runner commit: `8de7bbc980f58a6ab7152537a701251138cae4b7`
- launcher commit: `d2569b2ae3bd5126048aed70337458c29e73d9c7`
- exact source: `1a53d2755b05419f2401c5d839fc9a6cffdd0c2d`
- result: `FINAL_STATUS=FAIL`
- first failing stage: `lake_update`
- failing exit: `1` after `0.999 s`
- archive SHA-256: `d244e2a9bf746d3922784846ff11bca1998f4ce53054aba45aa37174d371c58a`
- evidence payload SHA-256: `a6d67110c4f8a2fff19569765b7f1a2c0fb6218341303267dd9ebb02afa3157`
- executed notebook SHA-256: `ce30844213781b5bd53317fa61593f051910600f608bc16c6666e54002090a93`

The fresh Colab CPU/high-RAM session verified runner transport, the official
toolchain asset, exact checkout, both source blobs, and both textual guards.
It then failed before dependency materialization because `lake update` could
not complete Mathlib's external `git` clone (`git` exit `128`). No Lean focal
or audit target ran, so this archive contains no mathematical evidence about
the source repair.

The fail-closed local verifier accepts the environment and source pins, the
successful prequeue prefix, and the single nonzero terminal `lake_update`
record. The same exact source/runner may be retried in a fresh session without
a mathematical change.

PRE-VALIDATION remains. Counters remain `20/41`, window 15 remains compatible
but unattained, and `TermSource = 0` remains exact.
