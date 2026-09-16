# CMP89 product telescope / physical dictionary cold gate: partial failure

- Date: 2026-09-02
- Runner revision: `cmp89-eq246-product-telescope-dictionary-cold-v1`
- Source checkpoint: `0f7a9292fe43e118c1ad56fdaebc7d41622c6cd0`
- Runner checkpoint: `d8feddd71fbe4774af470d52997a76a38b3152e5`
- Launcher checkpoint: `a5ca368c1ed327bafb2e094c709c452c9e958208`
- Lean: `4.29.0-rc6`
- Mathlib: `07642720480157414db592fa85b626dafb71355b`
- Archive SHA-256: `63974E5EE0E2034716EEF4C461010B7D5F9BC6927E582D9EF2D9A63AC355D4E9`

The fresh Colab Pro+ CPU/high-RAM gate restored no project build graph.
`product_contour_telescope_focal` passed in `1356.178 s`; its exact audit
passed in `19.108 s`. The queue then stopped at
`physical_contour_dictionary_focal`, exit `1`, after `133.249 s`; its audit
did not run.

The original browser tab disappeared after the runner finished, so the
original stdout transcript was not recoverable. A read-only recovery cell
verified the retained evidence archive and its canonical `evidence.json`.
The first compiler error was then reproduced by rerunning only the failed
target in the same retained checkout; `first-error.txt` records it. This is
partial failure evidence, not a compiler seal for the dictionary.

The error is definitional bookkeeping only: the already sealed telescope
uses the literal product measure and the scaled displacement of
`target-source`, whereas the wrapper exposed the named measure and the
difference of separately scaled displacements. No theorem statement,
hypothesis, radius, rate or constant changes in the repair.
