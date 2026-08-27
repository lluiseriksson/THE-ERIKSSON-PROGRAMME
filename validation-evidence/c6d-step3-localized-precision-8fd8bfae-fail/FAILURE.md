# C6d Step3 localized precision — cold failure

- Classification: `FAIL-COMPILER`, first focal target.
- Source checkpoint: `8fd8bfae2b52c540b56676f2837de5af26e65d8c`.
- Runner revision: `c6d-step3-localized-precision-v1`.
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`.
- Runtime: Colab Pro+ CPU / high RAM, opened
  `2026-08-27T01:07:40.458972+00:00`, closed after evidence preservation.
- Failed stage:
  `01_cmp99eq335physicallaplacianinternalcarrier_focal`, exit `1`,
  `1236.449` seconds.

## First real compiler error

`YangMills/RG/BalabanCMP99Eq335PhysicalLaplacianInternalCarrier.lean:45:10`

Lean's `rw [hUV ...]` did not find the literal application of `U` under
`covariantD0CLM`.  The failure is an elaboration/reduction boundary, not a
counterexample to the carrier-locality statement.  The next revision must
expose the one-bond covariant derivative application before rewriting; it
must not alter the theorem statement or add an equality hypothesis.

The same target also reported the later API/elaboration errors
`ContinuousLinearMap.coe_toLinearMap` unknown at line 102 and
`ContinuousLinearMap.toLinearMap_injective` unknown at line 106.  They are
preserved here, but repair remains scoped to this one failed source module.

No audit, downstream focal, root build, PRE-VALIDATION removal, counter
movement, or mathematical seal is claimed from this run.

## Preserved evidence

- Colab archive SHA-256:
  `DC530559A813EF569930E2519B43952B4EE0D957DF9FD02DC91D390181CB5D7B`.
- Executed notebook SHA-256:
  `94DCDB59D06E000EAA53E6D807E3DBE243D210EA765C75DA147F90A54D86231A`.
- Extracted `evidence.json` SHA-256:
  `069103F969EFD2480757B39C4823DF8C2BC61E425B5E0C92F9DA50795FE04E09`.

The executed notebook contains exactly one `FINAL_STATUS=FAIL`, exactly one
failed-stage record, the first compiler error above exactly once, the archive
digest exactly once, and `RUNTIME_RETAINED_FOR_EVIDENCE=1` exactly once.

