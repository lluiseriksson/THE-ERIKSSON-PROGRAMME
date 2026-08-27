# C6d Step3 rejected evidence vehicle

This directory preserves a cold Colab computation that reached
`FINAL_STATUS=PASS` for source checkpoint
`38c4d4df881c99b5fe1a32e97f98563bb1356c0f`, but is **not accepted as seal
evidence**.

The fail-closed post-verifier rejected the downloaded notebook before the
selective seal:

```text
C6D_STEP3_NOTEBOOK_CODE_CELL_COUNT=5 WANT=1
```

The runner archive itself reported SHA-256
`900ef8042b12f732efb6ebaa68cb1017c46ffe98a6e27343751059c409cdf1a5`.
The executed notebook is retained byte-for-byte so the rejected vehicle and
its computed prefix remain auditable.  No PRE-VALIDATION marker may be removed
and no C6d declaration may be called sealed from this incident.  The accepted
replacement must execute the canonical one-code-cell notebook at checkpoint
`214746e0370af6c348537ac0ab08c2d14392c8ea` and pass the unchanged verifier.

