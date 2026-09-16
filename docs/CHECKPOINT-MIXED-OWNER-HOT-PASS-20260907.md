# Mixed owner: diagnostic PASS, production seal pending

2026-09-07. Branch: `codex/cmp116-interacting-wilson-hessian`.
Base source: `bab8c90d09f7dfeaf7965ce3b0381a96bfabd19e`.

The fresh diagnostic failed before elaborating the draft: the queue omitted
`NeumannIntegerImageCountingKernel.olean`. Its failure archive is preserved in
`validation-evidence/neumann-mixed-owner-diagnostic-v1-failure-20260907/`;
SHA256 `f1fa6792dddc4850009dea28c0e7df122211d791153248b9e6439193e9a12493`.

On the same retained CPU/high-RAM Colab runtime:

- HOT v2 materialized the missing prerequisite (exit 0, 5.026217 s), then
  exposed the first proof error at draft line 85 (`omega could not prove the
  goal`). Recovery `sorryAx` output was rejected, not evidence of a theorem.
  Archive SHA256 `b5d97a81ad989b1588dfacef7bacc06766a8713cc79f67766bdf95fdb4a4de70`.
- HOT v3 stopped in the minimal repro: `Mathlib.Tactic.Omega.olean` does not
  exist. No project proof rerun took place. Archive SHA256
  `acbd5d405324d411d8cd53ac0dd835142a921102aedfc1b71901a5c90739f56a`.
- HOT v4 corrected that import to `Lean.Elab.Tactic.Omega`: minimal repro
  exit 0 / 1.498114 s; corrected draft exit 0 / 4.113973 s. Seven exact axiom
  declarations passed the independent local gate; only permitted subsets.
  Archive SHA256 `551bda077375b7ecf64560ee0a58537ed22356f1676674e6f6508d063117301c`.

HOT archives are under `validation-evidence/neumann-mixed-owner-hot-20260907/`.
The corrected source bytes inside v4 have SHA256
`898441dee7921c9f235e6142a11082f3fc034977c257d4fcee6ab27f0966c6d2`.
The JSON `source` denotes the original Git base; the corrected source is an
explicit overlay included in the archive, not byte-identical to that base.
The only mathematical-source edit replaces a simplifier call by explicit
integer equalities in the false/true branches before `omega`.

Downloads were performed by the assistant using Colab `files.download()`;
local hashes matched. Independent v4 verification took 0.114668 s with
16,965,632 bytes observed peak RSS. No Windows Lean/Lake execution.

Runtime opened 09:53:29.266994 UTC, close requested 10:05:49.738875 UTC
(approximately 12m20s). No Lean/Lake processes remained; `runtime.unassign()`
was followed by the visible reconnect state. The only browser tab was closed.

Next: promote the exact corrected draft into production module and audit,
prepare a cold queue that explicitly builds BOTH imported prerequisites,
validate the reader/transport, then perform a fresh cold seal. Do not repeat
the old launcher or describe this diagnostic as a production seal.

Scope: common-index owner transport and unchanged counting coefficient only.
No physical inverse, uniform B0 or window15 claim. Counters remain 20/41,
TermSource = 0. The broader goal is not complete.
