# CMP89 directed endpoint/envelope diagnostic v2 — FAIL

The fresh Colab Pro+ CPU/high-RAM diagnostic checked out exact source
`ef8bf1eab26821c0575cb00701ec0ce804628d4e`, verified the pinned Lean and
Mathlib objects and all four Git-blob hashes, and stopped at the first focal
error.

The three earlier elaboration defects were gone.  The only remaining error
was the final target/source phase subtraction: Lean did not transport the
real subtraction through the complex coercion automatically.  The queue
therefore contains exactly one nonzero focal record; no audit or envelope
stage ran.

- runner: `cmp89-eq246-directed-endpoint-envelope-diagnostic-v2`
- archive SHA-256:
  `39053ECA523A81FEC9C15F333EF46BD88A646C607E80879332CEB52D5BB23A28`
- embedded JSON SHA-256:
  `6609B52D1B6327AFA1FA452AA6EF946E4392D0472B898AC8D192AD8A8E59872A`
- focal time: `1004.629 s`
- status: `FAIL`

This is negative diagnostic evidence, not a seal.  All four source files
remain PRE-VALIDATION, `20/41` is unchanged, and `TermSource = 0` remains
exact.
