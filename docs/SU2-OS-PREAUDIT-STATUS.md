# SU(2) reduced Wilson-kernel lane — pre-audit status

Status recorded 2026-07-31.

## Frozen object

- PR: [#35](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/35)
- audited commit: [`a66b1c7da3c7441e06864e327b5c4efa43e9c79d`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/a66b1c7da3c7441e06864e327b5c4efa43e9c79d)
- annotated tag: [`su2-os-preaudit-pass-a66b1c7d`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/tree/su2-os-preaudit-pass-a66b1c7d)
- tag object: `27db6227abc3d35e2f998e81dcae314d286109b1`
- peeled tag target: `a66b1c7da3c7441e06864e327b5c4efa43e9c79d`
- source checkpoint certified by the transcript: `81118e2e5d64d6dc30c9cf44242b3246d8e222d5`
- source tree: `989802a0db73a6e3af89e013e7c45d22def12656`

The tag message is `internal blind pre-audit PASS; NOT gate 7; gate 7 remains
open`.  It is a citation anchor, not a terminal release.

## Independent pre-audit

The uncontaminated, no-channel adversarial pass returned:

| Criterion | Verdict |
|---|---|
| Overstatement | PASS |
| Vacuity | PASS |
| Physical identification | PASS |
| Global internal pre-audit | **3 PASS / 0 FAIL / 0 BLOCKED** |

This pass does **not** count as Gate 7.  It says only that the current public
claims cover what the code at the audited SHA proves.

Independent mechanical observations included:

- `lake build YangMills.OS.SU2WilsonReflectionEndpoint`: 8182 jobs, exit 0;
- `docs/su2-os/SU2OSOracle.lean`: 16 headlines, exit 0, empty stderr;
- every headline used only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, `sorryAx`, or project `axiom` declaration in the four
  lane modules;
- the `beta/4` coefficient was reconstructed independently from the two Schur
  moments;
- the Wilson sign and nonconstant normalization were checked against
  `S_W = beta (1 - Re tr(U)/2)`; and
- the lane is absent from the transitive `YangMillsCore` import closure, as its
  integration note declares.

## Exact scope

The proved object is the reduced SU(2) Wilson Haar kernel

```text
K_beta(x,y) = exp((beta/2) Re tr(x y^{-1}))
```

and its auxiliary gauge-pure pairing.  The crossing variable cancels and does
not participate in the weight or pairing.  No theorem here:

- derives a physical plaquette factorization from `GaugeConfig`;
- handles two independent transporters across a reflection cut;
- integrates the lane into `YangMillsCore`;
- proves continuum reflection positivity or reconstruction; or
- advances the Clay Yang--Mills statement.

## Known non-blocking infrastructure debts

The audited source is accepted as written, but two regression/provenance debts
remain queued:

1. `scripts/check_su2_os_honesty.py` is a phrase-presence canary, not a
   semantic honesty verifier.  An external mutation reversing the declared
   no-factorization sentence still returned exit 0.  The current source was
   manually reviewed and contains no such contradiction, so this does not
   overturn the pre-audit PASS; it means the guard cannot defend future edits.
2. All 16 LF-normalized hashes reproduced.  Ten raw worktree-byte hashes did
   not reproduce in a clean CRLF checkout.  Raw hashes must remain labelled as
   non-portable observations dependent on EOL checkout state; Git tree/SHA and
   LF-normalized hashes are the portable authorities.

The first negative regression cases for a later guard repair are the two
auditor-discovered mutations: introducing a claim of complete physical
plaquette factorization, and reversing the explicit no-factorization sentence.

## Gate and merge discipline

- Gate 7 remains open.
- Fable may be retried only after independent evidence that its quota renewed.
- Until Gate 7 is decided, do not modify `a66b1c7d`; guard and hash-documentation
  repairs stay queued.
- An audit certifies a SHA, not a branch.  If `a66b1c7d` receives terminal
  certification, merge it by fast-forward or merge commit so it remains an
  ancestor.  Squash/rebase would create an unaudited commit.
- A later guard repair belongs in a new commit and requires its own audit before
  inheriting any terminal verdict.
