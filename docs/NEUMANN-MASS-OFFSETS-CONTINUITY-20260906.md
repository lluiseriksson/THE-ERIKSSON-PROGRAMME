# Actual mass / complete-offset endpoint — continuity 2026-09-06

## Measured result

HOT PASS only, source6d02bcfd4091fb549dd9856f6fa95bb10e854643,
runner77251ad115f7ce5a4a966fe59a6a747d4b0df278. All9 stages exit0,
6 named declarations with exactly propext, Classical.choice, Quot.sound.
Ledger1157; prior v1/v2 failures1155/1156 are independently preserved.

Archive SHA256515f57a9898c8ef1460d353e9b85c6547cd9403514ad9521b39b73d30452382b.
Independent report SHA2561feb8e2622f4e9cde346f078d4bc5985ec3aac66b558b24d6c30fce595c49514.
Folder validation-evidence/neumann-mass-offsets-hot-v3-pass-20260906.
Physical .olean53d4425bada8c3c017f535041d5fbdd52067b8f09de185fd7c74b2e14cc59f49.
The archive contains real commands, exit codes, timings, inputs, outputs and logs.

## Preserved state and next exact operation

Branch codex/cmp116-interacting-wilson-hessian. Current production paths:

- YangMills/RG/NeumannGeneratedMassCompleteOffsets.lean
- YangMills/RG/NeumannGeneratedMassCompleteOffsetsAudit.lean

They are exact HOT-body promotions, PRE-VALIDATION until cold compilation.
Run the existing static promotion checker only under the measured local
30s/512MiB watchdog: scripts/check_neumann_mass_offsets_promotion.py.
It compares against Git blob6d02bcfd, checks all6 audit names and exact two-file
overlay/import guards. Last result exit0/0.4732454s/15966208RSS.

Prepare a new source-pinned cold runner and separate reader before opening
the next runtime. Reuse infrastructure, NOT stale cohort contract fields:
scripts/colab_neumann_complete_fibre_promoted_cold.py and corrected reader
scripts/verify_neumann_complete_fibre_promoted_cold_v2.py are the pattern.
New queue must be exactly:

```text
lake build YangMills.RG.NeumannGeneratedMassCompleteOffsets
lake env lean YangMills/RG/NeumannGeneratedMassCompleteOffsetsAudit.lean
```

These commands run ONLY in fresh Colab CPU/highRAM, never Windows. Fresh
checkout at the production source SHA, no restored project build outputs.
Pin both production Git blobs, exact six names, parent HOT source/archive,
toolchain4.29.0-rc6 and Mathlib07642720480157414db592fa85b626dafb71355b.
Test the actual producer/reader contract field sets, plus adversarial fixtures,
BEFORE opening Colab. The preceding metadata-reader error is already explained
in1153 and must not recur through an old expected field or fixture copy.

Runtime4609d7098347 has been disconnected/deleted after cold and all three
HOT archives were verified locally. At12:59:04UTC no Lean/Lake remained.
Browser tab5 is disconnected; do not run its old complete-fibre cell again.
No monitor, new cold run or CI was started by this unit.

## Scope

This endpoint is literal source-weighted/counting mass as a complete finite
offset sum, with w^depth versus w^(2*depth) kept distinct. The common image
identity shares one translation/parity across that fibre. No extra B^d factor.
It is not physical Green reflection covariance or a Neumann regional inverse.
R1/R3/R4 remain open; consult NEUMANN-INTEGER-TO-PHYSICAL-NEXT-20260906.md.
20/41,TermSource0,window15 compatible but unattained are unchanged.

Preserve unrelated complex-background drafts and the pre-existing deletion
under the older two-level-Poincare evidence folder. Never stage them with
this promotion. No Fable; no exploratory workflow_dispatch; FF-only Git.
