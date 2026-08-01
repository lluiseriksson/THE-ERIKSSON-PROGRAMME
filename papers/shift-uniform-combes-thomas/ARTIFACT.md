# Shift-uniform Combes--Thomas artifact manifest

Status date: 2026-08-01

## Immutable formal source

- Formal artifact commit: `b542b3f2f066b60a914977f2a50160e403a53367`
- Parent: `81e9cf064d6771f986978ccffb96018c78b5e459`
- Branch at creation: `codex/stieltjes-root`
- Lean: `4.29.0-rc6` (`00659f8e6071d7e46131ed643bf8003b99b044e9`)
- Mathlib: `07642720480157414db592fa85b626dafb71355b`

The formal artifact commit contains exactly the two edited theorem modules,
their oracle registrations, and verification-ledger Addendum 570. The paper
source and rendered PDF are kept in the subsequent manuscript commit so that
the paper can cite the already-fixed formal object without a circular hash.

## Reproduction commands

Run from the repository root:

```text
lake env lean YangMills/RG/PhysicalCoerciveCombesThomas.lean
lake env lean YangMills/RG/PhysicalCoerciveCombesThomasInverse.lean
lake build +YangMills.RG.PhysicalCoerciveCombesThomas:olean
lake build +YangMills.RG.PhysicalCoerciveCombesThomasInverse:olean
```

All four commands completed successfully on 2026-08-01 after the formal
artifact commit was created. The targeted axiom oracle for the seven core
declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Manuscript artifact

- Manuscript version: 0.2
- Pages: 11
- Output: `output/pdf/shift_uniform_combes_thomas.pdf`
- SHA-256: `BCC7705FE4A8F5A934591E07DD2AD9D703A08118B57FB3C06EA871C49F845F0E`

The Stieltjes formula and localized inverse-square-root corollary are proved at
paper level. They are not declarations in the formal artifact commit. The
positive real continuous-linear-map root, its integral identification, its
single-bond kernel bound, and the final
`PhysicalLocalizedCovarianceRootCertificate` remain open.

Remote publication and hosted CI for the two commits are release actions and
are not claimed by this local manifest.
