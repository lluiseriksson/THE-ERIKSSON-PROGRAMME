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
The version-0.2 manuscript commit is
`25f532eaeecbfb66ee146e264953cde0e2e0ea29`. Version 0.3 is identified by the
annotated release tag `shift-uniform-ct-v0.3` and is distributed as a complete
Git source archive in addition to the PDF.

- Version-0.3 source-package commit:
  `cba2b5d705bfadc377a9c04293a57a6bfcb82c19`
- Exact archive: `shift-uniform-combes-thomas-v0.3-source.zip`
- Archive entries: 7,350
- Archive SHA-256:
  `1B5EAB37038E071F1E3A1A1BA263D93048828EA079950273BF915B4605897823`

Version 0.3.1 is a documentation-only manuscript revision that adds these
identifiers to the PDF. It does not modify either Lean theorem module.

## Reproduction commands

Run from the repository root:

```text
lake env lean YangMills/RG/PhysicalCoerciveCombesThomas.lean
lake env lean YangMills/RG/PhysicalCoerciveCombesThomasInverse.lean
lake build +YangMills.RG.PhysicalCoerciveCombesThomas:olean
lake build +YangMills.RG.PhysicalCoerciveCombesThomasInverse:olean
lake env lean papers/shift-uniform-combes-thomas/ShiftUniformOracle.lean
```

All four commands completed successfully on 2026-08-01 after the formal
artifact commit was created. The targeted axiom oracle for the seven core
declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
The exact focused output, including one wrapper timeout followed by a clean
successful repetition, is recorded in `VERIFICATION-TRANSCRIPT.txt`.

## Manuscript artifact

- Manuscript version: 0.3.1 (documentation-only)
- Pages: 10
- Output: `output/pdf/shift_uniform_combes_thomas.pdf`
- SHA-256: `FC89026475CC959B2C2F4637F020DACB3BD183CF7DE1E7E8D7F7D9C68CFB2C86`

The detailed administrative status of thirteen other author-corpus records is
kept in `PUBLICATION-PROVENANCE.md`, outside the mathematical manuscript. It is
not a premise of the theorem.

The Stieltjes formula and localized inverse-square-root corollary are proved at
paper level. They are not declarations in the formal artifact commit. The
positive real continuous-linear-map root, its integral identification, its
single-bond kernel bound, and the final
`PhysicalLocalizedCovarianceRootCertificate` remain open.

Remote publication and hosted CI for the release tag are release actions and
are not claimed by this local manifest.
