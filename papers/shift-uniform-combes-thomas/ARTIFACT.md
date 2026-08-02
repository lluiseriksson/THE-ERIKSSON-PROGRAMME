# Shift-uniform Combes--Thomas artifact manifest

Status date: 2026-08-02

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
lake build YangMills.RG.FiniteDimensionalRealPositiveSqrt
lake build YangMills.RG.CoerciveCovariancePositiveSqrt
lake build YangMills.RG.PhysicalGaugeCovariancePositiveRoot
lake build YangMills.RG.StieltjesKernelIntegration
lake env lean papers/shift-uniform-combes-thomas/ShiftUniformOracle.lean
```

All four commands completed successfully on 2026-08-01 after the formal
artifact commit was created. The targeted axiom oracle for the seven core
declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
The exact focused output, including one wrapper timeout followed by a clean
successful repetition, is recorded in `VERIFICATION-TRANSCRIPT.txt`.

## Positive-root extension

- Formal root commit:
  `bd11e55f9cfe572d5ec4200f49c45339df4e3c03`
- New checked modules:
  `FiniteDimensionalRealPositiveSqrt.lean`,
  `CoerciveCovariancePositiveSqrt.lean`, and
  `PhysicalGaugeCovariancePositiveRoot.lean`
- Root target builds: successful on 2026-08-01
- Focused root oracle: only `propext`, `Classical.choice`, and `Quot.sound`

The extension constructs the positive real continuous-linear-map root and
derives its exact square, positivity, symmetry, and the algebraic fields of the
physical root certificate. The Stieltjes identification and localized root
kernel bound remain open. Two full `YangMillsCore` rebuild attempts timed out
after 10 and 20 minutes without a Lean diagnostic; this manifest claims the
successful module targets, not a fresh successful full-core rebuild.

## Manuscript artifact

- Manuscript version: 0.5
- Annotated local release tag: `shift-uniform-ct-v0.5`
- Manuscript commit: `76f858a24418daff2d4f11d6f6cbb7e6806d3c2b`
- Pages: 12
- Output: `output/pdf/shift_uniform_combes_thomas.pdf`
- SHA-256: `C261C9C5B046737548672E5259800227A6D84BBE1FDD0C722B3346E686411689`

The detailed administrative status of thirteen other author-corpus records is
kept in `PUBLICATION-PROVENANCE.md`, outside the mathematical manuscript. It is
not a premise of the theorem.

## Version 0.5 Stieltjes-integration extension

- Formal integration commit:
  `73179102f2bc2cdec77b4b448cf116b5128fdd4f`
- New checked module: `StieltjesKernelIntegration.lean`
- Strengthened modules: `CoerciveCovariancePositiveSqrt.lean` and
  `PhysicalGaugeCovariancePositiveRoot.lean`
- Focused target builds: successful on 2026-08-02
- Focused eighteen-declaration oracle: only `propext`, `Classical.choice`, and
  `Quot.sound`

Lean now proves the scalar improper integral, the exact Bochner transport from
an integrable `A / (c + t^2)` kernel family to `A / sqrt(c)`, its exponential
specialization, and the sharp coercive root norm `sqrt(c⁻¹)`.  The remaining
operator-level gap is to prove integrability of the canonical shifted inverse
and identify its normalized integral with the formal spectral root.  Therefore
the final `PhysicalLocalizedCovarianceRootCertificate` is reduced further but
still conditional on that identification/root-kernel bridge.

Remote publication and hosted CI for the release tag are release actions and
are not claimed by this local manifest.
