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
lake build YangMills.RG.CoerciveCovarianceStieltjes
lake build YangMillsCore
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

- Manuscript version: 0.6
- Annotated local release tag: `shift-uniform-ct-v0.6`
- Manuscript commit: `f4dd1ddc668025dd3c187dd02e84834315c32857`
- Pages: 13
- Output: `output/pdf/shift_uniform_combes_thomas.pdf`
- SHA-256: `75614BB276D528ACB3F6F9628B94C81C22D745990B789D632A5BF6732299800F`

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

## Version 0.6 canonical shifted-inverse extension

- Formal canonical-family commit:
  `9f19b2d7c3dbcee1cc95683c9bc1ea29629c6b91`
- New checked module: `CoerciveCovarianceStieltjes.lean`
- Strengthened module: `FiniteDimensionalRealPositiveSqrt.lean`
- Canonical-family target: successful, 8203 jobs, on 2026-08-02
- Fresh `YangMillsCore` build: successful, 8470 jobs, on 2026-08-02
- Focused twenty-six-declaration oracle: only `propext`,
  `Classical.choice`, and `Quot.sound`

Lean now defines the actual family `(K + t^2 I)⁻¹`, proves both inverse
identities, its resolvent identity, the sharp coercivity majorant,
operator-norm continuity, and Bochner integrability.  The physical capstone
proves the `2 / sqrt(c)` exponential kernel bound for the normalized integral
of this canonical family, without an abstract-family or integrability premise.
Positive square roots are also proved unique in finite real dimension.

The one remaining operator-level gap is the exact equality between this
already-localized integral and the separately constructed spectral positive
root.  The physical root certificate therefore remains conditional on that
single identification.  No volume-uniform coercivity, continuum limit, or
Clay implication is claimed.

Remote publication and hosted CI for the release tag are release actions and
are not claimed by this local manifest.
