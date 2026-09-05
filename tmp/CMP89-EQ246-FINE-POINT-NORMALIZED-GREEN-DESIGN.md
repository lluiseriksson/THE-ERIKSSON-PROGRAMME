# CMP89 Eq. (2.46): fine-point normalized Green — next brick

Status: promoted PRE-VALIDATION at source checkpoint
`73dec7a5f4ae7efaaf9a28ee38df5e7e0c5d6f0d`. The prerequisite fine-point
source gate was cold-sealed selectively in `f0f76668`; this brick remains
outside the import graph until its own compiler and axiom gate passes.

## Source-facing endpoint

The next producer starts from the already constructed literal objects:

- `cmp89Eq243NormalizedFinePointSource`, normalized against the `xi^4`
  counting measure in CMP89 (2.43);
- `cmp89Eq246StabilizedFinePointSourceSolution`, constructed internally by
  the complete diagonal-plus-rank-one solution of (2.46);
- `cmp89Eq246PhysicalFineToFineGreenIntegrand`, with distinct fine target
  and fine source endpoints and no `Q_j^*` source factor;
- `cmp89Eq249NormalizedFourDimensionalBrillouinIntegral`, which keeps the
  printed `(2*pi)^(-4)` normalization literal.

The intended new physical object is the normalized Brillouin integral of the
fine-to-fine integrand.  It is not the already sealed typed `G_j Q_j^*`
kernel from (2.48).

## Finite proof chain

1. Prove complex differentiability of every component of the complete
   fine-point solution under exactly the surviving noncentral-fine-symbol,
   stabilized-denominator and central-pair gates.  The common-radius theorem
   must discharge those gates; no free `hrow` may reach the consumer.
2. Restrict to the real Brillouin cube and prove continuity, hence
   integrability, of the complete fine-to-fine integrand.  Merely defining a
   Bochner integral is not a substitute for this proof.
3. Define the normalized fine-to-fine Fourier Green with the existing
   `(2*pi)^(-4)` integral and prove its literal unfolding theorem.
4. Integrate the finite alias-fibre equation.  Any exchange of the finite
   matrix sum with the integral must be a theorem using finite linearity, not
   a new Fourier/operator dictionary hypothesis.
5. Stop at the exact Fourier solution.  The inverse-transform/operator
   dictionary and the multiple-reflection identity (2.42) remain subsequent
   named bricks.

## Rejected shortcuts

- no independently supplied family of fibre solutions;
- no free equality from the normalized integral to the physical Green;
- no same-scale reuse of the typed (2.48) `G_j Q_j^*` kernel;
- no insertion of an averaging column into the fine point source;
- no definition of integrability by an assumption;
- no claim of (2.42), regional `B0`/`delta0`, window-15 attainment, terminal
  rows or `TermSource` from this brick.

## Acceptance gate

- source and audit modules carry one `PRE-VALIDATION` notice each until a
  fresh Colab CPU/high-RAM gate passes;
- overlay/import-prefix guards cover exactly the promoted files;
- the audit names every new source-facing theorem and accepts only
  `{propext, Classical.choice, Quot.sound}` (or a strict subset);
- the seal removes only the notices justified by that evidence;
- hard counters remain `20/41` and `TermSource = 0`.
