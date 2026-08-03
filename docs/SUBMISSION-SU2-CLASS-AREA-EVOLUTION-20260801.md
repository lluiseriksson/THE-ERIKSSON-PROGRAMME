# Submission record — positive-area SU(2) class evolution

**Submission state:** `SUBMITTED / PUBLIC IDENTIFIER PENDING`

**Submission date:** 2026-08-01

**Submission type:** new paper

**Venue/category:** ai.viXra — Mathematical Physics

**Author:** Lluis Eriksson

## Submitted manuscript

**Title:** *Machine-Checked Positive-Area Evolution of the Infinite SU(2)
Class Heat Kernel and Migdal Face Amplitudes*

The submitted eight-page manuscript gives a Lean 4/Mathlib positive-area
calculus for the concrete SU(2) class heat kernel used in two-dimensional
Yang--Mills theory.  It verifies convergence and termwise differentiation of
the infinite spectral jets at every positive time and derivative order,
packages the hierarchy as a smooth map on the positive-time half-line,
differentiates the normalized-Haar two-face Migdal integral, and proves the
exact Casimir area ODE for normalized Wilson characters.

This is a **new sequel**, not a replacement submission.

## Frozen submitted artifact

| Artifact | SHA-256 | Availability |
|---|---|---|
| Submitted PDF, 8 pages | `F0ADD12E208879F02800B44EEAE1E50AACD41EC16133C3C8F1DAC77E2AB836D7` | submitted to ai.viXra; public record pending |

Only the frozen PDF was submitted.  The TeX, Lean source archive, audit, and
review packet are retained for direct review and are not ai.viXra upload
artifacts.  This record therefore makes no claim that those supplementary
files have a permanent public locator.

Once ai.viXra exposes the public record, the front doors must be updated with
the assigned identifier and the server PDF must be compared against the frozen
submitted PDF by page count, title, metadata, and SHA-256.

## Verification and scope boundary

The submitted artifact reports a clean Lean rebuild, 25 public declarations,
no `sorry`, `admit`, or local axiom, and dependencies confined to `propext`,
`Classical.choice`, and `Quot.sound`.

The paper does **not** claim the four-face Makeenko--Migdal crossing equation.
Local Lie-group integration by parts and certified crossing geometry remain
explicitly outside this result.  It makes no claim about the continuum limit
or the Clay Yang--Mills mass-gap problem.
