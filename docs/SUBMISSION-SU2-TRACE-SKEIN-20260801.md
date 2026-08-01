# Submission record — finite-SU(2) trace-skein closure

**Submission state:** `SUBMITTED / PUBLIC IDENTIFIER PENDING`  
**Submission date:** 2026-08-01  
**Venue:** ai.viXra, Physics — Mathematical Physics  
**Author:** Lluis Eriksson

## Submitted manuscript

**Title:** *Machine-Checked Finite-SU(2) Trace-Skein Closure for
Makeenko-Migdal Crossing Terms*

The submitted manuscript is a nine-page Lean 4/Mathlib formalization of the
finite-SU(2) algebraic closure used at a loop crossing.  With normalized trace
and normalized anti-Hermitian Pauli directions, it checks the Casimir and
rank-two Fierz identities, the induced crossing contraction, the SU(2)
trace-skein identity, the two direct/reversed reconnections for four oriented
local branches, and an all-order reduction of products of fundamental traces
to single traces.

This is a **new companion paper**, not a replacement for
[ai.viXra:2607.0039](https://ai.vixra.org/abs/2607.0039).

## Frozen identities

| Artifact | SHA-256 | Availability |
|---|---|---|
| Submitted PDF | `A6647D22BFC044ACB060D94030E794CF8C2952B2AE373D2063967282DA2C3BC8` | submitted to ai.viXra; public record pending |
| Audited Lean source ZIP | `387D69A029D4718EEDB5AE5203C06540594066EA349820EF14376A86B6150F44` | retained for direct reviewer supply; not uploaded by ai.viXra |
| Full review packet | `EB1E7D7ED5BDEE56346DB0AFA31E286D75CA11ADEE50262C7810418A83F542D9` | retained as the local review package |

The submitted PDF was rechecked as a nine-page artifact.  The package audit
reported 9/9 top-level hashes and 5/5 nested review-package hashes matching.
The frozen Lean transcript records `Module exit code: 0`, `Audit exit code: 0`,
and `VERIFICATION RESULT: PASS`.

ai.viXra accepts the manuscript PDF but not the supplementary Lean archive.
Accordingly, this record does **not** claim that the ZIP has a permanent public
locator.  Once ai.viXra exposes the public record, this document and the front
doors must be updated with the assigned identifier and the server PDF must be
compared against the frozen submitted PDF.

## Exact scope boundary

The formalized contribution is the finite-dimensional SU(2) group-algebraic
closure from Pauli contraction to single-trace crossing terms.  It does **not**
formalize the Yang-Mills area derivative, the heat-kernel integration-by-parts
producer, planar loop geometry, or the full Makeenko-Migdal equation.  It makes
no claim about the continuum limit or the Clay Yang-Mills mass-gap problem.

