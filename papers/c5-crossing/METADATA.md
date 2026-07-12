# C5 editorial metadata (DRAFT, pre-audit; final at release commit)

## Title

The diagonal Amos-type family at real order: a machine-checked
quantitative crossing classification

## Author

Lluis Eriksson (lluiseriksson@gmail.com)

## Keywords

modified Bessel functions; Bessel function ratios; Amos-type bounds;
Riccati equation; crossing point; Turan-type inequalities;
interval arithmetic; formal verification; Lean 4; Mathlib

## MSC 2020

- 33C10 (Bessel and Airy functions, cylinder functions) — primary
- 26D07 (inequalities involving other types of functions)
- 68V20 (formalization of mathematics in connection with theorem
  provers)
- 65G30 (interval and finite arithmetic) — the certified companion

## Code and data availability

All Lean sources, the certified interval-arithmetic companion script
and its committed transcript, the full run history (seven green
build transcripts, the failed-attempt record, eight charter
amendments), and this manuscript are in the public repository
https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME at the
annotated tag `c5-v1.0` `[RELEASE-SLOT: tag commit id]`.
Verification: `lake build AmosClosure` (Lean
`leanprover/lean4:v4.29.0-rc6`, Mathlib pinned to `0764272048...`),
oracle `lake env lean AmosClosure/Oracle.lean`, companion
`python scripts/c5_crossing_arb.py` (python-flint 0.9.0).  Canonical
artifact hashes: `papers/c5-crossing/RELEASE-MANIFEST.md`.

## AI assistance statement

This manuscript and parts of the formal development were produced
with AI assistance (Claude-family agents) under the repository's
audit protocol: pre-registered charters and amendments in their own
commits before the work they govern, split fabrication/audit roles,
external evaluator checkpoints, and a five-role pre-release audit.
Every theorem is machine-checked in Lean 4 against a pinned Mathlib
with axiom oracle `[propext, Classical.choice, Quot.sound]`; the
numerical companion is a committed interval-arithmetic transcript.
The author reviewed and is responsible for all content.

## Repository / preprint abstract text (plain, no math markup)

For the one-parameter family B(x) = x/(nu+c+sqrt((nu+c)^2+x^2)) of
Amos-type expressions, whose member c = 1/2 is the classical
Amos-type upper bound for the modified Bessel ratio
I_{nu+1}/I_nu, we formalize in Lean 4, at every real order
nu >= 0 over the Gamma-power series, the full classification of the
parameter: uniform upper bound exactly when c <= 1/2, uniform lower
bound for c >= 1, with explicit rational counterexample witnesses
(the classification itself is known mathematics, due to
Ruiz-Antolin and Segura; we claim only the machine-checking).  The
contribution is the regime between the ends: for every nu >= 0 and
c strictly between 1/2 and 1 we prove that the fixed family member
crosses the ratio exactly once on (0, infinity) — a transversal
crossing in an explicit finite window, strictly above an explicit
threshold, with globally determined sign on both sides and a
two-sided scale law; degenerate contact is excluded by an exact
second-derivative identity.  The chain carries the axiom oracle
[propext, Classical.choice, Quot.sound] and no analytic hypothesis
beyond nu >= 0, x > 0; a pre-registered certified
interval-arithmetic companion verifies the crossing phenomenon
independently of the crossing theorems at 30 parameter pairs
spanning the hard regimes, all passing at 128 bits.

## BibTeX (self-entry; identifier fields land post-assignment)

```bibtex
@misc{ErikssonC5,
  author       = {Lluis Eriksson},
  title        = {The diagonal {A}mos-type family at real order:
                  a machine-checked quantitative crossing
                  classification},
  year         = {2026},
  month        = jul,
  howpublished = {Repository release \texttt{c5-v1.0},
                  \url{https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME}},
  note         = {ai.viXra.org identifier pending at the time of
                  this release}
}
```

## Declarations

- Competing interests: none.
- Funding: none.
- Human/animal subjects: not applicable.
