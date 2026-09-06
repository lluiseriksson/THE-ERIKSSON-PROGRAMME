# Research news

[YangMills](YangMills/README.md) · [hRpoly status](docs/HRPOLY-STATUS.md) · [Documentation](docs/README.md)

Selected developments with evidence and explicit scope. This is a reader's
guide, not the complete verification ledger. Entries distinguish work in
`main` from results recorded on an active research branch.

## 2026-09-06 — Physical Wilson reflection campaign started

**R1 local geometry compiled and its nine headline oracles passed.**
The first target is the literal four-link plaquette boundary, its reflection
and its dictionary to the existing Wilson holonomy. This precedes the
physical product-Haar identity, reflected positivity and transfer
construction. The [registered plan](docs/PHYSICAL-REFLECTION-PLAN.md) records
acceptance conditions and the fact that a half-tree alone supplies no
nonconstant gauge-invariant test observable. The initial ten-declaration
Colab diagnostic passed. The owner-requested
[ARR paper reuse audit](docs/PHYSICAL-REFLECTION-REUSE-AUDIT-20260906.md)
then identified existing original-edge gauge fixing and the exact conditioned
2D heat-kernel amplitude. R1's duplicate gauge-covariance proof was removed;
the revised source and nine headline oracles passed in a fresh Colab run.
The unchanged core rebuilt at 8466 jobs; the full oracle replay is still
running. R1 remains outside `YangMillsCore`, and terminal reproduction and
independent audit are not claimed. No
physical reflection positivity, transfer construction or mass gap is claimed.

The existing two-free-transporter Haar projection is also part of the reuse
inventory: a centered observable can have zero reflected norm. A candidate
spatial-cylinder continuation must prove a strictly positive norm, not just
nonconstancy. The [CI baseline note](docs/PHYSICAL-REFLECTION-CI-BASELINE-20260906.md)
records nine pre-existing Surface provenance failures; general CI is not green.

The [dashboard](docs/dashboard/) now separates current research updates
from historical proof checkpoints and verified node counts. The
[post-hRpoly audit](docs/POST-HRPOLY-CONTINUUM-AUDIT-20260906.md) distinguishes
the existing fixed-spacing thermodynamic state from the open continuum
construction and records the independent inputs allowed by hRpoly's
terminal checklist.

## 2026-09-05 — hRpoly: source-flow identities and the next physical bounds

**Research branch · PR #29 remains draft.** The campaign records fresh-checkout
checks for the source-flow full-Green residue and owner identities (Addendum
1111). A hybrid amplitude diagnostic also passed (Addendum 1113), while the
full uniform amplitude and physical regional estimates remain open. Today's
signature audit identifies the spacing and fibre-norm obligations needed for
the next step.

The terminal counters remain **20/41 producers**, **0 `TermSource` inhabitants**,
and **window 15 not attained**. These are scoped construction counts, not a
percentage of the Yang–Mills problem solved.

[Read the September status, exact commits and evidence →](docs/HRPOLY-STATUS.md)

**Repository documentation.** YangMills now has a dedicated introduction,
a concise status page, this news log and a documentation index. The update
connects readers to the active branch without importing its unfinished proof
tree or changing the canonical `main` proof-state contract.

## 2026-09-04 — Full-Green foundations and transport checkpoints

**Research branch.** The verification ledger records cold seals for
arbitrary-residue bounds, owner transport, source-flow scalar foundations and
inverse uniqueness (Addenda 1107–1109). Each result has its own exact source
and audit record. These foundations support the physical-bound campaign;
they do not supply the complete uniform `B0, delta0` pair.

[Evidence and remaining limitations →](docs/HRPOLY-STATUS.md#recent-developments)

## Earlier work

| Date | Where to read | Scope |
|---|---|---|
| 2026-08-03 | [Recorded Dobrushin manuscript submission](docs/DOBRUSHIN-MATRIX-V2-SUBMISSION-20260803.md) | Submission provenance, including branch-specific verification; this entry does not establish a later publication outcome |
| 2026-07-28 | [Surface Theorem closure notes](docs/SURFACE-CLOSURE-NOTES.md) | A separate Bessel/surface result; it does not close hRpoly |
| 2026-07-16 | [hRpoly CMP116 reduction v0.3, PR #28](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/pull/28) | Gaussian and physical-constraint reduction with an explicitly open interacting-Hessian frontier at that checkpoint |

For the full history, use the [main verification ledger](docs/VERIFICATION-LEDGER.md)
and the [pinned research-branch records](docs/HRPOLY-STATUS.md#source-snapshot).
No four-dimensional continuum mass gap is claimed; the historical
Clay-distance shorthand remains **~0% (<0.1%)**.
