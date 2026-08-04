# Dobrushin matrix paper — viXra v2 submission record

Date recorded: **2026-08-03**

Operation: **v2 replacement submitted to viXra**

Moderation/publication outcome: **not recorded here**

## Submitted paper

Title: *The Row Sums Were the Method, Not the Theorem: a Machine-Checked
Chain from a Positive Weight to Exponential Decay of Correlations, and a
Misattributed Uniformity Wall*

- Edition: v5.5 manuscript, used as the viXra v2 replacement
- Length: 20 pages
- Paper commit: [`e68b821f7b5a766551c7e249706aaf7dc4d0eb66`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/e68b821f7b5a766551c7e249706aaf7dc4d0eb66)
- Verified source anchor: [`8e8375d3415575e997765e61515e1a8af283df97`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/commit/8e8375d3415575e997765e61515e1a8af283df97)
- [Exact PDF at the paper commit](https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/e68b821f7b5a766551c7e249706aaf7dc4d0eb66/papers/dobrushin-matrix/dobrushin_matrix.pdf)
- PDF SHA-256: `3A0DDBCDB60E7E5A2EAA33E1A5D458312FEBE0B46F3A5481FA5287BF09E21888`
- PDF size: 424,277 bytes
- [Repository ZIP at the paper commit](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/archive/e68b821f7b5a766551c7e249706aaf7dc4d0eb66.zip)

The SHA-256 and byte count above were recomputed from the Git blob
`e68b821f7:papers/dobrushin-matrix/dobrushin_matrix.pdf`; they are not copied
from mutable local output.

## Reproduction evidence carried by the paper

The final fresh-clone Colab run recorded:

- all ten numerical judges exiting zero in normal and optimized modes before
  compilation;
- both Dobrushin lane modules building from a clean clone with their dependency
  chain;
- `Build completed successfully (8475 jobs)` for the full core;
- repository-wide oracle exit code zero over 2,980 reports, 76 belonging to
  this lane, with zero `sorryAx` and axiom union exactly
  `{propext, Classical.choice, Quot.sound}`.

The full record is in verification-ledger Addenda 583–590 on the paper branch.
The final repair to the sibling `SpatialReconstruction` module changed seven
proof/elaboration defects across three commits and did not change theorem
statements. That sibling paper's mathematical audit remains a separate matter.

## Scope and integration boundary

This is a submission record, not an integration claim. At the time this record
was written, `e68b821f7` was the head of remote branch `d3-closure` and was not
an ancestor of `main`. Consequently the 8,475-job and 2,980-report measurements
must not replace the canonical `main` checkpoint until the exact source history
is integrated and independently checked under the repository's merge rules.

The earlier 11-page `dobrushin_matrix3.pdf` at `c3d8e32d` is a superseded
ancestor of this manuscript. It must not be used as the viXra v2 replacement.
The v5.5 paper absorbs that earlier three-theorem version and closes the
formerly open Dobrushin comparison step; it does not prove a continuum limit,
a Yang–Mills mass gap, or a volume-family theorem beyond the hypotheses and
finite cells printed in the paper.
