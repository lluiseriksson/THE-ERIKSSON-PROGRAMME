# Fixed transverse product-slice obstruction (257)

The analytical proof at frozen commit `fed201fd10f952a04e638c324dc0e1359711911a`
extends the single-grid counterexample256 to every product-slice partition
whose transverse interval cutsets are fixed across all longitudinal slices.
Cut locations may depend on n and need not be separated or balanced.

For q transverse cells, L=log((n/4+1)/3), 4|n, n>=32, a=c/48 and H=cn^2,
the proof constructs an explicit real, nonzero actual coexact field annihilating
all original component means when L>=2^22 q. Its original weighted energy is
at most7c/16 times its squared counting norm. Consequently recovery in this
class requires q>L/2^22, or more than3nL/2^22 full channel1 rows. This is a
necessary order n log n count **only in this restricted class**.

The key improvement over the earlier unreviewed product-cutoff proposal is
taking the minimum of the one-corner logarithmic cutoffs. Both energy and
norm deficit then grow linearly with the number of corners. The higher
potential supplies exact corner telescoping; finite convolution commutators
control the original strong-source energy without assuming smooth cutoffs.

The separate involved Codex source audit accepted precisely this scoped
analytical result. The full original report, assignment, context, subject
captures and raw-byte manifest are in `source-audit257A/`. The parent read
the complete report and context and checked all seven manifested files.
The unchanged proof raw SHA256 is
`8b92c1aeae67c26832cdd4e53dfcfb62537640d3d2a0a96370e677c3cd1ddbbc`;
its Git blob is `127d3eb9dee11b6a45532c228c2c2fb896cec51e`.
Its initial candidate header is retained as historical phase provenance.

The audit is a separate session within the same involved programme, with
parent context visible. It establishes neither independent peer review nor
formal verification. No numerical experiment or new grade was performed.
Priority remains unestablished, the existence threshold is enormous, and
the wider relevance has not been established. The bounded primary-source
comparison is retained separately in `primary-reading257-bounded.txt`.

Q251 remains open for general canonical rectangle partitions, including
x1-dependent cutsets and nonproduct geometry. This source result is to be
grouped with related canonical/coexact work; it creates no separate paper,
new PDF or assessment, and does not alter the published255B PDF or its4/10.
PR29 remains20/41 with TermSource=0. No physical mass gap or continuum
construction is claimed. No Lean/Lake or mathematical computation ran on
Windows, no Colab runtime was required, and no desktop control was used.
