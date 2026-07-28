# Weak-main covariance transcript validator — preregistration (2026-07-28)

**Frozen before reading the production result.**

This validator is deliberately independent of `python-flint`.  It parses the
outward decimal intervals printed by the production and replay runs and
requires:

1. byte-identical production and replay transcripts;
2. the frozen worktree head
   `150f439ba30ac1ee915fc92e93ec0b4d708f4349`;
3. Python 3.12, `python-flint 0.9.0`, and 180 Arb bits;
4. exact current SHA-256 matches for every dependency printed by the
   certificate;
5. the frozen configuration
   `18*32` parameter boxes, side 12, grid ladder 24/48, order 4, `z0=20`;
6. exactly 576 rows in lexicographic `(delta_index,t_index)` order, with the
   exact rational partition registered by the certificate;
7. a strictly positive printed lower endpoint for every core `KD`;
8. a printed outward lower endpoint strictly greater than `-1/20` for every
   full `XMAIN`;
9. consistent grid counts summing to 576 and a terminal PASS/scope line;
10. empty production and replay stderr files.

The validator checks the transcript contract and printed outward endpoints.  It
does not reproduce the quadrature; the independent second execution supplies
that part of the audit.

No K2, G2, G6, or manuscript promotion follows until this validator itself has
been run successfully after both transcripts exist.
