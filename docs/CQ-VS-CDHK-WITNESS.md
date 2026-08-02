# An explicit witness that `C_q` and `C_DHK` are not equal in general

Written to answer a referee objection on the SU(2) crossing Ward paper, which
was correct and which the manuscript did not meet:

> Una diferencia sintáctica entre dos fórmulas de traza no constituye por sí sola
> una prueba impresa de desigualdad: podrían existir identidades especiales de
> SU(2) que las hicieran coincidir.

Exactly so.  SU(2) satisfies enough special identities that two syntactically
different trace expressions can silently coincide, and the manuscript asserted
non-equality from the shape of the formulas alone.  This document supplies the
missing object.

## The two operators, as printed in the manuscript

    C_DHK(a) = sum_A tr( a3^-1 beta a2 A a4^-1 alpha a1 A )
    C_q  (a) = sum_A tr( beta a2 a4^-1 A alpha a1 a3^-1 A )

`A` running over the three Pauli matrices `X, Y, Z`.

## The witness

    a1 = a2 = a3 = alpha = 1        a4 = beta = iX

Every entry is a Gaussian integer, and each of `1` and `iX` is genuinely in
SU(2): `det(iX) = -(i)(i) = 1`, and `(iX)† (iX) = (-iX)(iX) = X² = 1`.  This is
checked in the script rather than asserted.

**It is not a numerical near-miss.  Both values are integers, computed by hand.**

Using `(iX)^-1 = -iX`:

    C_DHK = sum_A tr( iX · A · (iX)^-1 · A )
          = sum_A tr( iX A (-iX) A )
          = sum_A tr( X A X A )            since -i² = 1

          A = X :  tr(XXXX) = tr(1)  = +2
          A = Y :  XYX = -Y, so tr(XYXY) = tr(-YY) = -2
          A = Z :  XZX = -Z, so tr(XZXZ) = tr(-ZZ) = -2

          C_DHK = 2 - 2 - 2 = -2

    C_q   = sum_A tr( iX · 1 · (iX)^-1 · A · 1 · 1 · 1 · A )
          = sum_A tr( (iX)(-iX) A A )
          = sum_A tr( A² )                 since (iX)(-iX) = X² = 1
          = 2 + 2 + 2 = +6

So

    C_DHK = -2        C_q = +6        C_q - C_DHK = 8

and the two operators are **not** equal, on an explicit pair of SU(2) elements,
with no floating point anywhere in the argument.

## Why they differ, in one line

In `C_DHK` the two Pauli insertions sit on either side of the conjugation and
survive as `X A X A`; in `C_q` the group elements collapse against each other
first and leave `A A`.  That is the referee's point made concrete: a single
orthogonal invariance of the Pauli sum cannot absorb two independent adjoint
conjugations.

## Robustness

An exhaustive search over `{1, iX, iY, iZ}` for all six arguments -- 4096
combinations -- finds **384** on which the two operators differ.  The witness
above is the one with the most identity arguments, chosen because it is the
cheapest to recheck by hand and the cheapest to compile.  Four further
witnesses are printed in the transcript for cross-checking.

Script: `scripts/witness_cq_vs_cdhk.py` (local-light: 978 ms wall, one process,
no worker pool, negligible RSS; run in normal and `-O` mode, both exit 0, and no
acceptance depends on an `assert`).
Transcript: `scripts/witness_cq_vs_cdhk_transcript.txt`.

## What this does and does not settle

It settles that the two operators are **not identified**, which is what the
manuscript needed and did not have.

It does **not** determine their precise relation, and nothing here should be
read as doing so.  Until that relation is established, the honest sentence for
the manuscript is the referee's own:

> The two operators are not identified here; their derived reverse-resolution
> expressions are different, and establishing their precise relation remains
> open.

with the witness above cited as the reason the first clause is a fact and not a
presumption.

## Still to do

This is an exact hand proof and an exact machine computation.  It is **not yet a
Lean theorem.**  Compiling it is straightforward -- the entries are Gaussian
integers, so `norm_num` closes it -- and until that is done the witness should
be described as verified by hand and by an audited script, not as machine
checked.
