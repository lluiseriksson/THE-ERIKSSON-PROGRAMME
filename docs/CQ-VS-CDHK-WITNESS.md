# An explicit witness that `C_q` and `C_DHK` are not equal in general

Written to answer a referee objection on the SU(2) crossing Ward paper, which
was correct and which the manuscript did not meet:

> Una diferencia sintáctica entre dos fórmulas de traza no constituye por sí sola
> una prueba impresa de desigualdad: podrían existir identidades especiales de
> SU(2) que las hicieran coincidir.

Exactly so.  SU(2) satisfies enough special identities that two syntactically
different trace expressions can silently coincide, and the manuscript asserted
non-equality from the shape of the formulas alone.

## The first version of this witness was in the wrong conventions

Recorded rather than quietly corrected.  The first script used the HERMITIAN
Pauli matrices and the UNNORMALIZED trace and printed `C_DHK = -2`, `C_q = 6`.
Those are true statements about a real inequality, but they are not the values of
the paper's equations (11)-(12), which use

    tr_2 = (1/2) Tr                the normalized fundamental trace
    A_k  = c i sigma_k             ANTIHERMITIAN generator directions

and the first version also wrote the group element as "iX", colliding with the
paper's `X`, which names an antihermitian direction.  The idea survived the
correction; the numbers did not.

## The witness, in the paper's conventions

    a1 = a2 = a3 = alpha = 1        a4 = beta = i sigma_x

`i sigma_x` is in SU(2) -- `det = 1`, unitary -- and this is checked in the
script, not assumed.  Using `(i sigma_x)^-1 = -i sigma_x`:

    C_DHK = sum_k tr_2( i sigma_x A_k (-i sigma_x) A_k )
          = sum_k tr_2( sigma_x A_k sigma_x A_k )
          = -c^2 + c^2 + c^2
          = + c^2

      because sigma_x A_x sigma_x A_x = -c^2 * 1        -> tr_2 = -c^2
          and sigma_x A_y sigma_x A_y = +c^2 * 1        -> tr_2 = +c^2
          and sigma_x A_z sigma_x A_z = +c^2 * 1        -> tr_2 = +c^2

    C_q   = sum_k tr_2( (i sigma_x)(-i sigma_x) A_k A_k )
          = sum_k tr_2( A_k^2 )
          = -3 c^2                 since A_k^2 = -c^2 * 1

Hence

    C_q - C_DHK = -4 c^2

## The normalization `c` is never needed

Both operators insert `A` exactly twice, so each is **homogeneous of degree 2
in `c`**, and therefore the witness separates them for **every `c != 0`** --
`c = 0` being excluded because it makes all three directions vanish and the Ward
identity vacuous.

**Which part of that is proved by which artifact, precisely.**  An earlier
version of this document said the homogeneity was "verified in the script ...
not argued from the shape of the formula".  That is backwards, and the referee
was right to separate them:

* the **universal statement over all `c != 0`** rests on the algebraic identity
  -- each operator contains exactly two `A_k` insertions, so rescaling
  `A -> cA` multiplies each by `c^2`.  That is a hand proof, and it is exact;
* the **script** proves the exact values at the particular rational `c` it runs,
  and corroborates the scaling law between `c = 1` and `c = 1/2`.  Sampling two
  points is not a proof of a law that holds at all of them.

So the honest description of the present state is:

> exact symbolic hand proof for every `c != 0`, with audited exact-arithmetic
> checks at selected rational values

and **not** "the script verifies every `c`".

This matters procedurally: closing this residue does **not** require reading `c`
off the Lean producer, which is not available.  The result is stronger than a
single numerical instance -- it is a statement about the whole family of
normalizations.

At the standard normalization `c = 1/2`, i.e. `A_k = (i/2) sigma_k`:

    C_DHK = 1/4          C_q = -3/4

## Why they differ, in one line

In `C_DHK` the two generator insertions sit on either side of the conjugation and
survive as `sigma_x A sigma_x A`; in `C_q` the group elements collapse against
each other first and leave `A A`.  That is the referee's point made concrete: a
single orthogonal invariance of the Pauli sum cannot absorb two independent
adjoint conjugations.

## What this settles

Closed: **the two operators are not equal in general.**

Open: their precise structural relation, and how that relation interacts with the
concrete four-face heat density.

### The manuscript sentence, with the witness printed

Printing the configuration costs one line and turns the non-equality from an
assertion into something a reader can check:

> The quotient-lifted compensated operator and the ordinary-edge
> Driver--Hall--Kemp operator are not equal in general.  Indeed, for
> `a1 = a2 = a3 = alpha = I`, `a4 = beta = i sigma_x`, and `A_k = c i sigma_k`
> with `c != 0`, one has `C_DHK = c^2` and `C_q = -3 c^2`.  What remains open is
> a structural comparison between the two operators and its interaction with the
> concrete four-face heat density.

### The claim ledger must split into two rows

The current ledger files the whole "comparison with the ordinary-edge DHK mixed
operator" as open, alongside the thermal identity and the Makeenko--Migdal
equation.  After the witness that is no longer accurate: a decisive part of that
comparison -- whether the two can be equal -- is closed.

| Statement                                                                     | Status                                |
| ----------------------------------------------------------------------------- | ------------------------------------- |
| `C_q = C_DHK` in general                                                      | **Refuted by explicit SU(2) witness** |
| Structural relation between `C_q` and `C_DHK`, incl. four-face heat density   | **Open**                              |

Leaving one undivided "comparison open" row would understate what is now known,
which is the same defect as overstating it, with the sign changed.

## Status of the artifact

Exact hand proof plus an exact machine computation over Gaussian rationals --
`Fraction` pairs, no floating point anywhere.  Four checks (SU(2) membership,
antihermiticity of the directions, degree-2 homogeneity, nonzero difference),
explicit counter, `PASS` only at 4 of 4.

**It is not yet a Lean theorem** and must not be described as machine checked
until it is one.

### The Lean step has a gate, and it is not `norm_num`

The cheap move -- a fresh module that restates the two expressions and closes
them with `norm_num` -- would **mechanize the exact defect this witness was
written to repair.**  The first version of this script proved something correct
about expressions that resembled the printed ones; a new module that retypes
`C_q` and `C_DHK` from the PDF can do the same thing again, only now with a green
build behind it, which makes it harder to notice rather than easier.

The binding criterion is therefore:

> import or version the original 26-declaration producer, instantiate **its**
> definitions of `C_q` and `C_DHK`, and obtain the two values there.

`c` is no longer a dependency.  The producer still is.  Until it is available,
the correct status is that the mathematics is closed and the formal
identification of the objects is not.

Script: `scripts/witness_cq_vs_cdhk.py` -- local-light, measured: 415 ms wall,
one process, no worker pool, negligible RSS; run in normal and `-O` mode, both
exit 0, no acceptance depending on an `assert`.
Transcript: `scripts/witness_cq_vs_cdhk_transcript.txt`.
