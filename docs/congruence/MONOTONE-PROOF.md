# MONOTONE, proved — and the Hilbert metric turned out to be unnecessary

Registered target (STABILISER-CHARTER.md):
`Δ(S M Sᵀ) ≤ Δ(M)` for entrywise positive `S`.

**Status: proved, elementary, and for `S` merely NONNEGATIVE.**  The charter's
intended route went through the Hilbert projective metric — `Δ` as the diameter
of the columns, plus non-expansiveness of positive maps, plus a
convex-combination lemma.  None of that is needed.  The charter also set a death
criterion: *if the proof needs the Birkhoff contraction constant, stop*.  It
needs neither the constant nor the theorem nor the metric.

## Statement

Let `M` be entrywise positive and `S` entrywise nonnegative with `T = S M Sᵀ`
entrywise positive.  Then `Δ(T) ≤ Δ(M)`, where

    Δ(M) = max_{i,j,k,l} log ( M_ik M_jl / (M_jk M_il) ).

## Proof

Write `e = exp Δ(M)`.  By definition, for all indices

    (1)   M_ab M_cd  ≤  e · M_cb M_ad .

Fix `i,j,k,l` and expand, with weights `w_abcd = S_ia S_kb S_jc S_ld ≥ 0`:

    T_ik T_jl = Σ_abcd w_abcd · M_ab M_cd
    T_jk T_il = Σ_abcd w_abcd · M_cb M_ad

The second line is the whole trick.  Expanding `T_jk T_il` gives the coefficient
`S_ja S_kb S_ic S_ld`; swapping the summation names `a ↔ c` leaves that
coefficient equal to `S_ia S_kb S_jc S_ld = w_abcd` and moves the swap onto the
`M`-factors, turning `M_ab M_cd` into `M_cb M_ad`.  **Same weights, swapped
matrix indices.**

Now apply (1) termwise.  Every weight is nonnegative, so

    T_ik T_jl  ≤  e · T_jk T_il ,

for all `i,j,k,l`, which is exactly `Δ(T) ≤ Δ(M)`.  ∎

## Why this is the right proof and not a shortcut

The cross-ratio bound (1) is not an estimate about `M`; it *is* the definition of
`Δ(M)`.  The proof therefore says something sharper than "mixing contracts":
the quantity `Δ` is defined by a family of bilinear inequalities that is closed
under congruence by any nonnegative matrix, because congruence acts on those
inequalities by a nonnegative change of weights.  Positivity of `S` is not used;
only nonnegativity, plus enough of it that `T` stays positive.

## What is verified

* `scripts/probe_stabilizer.py` — reconnaissance, sanity exact to 4.4e-16.
* `scripts/gate_JA.py` — the pre-registered adversarial gate: 600 checks, five
  families built to try to *increase* `Δ` (near-singular `S`, row scales
  spanning 1e4, one dominant entry, near-monomial, near-proportional columns),
  `n` up to 8, `μ` down to 1e-3.  Worst gap `-3.3e-08`; never positive.
* `scripts/check_proof.py` — the weight-matching identity itself, the one step
  derived by hand, checked on 1440 index quadruples: max deviation 9.2e-14.
  Also confirms the consequence for `S` merely nonnegative.

## What is NOT proved

The converse half of the charter — **STABILISER**, that equality for all `M`
holds exactly on the monomial group — is untouched.  The reconnaissance is
suggestive (equality breaks at a perturbation of `1e-4`, and the near-monomial
family in gate JA gives gaps of order `1e-8` that shrink continuously to zero),
but suggestive is not proved.  Gate JB is registered and has not been run.

From the proof, the shape of the converse is visible: equality forces (1) to be
tight on every quadruple carrying positive weight.  A monomial `S` only ever
gives weight to quadruples with `a = c`, where (1) is an identity; a mixing `S`
gives weight to quadruples where it can be made strict.  Turning that into a
theorem needs, for each non-monomial `S`, an explicit `M`.  That is the next
piece of work, and it is where the paper can still die.
