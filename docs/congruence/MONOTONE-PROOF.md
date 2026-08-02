# Positive mixing cannot increase the projective diameter

Architecture after external review.  What was first written as a statement about
*congruence* of a *symmetric* matrix is neither: symmetry is never used, and the
two sides need not be transposes of each other.

## Notation, logarithm-free — and the orientation is fixed here, once

For `M` entrywise positive,

    Φ(M) := max_{a,b,c,d}  M_ab M_cd / (M_cb M_ad),      Δ(M) = log Φ(M),
    φ(M) := min_{a,b,c,d}  M_ab M_cd / (M_cb M_ad)  =  1 / Φ(M).

The cross-ratios are closed under reciprocal — swapping `a ↔ c` inverts the
ratio — so `min = 1/max` and the two descriptions carry the same information.

**They do not carry the same indices, and that is a trap.**  The Lean interface
`CrossRatioLB φ T` (and `BirkhoffInterface` in `CongruenceSpectrum`, whose
orientation it copies) is the **lower** bound

    φ · (M_cb M_ad)  ≤  M_ab M_cd ,

so its equality cases form a **`TightSet`** — the quadruples attaining the
*minimum* — and **not** the `ArgMax` of the ratio.  For the witness `M^{pq}`
below the two sets are disjoint:

    TightSet(M^{pq}) = { (p,q,q,p), (q,p,p,q) }      at  φ = μ²
    ArgMax  (M^{pq}) = { (p,p,q,q), (q,q,p,p) }      at  Φ = μ⁻²

verified exhaustively.  Everything from Theorem B onward is therefore stated in
the **`TightSet` / lower-bound** convention, to match the formalisation.  Writing
Theorem B against `ArgMax` while the Lean carries `CrossRatioLB` would give a
correct proof about the wrong quadruples.

## Theorem A (two-sided).  `Δ(A M B) ≤ Δ(M)`

`A, B` entrywise nonnegative, `M` entrywise positive, `T = A M B` entrywise
positive.  Then `Φ(T) ≤ Φ(M)`.

*Proof.*  Fix `i,j,k,l` and put `w_abcd = A_ia A_jc B_bk B_dl ≥ 0`.  Expanding,

    T_ik T_jl = Σ w_abcd · M_ab M_cd
    T_jk T_il = Σ w_abcd · M_cb M_ad

— the same weights.  The second line is the whole argument: expanding
`T_jk T_il` produces the coefficient `A_ja A_ic B_bk B_dl`, and renaming the
summation indices `a ↔ c` returns it to `w_abcd` while moving the swap onto the
`M`-factors.  By definition of `Φ(M)`, `M_ab M_cd ≤ Φ(M) · M_cb M_ad` for every
quadruple; all weights are nonnegative, so the inequality survives summation. ∎

**Corollary A1 (congruence).**  `B = Aᵀ`: `Δ(S M Sᵀ) ≤ Δ(M)` for `S ≥ 0`.  This
answers §8 of *Congruence Rigidity and the Fusion Bound*: beyond the diagonal
case the diameter is not merely non-invariant, it is **monotone**.

**Remark (the hypothesis is not opaque).**  With `M > 0` entrywise,
`S M Sᵀ > 0` **iff no row of `S` is zero**.  Positivity of the image is a
structural condition on `S`, not an extra assumption to be carried.

## A transported bound is not an optimal bound

`CrossRatioLB φ M` says only that `φ` is *a* valid lower bound.  The transport
theorem gives `CrossRatioLB φ (A M B)` for the same `φ`, which is
**not yet** a statement about diameters: if `φ` sat strictly below the true
minimum of `M`'s cross-ratios, nothing about `Δ` follows.

The layer that is needed, and which must exist in Lean before any equality
statement:

    IsOptimalCrossRatioLB φ M  :=  CrossRatioLB φ M ∧ ∀ ψ, CrossRatioLB ψ M → ψ ≤ φ

equivalently `IsGreatest {ψ | CrossRatioLB ψ M} φ`.  Writing `φ_M` for that
greatest bound, the correct chain is

    CrossRatioLB φ_M M          (definition)
    CrossRatioLB φ_M (A M B)    (S-2a, transport)
    φ_{AMB} ≥ φ_M               (because φ_M is *a* bound for A M B, and φ_{AMB} is the greatest)
    Δ(A M B) ≤ Δ(M)             (since Δ = -log φ under the fixed convention)

and only then:

    Δ(A M B) = Δ(M)   ⟺   some output quadruple of A M B is tight at φ_M.

**The monotonicity is `φ_{AMB} ≥ φ_M`, not the transport itself.**  Transport
alone is an inequality about one fixed number; the diameter statement is about
two optima.  Recording the difference here because the two are easy to conflate
and the conflation would make Theorem B unsound.

## Theorem B (equality, by supports)

`φ(T) = φ(M)` iff there is a quadruple of output indices `(i,j,k,l)` with

    supp A_i × supp B_·k × supp A_j × supp B_·l  ⊆  TightSet(M),

with the coordinate order matching the expansion.  *Reason.*  Equality forces
the termwise inequality to be tight on **every** quadruple carrying positive
weight: `φ · M_cb M_ad - M_ab M_cd ≤ 0` termwise, and a weighted sum of
nonpositive terms vanishes exactly when every positively-weighted term does.

**Corollary B1 (strict contraction).**  If every entry of `S` is positive and
`Δ(M) > 0`, then `Δ(S M Sᵀ) < Δ(M)`, strictly.  All weights are positive, and
the quadruples with `a = c` give ratio exactly `1 < Φ(M)`, so positive weight
sits on a non-maximising term.

**Corollary B2 (the universal stabiliser is the monomial group).**  For `S`
square, nonnegative, with no zero row:

    [ ∀ M > 0 :  Δ(S M Sᵀ) = Δ(M) ]  ⟺  S = D P,  D positive diagonal, P a permutation.

*Route, via witnesses.*  For `p ≠ q` and `0 < μ < 1` let `M^{pq}` be all ones
except `M_pq = M_qp = μ`.  In the fixed convention, `φ(M^{pq}) = μ²` and
`TightSet(M^{pq}) = {(p,q,q,p), (q,p,p,q)}` — **exactly two quadruples**,
verified exhaustively, and symbolically immediate: every factor is `1` or `μ`,
so reaching `μ²` demands both numerator factors `μ` and both denominator factors
`1`, which leaves only those two.  By Theorem B, equality at `M^{pq}` forces four supports whose
Cartesian product lands inside that two-element set, hence all four are
singletons in `{p,q}`; so `S` has a row supported purely on column `p` and
another purely on column `q`.  Ranging over all pairs, every column of `S` owns a
pure row; `n` such rows exhaust the rows and match them to columns bijectively.

## The quantifier is where this can go wrong

**False as stated:** *`S` non-monomial ⟹ `Δ(S M Sᵀ) < Δ(M)` for every `M > 0`.*
Take `M = 𝟙𝟙ᵀ`: `Δ = 0`, and every transformation preserves zero.  The correct
object is the **universal** stabiliser — equality for *all* `M` — not equality at
a fixed `M`.

## Novelty, stated narrowly

Positive operators are non-expansive, and under stronger hypotheses contractive,
for Hilbert's projective metric; that is the classical Birkhoff–Hopf circle, and
Eveson–Nussbaum present positive operators precisely as contractions of the
projective geometry.  **Theorem A is very probably a finite-dimensional shadow of
that principle, and we do not claim the monotonicity itself as new.**

What a directed search did not find:

* this finite *same-weights* identity as an elementary, mechanisable proof that
  never mentions the metric, the cone, or the contraction constant;
* the equality criterion by supports (Theorem B);
* the classification of the universal stabiliser as the monomial group.

That is the resistant claim, and it is deliberately smaller than "we prove that
positive maps contract".

## Verified

* `scripts/probe_stabilizer.py` — reconnaissance; sanity exact to 4.4e-16.
* `scripts/gate_JA.py` — pre-registered adversarial gate, 600 checks, five
  families built to try to *increase* `Δ`, `n ≤ 8`, `μ ≥ 1e-3`; worst gap
  `-3.3e-08`, never positive.
* `scripts/check_proof.py` — the same-weights identity itself, 1440 quadruples,
  max deviation 9.2e-14.
* `scripts/check_restructure.py` — Theorem A two-sided with `M` **not**
  symmetric (450 cells, worst `-0.30`); strict contraction for `S > 0` (300
  cells, strict in every one); and `ArgMax(M^{pq})` computed **exhaustively**,
  exactly the two predicted quadruples at every `n, p, q, μ` tested.

## Not done

Theorem B and Corollaries B1, B2 are proved on paper with their ingredients
measured, but **nothing here is in Lean yet**, and gate JB as originally
registered (a witness *search*) has been superseded by the witness
*construction* above — better, but a change to a pre-registered gate, and
recorded as such rather than allowed to pass quietly.
