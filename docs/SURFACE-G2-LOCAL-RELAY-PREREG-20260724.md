# G2 local relay lemma — preregistered acceptance contract

**State:** design-only; no finite-beta or G2 promotion

This contract is the required bridge between a signed-bilinear endpoint row
and a finite-beta cell.  It is intentionally local: a global relay may be
assembled only after every cell in the registered beta/t union passes this
predicate and the cells share a separately proved `(H_tail)` budget.

For each rational cell `U = [beta_0,beta_1] x [t_0,t_1]`, the proof package
must provide:

1. an endpoint sign margin `m(U)>0`, represented by an outward-rounded upper
   bound for the normalized signed-bilinear quantity on the full `t` row;
2. an analytic, interval-certified deviation bound `L_beta(U)` for the
   *project's explicitly defined finite-beta relay functional* `R`, namely
   `|R(beta,t)-R(beta_0,t)| <= L_beta(U)*(beta_1-beta_0)` throughout U.
   The proof package must define `R` and derive this inequality; the symbol
   `R` is not interchangeable with the endpoint `W^J` without that derivation;
3. an independent absolute tail charge `T_tail(U)` for the extracted
   derivative/tail terms, with the exact normalization used by `(H_tail)`;
4. the strict acceptance inequality

   `m(U) - L_beta(U)*(beta_1-beta_0) - T_tail(U) > 0`.

The implication from this inequality to the manuscript relay statement must
be proved symbolically before any production run.  A production transcript
may only evaluate the frozen predicate on a finite cover; it may not infer the
analytic implication from row counts or replay equality.

The cover contract is fixed before measurement: rational beta/t endpoints,
the registered root cages for R7/R8 as explicit boundaries, outward Arb
rounding, exact adjacency, and a production/replay byte-equality check.  A
failed cell is a declared gap or a preregistered subdivision, never silently
repaired after seeing its margin.

Passing the endpoint sign rows alone, or passing the first two terms while
`T_tail` is missing, does not certify K2, `(H_tail)`, G2, or G6.  Until this
contract is proved and exhaustively instantiated, all such rows remain
quarantined evidence.
