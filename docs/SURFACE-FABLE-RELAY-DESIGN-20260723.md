# Independent relay design review — 2026-07-23

Claude Fable 5 High was queried through the Fable Bridge with the explicitly
selected profile `lluiseriksson` (`lluiseriksson@gmail.com`).  The bridge
confirmed `verified_model: claude-fable-5` and no error.  Fable inspected only
the repository and did not edit files.

## Useful result

The review located the exact objects used by the current manuscript:

- `W^J=\exp(-8\beta)W` and `W=4F_B^2E'` are positive-rescaling identities.
- `(H_tail)` is an absolute bound on `|\tau|`; it is not itself a signed
  quantity, so pointwise rows with `W^J<0` cannot be substituted for it without
  a separate role-audited implication.
- The registered Cauchy budget uses `\rho=7/100`, `\delta_1=1/15`, and requires
  `M\le 0.002763129991319444...` for the relevant complex supremum.

Fable's proposed single relay lemma is conditional: on each frozen `t` cell,
certify (i) analyticity of the repaired carrier in the complex `\delta` disk,
(ii) an outward-rounded supremum `M_j` for the complete quotient on that disk,
and (iii) the already manifested head coefficients.  Cauchy's estimate would
then turn the explicit `M_j` budgets into the missing absolute tail bound.

## Independent verification and disposition

The local audits were rerun after the review:

```
H_TAIL CAUCHY BUDGET AUDIT
required_M_for_C4 0.002763129991319444...
M_SUPREMUM UNSUPPLIED
NO_H_TAIL_PROMOTION

G2 RELAY AUDIT ONLY; NO G2/G6 PROMOTION
beta_union_complete: false
relay_status: RELAY_LEMMA_UNPROVED
promotion: NONE
```

Thus the review supplies a precise design target, not a theorem.  The next
falsifiable experiment is a one-cell complex-disk measurement of the complete
quotient, including a denominator lower bound; exceeding the budget stops the
route.  Until such certificates exist, G2 remains nonterminal and the paper's
terminal seal must not be changed.
