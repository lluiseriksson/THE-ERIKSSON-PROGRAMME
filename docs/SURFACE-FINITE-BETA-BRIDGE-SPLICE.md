# Finite-beta bridge: exact scaling and splice obligation

**Status:** `IDENTITY-CLOSED`; global splice still open

For

```text
J_m(beta) = exp(-beta) I_m(beta),
a_m^J = (m-1) J_{m-1}^2 J_m^2
        + (m+1) J_m^2 J_{m+1}^2,
b_m^J = m J_m^4,
```

one has, identically for every `beta>0`,

```text
a_m^J = exp(-4 beta) a_m,
b_m^J = exp(-4 beta) b_m,
F_A^J = exp(-4 beta) F_A,
F_B^J = exp(-4 beta) F_B,
W^J = exp(-8 beta) W,
```

where the manuscript normalization is

```text
W = 2 (F_A' F_B - F_A F_B').
```

Thus `W=4 F_B^2 E'` for `E=F_A/(2F_B)`. Since `exp(-8 beta)>0`, the scaled and
unscaled sign predicates are equivalent.  This identity is algebraic and
does not depend on truncation, quadrature, or interval precision.

It is not, by itself, the finite-beta relay.  A terminal splice must still
provide all of the following as one frozen proof object:

1. a complete rational beta union on `[20,1000/9]`;
2. for each beta box, a closed `t` union from `3/5` to
   `pi-(3/2)/beta`, with exact overlap at the G4 and G5 seams;
3. the bulk tail-contract verifier for the actual beta/t derivative orders;
4. an explicit implication from the union's `W<0` predicate to the
   manuscript's `(H_tail)` relay statement, followed by the exact splice to
   Proposition `k2endpoint` at `beta=1000/9`.

There is also a direct theorem-level implication that must be recorded if the
finite bridge is used as a replacement relay rather than as an `(H_tail)`
certificate.  On every certified box, the row predicate is an outward-rounded
upper bound

```text
upper_J >= W^J(t,beta),   upper_J < 0.
```

The algebraic identity above then gives

```text
W(t,beta) = exp(8 beta) W^J(t,beta) < 0.
```

Since Theorem `A` independently proves `F_B(t)>0` on `(0,pi)`, the exact
Wronskian identity `W=4 F_B^2 E'` yields `E'(t,beta)<0` on that box.  This
implication is pointwise and needs no continuity interpolation between boxes;
it is valid only after an exhaustive rational beta/t cover proves that every
point belongs to one certified row.  It does **not** discharge the separate
K2/K4/S1'''/S2''' remainder obligations, nor does it turn a disconnected
candidate archive into a global theorem.

The current executable high-order tail audit is
[`verify_surface_scaled_bulk_cwin3p2_high_tail_contract.py`](../scripts/verify_surface_scaled_bulk_cwin3p2_high_tail_contract.py).
The current production files intentionally retain the footer
`candidate ... no G2/G6 promotion`; this document must not be read as a
theorem claim until the four gates above and the independent claim audit are
green.

## Logical boundary of the relay

The identities in this file prove only the pointwise implication

```text
W^J < 0  =>  W < 0  =>  E' < 0,
```

after exhaustive coverage and the independent positivity theorem for `F_B`.
They do not imply the extraction remainder hypothesis `(H_tail)`, which is a
separate weighted derivative/tail-domination inequality. A common positive
rescaling of both Fourier families leaves the ratio `E` and the sign of `W`
unchanged while changing such derivative majorants, so no proof of `(H_tail)`
can use the sign rows alone. Promotion therefore requires an independent
tail-domination certificate (finite extracted part plus an explicit geometric
remainder) on the same cover.

The current rescue-300 backend has a local contraction audit in
`scripts/verify_surface_scaled_bulk_cwin3p2_rescue300_tail_contract.py`, and
the static role audit is `scripts/audit_surface_h_tail_role_usage.py`.  Both
pass on the six available rescue units, but they deliberately leave the
manuscript row candidate-only until the beta/t cover is exhaustive and the
direct-sign proposition is installed in the manuscript.
