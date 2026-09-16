# Step 8b.24 C6c.7 — CMP96 Proposition 2.2 / equation (2.67)

Status: primary-source and target-type audit only.  No C6c.7 producer,
`.olean`, focal or axiom verdict exists.

## Source statement

CMP96 printed p. 234 states Proposition 2.2 after constructing the single
Neumann series (2.50).  At the retained rate `delta0/2`, the *same* Green
`G' = Delta'_a^-1` satisfies six actions:

```text
G' lambda                    scale (L^j eta)^2
nabla G' lambda              scale  L^j eta
G' nabla* lambda             scale  L^j eta
Holder(nabla G' lambda)      scale (L^j eta)^(1-alpha)
Holder(G' nabla* lambda)     scale (L^j eta)^(1-alpha)
Delta G' lambda              scale  1
```

All six share the endpoint decay
`exp(-(delta0/2) * d(y,y'))` and the same source-supported input.  The
random-walk representation is asserted convergent in exactly these norms.

The terminal `CMP99Eq342SourceLocalizedGreenCertificate` consumes the first,
second, third and sixth actions with scale vector `[ell^2, ell, ell, 1]`.
The two Holder actions are not fields of that certificate.  Therefore C6c.7
may expose a four-action terminal projection, but it may not call that
projection the whole of Proposition 2.2.  The Holder pair remains a separately
named source result if later hRpoly consumers need it.

## Measured producer state

Searches for the exact four action shapes find only their declarations in
`BalabanCMP99Eq342RegionalGreenCertificate` and
`BalabanCMP99Eq342SourceLocalizedGreenCertificate`, plus downstream field
uses.  No theorem constructs the right-adjoint-derivative or Laplacian fields.

The existing structures are honest target types because they fix every
operator definitionally to one canonical Green.  They are not producers and
must not be passed into C6c.7 as inputs.

## What follows from C6c.6, and what does not

* **Value.**  This is the direct (2.66) action of the constructed Neumann
  Green.
* **Left derivative.**  Compose the C6c.4 local `D G'(box)` head with the
  same C6c.6 Neumann coefficient.  The sealed rectangular owner-fibre
  convolution algebra is sufficient once the source/target owner types are
  pinned explicitly.
* **Right adjoint derivative.**  This does **not** follow merely by saying
  that the Green or precision is self-adjoint.  The required estimate is an
  output-fixed complete-owner supremum row.  Taking adjoints reverses the
  block action, and the already measured orientation no-go shows that the
  same fixed-vector row constant is not automatic.  C6c.7 needs either the
  direct reverse-head random-walk estimate printed by the source or a proved
  block-operator-norm symmetry strong enough to preserve the owner-fibre
  coefficient.  A generic `by adjoint` bridge is not accepted.
* **Laplacian.**  The exact inverse identity suggests
  `Delta G' = I - Q'^* a_j Q' G'`, but this is admissible only after C6c.2
  and C6c.6 identify the local precision literally with the source-faithful
  `Delta + Q'^* a_j Q'`, where `a_j` is the exact CMP85 prefix coefficient
  (including its displayed spacing normalization).  The identity term and
  that source mass contribution must be bounded separately; a free
  Laplacian action is not an input.  In particular
  `cmp99SourceGeneratedPhysicalMass` is the coefficient of a different
  Poincare-normalized precision and cannot enter through a rewrite or
  specialization shortcut.

Thus C6c.7 is not a fourfold repetition of the value proof.  The right action
has a genuine orientation gate and the Laplacian action has a genuine
operator-dictionary gate.

## Required construction

1. Fix `alpha = 1/2` in the C6c.6 source window and prove the retained rate
   `delta0/2` is positive.
2. Reuse the *same* Neumann operator and coefficient for every action.  No
   independently chosen family of bounded Greens is admissible.
3. Produce the value and left-derivative actions by composing the C6c.6
   Neumann row with the corresponding C6c.4 heads.  Preserve exact scale
   powers `ell^2` and `ell`.
4. Produce `G' D*` by a direct, orientation-correct source argument as
   described above.  If a block-adjoint transport is used, its coefficient
   equality must be a named theorem, not an inference from scalar
   self-adjointness.
5. Produce `Delta G'` from the literal precision/inverse identity, with the
   identity and the exact CMP85 `a_j Q'^*Q'` contribution displayed
   separately before choosing a common amplitude.  This step must consume the
   same C6c.2 coefficient and Green that feed C6c.6; it may not switch to the
   older generated-physical-mass Green family.
6. Choose one positive `B0` that majorizes all four displayed amplitudes and
   one positive `delta0/2` before quantifying over depth and the `j`/`j+1`
   branch.  Per-action or per-depth constants do not satisfy the source.
7. Package exactly these four results in an intermediate source-specific
   object.  Construction of the terminal CMP99 certificate waits for the
   C6c.8 gauge/dictionary transport.

## Acceptance endpoint and exclusions

C6c.7 ends with four actions of one internally constructed CMP96 Green, at
one common positive rate and the exact scale vector `[ell^2, ell, ell, 1]`.
It may additionally expose the two Holder actions under a distinct name.

It does not accept any of the four terminal fields as hypotheses, identify
the CMP96 Green with the final CMP99 regional Green by fiat, or claim the
Corollary-3.6 gauge transport.  It does not yet construct
`CMP99Eq342SourceLocalizedGreenCertificate`; that is C6c.9 after C6c.8.
The specialized wrapper
`BalabanCMP99SourceGaugeRegularGeneratedGreen` is therefore auxiliary only:
its `cmp99SourceGeneratedPhysicalMass` endpoint is not a C6c.7 input or a
C6c.8 conclusion for this source-faithful chain.

## Exact target-type closure (2026-08-18)

A fresh read of
`BalabanCMP99Eq342SourceLocalizedGreenCertificate.lean` fixes the four
eventual projections without abbreviation:

| action | literal operator | source owner | target owner | amplitude |
|---|---|---|---|---|
| value | `cmp99RegionalDirichletGreen Omega A hc hAcoer` | active site | active site | `B0 * ell^2` |
| left | `D0.comp Green` | active site | physical bond | `B0 * ell` |
| right | `Green.comp D0.adjoint` | physical bond | active site | `B0 * ell` |
| Laplacian | `Laplacian.comp Green` | active site | active site | `B0` |

Here `ell = L^(depth+1)`.  All four predicates are
`FinitePiLpTypedBlockLocalizedSupBound` with the same `finBoxDist` and the
same positive `delta0`.  In particular, the two derivative actions have
opposite source/target types.  They cannot be exchanged by a field-name
rewrite or by scalar self-adjointness.

The current f5a retained-prefix package supplies only the internally
generated retained towers and their terminal `Qprime` equality.  It supplies
none of the four actions, no regional Green inverse, and no common amplitude
or rate.  Conversely, C6c.4 and C6c.6 currently have source contracts but no
producer types.  Therefore a Lean `structure` for C6c.7 written now would
necessarily take one or more of the desired bounds as constructor data.  That
would be a renamed conclusion and is deliberately not materialized.

The next admissible C6c.7 source file may be written only after C6c.4 and
C6c.6 expose the *constructed* local head and Neumann Green.  Its public
headline must be a theorem returning the four-action package from those
generated objects; neither that package nor any terminal projection may be a
caller parameter.  This type audit is static only and does not alter the
status of C6c.7.
