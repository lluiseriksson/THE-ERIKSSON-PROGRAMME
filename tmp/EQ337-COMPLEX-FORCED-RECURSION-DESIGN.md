# Eq. (3.37) complex forced finite recursion

Status: DESIGN ONLY / PRE-VALIDATION.  No `.olean`, compiler, or axiom-oracle
verdict exists for the proposed modules below.

Source checkpoint inspected: `c1ec63d9b17f6412f59a8194a6f71d5de7c4800f`.

## Existing source-facing leaf

`cmp99Eq337SourceComplexLocalizedNextBackground` constructs one coarse
`SL(N,C)` background internally from the literal physical inputs

- `U`,
- the Eq. (3.37) one-cochain `A`,
- `eta`, `epsilonU`, and `rA`, and
- the proved link, small-field, and no-winding inequalities.

It does not accept a preselected coarse background or a free deviation
family.  This is the correct one-step leaf, not yet a finite recursion.

## Existing recursion pattern

`BalabanCMP99SourceLocalizedRetainedTower.lean` already contains the private
recursion `cmp99SourceLocalizedCanonicalRetainedAux`.  It constructs every
localized and canonical prefix internally and proves the prefix-Qprime
equalities.  No scale-indexed background or tower family is caller data.

The complex recursion must reuse this logical pattern.  It must not accept a
finished family `Fin (depth + 1) -> background` or per-scale equalities.

## Actual missing producer

The complex one-step output currently has no theorem bounding

```lean
‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) C) - 1‖
```

uniformly on every oriented coarse edge.  Without that theorem, a recursive
interface would have to receive the next small-field fact as an input, which
would merely rename the pending obligation.

The required producer is source-internal and has four stages.

1. Reuse the probability-vector identity for the source block weights.
2. Prove the `SL(N,C)` exponent estimate with the existing
   `MatrixNearLogNoWindingBudget`; this is the same Banach-algebra estimate as
   the sealed unitary producer and does not use unitarity.
3. Bound the coarse source transport directly by the complex Wilson-line
   estimates.  Its literal path has length `M`; no unitary norm-one weakening
   is permitted.
4. Use the literal product identity

   ```text
   F * C - 1 = (F - 1) * C + (C - 1)
   ```

   so the factor norm and coarse deviation remain separate and visible.

For an oriented-link radius `r` and no-winding budget `B`, the first honest
candidate recurrence is

```text
r_next = cmp99UbarExpRadius(B) * (1 + r)^M
       + M * r * (1 + r)^M.
```

This is a candidate definition to be compiled, not a claimed theorem.  The
two summands must remain separate in the Lean definition and audit.

## Forced chain after the producer

Only after the preceding output bound compiles should the tree introduce a
scalar inductive chain analogous to `CMP99SourceUbarRadiusChain`:

```text
stop : nonnegative r -> chain 0 r
step : nonnegative r
    -> literal no-winding gate for r
    -> cmp99UbarLogRadius(B(r)) < 1
    -> chain depth (r_next r)
    -> chain (depth + 1) r
```

The recursion then takes one initial complex background and this scalar
chain, constructs each next background internally, and returns the terminal
background (and, if a consumer needs it, private prefixes plus public
projection lemmas).  It must not accept a background family, a free `hdev`, a
free next-background smallness proof, or a terminal equality.

## Acceptance gates

1. The final source-facing leaf still constructs the first perturbed
   background from literal `U`, `A`, and `eta`.
2. The public recursive constructor has no argument whose type is a
   scale-indexed background family.
3. The public recursive constructor has no free `hdev` or per-scale
   small-field hypothesis for internally generated backgrounds.
4. Both orientations are proved; negative edges are not inherited from the
   unitary inversion-isometry lemma.
5. The complex coarse factor pays its explicit norm `(1 + r)^M`.
6. Every PRE-VALIDATION module is compiled in Colab before promotion; the
   diagnostic gate is not permission to remove PRE-VALIDATION.
7. This work does not move `20/41`, does not instantiate `TermSource`, and
   does not declare window 15 attained.
