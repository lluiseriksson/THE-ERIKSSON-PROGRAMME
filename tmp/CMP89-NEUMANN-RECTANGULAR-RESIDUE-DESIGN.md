# CMP89 rectangular Neumann residues: finite continuation after the hot gate

Status: design only. The exact displacement and distance dictionary is
PRE-VALIDATION at source object
`dd27cd6081b0e276d3059a7fdcfb36fb0f634178`. No module below may be promoted
until that dictionary and audit pass in the retained Colab runtime.

## Source-fixed conventions

- CMP89 (1.1) gives the lattice carrier `0 <= x_mu < m_mu`; printed page 584
  writes the inclusive geometric envelope, not an extra lattice site.
- CMP89 (2.42) has positive image terms. A branch is one Boolean per
  coordinate; there is no alternating Dirichlet sign.
- The two one-coordinate image orbits are `2*k*m+n` and `2*k*m-n-1`.
- The period is coordinatewise `2*m_mu`. It must not be collapsed to a scalar
  unless an explicit cube dictionary proves all side lengths equal.

## Finite route to the regional decay producer

1. **Exact residue dictionary** (current hot-gated brick).
   Prove
   `x-image = baseResidue + (2*m)*(-k)` coordinatewise, with direct residue
   `x-n` and reflected residue `x+n+1`. On the half-open carrier, both centered
   reflected distances `x+n+1` and `2*m-x-n-1` dominate `|x-n|`.

2. **Canonical centered rectangular representative.** Construct it internally
   for every coordinate modulo `2*m_mu`, together with its carry. Required
   outputs are the exact reconstruction equality, centeredness
   `2*|u_mu| <= 2*m_mu`, and the direct-distance lower bound. A representative
   supplied by the caller is not accepted.

3. **Rectangular affine-fibre equivalence.** Reindex `k` by the internally
   constructed carry. The equivalence is coordinatewise translation/negation
   on `Fin d -> Int`; no injectivity hypothesis or finite-cardinality factor is
   admitted.

4. **Product residue sum with varying periods.** Generalize the sealed
   one-dimensional geometric estimate coordinatewise. The endpoint must keep
   the exact product

   ```text
   product_mu 2 / (1-exp(-delta*(2*m_mu)))
   ```

   multiplying the retained direct weight. Replacing it by a ball count or by
   the number of sites in the rectangle is rejected.

5. **Reflection branch sum.** Sum the `2^d` Boolean branches literally. The
   only branch multiplicity is the visible factor `2^d`; it is independent of
   every `m_mu` and of the rectangle volume.

6. **Full-lattice Green insertion.** Consume the already constructed physical
   full-lattice Green bound termwise. The common `B0` and `delta0` must be the
   same objects for every image and branch. No independently chosen family of
   image bounds is accepted.

7. **Regional representation.** Consume the named CMP89 (2.42)
   representation certificate. This step may use its equality only after the
   absolute summability required by the certificate is available. It produces
   the regional value bound; derivative/Laplacian actions remain separate.

8. **Scale/owner transport.** Convert the fine `l1` decay to the literal
   regional/owner metric through named dictionaries. Every lattice unit is
   recorded explicitly; no mental identification of fine distance, block
   distance and owner distance is accepted.

## Acceptance gates

- `side_pos` constructs a nonempty carrier; empty rectangles cannot discharge
  a theorem vacuously.
- The centered representative and carry are constructed, not assumed.
- The reflected distance comparison is proved on the half-open carrier.
- The sum has `2^d` times a product of geometric constants and no factor
  `product_mu m_mu`.
- All image terms carry the same physical `B0`, `delta0` and kernel.
- A hot PASS is diagnostic only. PRE-VALIDATION retires only after a cold
  checkout gate of the exact source object.
- The route is infrastructure toward uniform physical `B0, delta0`; it does
  not move `20/41`, instantiate `TermSource`, or attain window 15 by itself.
