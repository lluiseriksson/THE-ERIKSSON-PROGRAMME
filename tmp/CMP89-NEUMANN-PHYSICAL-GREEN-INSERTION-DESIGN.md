# CMP89 rectangular Neumann series: physical Green insertion design

Status: design only.  No Lean declaration in this note is compiler-verified
and this file is not seal authority.

## Boundary

This is step 6 of `CMP89-NEUMANN-RECTANGULAR-RESIDUE-DESIGN.md`.  The exact
affine fibre, varying-period residue product and branch-distance retention are
cold-sealed; the literal `2^d` branch sum remains open.  Physical Green insertion starts only after
that branch sum is sealed, and ends before the CMP89 (2.42) representation
certificate is consumed.

## One common decay object

The analytic input is one certificate for one explicit full-lattice kernel:

```text
fullGreen : (Fin 4 -> Int) -> (Fin 4 -> Int) -> Complex
B0 delta0 : Real
B0_nonneg : 0 <= B0
delta0_pos : 0 < delta0
bound : forall x y,
  norm (fullGreen x y) <=
    B0 * signedL1Weight delta0 (x-y)
```

`B0`, `delta0` and `fullGreen` are parameters of the certificate type, not
fields selected separately for an image or reflection branch.  Every use in
the Neumann series must therefore consume the same three objects.

The first wrapper may be generic algebra over this explicit certificate, but
it is not a physical producer.  The source-facing producer must instantiate
`fullGreen x y` by the literal normalized CMP89 (2.48) Fourier Green at
displacement `x-y` and derive `bound` from
`norm_cmp89Eq248NormalizedFineLatticeStabilizedFourierGreen_le_massUniform_draft`.
The fine decay rate `rho / L^j` and the amplitude
`cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho` must remain
visible until the later fine-to-owner scale dictionary is applied.

## Required outputs

1. For every fixed reflection branch, absolute summability over the integer
   image fibre follows by comparison with the already constructed scalar
   branch-image weight.
2. The finite branch sum is summable with no rearrangement before absolute
   summability is established.
3. The full image series has the bound

   ```text
   norm series <=
     2^4 * B0 *
       (product_mu 2 / (1-exp(-delta0*(2*m_mu)))) *
       signedL1Weight delta0 (x-n).
   ```

   Association of nonnegative factors may differ definitionally, but every
   factor must stay literal.  No rectangle cardinality, common scalar period,
   ball count or independently chosen image constant is admitted.
4. Only after these outputs exist may the CMP89 (2.42) representation
   certificate replace the regional kernel by the series.

## Acceptance gates

- The source-facing wrapper fixes `d = 4`; a generic algebraic helper does not
  by itself count as the physical producer.
- The `mass^2 <= 1`, common-radius and complex-window inputs used by the
  Eq. (2.48) Green remain visible.  This route does not discharge them.
- The order `tsum k (sum branch ...)` from the printed representation is not
  exchanged with `sum branch (tsum k ...)` before branchwise summability has
  been proved.
- The result is infrastructure toward uniform regional `B0, delta0`; it does
  not move `20/41`, attain window 15 or construct a `TermSource`.
