# R7/R8 root-partition audit — preregistration

**State:** exact sign-partition audit only; no K2/G2/G6 promotion

This contract audits the two symbolic heads recorded in
`SURFACE-REMAINDER-R7-R8-DESIGN-20260723.md`.  Put `x=c^2`; the registered
carrier domain is `x in [1/2,1]`.  The exact numerator polynomials are fixed
by that design record and are not refitted from numerical samples.

## Frozen checks

1. Use exact rational arithmetic and a Sturm/root-count method to count real
   roots in `[1/2,1]` and in each of the cages below.
2. Check exact endpoint signs at `x=1/2` and `x=1`.
3. Check exact signs at the cage endpoints.  The two cages are deliberately
   fixed before the run:

   - R7: `[7105/10000, 7106/10000]`;
   - R8: `[6822/10000, 6823/10000]`.

4. Report the resulting decomposition as a sign-obstruction audit.  The
   root cages are not claimed to be sign-constant; they are excluded from any
   future piecewise majorant until a separate bound handles them.

The output may certify only the root counts and endpoint signs.  It must not
promote R7/R8 to uniform majorants, and it must not alter K2, G2, or G6.
