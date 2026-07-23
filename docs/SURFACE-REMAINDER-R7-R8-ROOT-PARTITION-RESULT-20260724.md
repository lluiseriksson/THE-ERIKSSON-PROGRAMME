# R7/R8 exact root-partition audit — result

**State:** exact sign-obstruction evidence; no K2/G2/G6 promotion

The preregistered audit in
`SURFACE-REMAINDER-R7-R8-ROOT-PARTITION-PREREG-20260724.md` passed with
SymPy exact rational arithmetic and root counts:

- R7 has exactly one root in `[1/2,1]`, and exactly one root in
  `[1421/2000,3553/5000] = [7105/10000,7106/10000]`.
- R8 has exactly one root in `[1/2,1]`, and exactly one root in
  `[3411/5000,6823/10000] = [6822/10000,6823/10000]`.
- Both numerator polynomials have exact endpoint signs `(+, -)` on
  `[1/2,1]`; the same `(+, -)` signs occur at the endpoints of their root
  cages.

The machine transcript is
`scripts/surface_remainder_r7_r8_root_partition_transcript.txt`.  This is an
exact root-isolation audit, not a sign certificate inside the cages and not a
uniform majorant.  Any future piecewise use of R7/R8 must separately handle
the two cages and prove the relay/tail inequalities; the Surface closure gate
is unchanged.
