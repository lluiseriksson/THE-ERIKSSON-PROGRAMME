# After physical reflection: exact image-seam gate

Source context: 84ceb5f2f466ab8f4e9dea175fd412c7bf63a21e.
The 17-module physical reflection prefix is cold-sealed in 7b69f8337,
Addendum 1197. The seam construction below remains STATIC DESIGN, not a
compiler result. Its fixed-source orbit draft failed before elaboration
because ReflectionOrbitAlgebra.olean was absent from the retained checkout.
The v2 diagnostic explicitly builds that prerequisite, with the original
source108f30f9 and blob8abe85a4 unchanged. It does not rerun the sealed prefix.

## Inputs inspected

Update 2026-09-07 (Addenda1198-1200): fixed-source coordinate permutation
and source-order series reindexing now pass bounded HOT diagnostics.
The latter preserves the nested order without exchanging sums. Its first
rewrite FAIL is preserved; the explicit paired equality retry passed.
The physical endpoint-transfer draft remains uncompiled, and the physical
seam is not inferred from these algebraic diagnostics. Next: materialize
the sealed physical prefix as an explicit prerequisite and compile that
transfer, then combine with the reindex theorem and boundary-size dictionary.

- NeumannPhysicalHalfCellReflection: simultaneous reflection of BOTH
  endpoints of the literal normalized full Green, at fine boundary N*B,
  where N=L^j and B is an integer. This is not fine-translation invariance.
- BalabanCMP89NeumannReflectionOrbitAlgebra: lower reflection sends
  (k,false) to (-k,true), and (k,true) to (-k,false); upper reflection
  sends them to (1-k,true) and (1-k,false), respectively.
- NeumannActualFullGreenReflectionSummability: actual Eq246 source-image
  sum, with strictly positive rho and positive rectangle sides. Its fine
  rate is rho/N; its amplitude and all mass/strip windows remain explicit.

## Finite next proof, without assuming the seam

Write I_h(n,k,b)=2*k*h+n for b=false, and 2*k*h-n-1 for b=true.
All equations below concern one chosen coordinate mu; other coordinates
stay fixed. Let R be reflection in the lower boundary or upper boundary h.

1. Construct the involutive index maps on the integer Pi index and the
   Boolean Pi branch. Lower: k_mu -> -k_mu, b_mu -> not b_mu.
   Upper: k_mu -> 1-k_mu, b_mu -> not b_mu. Prove the image identity
   R(I_h(n,k,b))=I_h(n,k',b') using the existing orbit lemmas.
2. From simultaneous physical covariance and R(R(y))=y derive
   G(R(x),y)=G(x,R(y)). Do not assume symmetry, transposition, or
   displacement-only dependence of G.
3. Reindex the finite branch sum and then the integer tsum by the above
   equivalences. Keep the source n fixed. This yields the target-boundary
   seam for the actual all-reflecting image series. If changing nested
   summation order, use the existing absolute summability theorem rather
   than treating that exchange as definitional.
4. Specialize to x_mu=0 for the lower ghost value at -1, and to x_mu=h-1
   for the upper ghost value at h. These are the values needed by the
   internal-bond stencil, not a claim that every reflected point is inside.

The upper physical covariance requires h_mu=N*B_mu. This dictionary must
be an explicit construction/equality, with B_mu the regional block count;
arbitrary fine h_mu cannot silently be used as a block boundary. Positivity
of h is required by the summability input, not by the orbit algebra alone.

## What this still does not prove

The seam is necessary but not the regional Green equation. Applying the
actual generated averaging action to the image series, justifying the
operator/sum exchange, and the full-lattice Fourier point-source equation
remain separate. The fine-density-to-counting factor N^-4 is applied once.
Only a proved regional point-source equation may feed inverse uniqueness.

For FULL directions of the finite torus, this all-reflecting family is not
the proposed mixed family. Preserve the original non-strict carrier fit.
The periodic branch n+k*P (one branch, not two) and its seam need the separate
M1/M2/M4 construction in NEUMANN-MIXED-BOUNDARY-CANDIDATE-20260907.md, unless
a physical geometry theorem genuinely excludes FULL directions. Nothing
here excludes them or changes the source kernel.

Counters unchanged: 20/41, TermSource=0, window15 not attained; Clay<0.1%.
