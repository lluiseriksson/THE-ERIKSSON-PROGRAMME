# Physical image seam: assembly acceptance gate

Status: STATIC DESIGN; not compiler evidence. Transfer diagnostic source
ca988d2a270e89f38a29b89949212c5ccbfeee1c is running after the explicit
NeumannPhysicalHalfCellReflection prerequisite in the retained Colab checkout.
Do not promote dependent sources before the transfer result is preserved.

## Exact endpoint and units

Keep the literal cmp89Eq246NormalizedPhysicalFineToFineGreen L j mass a.
Let N=L^j, m be fine integer side lengths, mu the selected coordinate.
The image reflection uses 2*c*m(mu)-1-x(mu), while the physical theorem
uses 2*N*B-1-x(mu). Require the explicit equality c*m(mu)=N*B.
Lower boundary: c=0,B=0. Upper boundary: c=1 and m(mu)=N*B.
This is not arbitrary fine-translation invariance or transposition.

## Finite assembly

1. Use the proved physical endpoint transfer separately at every source image.
2. Apply Finset.sum_congr, then tsum_congr to retain the printed nested order.
3. Consume neumannBoundaryImage_reflected_source_sum with the source fixed.
4. Retain summable_neumannActualFullGreenReflection_sum explicitly: rho>0,
   positive fine side lengths, and all mass/strip windows. Totalized-tsum
   reindexing alone must not be presented as analytic convergence.
5. Derive lower ghost equality at x(mu)=0 and upper ghost equality at
   x(mu)=m(mu)-1 by named coordinate equalities. No new kernel parameter.

## Remaining boundary

Even a successful seam does not construct the regional inverse: generated
averaging action, justified operator/sum exchange and the full-lattice
point-source equation remain separate. Mixed FULL torus directions retain
their one-branch periodic family; this all-reflecting family does not cover
them by fiat. No stricter carrier-fit hypothesis may silently exclude them.

Counters remain20/41,TermSource=0,window15 not attained.
