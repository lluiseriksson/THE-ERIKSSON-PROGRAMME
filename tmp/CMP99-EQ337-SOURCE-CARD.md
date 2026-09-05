# CMP99 Eq. (3.37) - visual source card

Status: source-verified; the real/complex domain and printed-background
dictionary are present in PRE-VALIDATION scratch. This card is evidence for
the printed statement only; it is not compiler evidence and does not assert
that the scratch objects elaborate.

Additional render used for the tower frontier:

- printed p. 393, (3.19):
  `tmp/pdfs/cmp99-p393-05.png`, SHA-256
  `D1568836A8AA884A830520FB7CDF94D3DFF05246244E7906604D2203BEEA0FDA`
  (295192 bytes).
- printed p. 402, (3.58)--(3.63):
  `tmp/pdfs/cmp99-p402-14.png`, SHA-256
  `D1108C8288EDE05C059818D3800F5AA98A5E57B0AD9E871A1435E1F21DDED28E`
  (289209 bytes).
- printed p. 401, (3.54)--(3.57):
  `tmp/pdfs/cmp99-p401-13.png`, SHA-256
  `26536DF97D43B795F1C4CCD7526D6C19F06DD4B0B8793CEE9377C2BF2B402459`
  (273090 bytes).
- printed p. 39, Proposition 4 continuation and (136):
  `tmp/pdfs/cmp98/eq337-renders/printed-39.png`, SHA-256
  `47D4521C483EC2A0C6D0615F08F2DE9FFD1628FA4260A91C11DD6F04E7B3312F`.

## Primary render

- paper: T. Bałaban, *Propagators for lattice gauge theories in a background
  field*, CMP 99 (1985), 389--434, printed p. 396;
- local render: `tmp/pdfs/cmp99-p396.png`;
- bytes: `277950`;
- SHA-256:
  `15BDDA14DBE560AFE172128D4FDF5234E9B0D6F652F8B811B072A878179F452E`.
- companion render for printed p. 397, fixing the full tensor norm (3.39):
  `tmp/cmp99-p397.png`, `257539` bytes, SHA-256
  `64A9857D6A8750BA59A0D2AA4B705D3213D26437410C47E34FD35D6834683F0D`.

## Exact visual transcription

The complex configuration has the form `U' U`, where `U` takes values in
`G`, `U' = exp(i eta A')`, and `A'` takes values in the complexified Lie
algebra. For `j = 0,...,k`, equation (3.37) requires on `Omega_j`:

```text
U satisfies (3.35), and
|A'| < alpha1 (L^j eta)^-1,
|nabla^eta_U A'| < alpha1 (L^j eta)^-2.
```

The extracted OCR had made the second norm look as if it carried a factor
`2d`; the visual render shows that no such factor is printed.

## Dictionary boundary

- The `A'` of (3.37) is the external multiplicative perturbation. It is not
  the logarithmic representative used earlier to gauge-fix the regular
  baseline background on a cube.
- When the baseline is replaced by that local gauge representative, `A'`
  must be transported by the same adjoint gauge action.  The identity
  `exp(i eta R(u)A') U^u = (exp(i eta A') U)^u` is present as uncompiled
  PRE-VALIDATION scratch; using the untransported `A'` on `U^u` is rejected.
- The physical real slice can reuse
  `cmp98PhysicalSuLeftVariation U A eta` for `U' U`.
- Printed (3.3) fixes the tensor component as
  `eta^-1 * (R(U(x,x+eta e_mu)) A'_nu(x+eta e_mu) - A'_nu(x))`.
  Printed p. 397, (3.39), confirms that the norm in (3.37) is the supremum
  over the complete `(mu,nu)` tensor.  This is the covariant construction
  formerly rejected for ordinary (3.35); it may be reused only under new
  (3.37) provenance, while the historical retraction remains intact.
- The complex theorem needs a complexified one-cochain and its covariant
  derivative. A real sup-norm hypothesis is not an adequate replacement.
- The scratch frontier now constructs the complex-linear matrix realization
  of `SUNLieComplexCoord`, proves its trace is zero, keeps the printed
  Hermitian coordinate as an explicit `1/i` normalization, forms
  `exp(i eta A') U`, packages it in `SL(N,C)`, and states the real-slice
  equality with `cmp98PhysicalSuLeftVariation`.  All of these declarations
  remain uncompiled PRE-VALIDATION source.  They must not be replaced by a
  free complex background if elaboration exposes a mechanical defect.
- The source-facing real and complex domains fix the background action to
  `matrixSUNAdjointModel`; accepting an arbitrary caller-selected adjoint
  model would weaken the physical statement.
- The two inequalities belong to the same fine-lattice field on the
  nonterminal global regions `Omega_j`.  Only after that source domain is
  fixed may a separate dictionary transport the perturbed background into
  the typed regional `Qprime` tower; the bounds themselves must not be
  reformulated as a free family on the coarsened chain.
- The existing retained tower takes real linear isometries and therefore
  applies only on the compact real slice.  The `SL(N,C)` continuation requires
  a separate complex-linear average and a separately constructed analytic
  starred synthesis; neither a fake isometry nor the Hilbert `.adjoint` is a
  valid complex dictionary.
- The finite replacement contract is now explicit in
  `tmp/NEXT-BRICK-C6D-PHYSICAL-REGIONAL-BRIDGE.md`: one-scale analytic
  average, finite complex recursion, independently constructed starred
  synthesis, theorem-proved real-slice agreements, simultaneous gauge
  covariance, and only then the two printed differences.  Visual inspection
  of p. 393 confirms the finite kernel (3.19), while visual inspection of
  p. 402 confirms that the real adjoint has a similar expansion and explicitly
  warns that `F'_2*(A)` is not an adjoint of `F'_2(A)`.  Thus the starred
  one-scale map must be derived as the spacing-weighted algebraic transpose
  of (3.19), checked on the real slice, and complexified without Hermitian
  conjugation; it is production from the printed kernel, not transcription of
  a missing displayed formula.
- The printed pairing fixes the derived normalization: the coarse volume
  factor `(L^j eta)^d` cancels the average row mass `L^{-jd}` against the fine
  weight `eta^d`.  Hence the real starred leaf is unit synthesis with inverse
  transport.  Its analytic continuation must preserve that algebraic formula;
  a second row-mass factor or block-cardinality correction would repeat the
  earlier mass-versus-counting convention bug.
- The transpose used by this analytic continuation must be stated through the
  complex-bilinear extension of the real invariant pairing,
  `B (R(g) X) Y = B X (R(g^{-1}) Y)`.  A Hermitian/sesquilinear pairing would
  add conjugation and lose holomorphy; it is therefore not the source star.
- The interacting complex recursion has one algebraic prerequisite absent
  from the tree: `cmp99SUNLieComplexCoordMatrixLM` currently maps coordinates
  into traceless matrices but is not an equivalence.  Its inverse can be
  constructed explicitly by decomposing a traceless complex matrix `Z` as
  `(Z-Z†)/2 + i (Z+Z†)/(2i)` and applying `suLieCoordIso` to the two
  skew-Hermitian traceless parts.  This equivalence, rather than a fake
  isometry, must transport `SL(N,C)` conjugation back to source coordinates.
- Visual (3.55) confirms a second prerequisite: the `j`-scale contour uses
  the recursively coarsened complex backgrounds
  `overline{U'U}, overline{overline{U'U}}, ...`.  The present finest-scale
  `SL(N,C)` background is therefore insufficient by itself.  A complex
  `Ubar` recursion must produce this chain internally; a free background
  family would rename the source construction rather than implement it.
- CMP99 p. 401 names the exact upstream source for that producer: CMP98 [5]
  definitions (52),(53), identity (97), estimates (102),(103),(160)--(162)
  and Proposition 4.  Authenticated Drive discovery on 2026-08-25 located the
  complete 2629073-byte primary paper as `Averaging operations.pdf` (file ID
  `1MUK4O9gbYz_rI9eSIjEwdajH3vAW17OD`) and a same-size `CMP 98.pdf` copy
  (file ID `11yVLnkAZuZ_FyyqpcOwFuUc7OPHAhfLT`).  The materialized PDF has
  SHA-256 `03409AD81885593D65535550EAFAC08639E66123D4ACF92462847AE2EE4DD7D6`,
  exactly the digest reported by the source packet.  Targeted 300-dpi renders
  visually confirm Proposition 2 and (52)--(53) on printed p. 26, (97) on
  p. 32, (102)--(103) on p. 33, Proposition 4 and (134)--(135) on p. 38,
  its uniformity clause and homogeneous expansion (136) on p. 39, and
  (160)--(162) on p. 42.  Proposition 4 therefore supplies a `k`-uniform
  logarithmic analytic input; it does not itself state a matrix-valued bound
  on the literal `UbarDeviation`.  The analytic `Ubar` chain is
  implementation-open, not source-blocked; the remaining work is the finite
  exp/log recursion and normalization dictionary.  A free deviation bound
  would rename this remaining implication and is not an accepted producer.
- Bibliographic incident closed 2026-08-24: the former CMP98 catalog DOI
  `10.1007/BF01205787` resolves to an unrelated Gustavo Ponce article in the
  same volume.  Springer identifies Bałaban's pp. 17--51 article by DOI
  `10.1007/BF01211042`.  The corrected DOI repairs acquisition metadata only;
  it did not by itself promote any formula; the separate 2026-08-25 hash and
  targeted-render audit above discharges that clean-primary visual gate.
- The same p. 402 render fixes the exact (3.60) bookkeeping:
  `Delta_(U'U) + Q'^*(U'U) a Q'(U'U)` equals the baseline precision minus
  `V'_1(A)` plus the three terms
  `F'_2*(A) a Q'(U)`, `Q'^*(U) a F'_2(A)`, and
  `F'_2*(A) a F'_2(A)`, and this total is defined as baseline minus `V'(A)`.
  Thus `V'(A)` is `V'_1(A)` minus those three averaging terms; the existing
  real-slice scratch signs agree with the rendered formula.
