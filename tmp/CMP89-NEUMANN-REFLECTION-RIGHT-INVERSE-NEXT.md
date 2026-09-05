# CMP89 (2.42) right-inverse continuation checkpoint

The current specialization removes both arbitrary dictionaries before the
physical identity is attempted:

1. `cmp89SourceNeumannIteratedLiftedRectangleSiteEquiv` fixes the regional
   carrier to the exact complete-block lift of the literal half-open source
   rectangle.
2. The former candidate
   `cmp89SourceFlatGeneratedFiniteDepthCanonicalNeumannPhysicalFullGreen`
   is **not** the full-space scalar required by (2.42).  It specializes the
   same-scale wrapper around CMP89 (2.48), whereas the cold-sealed source-role
   correction identifies (2.48) as `G_j Q_j^*`, with a fine output endpoint
   and a coarse input endpoint.  Addendum 1006 therefore forbids using this
   candidate as the fine-to-fine Green in a physical right-inverse proof.
3. The source-faithful scalar must instead be built from the arbitrary-fine-
   source (2.46) lane, whose integral object is
   `cmp89Eq246NormalizedPhysicalFineToFineGreen`.  The generated periodic
   point-source endpoint is supporting finite Fourier evidence; it does not
   by itself identify the infinite-lattice kernel used by (2.42).
4. Only after that replacement may `cmp89NeumannScalarReflectionOperator`
   construct the finite regional image-series operator internally and
   `cmp89CanonicalNeumannReflectionRepresentation_of_rightInverse` derive
   the target reflection equality by uniqueness.

The remaining load-bearing equality is therefore not (2.42) itself but

```text
regionalPrecision.comp imageGreen = id,
```

where `imageGreen` is built from the fine-to-fine (2.46) kernel, never from
the same-scale (2.48) wrapper. It must be proved for the literal three-term Neumann precision: internal-bond
flat Laplacian, `mass^2`, and the generated `a Q'^* Q'` term.  The proof must
split those three terms before estimation or cancellation.  The complete
block rectangle lift is the alignment input for the `Q'` reflection step.

Before claiming the physical endpoint, also discharge:

- summability of the real slice from the sealed complex Eq. (2.48) decay;
- exact agreement between the generated canonical precision/Green pair and
  the precision used in the right-inverse equation;
- positivity of the scaled rectangle sides;
- the fact that taking `.re` is explicit (no unproved claim that the complex
  Fourier coefficient is real).

## Finite brick chain to the right-inverse law

The physical proof is now bounded by the following seven outputs. A green
prefix does not imply the next item.

1. **Scalar convention gate.** Canonical fine spacing makes terminal spacing
   one.  The regional precision retains the counting-Hilbert coefficient
   with its one volume conversion.  The coefficient identity previously
   written for (2.48) remains valid algebra, but it does not select the
   fine-to-fine kernel and is no longer a producer for this chain.
2. **Full-lattice fundamental solution.** Prove that the literal three-term
   flat full-space precision applied to
   `cmp89Eq248PhysicalFullLatticeGreen` is the point source. This is the
   Fourier inversion content; decay/summability alone does not imply it.
3. **Neumann Laplacian reflection.** On the half-open rectangle, show that
   the even image family transports the ambient flat stencil to the
   internal-bond Neumann Laplacian, including the two boundary faces.
4. **Block-average reflection.** Show that the complete-block rectangle and
   terminal generated `Q'` commute with the same image family. This must use
   the exact retained tower; an arbitrary average is forbidden.
5. **Mass reflection.** The pointwise `mass^2` term commutes with the image
   sum without changing normalization.
6. **Operator/sum interchange.** Use the sealed absolute summability to move
   the finite regional precision through the image sum, combine items 2--5,
   and derive the literal operator equality
   `regionalPrecision.comp imageGreen = id`.
7. **Inverse uniqueness (written, PRE-VALIDATION).** Consume item 6 together
   with the sealed canonical Green inverse/coercivity and derive the printed
   representation; the target equality is never accepted as input.

Items 2--6 are the remaining analytic core. No item in this note moves
`20/41`, constructs a `TermSource`, or attains window 15 until the literal
right-inverse equality is proved and consumed.

## Point-source reduction checkpoint (2026-09-01)

The finite operator equation is now reduced, without loss, to the literal
coordinate point sources by
`finitePiLp_comp_eq_id_iff_pointSources`. The source checkpoint is
`7648e39ae985d13d68b281f682d3044352eb073b`; both the lemma and its audit
remain `PRE-VALIDATION` until their Colab gate passes.

The old combined debug runner at checkpoint `c8c2a40f` must not be used to
seal the physical assembler: its final target still consumes the withdrawn
same-scale (2.48) candidate.  Its mass-reflection stage remains independently
useful and may be checked alone.  A replacement runner must end in the
fine-to-fine (2.46) fundamental-solution and reflection chain above.  This
replacement is not launched while the generated point-source cold gate is in
flight.
