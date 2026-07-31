# Dependency map

```text
YangMills/L0_Lattice/SU2Basic.lean
YangMills/P8_PhysicalGap/SUN_StateConstruction.lean
Mathlib unitary-matrix identities
        |
        v
SU2WilsonReflectionKernel.lean
  - Re tr(x y⁻¹) as a finite rank-one combination
  - products/powers
  - non-negative Taylor coefficients
  - uniform Taylor convergence
  - two one-variable dominated integral limits
  - Haar quadratic positivity
        |
        +--------------------------+
        |                          |
        v                          v
SU2WilsonReflectionGeometry.lean   SU2WilsonReflectionEndpoint.lean
  - finite cut data                - β > 0
  - Half × Cross × Half            - exact endpoint
  - orientation inversion          - strict non-vacuity
  - factorization identity         - non-constant witness
        |                          - Haar inequality
        +-------------+------------+
                      |
                      v
             SU2OSOracle.lean
             CERTIFICATION.md
             AUDIT.md
```

## Separation of obligations

- **Splitting identity:** an equality of the declared gauge-fixed weight with
  two half weights times the crossing kernel.
- **Kernel PSD:** the Taylor/Fock sum-of-squares theorem; no geometry is used.
- **Cut geometry:** a finite set of crossing plaquettes and an explicit swap
  reflection, with separately integrated crossing variables; no analytic
  positivity is used.
- **Haar quadratic positivity:** an integral theorem obtained from the kernel
  expansion, uniform bounds, and the finite probability Haar measure.
- **Final instance:** combines only the already-proved pieces and includes a
  non-constant SU(2) witness.

## Executed dependency chain

```text
su2_trace_mul_inv_eq_sum_entries
  -> su2WilsonExponent_finiteRank
  -> su2WilsonTaylor_hasContinuousPositivePresentation
  -> su2WilsonTaylor_isHaarPSDKernel
  -> su2WilsonTaylor_tendstoUniformlyOn
  -> su2WilsonInnerIntegral_tendsto
  -> su2WilsonKernelIntegralForm_tendsto
  -> su2WilsonCrossing_isHaarPSDKernel
  -> su2OnePlaquette_reflection_positive
```

## Existing modules inspected but not owned

- `YangMills/OS/ReflectionSplitting.lean`
- `YangMills/OS/SpatialReflection.lean`
- `YangMills/OS/Z2Quotient.lean`
- `YangMills/OS/PSDKernel.lean`
- `YangMills/OS/WilsonCharCombo.lean`
- `YangMills/OS/ZNSubstrate.lean`
- `YangMills/ClayCore/GenericSchurOrthogonality.lean`
- `YangMills/ClayCore/SchurFundamentalOrthogonality.lean`

## Verified obstruction in the published finite API

Let an edge involution have `E` edges and `f` fixed edges, with `N ≥ 2`.
If `Config ≃ Half × Half` intertwines configuration reflection with swap, then
cardinality gives `|Half|² = N^E`.  Fixed points give independently
`|Half| = N^((E+f)/2)`, because a reflected configuration is constant on each
edge orbit.  Comparing the two equalities forces `f = 0`.  Therefore the
published split can only represent a free edge involution.  A physical cut
with fixed/crossing edge variables requires the `Cross` factor above.

There is a second independent mismatch: published `reflConfig` only permutes
edges, while oriented gauge reflection also inverts the reflected link.

The owned endpoint therefore consumes the general Haar finite-rank producer
defined in `SU2WilsonReflectionKernel.lean`; it does not claim to instantiate
the incompatible finite `ZMod N` consumer.
