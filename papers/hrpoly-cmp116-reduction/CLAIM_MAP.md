# Claim map

## Machine-checked claims

- Physical interior, boundary, and least admissible localization core.
- Canonical scalar carrier and diagonal projector induced by physical `Z0`.
- Exact finite-dimensional complex Gaussian identities, including correlated
  and coupled forms.
- Exact physical-root matrix action and norm transport.
- `||R_matrix||^2 = ||covariance||` under the certified self-adjoint square
  root identity.
- Positivity of `I - alpha5 R^T P_Z0 R` from
  `alpha5 * covNormBound < 1/2`.
- Analytic implications of (2.20)--(2.21) from explicit exponential-kernel
  and row-sum hypotheses, with no volume factor.
- Literal large-field cutoff suppression (2.22), including retention of the
  cardinality penalty through Gaussian integration.
- Quantitative determinant and inverse-source estimates for (2.24), combined
  into the full parametric majorant
  `sqrt((1-q)^n)^(-1) * exp(||R||^2 sourceNormBound / (2*(1-q)))`.
- Reduction of the finite equation-(2.14) term to `hdom`, a scalar uniform
  source-norm bound, and routine contour/outer-weight bounds; `hmajorant` is
  produced internally.

## Explicitly not claimed

- The concrete CMP116 Wilson-potential and `R1/R2/R3` kernel estimates needed
  to instantiate the proved implications of (2.20)--(2.21).
- A model-specific uniform source-norm bound on the Cauchy contours.
- The termwise estimate (2.26).
- `hraw`, `hRpoly`, or a new Yang--Mills polymer decay theorem.
- Thermodynamic or continuum limits.
- Osterwalder--Schrader/Wightman reconstruction or a mass gap.

## Authoritative endpoints

- `CMP116Eq214FiniteGaussianData.norm_innerIntegral_le_of_physicalGaussianReduction`
- `CMP116Eq214FiniteGaussianData.norm_term_le_cauchyRate_of_physicalGaussianReduction`
- `CMP116Eq214FiniteGaussianData.norm_term_le_cauchyRate_of_physicalGaussianReduction_sourceNorm`
- `cmp116Eq224_localized_gaussianMajorant_le_of_sourceNorm`
- `cmp116Eq224_localized_determinant_prefactor_le`
- `PhysicalGaugeCMP116Dictionary.posDef_physicalRootMatrix_of_alpha5_covariance_half_small_physicalZ0`
- `PhysicalGaugeCMP116Dictionary.coordEquiv_symm_mem_physicalLocalizedCoordinates_localizationCore`
