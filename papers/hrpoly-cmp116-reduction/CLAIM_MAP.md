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
- Physical sparse right inverse `E` for the flat block constraint `Q`, with
  `Q E = I`.
- Physical constraint elimination `C = I - E Q`, with `Q C = 0`, `C` fixing
  `ker Q`, and `C^2 = C`.
- Exact sparse norm `||E B|| = M^(d-1) ||B||` and the volume-independent
  estimate `||C|| <= 1 + M^(d-1)` for `d >= 3`.
- Isometric transport of `C` to the finite CMP116 matrix and literal insertion
  into the flat-background Gamma source.
- Literal complement localization `C P_(Z0^c)` and its norm bound by `||C||`.
- Concrete flat Hessian `Delta_flat = K0 + a Q^*Q` and an explicit
  volume-independent finite-range operator-norm bound.
- Rank-localized determinant bound for (2.24), exact outer Gaussian moment
  (2.25), physical carrier cardinality, and their combined absorption into
  `exp(c * |Z0|)` with no ambient-volume exponent.
- Reduction of the finite equation-(2.14) term in the exactly identified
  trivial-background sector to the physical domination `hdom` and routine
  scalar smallness/outer-weight inputs. The source rate, determinant,
  cardinality, and Gaussian integrations are produced internally.

## Explicitly not claimed

- The second variation of the nonabelian Wilson action at the generally
  nontrivial small background `Ubar`.
- The random-walk construction and kernel estimate (2.16) for `R1/R2/R3`.
- The physical interacting-background instance of `hdom`.
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
- `flatBlockConstraint_comp_cmp96ConstraintEliminationCLM`
- `cmp96ConstraintEliminationCLM_idempotent`
- `norm_cmp96ConstraintPivotInsertion`
- `norm_cmp96ConstraintEliminationCLM_le`
- `PhysicalGaugeCMP116Dictionary.norm_cmp116Eq214PhysicalConstraintMatrix_le`
- `PhysicalGaugeCMP116Dictionary.cmp116Eq214PhysicalConstraintMatrix_action`
- `CMP116Eq214FiniteGaussianData.norm_term_le_cauchyRate_of_physicalConstraintGamma_flatDelta_expCard`
