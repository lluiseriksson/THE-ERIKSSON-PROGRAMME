# (9) Fabricante del prisma theta: public-definition anti-vacuity audit

Status: **MANUAL MANUFACTURER REVIEW COMPLETE; NOT AN EXTERNAL AUDIT**

Every public definition in `YangMills/SU2ThetaPrism` was inspected after the
oracle build.  The audit question is whether a target theorem follows because a
definition has already stored its answer, or from a zero/singleton/empty-domain
degeneracy.

| Public definitions | Review |
|---|---|
| `HalfVertex`, `Branch`, `ReducedBranch`, `connectedCycleRank` | Encode the finite cell data, not the computed ranks.  Ranks `2` and `1` are separate cardinality theorems. |
| `HasThreeDistinctBranches`, `PruningLocalHypothesis` | General predicates over an arbitrary branch/edge type.  Neither is defined as the desired three-branch conclusion; pruning contains the required local observable-independence premise. |
| `CellConfiguration`, `reflect`, `holonomy`, `relativeU`, `relativeV` | Concrete group expressions only.  The reflection identity is proved by group normalization. |
| `chi`, `fundamentalRep` | Concrete matrix trace and defining representation.  Conjugation invariance is a theorem. |
| `TraceRealityCertificate`, `CharacterBoundCertificate` | Missing technical trace steps only; neither contains a weight-invariance, integrability, pairing, norm, or gate conclusion. |
| `branchWeight`, `cellWeight` | Registered three-factor weight.  They contain no target rational constant. |
| `witness` | Contains the pre-registered coefficient `1/2` because that coefficient is part of the supplied witness formula.  Nonzero, norm `3/4`, projection, pairing, and gate do not follow definitionally; `witness_one_one` evaluates it to `3`. |
| `negIdentitySU2` | Concrete `-I_2`; proves the group is not a singleton independently of Haar or endpoint inputs. |
| `su2PositiveCompacts`, `haarSU2` | Standard normalized Haar construction.  `haar_measure_nonzero` proves total mass is nonzero. |
| `HaarSchurSteps` | Stores first/two-character and translated-coordinate integration steps, never a conditional-zero or orthogonality headline. |
| `conditionalU`, `conditionalV`, `conditionalRelative` | Actual Haar integrals of the concrete witness.  Zero is proved later. |
| `pairingU`, `pairingV`, `pairingRelative` | Actual product-Haar pairings with arbitrary test functions. |
| `UPairingIntegrable`, `VPairingIntegrable`, `RelativePairingIntegrable` | General integrability predicates, not orthogonality conclusions. |
| `FubiniCoordinateSteps` | Stores only the three exchange/coordinate equalities.  The zero pairings require the locally proved conditional identities. |
| `CompleteUOrthogonality`, `CompleteVOrthogonality`, `CompleteRelativeOrthogonality` | Universally quantified definitions over all admissible test functions; none is defined as a particular result tuple. |
| `witnessNormSq` | Concrete product-Haar integral; it contains no `3/4`. |
| `NormMomentSteps` | Four component Schur moments and integrability facts.  It contains no witness-norm conclusion; the pointwise witness expansion and integral algebra remain necessary. |
| `WeightMeasurabilityStep` | Measurability only, not integrability or its explicit bound. |
| `TwiceSpin`, `representationDimension`, `CouplingAdmissible`, `couplingMultiplicity`, `CouplingChannel` | General twice-spin triangle/parity interface.  No `Sector` predicate is defined to equal `(2,1,1)`; multiplicity one is computed separately. |
| `singletProjectionCoefficient` | Defined as inverse `representationDimension 1`, not as `1/2`; the exact half is a theorem. |
| `halfTensorMultiplicity` | General adjacent-binomial tensor rule, checked at three low-order cases. |
| `BetaDomain` | Exactly `0 < beta` and `beta <= 1`; `beta=0` is excluded and `beta=1` is proved to belong. |
| `RealCharacterFamily`, `alpha` | General family and the registered Haar integral.  No coefficient value is stored. |
| `centralMultiplier` | Divides by the general representation dimension, not by a target-specific numeral. |
| `thetaPairingFromMultipliers` | Product of the norm and three general central multipliers; contains no `1/16`. |
| `CoefficientRemainderSteps` | The two pre-registered technical series lower steps.  It contains no pairing or `beta^4/512` conclusion. |
| `certifiedThetaPairing` | Uses the real part of the actual `witnessNormSq`; it contains neither `3/4` nor `1/16`. |
| `ManufacturingTechnicalInputs` | Aggregates only the technical records above.  Static validation and the participation review confirm that it contains no endpoint headline. |

Literal inspection confirms that no public `def` stores `3/4`, `1/16`, or
`beta^4/512`.  The unavoidable `1/2` in `witness` is the registered observable
itself; the distinct singlet coefficient is derived from dimension.  The
endpoint also uses the independent witnesses `F(1,1)=3`, Haar mass one,
`beta=1`, three branch cardinality, and `I_2 != -I_2`.

Conclusion: no delivered headline is obtained from `F=0`, `beta=0`, an empty
or singleton group, a zero measure, a missing third branch, or a public
definition that already stores the headline constant.
