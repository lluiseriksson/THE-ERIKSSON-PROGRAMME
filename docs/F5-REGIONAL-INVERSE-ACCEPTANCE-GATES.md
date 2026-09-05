# F5 regional inverse: source-object gates after ambient value action

Static type review at source10437a1a824bdd920282778cabe2f3da6c40ce4e.
No new theorem, compiler result or regional estimate is claimed here.
The value-action cold gate runs separately. 20/41, TermSource=0,
window15 unattained; Clay <0.1% remain unchanged.

## Existing facts and their exact limits

1. BalabanCMP89CanonicalNeumannReflectionInverseProducer constructs the
   image operator internally and identifies it with the canonical Green
   by rightInverse_unique_of_isCoerciveCLM. Its himage argument still asks
   for the actual regional right-inverse identity. The identity is not
   already supplied by the existence of this conditional producer.
2. BalabanCMP89NeumannDirichletBoundaryNoGo distinguishes internal-bond
   Neumann differentiation from differentiation after zero extension.
   Boundary-crossing bonds are the measured obstruction. It is not a
   theorem comparing Green norms, and it must not be strengthened in prose.
3. The old PhysicalReflectionRepresentation specialization uses Eq248.
   Ledger1006 already reclassified that object as G_j Q_j*, not the full
   fine-to-fine Green. Reuse of the generic inverse-uniqueness theorem does
   not authorize reuse of that physical specialization.
4. cmp99SourceFlatFullPointSourcePhysicalFineToFineGreenIntegrand_neg_swap
   proves a simultaneous negative-momentum/negative-endpoint swap. It does
   not state invariance under the half-cell reflection n -> -n-1.
   BalabanCMP89NeumannReflectionOrbitAlgebra defines the latter explicitly,
   including the upper reflection 2*m-1-n and both orbit branches.

## Finite acceptance sequence; no inferred endpoint equality

| Gate | Required output | Present limitation |
|---|---|---|
| R1: boundary and averaging dictionary | Specify the exact regional precision, rectangle embedding, spacing, and retained Q tower used by the consumer; distinguish Neumann from zero-extension Dirichlet. | Ambient action alone supplies none of these identifications. |
| R2: physical reflection compatibility | Prove the half-cell reflection/intertwining laws for that literal precision, including its Q*Q term and block alignment. | Negative-endpoint swap is not this law. A doubled-torus construction is only a candidate until these identities are proved. |
| R3: internally constructed regional inverse | Build the correct full fine-to-fine image operator and prove precision.comp imageGreen = id; use inverse uniqueness only after this proof. | Do not accept imageGreen=regionalGreen or the right-inverse law as a replacement for producing it. Infinite-image construction additionally needs its genuine summability and sum/operator interchange. |
| R4: regional quantitative endpoint | Transfer value and the required derivative-action estimates to the physical regional consumer, preserving source-owner orientation, one-fibre count, and common depth-uniform constants. | Ambient C*R^2 is neither derivative B0 nor window15. |

The next design check is R1/R2, not an additional generic norm wrapper.
If the actual Q tower does not intertwine with the half-cell reflection,
record the exact discrepancy before choosing a different construction.
No candidate is source-faithful merely because it is called a Green kernel.

This list bounds the named interfaces, not the difficulty or number of
lemmas needed to prove them. In particular, R2 and R3 remain genuine design
and analytic obligations, not mechanical transports.
