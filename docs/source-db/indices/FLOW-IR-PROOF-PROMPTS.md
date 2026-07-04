# Flow/IR Proof Prompts

## Prompt A - Marginal Coupling Flow

Open `proof.flow.ir.bridge` and `crosswalk.flow-ir-asymptotic-freedom-route`.

Return:

- exact source statement for the coupling recursion or beta-flow;
- hypotheses on coupling smallness, scale, and constants;
- whether the source proves logarithmic/marginal decay rather than geometric decay;
- proposed Lean premise for `BalabanCMP116SourceAssumptions.coupling_recursion`;
- blockers that remain before any gauge-coupling flow consumer can be theorem-fed.

Do not substitute `CouplingFlow.logistic_geometric_decay` for the source beta-flow statement.

## Prompt B - Irrelevant Contraction Boundary

Separate the irrelevant-operator or remainder contraction field from the marginal gauge-coupling field.

Return:

- source object whose contraction may legitimately be geometric;
- metric, scale, and norm convention for that contraction;
- Lean target, if any, for `remainder_geometric_of_logistic`;
- whether this field is only a surrogate or can feed an actual source theorem;
- remaining bridge needed before it can interact with RG source assumptions.

Do not use an irrelevant-remainder contraction theorem to prove `g_k <= C*r^k`.

## Prompt C - IR Covariance Bound

Open the Flow/IR card and the repository declarations around `BalabanCMP116SourceAssumptions.ir_bound`.

Return:

- exact source IR covariance or large-distance bound;
- field variables and scale regime;
- dictionary from source covariance object to the repository IR-bound premise;
- dependencies on CMP109/CMP119 scale conventions;
- blockers separate from the marginal coupling recursion.

Do not infer covariance decay from the existence of a coupling-flow recurrence alone.
