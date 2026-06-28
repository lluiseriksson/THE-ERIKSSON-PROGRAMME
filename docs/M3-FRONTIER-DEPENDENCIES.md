# M3 Frontier Dependencies

This note mirrors the executable graph in
`YangMills/RG/M3FrontierDependencies.lean`.

The graph has one source node for each field of
`CMP116RawSourceM3Frontier`, plus four derived nodes:

* `rawSourceScaleFamily`;
* `rawHsharpFrontierProjection`;
* `rawSourceHsharpUVDecay`;
* `marginalM3Assembly`.

The source fields are classified as analytic, geometric, measure-theoretic, or
RG-flow facts.  Derived results such as `hraw`, H# decay,
`SingleScaleUVDecay`, and the M3 conclusion are not frontier fields.

Executable checks in Lean verify:

* the graph is acyclic by a declared topological rank;
* all 30 frontier fields have graph nodes;
* all 30 frontier fields are consumed by at least one derived-node input list;
* the role profile is stable: 11 analytic, 9 geometric, 2 measure-theoretic,
  and 8 RG-flow fields;
* the raw-source scale-family adapter consumes no RG-flow fields;
* the final marginal assembly inputs are RG-flow/IR-side fields;
* derived formal consumers have positive rank and are not source-field nodes;
* every nonterminal derived node is consumed by a later derived node;
* the final `marginalM3Assembly` node transitively depends on every frontier
  field.

This is an audit layer only.  It proves no physical source theorem and does not
construct a witness for the frontier.
