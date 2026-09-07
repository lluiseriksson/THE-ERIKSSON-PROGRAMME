# Eq351 cold v1 — fail-closed evidence

The cold Colab run stopped at the first source stage because
`BalabanCMP99Eq337PhysicalComplexPerturbationDomain` imported
`BalabanCMP99Eq337PhysicalRealPerturbationDomain`, while that prerequisite
had not been promoted into source checkpoint
`1315643bad6c5176e1696d9e260cc9a43a5f0d3b`.

This is instrumentation/source-boundary evidence, not a mathematical FAIL.
The runner reported `FINAL_STATUS=FAIL`, retained the runtime for diagnosis,
and emitted the archived evidence preserved here.  The repair widened the
exact gate to include and audit the real perturbation-domain source rather
than silently treating it as an external `.olean`.

The repaired gate is pinned separately; this directory remains immutable
historical evidence for the rejected v1 boundary.
