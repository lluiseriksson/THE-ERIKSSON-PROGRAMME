# Eq337 closed physical recursion cold gate v2 — first failure

- Source checkpoint: `609232f4bc9e57365c51e1398ee235e50ea030ff`
- Runner checkpoint: `b79c3318e23a8a9a5d387467ad771597e51e469f`
- Notebook checkpoint: `bc83332d0e0e8a159a8f892f0da1fcbd7441f5f2`
- Runner revision: `eq337-closed-physical-recursion-promoted-cold-v2`
- Failed stage: `eq337_closed_physical_03_balabancmp99eq337complexclosedrecursivebackground_source`
- Materialization duration: `1289.075` seconds
- Failed-stage duration: `6.736` seconds
- Failed-stage exit: `1`
- Canonical evidence payload SHA-256 printed by Colab: `8cd9cddabb9adbb7ba80dde958ea2943b60bd5353176bf86c24f37d811667759`
- Downloaded archive SHA-256: `bcef9acc733ce9195cc7e038bb7187ec80355e81c519ad0bda690f6c113beb65`
- Terminal sentinel: `FINAL_STATUS=FAIL`
- Runtime: disconnected and deleted after the archive was downloaded and verified.

The first compiler error was:

```text
YangMills/RG/BalabanCMP99Eq337ComplexClosedRecursiveBackground.lean:117:10: error:
Type mismatch: after simplification, `tail.bound e` concludes the radius at
`k + (1 + remaining)`, while the goal expects `k + (remaining + 1)`.
```

The same source pass exposed a second normalization mismatch at line 175:
the constructed bound ends at `0 + depth`, while the public theorem expects
`depth`. Both are arithmetic normalization defects in the same module; no
statement, physical constant, hypothesis, or source dictionary is changed by
the repair.

The two preceding source/audit pairs compiled successfully and their audit
declarations used only the allowed axiom set. They remain prefix evidence, not
a seal for the failed recursion module or its downstream root.
