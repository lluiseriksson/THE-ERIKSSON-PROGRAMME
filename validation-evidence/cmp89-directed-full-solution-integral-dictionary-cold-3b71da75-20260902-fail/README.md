# CMP89 directed full-solution integral dictionary cold failure

- runner revision: `cmp89-eq246-directed-full-solution-integral-dictionary-cold-v1`
- runner commit: `8ca9407146aa775c05301278ec43a7e33eec13ca`
- runner SHA-256: `e23b8725c42abf8678f172d0ddc291b416247847a858e7cfaec5345612232c4b`
- notebook commit: `329a41574f24e281e3b5aa85b186efcefde48c3c`
- exact source: `3b71da757fa69acfeb02312882b4d147fe1ff972`
- result: `FINAL_STATUS=FAIL`
- first failing stage: `directed_full_solution_integral_dictionary_focal`
- focal exit: `1` after `1336.262 s`
- archive SHA-256: `67060bad796d13d6d95731075ea5e838b0eab073dc942b0b1b966ddf7b6c66a9`
- evidence payload SHA-256: `678dcc81f3f4d49bc2dba7e9d51daa508a9491f08540250b5cdfed293fc5e6f5`

The fresh Colab CPU/high-RAM checkout reached `8522/8523`. The first and
only failing target was
`YangMills.RG.BalabanCMP89Eq246DirectedFullSolutionIntegralDictionary`;
its audit did not run.

The exact Lean errors were at lines 70 and 91: `integral_congr_ae` could not
match a goal still wrapped by
`cmp89Eq249NormalizedFourDimensionalBrillouinIntegral`. The repair unfolds
that wrapper immediately before the two applications. No statement,
constant or hypothesis changes. PRE-VALIDATION remains in force and this
archive is not compiler evidence for the repair.

Counters remain `20/41`, window 15 remains compatible but unattained, and
`TermSource = 0` remains exact.
