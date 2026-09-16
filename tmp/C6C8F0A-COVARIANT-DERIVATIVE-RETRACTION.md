# C6c.8f0a retraction: (3.35) is not the covariant (3.39) tensor

Status: STATIC NO-GO / NO COMPILER EVIDENCE WAS WITHDRAWN.

The initial C6c.8f0a candidate identified the second bound in CMP99 (3.35)
with the full covariant tensor `D^U_mu A_nu` later defined in (3.39).  Primary
visual inspection of printed p. 396 refutes that identification: (3.35)
prints `|nabla^eta A|`, and (3.36) continues with the ordinary second
difference `|partial_eta^* partial_eta A|`.  The covariant norms are introduced
separately on printed p. 397 for the propagator estimates.

The decisive crop is
`tmp/pdfs/cmp99-p396-eq335-crop.png`, SHA-256
`D7BB6CE7BDC58C61451DA528DB58D2883C993588F59C4DB729AE546EA7AAB653`.

The rejected files originally had hashes

```text
93CC7703B3241BD675CB6E7BD89C22B4EE87059C0A09D7CB5709C50F739325B6  source
FACD927CA939077443D6CE137D66AFD0327E693CAD832B5C424E70F56E1C559C  audit
```

They were never promoted, compiled or counted.  Their status headers now mark
them retracted.  The replacement source dictionary uses the already literal
periodic `torusForwardDiff`, scaled by `eta^-1`, with no background argument.
The covariant construction may later be renamed and reused for (3.39), but it
cannot discharge the regularity hypothesis (3.35).
