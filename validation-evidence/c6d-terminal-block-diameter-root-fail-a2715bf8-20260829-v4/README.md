# C6d terminal-block diameter v4 — cold root failure

Classification: `FAIL` at the mandatory same-checkout `YangMillsCore` root.
The terminal-block diameter focal and audit completed successfully; no
PRE-VALIDATION notice is retired from this evidence alone.

- mathematical source: `a2715bf8cdae841dfc313ea9f34a23fe1d2bdd35`
- runner checkpoint: `eb854b023ac88576587306adc1b0737a64a631ea`
- evidence payload SHA-256:
  `4F7C8606C9A497141BA8AEC433D0CFAC8B6EEFDDDCC43867D8EA55B02A93CB87`
- downloaded archive SHA-256:
  `0723B11FE2CB06DB7E56890C2678936EC4884D4BA06CADFD4B2F583CFE5B22B7`
- executed notebook SHA-256:
  `1E1C20A84F458A1680F5F451BA606DA548409EC7BB781B0B5B7CDBA3A59936D7`
- failing stage: `02_c6d_terminal_block_diameter_yang_mills_core_root`
- stage exit: `1`
- stage duration: `7091.866` seconds

The first real error is in the unrelated, older
`BalabanCMP99Eq360C6dCanonicalAmbientCompletion` consumer: proof-local names
`A`, `hc`, and `hA` are out of scope.  The later `whnf`/`isDefEq` timeouts are
downstream noise.  Commit `7e90203e8bfd1deb58d998fb5cdad0baab925af5`
binds those proof locals explicitly.  The two terminal-block diameter blobs
are byte-identical between the failed source and that repair commit.

Counters remain exactly `20/41`, `TermSource = 0`; window 15 remains
compatible but unattained.
