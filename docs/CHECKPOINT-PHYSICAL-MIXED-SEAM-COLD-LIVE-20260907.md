# Physical mixed seam promoted cold gate — completed

Current status: COLD PASS (ledger1226), followed by the prepared normalization
HOT PASS (ledger1227). Both archives were downloaded automatically and
independently verified locally. Runtime unassigned2026-09-07T13:38:42.156745Z
after NO_LEAN_LAKE_ACTIVE; Reconnect UI confirmed and tab61 closed.
Connected duration37m53.016s. No runtime remains from this checkpoint.
The launch details below are historical, not instructions to resume a PID.

Cold archive SHA256 c78fa27d32898b92f5b16d1862fd30cc55ff9c007cdfe7be6052cb4a3669e50c.
HOT archive SHA256 d80bf1b479adfafb568d43335c229c98b060aab77b7d26cadfbabbed5c9e83de.
Both live under their corresponding validation-evidence folders dated20260907.
Next: promote the two validated normalization drafts with exact-body checks;
the physical phase/source/action dictionary remains open. The separate masked
difference repro has NOT run. Counters20/41,TermSource0,window15open.

Source `a5811d5ddd78faf6fe638aa00db30276af826baf`; runner checkpoint
`c63ba76393e82cd6b3b22c127f1c0baa788eb76d`; notebook checkpoint
`63c98b3139dac779a3a936e778b57017b330167e`. All published by fast-forward.
The promotion's proof body and audit lines match the HOT v2 source exactly
(excluding only outer blank lines and the changed PRE-VALIDATION header).
The text guard covers both promoted files.

Runner hash: `dc4ded00a3e31b8db1f688c24038053c0c5864cb9b34d316787f43c0fb84ddb1`.
Independent reader hash: `13861b95a778c480aadac3caeda22f9a761aa4e1d8da324229d6c6d4bd22c6ba`.
Source blobs:
- NeumannPhysicalMixedSeam.lean: `86bb135f617face75445e88a78f7906c596676fdb30fc900c47e453a9d2d3e79`
- NeumannPhysicalMixedSeamAudit.lean: `a8e112a0aa4c90033c8fdb80f7a7799be2752abb7c4a387359c1dcc7f9a46fcb`

Colab CPU/high-RAM50.99028778076172GiB, account lluiseriksson@gmail.com.
Opened 2026-09-07T13:00:49.141010Z, PID2847. One launch, tab61:
https://colab.research.google.com/github/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/63c98b3139dac779a3a936e778b57017b330167e/scripts/colab_neumann_physical_mixed_seam_promoted_cold.ipynb

The own-code security dialogue was confirmed once. UI runner revision and
digest were checked before launch. Do not execute cell1 again.
Cell2 reads the process/log only; it can be used for coarse monitoring.

- Launch log: `/content/physical-mixed-seam-cold-launch-v1/launch.log`.
- Checkout: `/content/hrpoly-neumann-physical-mixed-seam-promoted-cold-v1`.
- Expected archive: `/content/hrpoly-neumann-physical-mixed-seam-promoted-cold-v1-evidence.tar.gz`.
- Queue: physical_seam_prerequisites, physical_seam_focal, physical_seam_audit.
- Audits: summable_neumannPhysicalMixedGreenSeries,
  neumannPhysicalMixedGreenSeries_periodic,
  neumannPhysicalMixedGreenSeries_properBoundary (all namespace YangMills.RG).
- Production output: NeumannPhysicalMixedSeam.olean.

Stop on first real child error. Download and independently verify the
archive before cleanup. In PASS retire only these two production headers;
do not change proof bodies. In FAIL preserve the error before a bounded
repair. The runtime is retained only for evidence handling; disconnect
and close the auxiliary tab when that work is complete.

No cold result yet. The preceding HOT result is ledger1225, not this gate.
Counters20/41, TermSource0, window15 open. Physical source equation,
finite operator interchange and inverse remain separate obligations.
The normalized-Haar and alias-character drafts are still uncompiled and
are not part of this cold queue. No Windows Lean/Lake, Fable or exploratory CI.

## Prepared bounded HOT follow-up after cold evidence preservation

To avoid a separate bootstrap, the retained runtime may now run the
already prepared normalization diagnostic after the cold archive has been
downloaded and independently checked. This explicitly supersedes the
earlier evidence-only cleanup plan, not the mathematical cold queue.
Never launch the HOT diagnostic while a cold child is active or before
the preservation acknowledgement exists.

Runner checkpoint `4f721f8143617fad259c5b2d013a98c1444014e3`:
`scripts/colab_neumann_pointsource_normalization_hot.py`, SHA256
`72b5a1542213276b49a1f68861724769f62b5af8367a84ce7270b83da8cb25ec`.
It verifies the two draft blobs already present at the exact cold source:

- NeumannTorusCharacterIntegralRepro.lean:
  `78e060fc4b296ca2aa14b79281850e6f0921fd17df183f24b809d18754c64317`
- NeumannCenteredAliasCharacterDraft.lean:
  `33e22d4852cbdf17f2d44445528fef1afbd2106f9b63c74d6ca10c867a926b53`

Queue: Mathlib-only Haar repro first; if it passes, alias prerequisites
then alias character repro. Stop on first error; real exits and exact
five names across two audits. No physical source equation claim, no
PRE-VALIDATION retirement. Independent reader:
`scripts/verify_neumann_pointsource_normalization_hot.py`; synthetic
tests accepted1/rejected8, exit0/0.2097599s/19222528bytes observed peak RSS.
Expected HOT archive `/content/neumann-pointsource-normalization-hot-v1.tar.gz`.
After its evidence is preserved, disconnect the runtime cleanly.
