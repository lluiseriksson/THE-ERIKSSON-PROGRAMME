# Physical mixed seam promoted cold gate — live

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
are not part of this queue. No Windows Lean/Lake, Fable or exploratory CI.
