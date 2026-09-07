# Mixed owner transport cold gate in progress

Source `4f2f812dc06d82e5f0b7d93ad6d91d87ad07fe67`.
Runner/reader `53d1fffffe32180bd48f5eb0229113143b6fc8c0`.
Notebook/published HEAD `0be3352323b18850925bc6315b7d14e3573ec290`.
Runner SHA256 `02369cc0f82777652b4877e79da4d4e9c30e84836871686289705c1c86a6ba71`.

Opened 2026-09-07T10:12:52.011513 UTC; CPU 50.99028778076172 GiB;
PID 969; account lluiseriksson@gmail.com. Toolchain installed and versions
verified; last observed stage `clone`, no terminal result yet.
Only tab 54 remains. Do not execute Cell 1 again. Cell 2 is the log reader.

Notebook: https://colab.research.google.com/github/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/0be3352323b18850925bc6315b7d14e3573ec290/scripts/colab_neumann_mixed_owner_transport_promoted_cold.ipynb

Runtime root `/content/hrpoly-neumann-mixed-owner-transport-promoted-cold-v1`.
Launcher `/content/mixed-owner-transport-cold-launch-v1/launch.log`.
Expected archive root plus `-evidence.tar.gz`.

Queue explicitly builds NeumannMixedBranchPackaging AND
NeumannIntegerImageCountingKernel, then NeumannMixedOwnerTransport, then
NeumannMixedOwnerTransportAudit. Stop on first error. Reader:
`scripts/verify_neumann_mixed_owner_transport_promoted_cold.py`.
Self-tests: 1 synthetic positive / 8 negative cases; axiom gate 2/9.

On result: download with Colab files.download (worked directly for all prior
HOT packages), verify archive and reader locally under measured watchdog,
then release runtime and selectively seal only if the cold evidence passes.
No CI, no Windows Lean/Lake. 20/41 and TermSource=0 unchanged.
