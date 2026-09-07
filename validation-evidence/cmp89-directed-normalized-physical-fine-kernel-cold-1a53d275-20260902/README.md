# CMP89 directed normalized physical fine-kernel cold seal

- Result: `PASS`.
- Source checkpoint: `1a53d2755b05419f2401c5d839fc9a6cffdd0c2d`.
- Runner revision: `cmp89-eq246-directed-normalized-physical-fine-kernel-cold-v2`.
- Runner commit: `8de7bbc980f58a6ab7152537a701251138cae4b7`.
- Launcher commit: `d2569b2ae3bd5126048aed70337458c29e73d9c7`.
- Runtime: Colab Pro+ CPU/high RAM, 50.99 GiB.
- Connected interval: `2026-09-02T10:25:05.940746Z` to
  `2026-09-02T10:45:58.071078Z`.
- Focal: exit 0, `1116.921 s`.
- Audit: exit 0, `11.069 s`.
- Source blob SHA-256:
  - source: `c5c2ac76669a10dcb1e983d7f85fed7efb145787b7c8a348107586bbb4200d32`;
  - audit: `efe636469898034e98c75c01a622f4fbf53efcaeef66e172c496820d61759d56`.
- Evidence payload SHA-256:
  `11AA8B5808C4553EDF33C28B72CE6C5EE9C1B263895E9E143409765B74B0A0F9`.
- Archive SHA-256:
  `7FF8BECE1CE3DC04080CDC1E38F35525099479D2C837D6039941212C0C4ECB8F`.

The fail-closed verifier accepted the official toolchain pin, exact Mathlib
pin, source blobs, textual guards, two zero-exit queue stages and the exact
axiom gate.  Colab lost the historical cell identifier while reconnecting,
so no notebook download is represented as an executed transcript; the
runner-produced archive and its verified payload are the canonical evidence.

This seal is infrastructure for the physical CMP89 contour dictionary.  It
does not prove the generated-finite-Green identification, CMP89 (2.42),
uniform physical `B0`/`delta0`, window 15, rows 23--24, or a `TermSource`.
Counters remain `20/41` and `TermSource = 0`.
