# C6d Eq. (3.36) physical-adjoint cold seal

- Verdict: `PASS` in a fresh Colab Pro+ CPU/high-RAM runtime.
- Source checkpoint: `010502d5f48f542856b9c567e97bdc274e65f276`.
- Runner commit: `aeef04f7ff76d14fdd34ae7585c97c312651140d`.
- Runner revision: `c6d-eq336-adjoint-hot-debug-v15`.
- Mathlib pin: `07642720480157414db592fa85b626dafb71355b`.
- Lean toolchain asset SHA-256:
  `bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e`.
- Runtime interval: `2026-08-24T09:49:49.018119Z` to
  `2026-08-24T10:12:37.164888Z`.
- Canonical evidence payload SHA-256:
  `5d443cd083e2aab0caa085e418816a6bfe1682e198f0212383ec67c8f615187c`.
- Stored `evidence.json` SHA-256 (payload plus terminal newline):
  `ec0f6989e4cdca6a8969501e0e9e5f06259680c2ce801d52e0ab269ec21adb1a`.
- Downloaded archive SHA-256:
  `40f74ed1d7599d2e0e9a3c8dabfcda73c598ca92ad1fb8a9e8766afb2ce13520`.

The runner cloned the raw source checkpoint, verified all eleven source blobs,
materialized the pinned dependency graph without restoring `.lake/build`, and
ran the queue stop-on-first-error.  Every child returned exit code zero:
regular-cube source/audit, the Eq. (3.35) forward/witness/class chain, the
finite summation-by-parts reproduction, and the Eq. (3.36) physical
source/audit.  The cold prerequisite build took 1088.999 seconds; the final
Eq. (3.36) source and audit took 21.386 and 23.854 seconds respectively.

The Eq. (3.36) audit printed seventeen allowed axiom blocks drawn from
`propext`, `Classical.choice`, and `Quot.sound`, plus one declaration that
depends on no axioms.  The archive was downloaded, its SHA-256 was verified on
Windows, and the Colab runtime was then disconnected cleanly.

This is a cold seal of the scratch implementation only.  It does not by itself
certify the later promoted paths, remove their `PRE-VALIDATION` notices, move
the `20/41` terminal counter, instantiate `TermSource`, or establish attainment
of window 15.
