/- Copyright (c) 2026 Lluis Eriksson.
SPDX-License-Identifier: AGPL-3.0-or-later -/

import AmosClosure.Core
import AmosClosure.NonVacuity
import AmosClosure.BesselInterface
import AmosClosure.BesselDeriv
import AmosClosure.Riccati
import AmosClosure.AmosBoundProof
import AmosClosure.AmosBarrier
import AmosClosure.BesselRealInterface
import AmosClosure.BesselRealDeriv

/-!
# AmosClosure

One Amos bound (`AmosClosure.AmosBound`), stated once, consumed by
the calibration engine, the surface-track φ-step family, and the
Feynman–Hellmann unit-step family — all inside the pinned mother
core, with rational non-vacuity witnesses.
-/
