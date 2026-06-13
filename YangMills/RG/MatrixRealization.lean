/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/
import Mathlib
import YangMills.RG.HolonomyGauge
import YangMills.RG.NearLog

/-!
# Matrix realization of the lattice gauge group (gauge-RG campaign, brick B4-Ū lattice bridge)

`docs/BALABAN-RG-PLAN.md` B4-Ū (lattice).  The algebra-level gauge
covariance of Bałaban's renormalization-group field map `Ū`
(`NearLog.UbarBlock_conj`, `nearLog_conj`) is stated for units of a
normed algebra.  To act on the **lattice** gauge theory — whose gauge
group `G` is abstract (`GaugeConfig d N G`, `wilsonLine`) — one needs a
representation of `G` as such units.  This file provides that bridge and
transports the lattice holonomy gauge law into the matrix algebra.

**Source.** The matrix realization is the defining representation used
throughout Bałaban's series (CMP 98/109); strategy/framing: Lluis
Eriksson (ai.viXra:2602.0088).

Oracle target: `[propext, Classical.choice, Quot.sound]`. No sorry, no
axioms.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig

/-- A **matrix realization** of a group `G` as units of a complete normed
ℝ-algebra `𝔸` — the bridge between the abstract lattice gauge group and
the matrix `exp`/`log` field map `Ū`.  Inhabited (e.g. `G = 𝔸ˣ` with the
identity homomorphism), hence non-vacuous; for the physical theory
`G = SU(N)` with its defining matrix representation. -/
class MatrixRealization (G : Type*) [Group G] (𝔸 : Type*) [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] where
  /-- The representation as a group homomorphism into the units. -/
  rep : G →* 𝔸ˣ

variable {d N : ℕ} {G : Type*} [Group G] [FiniteLatticeGeometry d N G]
  {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
  [MatrixRealization G 𝔸]

/-- **Lattice holonomy gauge law, transported to the matrix algebra**
(B4-Ū lattice bridge): the represented Wilson line along a connected path
transforms by endpoint conjugation under a gauge transformation.  This
carries the group-level law `wilsonLine_gaugeAct_path` into `𝔸ˣ` via the
representation (a homomorphism), giving the lattice-facing form of the
algebra-level conjugation laws (`nearLog_conj`, `UbarBlock_conj`) that
make `Ū` gauge covariant. -/
theorem rep_wilsonLine_gaugeAct (u : GaugeTransform d N G) (A : GaugeConfig d N G)
    (es : List (FiniteLatticeGeometry.E (d := d) (N := N) (G := G)))
    (a : FinBox d N) (hpath : IsPathFrom a es) :
    (MatrixRealization.rep (wilsonLine (gaugeAct u A) es) : 𝔸ˣ)
      = MatrixRealization.rep (u a)
        * MatrixRealization.rep (wilsonLine A es)
        * (MatrixRealization.rep (u (pathEnd a es)))⁻¹ := by
  rw [wilsonLine_gaugeAct_path u A es a hpath, map_mul, map_mul, map_inv]

end YangMills.RG
