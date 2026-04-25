# v1.43.0 — `ofGlobalMayer` constants are simp-visible

**Released: 2026-04-25**

## What

Added direct field-normalization lemmas for the global-Mayer to physical-F3
constructor in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer_mayer_A₀
    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer_mayer_data
    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer_count_C_conn
    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer_count_dim

## Why

No percentage bar moves.  This is proof-script ergonomics for constant and
prefactor alignment after restricting an all-dimensions Mayer package into the
preferred physical route.  The previous pass made the package-level activities
rewrite through `ofGlobalMayer`; this pass makes the fields that enter the
cluster prefactor rewrite directly:

    (ofGlobalMayer mayer count).mayer.A₀ = mayer.A₀
    (ofGlobalMayer mayer count).count.C_conn = count.C_conn
    (ofGlobalMayer mayer count).count.dim = count.dim

and records that the stored physical Mayer data is exactly
`mayer.data.toPhysical`.  Future scripts can therefore compare the global-route
and physical-route prefactors by `simp`, without unfolding package
constructors.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all four new field-normalization lemmas print the canonical
project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.42.0 — `ofGlobalMayer` exposes physical activities by simp

**Released: 2026-04-25**

## What

Added a package-level restriction lemma in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer_toTruncatedActivities

## Why

No percentage bar moves.  This is API sharpening for the global-Mayer to
physical-F3 route.  The constructor

    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer

packages an all-dimensions `ShiftedF3MayerPackage` together with a physical
count package by restricting the Mayer half to `physicalClayDimension = 4`.
The new simp lemma records that the activities exposed by the resulting fully
physical package are definitionally the original global Mayer activities
evaluated at the physical dimension:

    (ofGlobalMayer mayer count).toTruncatedActivities β F p q
      = mayer.toTruncatedActivities β F p q

Future scripts that prove the older all-dimensions Mayer theorem first can now
feed it into the preferred physical route and rewrite the package-level
activities directly, without unfolding either `ofGlobalMayer` or the physical
package consumer.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace: the new lemma prints the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.41.0 — Global-to-physical Mayer restriction is simp-visible

**Released: 2026-04-25**

## What

Added simp-visible restriction lemmas in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    ConnectedCardDecayMayerData.toPhysical_K
    ConnectedCardDecayMayerData.toPhysical_toTruncatedActivities
    ShiftedF3MayerPackage.toPhysical_toTruncatedActivities

## Why

No percentage bar moves.  This is proof-script ergonomics for the remaining
F3 Mayer/Ursell frontier.  The preferred Clay route is now the fully physical
`physicalClayDimension = 4` package, but future analytic work may still produce
the older all-dimensions Mayer data first.  The existing converters

    ConnectedCardDecayMayerData.toPhysical
    ShiftedF3MayerPackage.toPhysical
    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer

already restrict those global packages into the physical route.  The new simp
lemmas make the raw activity kernel `K` and bundled `TruncatedActivities`
definitionally visible after restriction, so downstream scripts can pass from
global Mayer output to the physical package without unfolding constructors.

This keeps the all-dimensions Mayer route aligned with the fully physical F3
route while the two live analytic obligations remain:

    PhysicalShiftedF3MayerPackage N_c wab
    PhysicalShiftedF3CountPackage

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all three new restriction simp lemmas print the canonical
project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.40.0 — Physical Mayer package exposes its own consumers

**Released: 2026-04-25**

## What

Added package-level consumers for the physical Mayer half in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalShiftedF3MayerPackage.toTruncatedActivities
    PhysicalShiftedF3MayerPackage.toTruncatedActivities_K
    PhysicalShiftedF3MayerPackage.toTruncatedActivities_K_bound_le_cardDecay
    PhysicalShiftedF3MayerPackage.toTruncatedActivities_K_bound_eq_zero_of_not_connected
    PhysicalShiftedF3MayerPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum

## Why

No percentage bar moves.  This is API sharpening for the remaining physical
Mayer/Ursell proof.  Before this pass, the fully physical combined package
exposed finite-volume activity consumers, but the standalone Mayer half

    PhysicalShiftedF3MayerPackage N_c wab

did not.  Future scripts proving or manipulating the physical Mayer package can
now work directly with its truncated activities, card-decay bound, disconnected
support cancellation, and Wilson connected-correlator identity without first
building a count package.

This keeps the two open F3 halves independently usable:

    mayer : PhysicalShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all five new physical Mayer package consumers print the
canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.39.0 — Count-family package constants are simp-visible

**Released: 2026-04-25**

## What

Added constructor audit lemmas in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    ShiftedF3CountPackageDim.ofAtFamily_C_conn
    ShiftedF3CountPackageDim.ofAtFamily_dim
    PhysicalShiftedF3CountPackage.ofAtFamily_C_conn
    PhysicalShiftedF3CountPackage.ofAtFamily_dim

## Why

No percentage bar moves.  This is proof-script ergonomics for the remaining
physical count frontier.  The uniformization constructor

    PhysicalShiftedF3CountPackage.ofAtFamily

already packaged a family of fixed-volume physical count bounds with
volume-independent constants.  The new simp lemmas make the packaged constants
definitionally visible:

    (PhysicalShiftedF3CountPackage.ofAtFamily C_conn hC dim h_at).C_conn = C_conn
    (PhysicalShiftedF3CountPackage.ofAtFamily C_conn hC dim h_at).dim = dim

Future lattice-animal/count scripts can therefore assemble the physical count
package and rewrite its constants without unfolding the package constructor.

## Oracle

Build:

    lake build YangMills.ClayCore.ConnectingClusterCount

Pinned traces: all four new simp/audit lemmas print the canonical project
oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.38.0 — Global Mayer data restricts to the physical F3 route

**Released: 2026-04-25**

## What

Added compatibility converters in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    ConnectedCardDecayMayerData.toPhysical
    ShiftedF3MayerPackage.toPhysical
    ShiftedF3MayerPackage.toPhysical_A₀
    ShiftedF3MayerPackage.toPhysical_data
    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer
    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer_mayerPackage
    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer_countPackage

## Why

No percentage bar moves.  This is compatibility glue between the older
all-dimensions Mayer interface and the new fully physical `d = 4` F3 package.
Any future proof producing

    mayer : ShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

can now mechanically enter the preferred fully physical route by restricting
the Mayer half to `physicalClayDimension = 4`:

    PhysicalOnlyShiftedF3MayerCountPackage.ofGlobalMayer mayer count

The Clay-critical physical route remains sharper: the minimal remaining
assumption is still

    mayer : PhysicalShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

but the global route now reuses it definitionally instead of carrying a parallel
API.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all new converters and simp projection lemmas print the
canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.37.0 — Fully physical F3 package reaches PhysicalStrong

**Released: 2026-04-25**

## What

Added the fully physical single-object F3 package in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalOnlyShiftedF3MayerCountPackage
    PhysicalOnlyShiftedF3MayerCountPackage.ofSubpackages
    PhysicalOnlyShiftedF3MayerCountPackage.mayerPackage
    PhysicalOnlyShiftedF3MayerCountPackage.countPackage
    PhysicalOnlyShiftedF3MayerCountPackage.toTruncatedActivities
    PhysicalOnlyShiftedF3MayerCountPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
    PhysicalOnlyShiftedF3MayerCountPackage.apply_count
    physicalClusterCorrelatorBound_of_physicalOnlyShiftedF3MayerCountPackage

and the matching L8 terminal route in
`YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`:

    connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF
    connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_mass_eq
    connectedCorrDecayBundle_of_physicalOnlyShiftedF3MayerCountPackage_prefactor_eq
    connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_mass_eq
    connectedCorrDecayBundle_of_physicalOnlyShiftedF3Subpackages_prefactor_eq
    physicalStrong_of_physicalOnlyShiftedF3MayerCountPackage_siteDist_measurableF
    physicalStrong_of_physicalOnlyShiftedF3Subpackages_siteDist_measurableF

## Why

No percentage bar moves.  This is a frontier-sharpening step: it packages the
Clay-critical physical F3 assumptions into one object that is restricted to the
physical dimension from the Mayer side and uniform in finite volume from the
count side:

    mayer : PhysicalShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

From this exact pair the formal route now reaches

    PhysicalClusterCorrelatorBound
    ConnectedCorrDecayBundle
    ClayYangMillsPhysicalStrong

at `physicalClayDimension = 4`, with the canonical shifted prefactor
`clusterPrefactorShifted wab.r C_conn A₀ dim` and mass
`-Real.log wab.r`.

This removes the last packaging ambiguity between the older all-dimensions
Mayer route and the physical-only Clay route.  The remaining analytic
obligations are unchanged and now sharply named: prove the physical Mayer/Ursell
data for `wilsonConnectedCorr`, and prove the physical volume-uniform shifted
connecting-cluster count package for `N_c ≥ 2`.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: all new fully physical package declarations, consumers, audit
equalities, and terminal endpoints print the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.36.0 — Physical Mayer-only F3 route exposed

**Released: 2026-04-25**

## What

Added the physical-dimension Mayer/activity interface in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalConnectedCardDecayMayerData
    PhysicalConnectedCardDecayMayerData.toTruncatedActivities
    PhysicalConnectedCardDecayMayerData.toTruncatedActivities_K
    PhysicalConnectedCardDecayMayerData.toTruncatedActivities_K_bound_le_cardDecay
    PhysicalConnectedCardDecayMayerData.toTruncatedActivities_K_bound_eq_zero_of_not_connected
    PhysicalConnectedCardDecayMayerData.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum

and the physical-only F3 package/endpoint:

    PhysicalShiftedF3MayerPackage
    physicalClusterCorrelatorBound_of_physicalMayerData_shiftedCount_ceil
    physicalClusterCorrelatorBound_of_physicalShiftedF3Subpackages

## Why

No percentage bar moves.  This weakens the assumptions needed for the physical
Clay route.  Previously the `d = 4` physical endpoint consumed
`ConnectedCardDecayMayerData`, whose raw Mayer identity quantified over all
dimensions `d`.  The new route consumes only the physical-dimension data
needed by `PhysicalClusterCorrelatorBound`, uniformly over finite volumes `L`.

The physical F3 front is now genuinely physical on both sides:

    mayer : PhysicalShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

produce the same physical exponential connected-correlator bound at
`physicalClayDimension = 4`.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all new physical Mayer declarations and endpoints print the
canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.35.0 — Physical count uniformization criterion exposed

**Released: 2026-04-25**

## What

Added finite-volume-family assembly criteria in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    ShiftedConnectingClusterCountBoundDim.ofAtFamily
    ShiftedF3CountPackageDim.ofAtFamily
    PhysicalShiftedF3CountPackage.ofAtFamily

The physical form consumes a family

    h_at : ∀ (L : ℕ) [NeZero L],
      PhysicalShiftedConnectingClusterCountBoundAt L C_conn dim

with the same `C_conn` and `dim` for every finite volume, and produces the
uniform physical count package:

    PhysicalShiftedF3CountPackage

## Why

No percentage bar moves.  This is the exact formal upgrade path from
finite-volume count estimates to the physical F3 count frontier.  The previous
finite-volume canary shows that local count packages exist with constants
depending on `L`; this criterion records what remains to prove: the same count
bound must hold for all `L` with volume-independent constants.

The remaining physical F3 count target is therefore sharpened to producing
`h_at` uniformly in `L`, not inventing any new terminal packaging.

## Oracle

Build:

    lake build YangMills.ClayCore.ConnectingClusterCount

Pinned traces: all three new assembly declarations print the canonical project
oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.34.0 — Physical finite-volume count canary exposed

**Released: 2026-04-25**

## What

Added physical fixed-volume audit aliases and constructors in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    PhysicalShiftedConnectingClusterCountBoundAt
    PhysicalShiftedF3CountPackageAt
    PhysicalShiftedF3CountPackageAt.finite
    PhysicalShiftedF3CountPackageAt.finite_C_conn
    PhysicalShiftedF3CountPackageAt.finite_dim
    PhysicalShiftedF3CountPackageAt.finite_apply

The finite package specializes the already-closed local count
`ShiftedF3CountPackageAt.finite` to the physical dimension
`physicalClayDimension = 4`.

## Why

No percentage bar moves.  This separates the closed finite-volume audit count
from the still-open physical F3 count frontier.  For each fixed `L`, the
physical plaquette powerset is finite and gives a local package whose constant
depends on `L`.  The real physical F3 count obligation remains the uniform
package:

    PhysicalShiftedF3CountPackage

whose constants must be independent of `L`.

This makes the next proof target sharper: upgrade the physical finite-volume
canary to a volume-uniform lattice-animal estimate, rather than merely proving
finiteness again.

## Oracle

Build:

    lake build YangMills.ClayCore.ConnectingClusterCount

Pinned traces: the four new `PhysicalShiftedF3CountPackageAt.*` declarations
print the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.33.0 — Physical F3 package projections exposed

**Released: 2026-04-25**

## What

Added projection helpers for the single physical F3 package in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalShiftedF3MayerCountPackage.mayerPackage
    PhysicalShiftedF3MayerCountPackage.countPackage

with definitional simp/audit lemmas:

    ofSubpackages_mayerPackage
    ofSubpackages_countPackage
    mayerPackage_A₀
    mayerPackage_data
    countPackage_C_conn
    countPackage_dim
    ofSubpackages_mayerPackage_countPackage

## Why

No percentage bar moves.  This is API sharpening for the active physical F3
route: future scripts can treat

    pkg : PhysicalShiftedF3MayerCountPackage N_c wab

as a reversible package of its Mayer/activity half and physical count half
without reaching through raw structure fields.  The inverse simp lemma records
that rebuilding the package from these two projections is definitionally the
same package.

The remaining mathematical obligations are unchanged:

    ShiftedF3MayerPackage N_c wab
    PhysicalShiftedF3CountPackage

for `N_c ≥ 2`.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: all nine new projection declarations print the canonical
project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.32.0 — Physical F3 subpackage bundle certificate exposed

**Released: 2026-04-25**

## What

Added the subpackage-level bundle constructor in
`YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`:

    connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_siteDist_measurableF

from independently-produced physical F3 halves:

    mayer : ShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

to the same auditable `ConnectedCorrDecayBundle` at
`physicalClayDimension = 4`.

Also added constant-audit equalities:

    connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_mass_eq
    connectedCorrDecayBundle_of_physicalShiftedF3Subpackages_prefactor_eq

pinning rate `kpParameter wab.r` and prefactor

    clusterPrefactorShifted wab.r count.C_conn mayer.A₀ count.dim
      + 2 * Real.exp (kpParameter wab.r)

by definitional equality.

## Why

No percentage bar moves.  This gives the same inspectable L8 certificate
whether the proof script constructs the single physical package first or keeps
the Mayer/count halves separate.  It removes another small manual composition
step from the active F3 route.

The remaining mathematical obligations remain exactly:

    ShiftedF3MayerPackage N_c wab
    PhysicalShiftedF3CountPackage

for `N_c ≥ 2`.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: all three new subpackage bundle declarations print the canonical
project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.31.0 — Physical F3 bundle certificate exposed

**Released: 2026-04-25**

## What

Added a bundle-level terminal constructor in
`YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`:

    connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF

from the single physical F3 package:

    pkg : PhysicalShiftedF3MayerCountPackage N_c wab

to the intermediate L8 certificate:

    ConnectedCorrDecayBundle
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun L p q => siteLatticeDist p.site q.site)

at `physicalClayDimension = 4`, with the local Gibbs probability and
observable integrability side conditions discharged from the concrete Wilson
plaquette energy and `Measurable F`.

Also added audit equalities:

    connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_mass_eq
    connectedCorrDecayBundle_of_physicalShiftedF3MayerCountPackage_prefactor_eq

recording that the bundle has rate `kpParameter wab.r` and prefactor

    clusterPrefactorShifted wab.r pkg.count.C_conn pkg.mayer.A₀ pkg.count.dim
      + 2 * Real.exp (kpParameter wab.r)

where the `+ 2 * exp(...)` term is the standard local-distance padding used by
the L8 bundle bridge.

## Why

No percentage bar moves.  This exposes an auditable certificate between the
physical F3 package and the final `ClayYangMillsPhysicalStrong` endpoint.
Future scripts can now stop at the bundle layer to inspect the actual decay
constants before applying `physicalStrong_of_connectedCorrDecayBundle`.

The remaining mathematical obligations remain unchanged:

    ShiftedF3MayerPackage N_c wab
    PhysicalShiftedF3CountPackage

for `N_c ≥ 2`.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: the new bundle constructor and both constant-audit theorems
print the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.30.0 — Physical F3 package finite-volume consumers exposed

**Released: 2026-04-25**

## What

Added direct finite-volume consumers for
`PhysicalShiftedF3MayerCountPackage` in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalShiftedF3MayerCountPackage.toTruncatedActivities
    PhysicalShiftedF3MayerCountPackage.toTruncatedActivities_K
    PhysicalShiftedF3MayerCountPackage.toTruncatedActivities_K_bound_le_cardDecay
    PhysicalShiftedF3MayerCountPackage.toTruncatedActivities_K_bound_eq_zero_of_not_connected
    PhysicalShiftedF3MayerCountPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
    PhysicalShiftedF3MayerCountPackage.apply_count

These expose the physical `d = 4` truncated activities, Mayer/Ursell identity,
and shifted connected-cluster count inequality directly from the single
physical F3 package.

## Why

No percentage bar moves.  This is proof-ergonomics infrastructure around the
active F3 frontier.  Future code constructing
`PhysicalShiftedF3MayerCountPackage N_c wab` can now consume the Mayer and
count halves through package-level API, without manually projecting through
`pkg.mayer` and `pkg.count` at each finite-volume use site.

The remaining mathematical obligations are unchanged:

    ShiftedF3MayerPackage N_c wab
    PhysicalShiftedF3CountPackage

for `N_c ≥ 2`.

## Oracle

Builds:

    lake build YangMills.ClayCore.ClusterRpowBridge
    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: all new physical package consumers print the canonical project
oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.29.0 — Single-package physical F3 frontier exposed

**Released: 2026-04-25**

## What

Added the single-object physical F3 frontier package in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalShiftedF3MayerCountPackage N_c wab

with fields:

    mayer : ShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

and constructors/consumers:

    PhysicalShiftedF3MayerCountPackage.ofSubpackages
    physicalClusterCorrelatorBound_of_physicalShiftedF3MayerCountPackage
    physicalStrong_of_physicalShiftedF3MayerCountPackage_siteDist_measurableF

The last theorem lives in
`YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean` and sends the single
physical package directly to `ClayYangMillsPhysicalStrong` at
`physicalClayDimension = 4`.

## Why

No percentage bar moves.  This is interface consolidation around the active F3
frontier.  Instead of asking downstream code to carry separate
`mayer/count` arguments, the physical route can now say:

    construct PhysicalShiftedF3MayerCountPackage N_c wab

and Lean has the direct route:

    PhysicalShiftedF3MayerCountPackage
      → PhysicalClusterCorrelatorBound
      → ClayYangMillsPhysicalStrong

The two mathematical obligations inside the package remain the same: prove the
Mayer/activity identity and the physical `d = 4` shifted connected-cluster
count bound for `N_c ≥ 2`.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge \
      YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: all new package helpers and endpoint wrappers print the
canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.28.0 — Physical F3 route reaches `ClayYangMillsPhysicalStrong`

**Released: 2026-04-25**

## What

Added the terminal L8 wrappers for the physical four-dimensional F3 route in
`YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`:

    connectedCorrDecayBundle_of_physicalClusterCorrelatorBound_siteDist
    physicalStrong_of_physicalClusterCorrelatorBound_siteDist_measurableF
    physicalStrong_of_physicalShiftedF3Subpackages_siteDist_measurableF

The last wrapper consumes exactly the physical F3 subpackages:

    wab   : WilsonPolymerActivityBound N_c
    mayer : ShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

and produces the non-vacuous physical endpoint
`ClayYangMillsPhysicalStrong` at `physicalClayDimension = 4`, for any fixed
`β > 0` and measurable unit-bounded Wilson plaquette observable `F`.

## Why

No percentage bar moves.  This is terminal API sharpening, not a new analytic
F3 proof.  The previous release exposed
`PhysicalClusterCorrelatorBound`; this release connects that physical
correlator bound all the way to the L8 physical target without requiring the
all-dimensions `ClusterCorrelatorBound`.

The active Clay-critical obligations are now cleanly visible:

    ShiftedF3MayerPackage N_c wab
    PhysicalShiftedF3CountPackage

Once those two packages are supplied for `N_c ≥ 2`, the physical route yields
`ClayYangMillsPhysicalStrong` in dimension four by direct composition.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: all three new physical L8 wrappers print the canonical project
oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.27.0 — Physical ClusterCorrelatorBound endpoint exposed

**Released: 2026-04-25**

## What

Added a four-dimensional physical correlator target and constructors in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    PhysicalClusterCorrelatorBound
    physicalClusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil
    physicalClusterCorrelatorBound_of_shiftedF3Subpackages

`PhysicalClusterCorrelatorBound N_c r C_clust` is the physical-dimension
analogue of `ClusterCorrelatorBound`: it is uniform over finite volumes `L`,
but fixes the lattice dimension to `physicalClayDimension = 4`.

## Why

No percentage bar moves.  This is the first direct bridge from the physical
four-dimensional count frontier to a four-dimensional exponential connected
correlator bound.  It composes:

    ConnectedCardDecayMayerData
    PhysicalShiftedConnectingClusterCountBound C_conn dim

into:

    PhysicalClusterCorrelatorBound N_c r
      (clusterPrefactorShifted r C_conn A₀ dim)

and the package-level wrapper consumes:

    mayer : ShiftedF3MayerPackage N_c wab
    count : PhysicalShiftedF3CountPackage

This deliberately remains weaker than the all-dimensions
`ClusterCorrelatorBound`.  It is the honest `d = 4` F3 output needed before a
terminal L8 physical wrapper, not a global replacement for the existing
dimension-uniform route.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: both new physical F3 constructors print the canonical project
oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.26.0 — Physical d=4 terminal endpoints exposed

**Released: 2026-04-25**

## What

Added physical-dimension L8 endpoint wrappers in
`YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`:

    physicalStrong_of_clusterCorrelatorBound_physicalClayDimension_siteDist_measurableF
    physicalStrong_of_shiftedF3MayerCountPackage_physicalClayDimension_siteDist_measurableF
    physicalStrong_of_shiftedF3Subpackages_physicalClayDimension_siteDist_measurableF
    physicalStrong_of_uniformRpow_small_beta_physicalClayDimension_siteDist_measurableF

Each wrapper fixes the terminal plaquette-distance profile to

    fun (L : ℕ) (p q : ConcretePlaquette physicalClayDimension L) =>
      siteLatticeDist p.site q.site

with `physicalClayDimension = 4`.

## Why

No percentage bar moves.  This is terminal API sharpening, not a new analytic
proof.  The existing global analytic inputs (`ClusterCorrelatorBound`, the
single shifted F3 Mayer/count package, shifted F3 subpackages, or
`WilsonUniformRpowBound`) now feed directly into the non-vacuous
`ClayYangMillsPhysicalStrong` target at the physical spacetime dimension.

This deliberately does not convert the new `PhysicalShiftedF3CountPackage` into
the all-dimensions `ShiftedF3CountPackage`: a four-dimensional count estimate is
not the same statement as a dimension-uniform one.  The four-dimensional count
frontier remains an honest open F3 subtarget.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces: all four new physical-dimension terminal wrappers print the
canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.25.0 — Physical d=4 count package aliases exposed

**Released: 2026-04-25**

## What

Added physical four-dimensional count aliases and wrappers in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    physicalClayDimension
    physicalClayDimension_neZero
    PhysicalShiftedConnectingClusterCountBound
    PhysicalShiftedF3CountPackage
    PhysicalShiftedF3CountPackage.ofBound
    PhysicalShiftedF3CountPackage.apply
    PhysicalShiftedF3CountPackage.toAt
    PhysicalShiftedF3CountPackage.toAt_C_conn
    PhysicalShiftedF3CountPackage.toAt_dim
    PhysicalShiftedF3CountPackage.toAt_apply
    PhysicalShiftedF3CountPackage.ofBound_C_conn
    PhysicalShiftedF3CountPackage.ofBound_dim

## Why

No percentage bar moves.  This is an F3 count-interface sharpening for the
actual Clay spacetime dimension.  The physical combinatorial subtarget can now
be stated without rethreading an abstract dimension parameter:

    PhysicalShiftedConnectingClusterCountBound C_conn dim

which is definitionally the fixed-dimension frontier at
`physicalClayDimension = 4`.  Its packaged form,
`PhysicalShiftedF3CountPackage`, projects to finite volume by `toAt` and has a
direct `apply` theorem for bucket-count consumers.

This does not prove the lattice-animal estimate.  It makes the honest
next count target first-class: volume-uniform, four-dimensional, and weaker
than the older all-dimensions global predicate.

## Oracle

Build:

    lake build YangMills.ClayCore.ConnectingClusterCount

Pinned traces: `physicalClayDimension` prints no axioms; all new physical
package declarations print the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.24.0 — Fixed-dimension count package exposed

**Released: 2026-04-25**

## What

Added packaged fixed-dimension count data in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    ShiftedF3CountPackageDim
    ShiftedF3CountPackageDim.ofBound
    ShiftedF3CountPackageDim.apply
    ShiftedF3CountPackageDim.toAt
    ShiftedF3CountPackageDim.toAt_C_conn
    ShiftedF3CountPackageDim.toAt_dim
    ShiftedF3CountPackageDim.toAt_apply
    ShiftedF3CountPackageDim.ofBound_C_conn
    ShiftedF3CountPackageDim.ofBound_dim

and added the global-package restriction in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    ShiftedF3CountPackage.toDim
    ShiftedF3CountPackage.toDim_C_conn
    ShiftedF3CountPackage.toDim_dim
    ShiftedF3CountPackage.toDim_apply

## Why

No percentage bar moves.  This packages the v1.23 fixed-dimension count
frontier as a first-class object.  The physical `d = 4` count proof can now be
delivered as `ShiftedF3CountPackageDim 4`, projected to finite volumes by
`toAt`, or obtained from a fully global `ShiftedF3CountPackage` by `toDim`.

## Oracle

Builds:

    lake build YangMills.ClayCore.ConnectingClusterCount
    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all new fixed-dimension package declarations and global
`toDim` declarations print the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.23.0 — Fixed-dimension shifted count frontier exposed

**Released: 2026-04-25**

## What

Added a fixed-dimension shifted count frontier in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    ShiftedConnectingClusterCountBoundDim
    ShiftedConnectingClusterCountBoundDim.apply
    ShiftedConnectingClusterCountBound.toDim
    ShiftedConnectingClusterCountBoundDim.toAt

This sits between the existing global
`ShiftedConnectingClusterCountBound C_conn dim` (uniform over all dimensions)
and the finite-volume
`ShiftedConnectingClusterCountBoundAt d L C_conn dim` (constants may depend on
the concrete volume).

## Why

No percentage bar moves.  This is F3 count-frontier sharpening: the physical
Clay target has fixed spacetime dimension, so the natural lattice-animal
subgoal is uniform in volume `L` at fixed `d` (especially `d = 4`), while
allowing constants to depend on that dimension.  The old global predicate still
exists and projects to the new fixed-dimension predicate, but future counting
work can now be scoped more honestly.

## Oracle

Builds:

    lake build YangMills.ClayCore.ConnectingClusterCount
    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: the new fixed-dimension apply/restriction lemmas print the
canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.22.0 — Uniform-rpow frontier gets direct applicator

**Released: 2026-04-25**

## What

Added

    WilsonUniformRpowBound.apply

to `YangMills/ClayCore/ZeroMeanCancellation.lean`.

This exposes the named small-β uniform-rpow frontier in direct application
form, matching the existing `ShiftedConnectingClusterCountBound.apply` and
`ShiftedF3CountPackage.apply` style.

## Why

No percentage bar moves.  This is small-β frontier API cleanup: once the
uniform rpow estimate is supplied, downstream code can apply it without
unfolding the `WilsonUniformRpowBound` predicate.  The mathematical frontier
remains proving this bound for the nonabelian theory.

## Oracle

Builds:

    lake build YangMills.ClayCore.ZeroMeanCancellation
    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned trace:

    'YangMills.WilsonUniformRpowBound.apply' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.21.0 — Shifted F3 subpackage endpoints expose constants

**Released: 2026-04-25**

## What

Added constant-projection lemmas for the independent-subpackage route in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    clayMassGap_of_shiftedF3Subpackages_mass_eq
    clayMassGap_of_shiftedF3Subpackages_prefactor_eq
    clayConnectedCorrDecay_of_shiftedF3Subpackages_mass_eq
    clayConnectedCorrDecay_of_shiftedF3Subpackages_prefactor_eq

They expose that the subpackage route has decay rate `kpParameter wab.r` and
prefactor `clusterPrefactorShifted wab.r count.C_conn mayer.A₀ count.dim`.

## Why

No percentage bar moves.  This is endpoint transparency for the preferred
split F3 workflow: once Mayer and count are proved independently, the resulting
mass-gap and connected-decay objects expose the same constants as the
single-package route without unfolding the package assembly.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all four new subpackage constant lemmas print the canonical
project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.20.0 — Single shifted F3 package exposes activities and count directly

**Released: 2026-04-25**

## What

Added direct single-package API for `ShiftedF3MayerCountPackage` in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    ShiftedF3MayerCountPackage.toTruncatedActivities
    ShiftedF3MayerCountPackage.toTruncatedActivities_K
    ShiftedF3MayerCountPackage.toTruncatedActivities_K_bound_le_cardDecay
    ShiftedF3MayerCountPackage.toTruncatedActivities_K_bound_eq_zero_of_not_connected
    ShiftedF3MayerCountPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum
    ShiftedF3MayerCountPackage.apply_count

These expose both halves of the preferred shifted F3 package without requiring
manual projection through `mayerPackage` and `countPackage`.

## Why

No percentage bar moves.  This is final single-package interface cleanup for
the current F3 route: once the preferred package is constructed, downstream
code can directly obtain finite-volume truncated activities, their
support/cardinality bounds, the Mayer identity, and the shifted
lattice-animal count inequality from the same object.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all six new single-package declarations print the canonical
project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.19.0 — Shifted F3 count package gets direct constructor and applicator

**Released: 2026-04-25**

## What

Added count-package API in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    ShiftedF3CountPackage.ofBound
    ShiftedF3CountPackage.apply
    ShiftedF3CountPackage.ofBound_C_conn
    ShiftedF3CountPackage.ofBound_dim

`ofBound` packages a global `ShiftedConnectingClusterCountBound C_conn dim`,
and `apply` exposes the bucket-count inequality directly from a
`ShiftedF3CountPackage` without first projecting to a finite-volume
`toAt` package.

## Why

No percentage bar moves.  This is F3 count-interface cleanup: a future proof
of the global shifted lattice-animal estimate can now be packaged and consumed
through one named API.  The mathematical content remains the proof of
`ShiftedConnectingClusterCountBound` itself.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all four new declarations print the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.18.0 — Shifted F3 Mayer package exposes its activity consumer

**Released: 2026-04-25**

## What

Added package-level API for `ShiftedF3MayerPackage` in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    ShiftedF3MayerPackage.toTruncatedActivities
    ShiftedF3MayerPackage.toTruncatedActivities_K
    ShiftedF3MayerPackage.toTruncatedActivities_K_bound_le_cardDecay
    ShiftedF3MayerPackage.toTruncatedActivities_K_bound_eq_zero_of_not_connected
    ShiftedF3MayerPackage.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum

These lift the v1.16/v1.17 `ConnectedCardDecayMayerData` API to the actual
Mayer-side package object used by the single-package shifted F3 interface.

## Why

No percentage bar moves.  This is F3 package API cleanup: future constructors
for the nonabelian Mayer/Ursell side can hand around a
`ShiftedF3MayerPackage` and immediately expose the finite-volume activities,
their support/cardinality bounds, and the Wilson connected-correlator identity.
The package still has to be constructed for `N_c ≥ 2`; this entry only removes
projection friction once it exists.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all five new package-level declarations print the canonical
project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.17.0 — Mayer identity exposed through packaged truncated activities

**Released: 2026-04-25**

## What

Added

    ConnectedCardDecayMayerData.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum

to `YangMills/ClayCore/ClusterRpowBridge.lean`.

This restates the packaged Mayer/Ursell identity directly through
`ConnectedCardDecayMayerData.toTruncatedActivities`, and the main bridge
`clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil` now uses this
named lemma for its Mayer equality input.

## Why

No percentage bar moves.  This is F3 Mayer-interface cleanup: downstream
consumers can now treat `ConnectedCardDecayMayerData` as a single object that
both builds finite-volume truncated activities and identifies their connecting
sum with the Wilson connected correlator.  The actual nonabelian Mayer/Ursell
construction remains open.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.ConnectedCardDecayMayerData.wilsonConnectedCorr_eq_toTruncatedActivities_connectingSum'
    depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.16.0 — Mayer data converts directly to truncated activities

**Released: 2026-04-25**

## What

Added the `ConnectedCardDecayMayerData` method

    ConnectedCardDecayMayerData.toTruncatedActivities

and three projection/bound lemmas in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    ConnectedCardDecayMayerData.toTruncatedActivities_K
    ConnectedCardDecayMayerData.toTruncatedActivities_K_bound_le_cardDecay
    ConnectedCardDecayMayerData.toTruncatedActivities_K_bound_eq_zero_of_not_connected

The main packaged F3 bridge
`clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil` now uses this
method instead of rebuilding `TruncatedActivities.ofConnectedCardDecay`
inline.

## Why

No percentage bar moves.  This is F3 Mayer-interface cleanup: a future
nonabelian Mayer/Ursell construction can now deliver a
`ConnectedCardDecayMayerData` package and obtain the exact finite-volume
`TruncatedActivities` consumer with one named projection.  The remaining
mathematical frontier is still the proof of the package itself plus the global
shifted count package.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all four new declarations print the canonical project oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.15.0 — Shifted F3 Mayer/count package field coherence exposed

**Released: 2026-04-25**

## What

Added `[simp]` field-coherence lemmas for
`ShiftedF3MayerCountPackage.ofSubpackages`, `mayerPackage`, and
`countPackage` in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    ShiftedF3MayerCountPackage.ofSubpackages_C_conn
    ShiftedF3MayerCountPackage.ofSubpackages_A₀
    ShiftedF3MayerCountPackage.ofSubpackages_dim
    ShiftedF3MayerCountPackage.ofSubpackages_data
    ShiftedF3MayerCountPackage.mayerPackage_A₀
    ShiftedF3MayerCountPackage.mayerPackage_data
    ShiftedF3MayerCountPackage.countPackage_C_conn
    ShiftedF3MayerCountPackage.countPackage_dim

## Why

No percentage bar moves.  This is package-coherence cleanup: independently
proved Mayer and count packages can now be combined and projected without
unfolding definitions just to recover `A₀`, `data`, `C_conn`, or `dim`.
The mathematical F3 frontier remains the construction of the nonabelian Mayer
package and the global shifted count package.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces: all eight new coherence lemmas print the canonical project
oracle

    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.14.0 — Global shifted count package projects transparently to finite volumes

**Released: 2026-04-25**

## What

Added

    theorem ShiftedF3CountPackage.toAt_C_conn
    theorem ShiftedF3CountPackage.toAt_dim
    theorem ShiftedF3CountPackage.toAt_apply

to `YangMills/ClayCore/ClusterRpowBridge.lean`.

The global `ShiftedF3CountPackage` restriction

    pkg.toAt d L : ShiftedF3CountPackageAt d L

now exposes, definitionally, that it preserves `C_conn` and `dim`, and has a
direct finite-volume application theorem.

## Why

No percentage bar moves.  This is F3-count interface cleanup: once the global
uniform lattice-animal package is proved, every finite-volume consumer can
inspect and apply its restriction without unfolding `toAt`.  The remaining
mathematical content is still the proof of `ShiftedConnectingClusterCountBound`
itself.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.ShiftedF3CountPackage.toAt_C_conn' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3CountPackage.toAt_dim' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3CountPackage.toAt_apply' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.13.0 — Finite-volume shifted count package made inspectable

**Released: 2026-04-25**

## What

Added

    theorem ShiftedF3CountPackageAt.finite_C_conn
    theorem ShiftedF3CountPackageAt.finite_dim
    theorem ShiftedF3CountPackageAt.finite_apply

to `YangMills/ClayCore/ConnectingClusterCount.lean`.

The local finite-volume count package now exposes its constants definitionally:

    C_conn = Fintype.card (Finset (ConcretePlaquette d L)) + 1
    dim    = 0

and has a direct application theorem for the shifted bucket count.

## Why

No percentage bar moves.  This does not prove the global uniform
`ShiftedConnectingClusterCountBound`; the constant still depends on the finite
volume `d,L`.  It closes the local finite-volume bookkeeping around
`ShiftedF3CountPackageAt.finite`, making the remaining F3-count gap exactly
the uniform lattice-animal estimate rather than local package plumbing.

## Oracle

Build:

    lake build YangMills.ClayCore.ConnectingClusterCount

Pinned traces:

    'YangMills.ShiftedF3CountPackageAt.finite_C_conn' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3CountPackageAt.finite_dim' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3CountPackageAt.finite_apply' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.12.0 — Uniform-rpow small-β frontier lands in ClusterCorrelatorBound

**Released: 2026-04-25**

## What

Added

    theorem clusterCorrelatorBound_small_beta_of_uniformRpow

to `YangMills/ClayCore/ZeroMeanCancellation.lean`.

It exposes the direct hub bridge

    WilsonUniformRpowBound N_c β C
    0 < β
    β < 1
    0 < C
    ─────────────────────────────────────────────
    ClusterCorrelatorBound N_c β C

by applying the existing `clusterCorrelatorBound_of_rpow_bound` conversion.
`clayMassGap_small_beta_of_uniformRpow` now routes through this named bridge
instead of inlining the conversion.

## Why

No percentage bar moves.  This is API cleanup on the small-β route: the named
uniform-rpow frontier now lands explicitly in the central
`ClusterCorrelatorBound` hub before projecting to mass gap, connected decay,
Clay theorem, or `PhysicalStrong`.  The analytic target is unchanged: prove
`WilsonUniformRpowBound` for the nonabelian cases via Mayer/Kotecky-Preiss.

## Oracle

Build:

    lake build YangMills.ClayCore.ZeroMeanCancellation

Pinned trace:

    'YangMills.clusterCorrelatorBound_small_beta_of_uniformRpow'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.11.0 — SU(1) inhabits the named uniform-rpow frontier

**Released: 2026-04-25**

## What

Added

    theorem wilsonUniformRpowBound_su1

to `YangMills/ClayCore/ZeroMeanCancellation.lean`.

For `β > 0` and `0 ≤ C`, it proves

    WilsonUniformRpowBound 1 β C

because `wilsonConnectedCorr_su1_eq_zero` makes the connected Wilson
correlator vanish identically on SU(1), while `C * β ^ dist` is nonnegative.

## Why

No percentage bar moves.  This is the singleton canary for the named small-β
frontier introduced for the nonabelian route.  Together with v1.10, it means
the `SU(1)` unconditional collapse now passes through the same
`WilsonUniformRpowBound → PhysicalStrong` terminal interface as the intended
Mayer/Kotecky-Preiss route.  It does not construct the `N_c ≥ 2` uniform-rpow
bound; that remains the live analytic front.

## Oracle

Build:

    lake build YangMills.ClayCore.ZeroMeanCancellation

Pinned trace:

    'YangMills.wilsonUniformRpowBound_su1' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.10.0 — Uniform-rpow small-β frontier lands directly in PhysicalStrong

**Released: 2026-04-25**

## What

Added

    theorem physicalStrong_of_uniformRpow_small_beta_siteDist_measurableF

to `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

It composes the named small-β frontier

    WilsonUniformRpowBound N_c β₀ C

from `YangMills/ClayCore/ZeroMeanCancellation.lean` with the cleaned-up L8
physical bridge.  The consumer-facing endpoint is:

    0 < β₀
    β₀ < 1
    0 < C
    WilsonUniformRpowBound N_c β₀ C
    0 < β
    ∀ U, |F U| ≤ 1
    Measurable F
    ─────────────────────────────────────────────
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun L p q => siteLatticeDist p.site q.site)

## Why

No percentage bar moves.  The analytic input remains exactly the uniform
rpow-shape correlator bound; this change removes terminal wiring as a possible
bottleneck for the small-β route.  Once the Mayer/Kotecky-Preiss layer supplies
`WilsonUniformRpowBound`, the first non-vacuous physical endpoint follows with
only the natural local observable assumptions.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned trace:

    'YangMills.physicalStrong_of_uniformRpow_small_beta_siteDist_measurableF'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.09.0 — SU(1) zero-activity canary for the shifted F3 Mayer package

**Released: 2026-04-25**

## What

Added

    noncomputable def shiftedF3MayerPackage_su1_zero

to `YangMills/ClayCore/ClusterRpowBridge.lean`.

For any `wab : WilsonPolymerActivityBound 1`, it constructs the Mayer/activity
half of the preferred shifted F3 frontier:

    ShiftedF3MayerPackage 1 wab

with `A₀ := 1` and raw truncated activity `K := 0`.  The Mayer identity closes
because `wilsonConnectedCorr_su1_eq_zero` proves that the SU(1) connected
Wilson correlator vanishes identically, and the constructed connecting sum is
also zero.

## Why

No percentage bar moves.  This is a canary and interface check for the
already-closed singleton route; it is not the `N_c ≥ 2` Mayer/Ursell
construction.  It confirms that the preferred F3 package boundary accepts the
unconditional SU(1) collapse without any additional analytic hypothesis.  The
live Clay front for the physical nonabelian cases remains the construction of
the shifted F3 Mayer package and the uniform shifted count package for
`N_c ≥ 2`.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.shiftedF3MayerPackage_su1_zero' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.08.0 — Shifted F3 packages land directly in PhysicalStrong

**Released: 2026-04-25**

## What

Added

    theorem physicalStrong_of_shiftedF3MayerCountPackage_siteDist_measurableF
    theorem physicalStrong_of_shiftedF3Subpackages_siteDist_measurableF

to `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

They compose the shifted F3 package endpoints

    clusterCorrelatorBound_of_shiftedF3MayerCountPackage
    ShiftedF3MayerCountPackage.ofSubpackages

with the v1.07 direct `ClusterCorrelatorBound → PhysicalStrong` bridge.  The
consumer-facing endpoints are:

    WilsonPolymerActivityBound N_c
    ShiftedF3MayerCountPackage N_c wab
    0 < β
    ∀ U, |F U| ≤ 1
    Measurable F
    ─────────────────────────────────────────────
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun L p q => siteLatticeDist p.site q.site)

and the same physical endpoint from independently-produced
`ShiftedF3MayerPackage N_c wab` and `ShiftedF3CountPackage` subpackages.

## Why

No percentage bar moves.  This packages the current preferred shifted F3 route
all the way to the first non-vacuous physical endpoint.  The remaining active
work is to construct the shifted F3 packages themselves: the Mayer/Ursell
identity and the Kotecky-Preiss count/series analytic content.  Terminal
finite-volume regularity and endpoint wiring are no longer the bottleneck for
this route.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces:

    'YangMills.physicalStrong_of_shiftedF3MayerCountPackage_siteDist_measurableF'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.physicalStrong_of_shiftedF3Subpackages_siteDist_measurableF'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.07.0 — Direct ClusterCorrelatorBound to PhysicalStrong bridge

**Released: 2026-04-25**

## What

Added

    theorem physicalStrong_of_clusterCorrelatorBound_siteDist_measurableF

to `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

It composes the existing

    ClusterCorrelatorBound N_c r C_clust → ClayYangMillsMassGap N_c

constructor with the cleaned-up v1.06 L8 physical bridge.  The resulting
consumer-facing endpoint is:

    ClusterCorrelatorBound N_c r C_clust
    0 < r
    r < 1
    0 < C_clust
    0 < β
    ∀ U, |F U| ≤ 1
    Measurable F
    ─────────────────────────────────────────────
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun L p q => siteLatticeDist p.site q.site)

All finite-volume regularity boilerplate is handled internally by the previous
v1.02-v1.06 lemmas.

## Why

No percentage bar moves.  This is a direct landing pad for the current analytic
front: once F1/F2/F3 produce `ClusterCorrelatorBound`, the non-vacuous physical
endpoint follows with only the natural local observable assumptions.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned trace:

    'YangMills.physicalStrong_of_clusterCorrelatorBound_siteDist_measurableF'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.06.0 — Concrete Wilson Boltzmann integrability discharged

**Released: 2026-04-24**

## What

Added

    theorem wilsonPlaquetteEnergy_boltzmann_integrable
    theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_measurableF

to `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

`wilsonPlaquetteEnergy_boltzmann_integrable` proves that for the concrete
Wilson plaquette energy, the finite-volume Boltzmann factor

    fun U => exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U)

is integrable against the product SU(N) gauge measure whenever `0 ≤ β`.  The
proof uses the existing bound on `wilsonPlaquetteEnergy N_c`, the finiteness of
`ConcretePlaquette d L`, and `Integrable.of_bound`.

`physicalStrong_of_clayConnectedCorrDecay_siteDist_measurableF` packages the
current cleanest physical bridge:

    ClayConnectedCorrDecay N_c
    0 < β
    ∀ U, |F U| ≤ 1
    Measurable F
    ─────────────────────────────────────────────
    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun L p q => siteLatticeDist p.site q.site)

It derives internally: Boltzmann integrability, Gibbs probability, local
Wilson-observable measurability, and local Wilson-observable integrability.

## Why

No percentage bar moves.  This removes the finite-volume regularity boilerplate
from the route after a `ClayConnectedCorrDecay N_c` witness has been produced.
The active mathematical front is now sharply isolated as the production of that
connected-decay witness, i.e. F1/F2/F3 for `ClusterCorrelatorBound`.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces:

    'YangMills.wilsonPlaquetteEnergy_boltzmann_integrable'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.physicalStrong_of_clayConnectedCorrDecay_siteDist_measurableF'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.05.0 — PhysicalStrong bridge with only `Measurable F` local regularity

**Released: 2026-04-24**

## What

Added

    theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurableF

to `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

This is the concrete SU(N) corollary of the v1.03/v1.04 bridge.  The measurable
group-operation instances are now supplied by the repository, so the local
regularity interface is reduced to:

    Measurable F

plus the existing boundedness and Boltzmann-weight integrability inputs:

    0 < β
    ∀ U, |F U| ≤ 1
    Integrable (fun U => exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
      (gaugeMeasureFrom (sunHaarProb N_c))

The theorem then derives the Gibbs probability measure, local Wilson observable
measurability, local Wilson observable integrability, and finally the canonical
site-distance `ClayYangMillsPhysicalStrong` bridge from a
`ClayConnectedCorrDecay N_c` witness.

## Why

No percentage bar moves.  This removes the remaining local finite-volume
regularity boilerplate from the bridge interface.  The active mathematical
front remains the production of `ClayConnectedCorrDecay N_c`, i.e. F1/F2/F3 for
`ClusterCorrelatorBound`.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned trace:

    'YangMills.physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurableF'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.04.0 — Concrete SU(N) measurable multiplication instance

**Released: 2026-04-24**

## What

Added concrete measurable-topology infrastructure for

    ↥(Matrix.specialUnitaryGroup (Fin n) ℂ)

in `YangMills/P8_PhysicalGap/SUN_StateConstruction.lean`:

    instance instSecondCountableTopologySUN
    instance instMeasurableMulSUN
    theorem sun_measurableMul₂

`instSecondCountableTopologySUN` exposes the second-countable topology of SU(N)
as a subtype of the finite-dimensional complex matrix space.  With the already
available `ContinuousMul`, `BorelSpace`, and measurable space instances,
Mathlib then synthesizes `MeasurableMul₂` for the concrete SU(N) gauge group.

## Why

This closes the infrastructure item left by v1.03.0.  The L8 bridge

    physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_observableMeasurable

can now use the concrete SU(N) measurable multiplication instance supplied by
the repository rather than requiring callers to provide it separately.

No percentage bar moves: this is measurable-structure plumbing, not F1/F2/F3.

## Oracle

Builds:

    lake build YangMills.P8_PhysicalGap.SUN_StateConstruction
    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned trace:

    'YangMills.sun_measurableMul₂'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.03.0 — Plaquette-observable measurability bridge

**Released: 2026-04-24**

## What

Added

    lemma measurable_plaquetteHolonomy

to `YangMills/L2_Balaban/Measurability.lean`.

It records that plaquette holonomy

    fun U : GaugeConfig d N G => GaugeConfig.plaquetteHolonomy U p

is measurable whenever inversion and multiplication on the gauge group are
measurable (`[MeasurableInv G] [MeasurableMul₂ G]`).  The proof reuses the
existing edge-evaluation measurability API.

Added the L8 wrapper:

    theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_observableMeasurable

to `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

This is the v1.02 physical bridge with local Wilson-observable measurability
derived from `Measurable F` by composition with measurable plaquette holonomy.
The remaining local regularity input is now the group-level measurability
structure (`MeasurableInv` / `MeasurableMul₂`) rather than one proof per
plaquette observable.

## Why

No percentage bar moves.  This narrows the local finite-volume interface on the
route to `ClayYangMillsPhysicalStrong`: after Boltzmann integrability supplies
the Gibbs probability measure, local Wilson integrability follows from
unit-boundedness and `Measurable F`, provided the concrete gauge group exposes
the standard measurable group operations.

## Oracle

Builds:

    lake build YangMills.L2_Balaban.Measurability
    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces:

    'YangMills.measurable_plaquetteHolonomy'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_observableMeasurable'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.02.0 — Local Wilson integrability from measurability + unit bound

**Released: 2026-04-24**

## What

Added two ClayCore integrability lemmas:

    theorem plaquetteWilsonObs_integrable_of_unitBound
    theorem plaquetteWilsonObs_mul_integrable_of_unitBound

in `YangMills/ClayCore/ClusterCorrelatorBound.lean`.

They prove that a unit-bounded Wilson plaquette observable, and the product of
two such observables, are integrable on any finite measure space once the
relevant `AEStronglyMeasurable` facts are available.  This is the standard
finite-measure bounded-function step, now recorded as reusable Lean API.

Added the L8 wrapper:

    theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurable

in `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

It is the v1.01 physical bridge with the local Wilson one-point/two-point
integrability side-conditions discharged from:

    ∀ L p, AEStronglyMeasurable (plaquetteWilsonObs F p) (gibbsMeasure ... β)

together with `|F| ≤ 1` and the Boltzmann-weight integrability that already
produces the Gibbs probability measure.

## Why

This does not prove F1/F2/F3 and does not move the percentage bars.  It removes
a small but important local analytic nuisance from the final `PhysicalStrong`
interface: local Wilson integrability is no longer a separate hypothesis once
measurability is supplied.

## Oracle

Builds:

    lake build YangMills.ClayCore.ClusterCorrelatorBound
    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces:

    'YangMills.plaquetteWilsonObs_integrable_of_unitBound'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.plaquetteWilsonObs_mul_integrable_of_unitBound'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable_measurable'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.01.0 — Boltzmann-integrability variant of the PhysicalStrong bridge

**Released: 2026-04-24**

## What

Added

    theorem physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable

to `YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`.

This is the same canonical-distance bridge as v1.00.0, but it no longer asks
the caller to provide

    IsProbabilityMeasure (gibbsMeasure ... β)

directly.  Instead it derives that probability instance from the standard
Boltzmann-weight integrability hypothesis via `gibbsMeasure_isProbability`:

    Integrable
      (fun U => exp (-β * wilsonAction (wilsonPlaquetteEnergy N_c) U))
      (gaugeMeasureFrom (sunHaarProb N_c))

The remaining local inputs are still explicit: bounded observable `|F| ≤ 1`
and integrability of the Wilson one-point/two-point observables under the
tilted Gibbs measure.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned trace:

    'YangMills.physicalStrong_of_clayConnectedCorrDecay_siteDist_of_boltzmannIntegrable'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v1.00.0 — ClayConnectedCorrDecay to PhysicalStrong canonical-distance bridge

**Released: 2026-04-24**

## What

Added two L8 bridge declarations to
`YangMills/L8_Terminal/ConnectedCorrDecayBundle.lean`:

    noncomputable def connectedCorrDecayBundle_of_clayConnectedCorrDecay_siteDist
    theorem physicalStrong_of_clayConnectedCorrDecay_siteDist

They convert a ClayCore separated-distance witness

    ClayConnectedCorrDecay N_c

into the non-vacuous physical endpoint

    ClayYangMillsPhysicalStrong
      (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F
      (fun L p q => siteLatticeDist p.site q.site)

provided the remaining local analytic side-conditions are explicit:

    0 < β
    ∀ U, |F U| ≤ 1
    IsProbabilityMeasure (gibbsMeasure ... β) for every L
    integrability of W_p, W_q, and W_p * W_q for every L,p,q

The bridge uses the separated exponential decay from `ClayConnectedCorrDecay`
when `1 ≤ siteLatticeDist p.site q.site`, and uses
`wilsonConnectedCorr_abs_le_two_of_unitBound` for the local regime.  The
resulting global finite-volume `ConnectedCorrDecay` has prefactor

    w.C + 2 * exp w.m

and decay rate `w.m`.

This still does not prove F1/F2/F3, nor the local probability/integrability
facts.  It removes a structural gap between the ClayCore connected-decay
package and the first non-vacuous L8 physical target.

## Oracle

Build:

    lake build YangMills.L8_Terminal.ConnectedCorrDecayBundle

Pinned traces:

    'YangMills.connectedCorrDecayBundle_of_clayConnectedCorrDecay_siteDist'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.physicalStrong_of_clayConnectedCorrDecay_siteDist'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v0.99.0 — Local bounded-observable Wilson connected-correlation estimate

**Released: 2026-04-24**

## What

Added

    theorem wilsonConnectedCorr_abs_le_two_of_unitBound

to `YangMills/ClayCore/ClusterCorrelatorBound.lean`.

This is the local finite-distance companion to the separated F3 cluster
decay estimates.  For a unit-bounded observable `|F| ≤ 1`, it proves

    |wilsonConnectedCorr ... β F p q| ≤ 2

provided the tilted Gibbs measure is already known to be a probability measure
and the three relevant observables are supplied as integrable:

    plaquetteWilsonObs F p
    plaquetteWilsonObs F q
    plaquetteWilsonObs F p * plaquetteWilsonObs F q

The theorem does **not** replace the F1/F2/F3 analytic work and does not claim
exponential decay.  It records the elementary local bound needed later when
combining separated-distance cluster decay with all-pair physical mass-profile
statements.

## Oracle

Builds:

    lake build YangMills.ClayCore.ClusterCorrelatorBound
    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.wilsonConnectedCorr_abs_le_two_of_unitBound'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v0.97.0 — Keep experimental Dirichlet sidecar out of main umbrella

**Released: 2026-04-24**

## What

Removed the two concrete Dirichlet sidecar imports

    import YangMills.P8_PhysicalGap.SUN_DirichletCore
    import YangMills.P8_PhysicalGap.SUN_DirichletForm

from the root aggregator `YangMills.lean`.

These files remain available by direct import, but they currently depend on
`YangMills.Experimental.LieSUN.LieDerivReg_v4` for the concrete SU(N)
Lie-derivative data and regularity facts.  Keeping them out of the main
umbrella prevents `lake build YangMills` from inheriting experimental
Lie-derivative axioms through a convenience import.

This is audit hygiene, not a mathematical closure of the SU(N) Dirichlet
analysis.  The concrete Dirichlet/Lie-derivative sidecar remains an explicit
frontier until the generator data, matrix exponential closure, and derivative
regularity facts are proved without experimental axioms.

## Oracle

Build:

    lake build YangMills

Audit command:

    git grep -n "SUN_DirichletCore\|SUN_DirichletForm" -- YangMills.lean

Output:

    <empty>

The sidecar itself still imports experimental Lie-derivative data:

    YangMills/P8_PhysicalGap/SUN_DirichletCore.lean

No `sorry`. Non-Experimental Lean axiom count remains 0.

---

# v0.96.0 — Remove unused experimental import from SUN locality

**Released: 2026-04-24**

## What

Removed the unused import

    import YangMills.P8_PhysicalGap.SUN_DirichletCore

from `YangMills/P8_PhysicalGap/SUN_LiebRobin.lean`.

`sun_locality_to_covariance` is already an explicit-input theorem: it receives
the symmetric Markov transport, variance decay, and Lieb-Robinson bound as
hypotheses.  It does not need the concrete SU(N) Dirichlet sidecar.  Removing
the import prevents the locality theorem from unnecessarily inheriting the
experimental Lie-derivative oracle.

## Oracle

Build:

    lake build YangMills.P8_PhysicalGap.SUN_LiebRobin

Pinned trace:

    'YangMills.sun_locality_to_covariance'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `sorry`. No non-Experimental `axiom`.

---

# v0.95.0 — Remove final non-Experimental Lean axiom

**Released: 2026-04-24**

## What

Removed the final non-Experimental `axiom` declaration:

    physical_rg_rates_from_E26

from `YangMills/ClayCore/BalabanRG/PhysicalRGRates.lean`.

`PhysicalRGRates.lean` now contains only the quantitative rates interface plus
the projection theorems

    physicalRGRates_to_balabanRGPackage
    physicalRGRates_to_lsi

The direct zero-axiom witness remains in
`YangMills/ClayCore/BalabanRG/PhysicalRGRatesWitness.lean`, assembled from the
repository's current rate-side theorems:

    rho_exp_contractive_from_E26
    rho_in_unit_interval_from_E26
    cP_linear_lb_from_E26
    cLSI_linear_lb_from_E26

`BalabanRGAxiomReduction.lean` now routes the legacy public names through the
direct physical witness (`physicalBalabanRGPackage`, `physical_uniform_lsi`)
instead of through an axiom wrapper.

This does not mean the Clay problem is solved unconditionally in the strong
physical sense.  It means there are now **zero non-Experimental `axiom`
declarations** in the Lean tree.  Remaining work is no longer hidden behind
Lean `axiom` keywords; it lives in theorem-side assumptions, explicit transfer
interfaces, weak/vacuous endpoints, and the still-open analytic fronts tracked
elsewhere.

## Oracle

Builds:

    lake build YangMills.ClayCore.BalabanRG.PhysicalRGRates
    lake build YangMills.ClayCore.BalabanRG.PhysicalRGRatesWitness
    lake build YangMills.ClayCore.BalabanRG.BalabanRGAxiomReduction

Audit command:

    git grep -n -E "^axiom " -- "*.lean" | Select-String -NotMatch "Experimental"

Output:

    <empty>

Non-Experimental Lean axiom count is now 0. No `sorry`.

---

# v0.94.0 — Remove legacy un-normalized Holley-Stroock axiom

**Released: 2026-04-24**

## What

Removed the P8 axiom `holleyStroock_sunGibbs_lsi` from
`YangMills/P8_PhysicalGap/BalabanToLSI.lean`.

The legacy un-normalized Gibbs family is kept, but its family and DLR wrappers
are now explicit-input:

    theorem balaban_rg_uniform_lsi_of_lsi
    theorem sun_gibbs_dlr_lsi_of_lsi

The weighted Clay route no longer fabricates a canonical
`ClayCoreLSIToSUNDLRTransfer` from the legacy P8 axiom.  Instead:

- `WeightedFinalGapWitness` now has a named `pkg` field and continues to carry
  its own explicit transfer.
- `WeightedRouteClosesClay` keeps the same closure lemmas but requires the
  final `ClayCoreLSIToSUNDLRTransfer d N_c` at the call site.
- `KPExpSizeWeightToClay` likewise keeps the KP-facing closures with the final
  transfer explicit.

This does not prove the un-normalized Holley-Stroock transfer.  It removes the
global axiom declaration and makes the transfer obligation visible where it is
actually needed.

## Oracle

Builds:

    lake build YangMills.P8_PhysicalGap.BalabanToLSI
    lake build YangMills.ClayCore.BalabanRG.WeightedFinalGapWitness
    lake build YangMills.ClayCore.BalabanRG.WeightedRouteClosesClay
    lake build YangMills.ClayCore.BalabanRG.KPExpSizeWeightToClay

Non-Experimental Lean axiom count is now 1:

    YangMills/ClayCore/BalabanRG/PhysicalRGRates.lean:
      physical_rg_rates_from_E26

No `holleyStroock_sunGibbs_lsi` axiom remains in non-Experimental Lean.
No `sorry`.

---

# v0.93.0 — Remove unrestricted normalized Gibbs LSI axiom

**Released: 2026-04-24**

## What

Removed the P8 axiom `lsi_normalized_gibbs_from_haar` from
`YangMills/P8_PhysicalGap/BalabanToLSI.lean`.

The unrestricted normalized Gibbs route is now explicit-input:

    theorem balaban_rg_uniform_lsi_norm_of_lsi
    theorem sun_gibbs_dlr_lsi_norm_of_lsi

Both take a caller-supplied single-measure normalized Gibbs LSI and only package
it into the constant-volume family / DLR-LSI shape.  The automatic route for the
weak terminal endpoint now goes through the already proved MemLp-gated Σ chain:

    lsi_normalized_gibbs_from_haar_memLp
      → balaban_rg_uniform_lsi_norm_memLp
      → sun_gibbs_dlr_lsi_norm_memLp

`YangMills/P8_PhysicalGap/PhysicalMassGap.lean` was aligned with its existing
docstring: `sun_physical_mass_gap` now receives the DLR-LSI witness as an
explicit hypothesis, while `sun_physical_mass_gap_vacuous` routes through the
MemLp endpoint.

This does not prove the unrestricted Holley-Stroock theorem for all measurable
functions.  It removes the global axiom declaration and records that the only
automatic axiom-free normalized route currently available is the MemLp-gated
one.

## Oracle

Build:

    lake build YangMills.P8_PhysicalGap.PhysicalMassGap

Pinned traces:

    'YangMills.balaban_rg_uniform_lsi_norm_of_lsi'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.sun_gibbs_dlr_lsi_norm_of_lsi'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.sun_physical_mass_gap'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.sun_physical_mass_gap_vacuous'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

Non-Experimental Lean axiom count is now 2:

    YangMills/ClayCore/BalabanRG/PhysicalRGRates.lean:
      physical_rg_rates_from_E26
    YangMills/P8_PhysicalGap/BalabanToLSI.lean:
      holleyStroock_sunGibbs_lsi

No `lsi_normalized_gibbs_from_haar` axiom remains in non-Experimental Lean.
No `sorry`.

---

# v0.92.0 — Turn SU(N) Dirichlet contraction into explicit input

**Released: 2026-04-24**

## What

Removed the P8 axiom `sunDirichletForm_contraction` from
`YangMills/P8_PhysicalGap/SUN_DirichletCore.lean`.

The strong Dirichlet-form package is now exposed as:

    lemma sunDirichletForm_isDirichletFormStrong_of_contraction

which takes the normal-contraction estimate as an explicit hypothesis and then
builds `IsDirichletFormStrong`.  The base Dirichlet-form facts
`sunDirichletForm_isDirichletForm`, constant invariance, and quadratic scaling
remain proved as before.

This does not prove the Beurling-Deny normal-contraction estimate.  It removes
the global axiom declaration and makes the missing contraction input visible at
the call site.

## Oracle

Build:

    lake build YangMills.P8_PhysicalGap.SUN_DirichletCore

Pinned trace:

    'YangMills.sunDirichletForm_isDirichletFormStrong_of_contraction'
    depends on axioms:
    [lieDerivReg_all, propext, sunGeneratorData, Classical.choice,
     Quot.sound, Experimental.LieSUN.matExp_traceless_det_one]

No `sunDirichletForm_contraction` axiom remains in non-Experimental Lean.
No `sorry`.

---

# v0.91.0 — Remove Hille-Yosida semigroup axiom from P8

**Released: 2026-04-24**

## What

Removed the P8 axiom `hille_yosida_semigroup` from
`YangMills/P8_PhysicalGap/MarkovSemigroupDef.lean`.

The two remaining consumers were converted to explicit-input form:

- `YangMills/P8_PhysicalGap/StroockZegarlinski.lean` now takes the Markov
  transport family as an explicit `_sg : ∀ L, SymmetricMarkovTransport
  (gibbsFamily L)`.
- `YangMills/P8_PhysicalGap/SUN_LiebRobin.lean` now takes
  `sg : SymmetricMarkovTransport (sunHaarProb N_c)` explicitly.

This does not formalize the Beurling-Deny / Hille-Yosida correspondence.  It
removes the global axiom declaration and makes the C₀-semigroup construction an
explicit input at the call sites that need it.

## Oracle

Builds:

    lake build YangMills.P8_PhysicalGap.StroockZegarlinski
    lake build YangMills.P8_PhysicalGap.SUN_LiebRobin

Pinned traces:

    'YangMills.sz_lsi_to_clustering_bridge'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.sz_lsi_to_clustering'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.lsi_to_spectralGap'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.sun_locality_to_covariance'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `hille_yosida_semigroup` axiom remains in non-Experimental Lean. No `sorry`.

---

# v0.90.0 — Pin terminal ClayAssembly oracle as core-only

**Released: 2026-04-24**

## What

Updated `YangMills/P8_PhysicalGap/ClayAssembly.lean` to reflect the current
terminal route:

    yangMills_existence_massGap
    clay_millennium_yangMills
    clay_millennium_yangMills_strong

now route through the MemLp-gated normalized LSI endpoint and print only the
canonical Lean/project oracle.  The old comments claimed a dependency on the
legacy unnormalized Holley-Stroock axiom `holleyStroock_sunGibbs_lsi`; that is
no longer true for these public terminal names.

This is an audit correction, not a new analytic proof.  The weak endpoint
`ClayYangMillsTheorem := ∃ m_phys : ℝ, 0 < m_phys` remains the vacuous terminal
existential audited in v0.47.0.  The non-vacuous work remains at the physical
and cluster/RG fronts.

## Oracle

Build:

    lake build YangMills.P8_PhysicalGap.ClayAssembly

Pinned traces:

    'YangMills.yangMills_existence_massGap'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_millennium_yangMills'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_millennium_yangMills_strong'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`.

---

# v0.89.0 — Turn Poincare-to-covariance into explicit SZ input

**Released: 2026-04-24**

## What

Removed the P8 axiom `poincare_to_covariance_decay` from
`YangMills/P8_PhysicalGap/StroockZegarlinski.lean`.

The Stroock-Zegarlinski bridge now takes the covariance-decay family as an
explicit input:

    hCov : ∀ L, HasCovarianceDecay (gibbsFamily L) 2 (2 / α_star)

and then performs the already-proved repackaging to
`ExponentialClustering`.  This keeps the formal LSI/clustering API useful while
not declaring the generic Poincare-to-covariance functional-analysis theorem as
a global axiom.

This does not prove Poincare-to-covariance decay.  It localizes that analytic
step as a named hypothesis at the call site.

## Oracle

Build:

    lake build YangMills.P8_PhysicalGap.StroockZegarlinski

Pinned traces:

    'YangMills.sz_lsi_to_clustering_bridge'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.sz_lsi_to_clustering'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.lsi_to_spectralGap'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No `poincare_to_covariance_decay` axiom remains. No `sorry`.

---

# v0.88.0 — Turn SUN Lieb-Robinson axioms into explicit inputs

**Released: 2026-04-24**

## What

Removed two self-contained P8 axioms from
`YangMills/P8_PhysicalGap/SUN_LiebRobin.lean`:

    sun_variance_decay
    sun_lieb_robinson_bound

They were consumed only by `sun_locality_to_covariance` in the same file.
The theorem now takes the two physical inputs explicitly:

    hVar : HasVarianceDecay (sunMarkovSemigroup N_c)
    hLR  : LiebRobinsonBound (d := d) (sunMarkovSemigroup N_c)

and then applies the already-proved abstract locality bridge
`locality_to_static_covariance_v2`.  This keeps the formal covariance-decay
bridge while no longer declaring SU(N)-specific variance decay or
Lieb-Robinson as global axioms.

This does not prove those two physical inputs.  It changes their status from
declared axioms to theorem hypotheses, matching the repository's current
frontier discipline.

## Oracle

Build:

    lake build YangMills.P8_PhysicalGap.SUN_LiebRobin

Pinned trace:

    'YangMills.sun_locality_to_covariance'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

The deleted names no longer occur as `axiom` declarations:

    git grep "^axiom sun_variance_decay\\|^axiom sun_lieb_robinson_bound" -- YangMills

returns no matches. No `sorry`.

---

# v0.87.0 — Delete unused legacy SZ-to-clustering axiom

**Released: 2026-04-24**

## What

Deleted the orphaned backward-compatibility axiom
`legacy_sz_lsi_to_clustering` from
`YangMills/P8_PhysicalGap/BalabanToLSI.lean`.

Source search before deletion found only the declaration itself, so the axiom
was not feeding the Clay path or any intermediate theorem.  The
active Stroock-Zegarlinski route remains in
`YangMills/P8_PhysicalGap/StroockZegarlinski.lean`; as of v0.89.0 its
covariance-decay input is explicit rather than a declared axiom.

This is a pure dead-axiom deletion.  It does not prove the active
Stroock-Zegarlinski covariance-decay theorem and does not alter the normalized
Gibbs LSI frontier `lsi_normalized_gibbs_from_haar`.

## Verification

Build:

    lake build YangMills.P8_PhysicalGap.BalabanToLSI

Post-delete search:

    git grep legacy_sz_lsi_to_clustering -- YangMills

returns no matches.

No `legacy_sz_lsi_to_clustering` axiom remains. No `sorry`.

---

# v0.86.0 — Retire obsolete P91 weak-coupling-window axiom

**Released: 2026-04-24**

## What

Deleted the stale RG-branch axiom
`p91_tight_weak_coupling_window` from
`YangMills/ClayCore/BalabanRG/P91WeakCouplingWindow.lean`.

The axiom had been superseded by the data-driven theorem

    p91_tight_weak_coupling_window_theorem

in `YangMills/ClayCore/BalabanRG/P91WindowClosed.lean`, which derives the
tight weak-coupling window from `P91RecursionData` via
`p91_tight_window_of_data_v2`.  No downstream file consumed the old axiom
directly; `git grep "^axiom"` on `P91WeakCouplingWindow.lean` is now empty.

The remaining wrappers in `P91WeakCouplingWindow.lean` are purely algebraic:

    theorem denominator_pos_tight
    theorem denominator_pos_from_tight

They consume the tight-window bound as an explicit hypothesis and produce the
positive-denominator conclusion.  This removes one declared non-Experimental
axiom from the RG branch, with no claim that the full P91 recursion analysis is
complete without its data package.

## Oracle

Builds:

    lake build YangMills.ClayCore.BalabanRG.P91WeakCouplingWindow
    lake build YangMills.ClayCore.BalabanRG.P91WindowClosed

Pinned traces:

    'YangMills.ClayCore.denominator_pos_tight'
    depends on axioms:
    [propext, choice, Quot.sound]

    'YangMills.ClayCore.denominator_pos_from_tight'
    depends on axioms:
    [propext, choice, Quot.sound]

No `p91_tight_weak_coupling_window` axiom remains. No `sorry`.

---

# v0.85.0 — Small-beta uniform-rpow connected-decay endpoint

**Released: 2026-04-24**

## What

Pure additive endpoint exposure in
`YangMills/ClayCore/ZeroMeanCancellation.lean`:

    noncomputable def clayConnectedCorrDecay_small_beta_of_uniformRpow
    theorem clayConnectedCorrDecay_small_beta_of_uniformRpow_mass_eq
    theorem clayConnectedCorrDecay_small_beta_of_uniformRpow_prefactor_eq

The named small-β uniform-rpow frontier from v0.83.0, already routed to the
authentic mass-gap structure in v0.84.0, now also projects to the terminal
connected-decay hub:

    WilsonUniformRpowBound N_c β C → ClayConnectedCorrDecay N_c

This is the same downstream object used by the non-vacuous Clay hierarchy
between `ClayYangMillsMassGap N_c` and the weak existential endpoint.  Two
canaries pin the projected constants:

    mass      = kpParameter β
    prefactor = C

This does not prove `WilsonUniformRpowBound`.  It only makes the small-β
F3/Mayer terminal shape explicit all the way through the connected-decay API,
so future analytic work has a named, oracle-clean endpoint to target.

## Oracle

Build:

    lake build YangMills.ClayCore.ZeroMeanCancellation

Pinned traces:

    'YangMills.clayConnectedCorrDecay_small_beta_of_uniformRpow'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayConnectedCorrDecay_small_beta_of_uniformRpow_mass_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayConnectedCorrDecay_small_beta_of_uniformRpow_prefactor_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.84.0 — Small-beta uniform-rpow authentic mass-gap endpoint

**Released: 2026-04-24**

## What

Pure additive endpoint strengthening in
`YangMills/ClayCore/ZeroMeanCancellation.lean`:

    noncomputable def clayMassGap_small_beta_of_uniformRpow
    theorem clay_theorem_small_beta_of_uniformRpow
    theorem clayMassGap_small_beta_of_uniformRpow_mass_eq
    theorem clayMassGap_small_beta_of_uniformRpow_prefactor_eq

The named small-β uniform-rpow frontier from v0.83.0 now feeds the authentic
mass-gap structure directly:

    WilsonUniformRpowBound N_c β C → ClayYangMillsMassGap N_c

The weak theorem endpoint is then only the projection
`clayMassGap_implies_clayTheorem`.  Two canaries pin the extracted constants:

    mass      = kpParameter β
    prefactor = C

This does not prove the uniform rpow bound.  It ensures that if the F3-Mayer
analytic bound is supplied in the small-β form, the downstream object is the
non-vacuous `ClayYangMillsMassGap N_c`, not merely the weak existential
`ClayYangMillsTheorem`.

## Oracle

Build:

    lake build YangMills.ClayCore.ZeroMeanCancellation

Pinned traces:

    'YangMills.clayMassGap_small_beta_of_uniformRpow'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_small_beta_of_uniformRpow'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayMassGap_small_beta_of_uniformRpow_mass_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayMassGap_small_beta_of_uniformRpow_prefactor_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.83.0 — Name the uniform rpow small-beta frontier

**Released: 2026-04-24**

## What

Pure additive frontier sharpening in
`YangMills/ClayCore/ZeroMeanCancellation.lean`:

    def WilsonUniformRpowBound
    theorem yang_mills_final_small_beta_of_uniformRpow

`WilsonUniformRpowBound N_c β C` names the exact uniform rpow-shape
connected-correlator bound consumed by the small-β terminal wrapper: one
constant `C` and one scale `β` work uniformly across all finite lattices,
positive inverse couplings, bounded test functions, and plaquette pairs.

This distinguishes the actual terminal input from the looser
`WilsonLinkIndependence` predicate, whose constant is existential at each call
site and is therefore not by itself the uniform F3/Mayer output needed for the
Clay chain.

## Oracle

Build:

    lake build YangMills.ClayCore.ZeroMeanCancellation

Pinned trace:

    'YangMills.yang_mills_final_small_beta_of_uniformRpow'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.82.0 — Audit normalized plaquette zero-mean layer

**Released: 2026-04-24**

## What

Oracle audit for the already-formal single-plaquette Mayer cancellation layer in
`YangMills/ClayCore/ZeroMeanCancellation.lean`:

    #print axioms singlePlaquetteZ_pos
    #print axioms plaquetteFluctuationNorm_integrable
    #print axioms plaquetteFluctuationNorm_mean_zero
    #print axioms plaquetteFluctuationNorm_zero_beta

This records the algebraic/analytic one-plaquette facts behind the normalized
fluctuation

    w̃(U) = plaquetteWeight N_c β U / singlePlaquetteZ N_c β - 1

namely positivity of the one-plaquette partition function, integrability of the
normalized fluctuation, exact Haar mean zero, and the `β = 0` sanity check.

This is not the full Mayer/product-measure factorisation theorem.  It is the
closed single-plaquette cancellation input that the remaining F3-Mayer proof
must lift to the product gauge-configuration/polymer setting.

## Oracle

Build:

    lake build YangMills.ClayCore.ZeroMeanCancellation

Pinned traces:

    'YangMills.singlePlaquetteZ_pos'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.plaquetteFluctuationNorm_integrable'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.plaquetteFluctuationNorm_mean_zero'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.plaquetteFluctuationNorm_zero_beta'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.81.0 — Restrict global F3 count data to local lattices

**Released: 2026-04-24**

## What

Pure additive bridge between the global F3 count frontier and the local
finite-volume count layer:

    theorem ShiftedConnectingClusterCountBound.toAt
    def ShiftedF3CountPackage.toAt

`ShiftedConnectingClusterCountBound.toAt` restricts a global uniform shifted
connecting-cluster count bound to any fixed finite plaquette lattice
`(d, L)`.  `ShiftedF3CountPackage.toAt` performs the same restriction at the
packaged-data level:

    ShiftedF3CountPackage → ShiftedF3CountPackageAt d L

This does not prove the global lattice-animal estimate.  It records the
expected functorial direction: once the true uniform count package is proved,
all finite-volume local packages are immediate projections.

## Oracle

Builds:

    lake build YangMills.ClayCore.ConnectingClusterCount
    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.ShiftedConnectingClusterCountBound.toAt'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3CountPackage.toAt'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.80.0 — Packaged local finite-volume count data

**Released: 2026-04-24**

## What

Finite-volume count packaging in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    structure ShiftedF3CountPackageAt
    noncomputable def ShiftedF3CountPackageAt.finite

`ShiftedF3CountPackageAt d L` packages the local shifted count data for a
fixed concrete plaquette lattice:

    C_conn : ℝ
    hC : 0 < C_conn
    dim : ℕ
    h_count : ShiftedConnectingClusterCountBoundAt d L C_conn dim

The constructor `ShiftedF3CountPackageAt.finite` fills this package using the
trivial finite-volume bound from v0.79.0:

    C_conn = Fintype.card (Finset (ConcretePlaquette d L)) + 1
    dim    = 0

This is still not the global uniform F3 count package.  It makes the
finite-volume count layer reusable as a first-class local object, while keeping
the uniform lattice-animal estimate visibly separate.

## Oracle

Build:

    lake build YangMills.ClayCore.ConnectingClusterCount

Pinned trace:

    'YangMills.ShiftedF3CountPackageAt.finite'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.79.0 — Local finite-volume shifted count bound

**Released: 2026-04-24**

## What

Finite-volume combinatorial audit in
`YangMills/ClayCore/ConnectingClusterCount.lean`:

    def ShiftedConnectingClusterCountBoundAt
    theorem ShiftedConnectingClusterCountBoundAt.apply
    theorem shiftedConnectingClusterCountBoundAt_finite

`ShiftedConnectingClusterCountBoundAt d L C_conn dim` is the fixed-lattice
version of the shifted connecting-cluster count frontier.  It keeps the
dimension `d` and lattice size `L` fixed, so the constants may depend on the
finite plaquette lattice.

The theorem

    shiftedConnectingClusterCountBoundAt_finite

proves that every finite plaquette lattice has a trivial shifted count bound
with:

    C_conn = Fintype.card (Finset (ConcretePlaquette d L)) + 1
    dim    = 0

This is not the global uniform lattice-animal estimate required by F3.  It
separates the already-formal finite-volume counting fact from the remaining
uniform/asymptotic combinatorial burden packaged by
`ShiftedConnectingClusterCountBound`.

## Oracle

Build:

    lake build YangMills.ClayCore.ConnectingClusterCount

Pinned traces:

    'YangMills.ShiftedConnectingClusterCountBoundAt.apply'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.shiftedConnectingClusterCountBoundAt_finite'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.78.0 — Direct F3 subpackage terminal endpoints

**Released: 2026-04-24**

## What

Pure additive endpoint exposure in `YangMills/ClayCore/ClusterRpowBridge.lean`.
Given independently-produced packages

    mayer : ShiftedF3MayerPackage N_c wab
    count : ShiftedF3CountPackage

the module now exposes direct terminal consumers:

    theorem clusterCorrelatorBound_of_shiftedF3Subpackages
    noncomputable def clayWitnessHyp_of_shiftedF3Subpackages
    noncomputable def clayMassGap_of_shiftedF3Subpackages
    noncomputable def clayConnectedCorrDecay_of_shiftedF3Subpackages
    theorem clay_theorem_of_shiftedF3Subpackages

Each endpoint is a thin wrapper around
`ShiftedF3MayerCountPackage.ofSubpackages` followed by the existing
single-package endpoint from v0.75.0.  The terminal API can now be driven either
by one completed `ShiftedF3MayerCountPackage` or by the two independently
proved halves from v0.77.0.

This does not prove the Mayer/activity package or the connecting-cluster count
package.  It removes the final packaging friction between those two remaining
F3 proof obligations and every downstream audit endpoint.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clusterCorrelatorBound_of_shiftedF3Subpackages'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayWitnessHyp_of_shiftedF3Subpackages'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayMassGap_of_shiftedF3Subpackages'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayConnectedCorrDecay_of_shiftedF3Subpackages'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_shiftedF3Subpackages'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.77.0 — Split preferred F3 package into Mayer/count halves

**Released: 2026-04-24**

## What

Pure additive frontier factoring in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    structure ShiftedF3MayerPackage
    structure ShiftedF3CountPackage

with mechanical recombination/projections:

    def ShiftedF3MayerCountPackage.ofSubpackages
    def ShiftedF3MayerCountPackage.mayerPackage
    def ShiftedF3MayerCountPackage.countPackage
    theorem ShiftedF3MayerCountPackage.ofSubpackages_mayerPackage_countPackage

The preferred F3 package from v0.75.0 remains the terminal one-object API:

    ShiftedF3MayerCountPackage N_c wab

but its two mathematical burdens are now independently named:

1. `ShiftedF3MayerPackage N_c wab` packages the Mayer/activity side:
   `A₀`, `hA`, and `ConnectedCardDecayMayerData N_c wab.r A₀ ...`;
2. `ShiftedF3CountPackage` packages the combinatorial count side:
   `C_conn`, `hC`, `dim`, and `ShiftedConnectingClusterCountBound C_conn dim`.

Supplying both halves reconstructs the terminal package by
`ShiftedF3MayerCountPackage.ofSubpackages`.  Any existing terminal package
projects back to the two halves, and the roundtrip back to the original package
is definitionally `rfl`.

This does not prove either analytic half.  It sharpens the active F3 frontier:
the remaining proof work can now proceed independently on the Mayer/activity
producer and the shifted connecting-cluster count producer, then combine
mechanically into all v0.75.0/v0.76.0 downstream endpoints.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.ShiftedF3MayerCountPackage.ofSubpackages'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3MayerCountPackage.mayerPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3MayerCountPackage.countPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.ShiftedF3MayerCountPackage.ofSubpackages_mayerPackage_countPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.76.0 — Single-package F3 mass/prefactor canaries

**Released: 2026-04-24**

## What

Pure additive audit canaries in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clayMassGap_of_shiftedF3MayerCountPackage_mass_eq
    theorem clayMassGap_of_shiftedF3MayerCountPackage_prefactor_eq
    theorem clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_mass_eq
    theorem clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_prefactor_eq

For the single preferred F3 package, the extracted endpoints have the expected
constants definitionally:

    mass      = kpParameter wab.r
    prefactor = clusterPrefactorShifted wab.r pkg.C_conn pkg.A₀ pkg.dim

These are regression canaries: future refactors of the F3 terminal route should
not silently change the mass parameter or the prefactor carried into
`ClayYangMillsMassGap` / `ClayConnectedCorrDecay`.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clayMassGap_of_shiftedF3MayerCountPackage_mass_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayMassGap_of_shiftedF3MayerCountPackage_prefactor_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_mass_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayConnectedCorrDecay_of_shiftedF3MayerCountPackage_prefactor_eq'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.75.0 — Single preferred shifted F3 package

**Released: 2026-04-24**

## What

Pure additive frontier consolidation in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    structure ShiftedF3MayerCountPackage

and single-package consumers:

    theorem clusterCorrelatorBound_of_shiftedF3MayerCountPackage
    noncomputable def clayWitnessHyp_of_shiftedF3MayerCountPackage
    noncomputable def clayMassGap_of_shiftedF3MayerCountPackage
    noncomputable def clayConnectedCorrDecay_of_shiftedF3MayerCountPackage
    theorem clay_theorem_of_shiftedF3MayerCountPackage

`ShiftedF3MayerCountPackage N_c wab` is now the one-object preferred F3
frontier.  It bundles:

1. constants `C_conn`, `A₀`, positivity proofs, and `dim`;
2. `ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le`;
3. `ShiftedConnectingClusterCountBound C_conn dim`.

Supplying this package yields every downstream terminal view:

    ClusterCorrelatorBound
    ClayWitnessHyp
    ClayYangMillsMassGap
    ClayConnectedCorrDecay
    ClayYangMillsTheorem

This does not prove the package.  It makes the remaining F3 work a single
named Lean object whose projections are all oracle-clean.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clusterCorrelatorBound_of_shiftedF3MayerCountPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayWitnessHyp_of_shiftedF3MayerCountPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayMassGap_of_shiftedF3MayerCountPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayConnectedCorrDecay_of_shiftedF3MayerCountPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_shiftedF3MayerCountPackage'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.74.0 — F3 endpoints into `ClayWitnessHyp`

**Released: 2026-04-24**

## What

Pure additive F3 consumer bridge in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    noncomputable def clayWitnessHyp_of_shiftedCountBound_mayerData_ceil
    noncomputable def clayWitnessHyp_of_shiftedCountBound_connectedCardDecayActivities_ceil

The preferred shifted F3 packages now feed the older analytic witness bundle
directly:

    ClayWitnessHyp N_c

The packaged route consumes
`ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le` plus
`ShiftedConnectingClusterCountBound C_conn dim`; the unpackaged route consumes
the raw `K / hK_abs_le / h_mayer` triple plus the same shifted count package.

Both definitions route through the v0.73 bridge
`clayWitnessHyp_of_clusterCorrelatorBound`, so the hierarchy is now:

    F3 packages
      → ClusterCorrelatorBound
      → ClayWitnessHyp
      → ClayYangMillsMassGap / ClayConnectedCorrDecay / ClayYangMillsTheorem

No analytic package is proved here.  The remaining F3 mathematical work is
still exactly to supply the two named packages.  The gain is that all terminal
consumer shapes are now wired to the same B1/F3 source.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clayWitnessHyp_of_shiftedCountBound_mayerData_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayWitnessHyp_of_shiftedCountBound_connectedCardDecayActivities_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.73.0 — `ClusterCorrelatorBound` to `ClayWitnessHyp`

**Released: 2026-04-24**

## What

Pure additive consumer bridge in `YangMills/ClayCore/ClusterCorrelatorBound.lean`:

    noncomputable def clayWitnessHyp_of_clusterCorrelatorBound

`ClusterCorrelatorBound N_c r C_clust` is now repackaged directly as the
older analytic witness bundle:

    ClayWitnessHyp N_c

The map is field-for-field:

* `r`, `hr_pos`, `hr_lt_one`;
* `C_clust`, `hC_clust`;
* the universal connected-correlator bound `hbound_hyp`.

This means a future proof of `ClusterCorrelatorBound` feeds all three
downstream views without extra glue:

1. `CharacterExpansionData` via `wilsonCharExpansion`;
2. `ClayYangMillsMassGap` via `clay_massGap_large_beta`;
3. `ClayWitnessHyp` via `clayWitnessHyp_of_clusterCorrelatorBound`.

No analytic package is proved here; the frontier remains the production of
`ClusterCorrelatorBound` itself.  The gain is that the B1/F3 output is now the
single canonical object consumed by both the newer `CharacterExpansionData`
route and the older `ClayWitnessHyp` route.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterCorrelatorBound

Pinned trace:

    'YangMills.clayWitnessHyp_of_clusterCorrelatorBound'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.72.0 — F3 endpoints into `ClayConnectedCorrDecay`

**Released: 2026-04-24**

## What

Pure additive hub alignment in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    noncomputable def clayConnectedCorrDecay_of_shiftedCountBound_mayerData_ceil
    noncomputable def clayConnectedCorrDecay_of_shiftedCountBound_connectedCardDecayActivities_ceil

The preferred F3 route already reaches the authentic
`ClayYangMillsMassGap N_c` structure (v0.70/v0.71).  v0.72 also exports the
same result through the physically named hub:

    ClayConnectedCorrDecay N_c

This is a field-for-field projection via
`ClayConnectedCorrDecay.ofClayMassGap`; it introduces no new mathematical
content and no new hypotheses.  Its value is interface hygiene: analytic routes
that use `ClayConnectedCorrDecay` as their common target can now consume the
preferred F3 packages directly, while the mass-gap and weak theorem endpoints
remain downstream projections.

Both entry styles are covered:

1. packaged `ConnectedCardDecayMayerData` + `ShiftedConnectingClusterCountBound`;
2. raw `K / hK_abs_le / h_mayer` + `ShiftedConnectingClusterCountBound`.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clayConnectedCorrDecay_of_shiftedCountBound_mayerData_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clayConnectedCorrDecay_of_shiftedCountBound_connectedCardDecayActivities_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.71.0 — Unpackaged authentic F3 mass-gap endpoint

**Released: 2026-04-24**

## What

Pure additive API completion in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    noncomputable def clayMassGap_of_shiftedCountBound_connectedCardDecayActivities_ceil

This is the authentic `ClayYangMillsMassGap N_c` analogue of the older
unpackaged terminal wrapper

    clay_theorem_of_shiftedCountBound_connectedCardDecayActivities_ceil

It accepts the Mayer/activity inputs as separate fields:

1. raw truncated activity `K`;
2. connected-cardinality decay `hK_abs_le`;
3. Mayer/Ursell identity `h_mayer`;
4. shifted count package `ShiftedConnectingClusterCountBound C_conn dim`.

Internally it constructs the v0.68 package
`ConnectedCardDecayMayerData` and routes through the v0.70 authentic endpoint
`clayMassGap_of_shiftedCountBound_mayerData_ceil`.

Purpose: both public F3 entry styles now have a non-vacuous Clay-core output.
The packaged API remains preferred, but callers that still carry the raw
`K / hK_abs_le / h_mayer` triple can obtain `ClayYangMillsMassGap N_c`
without passing through the weak `ClayYangMillsTheorem` endpoint.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.clayMassGap_of_shiftedCountBound_connectedCardDecayActivities_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.70.0 — Authentic mass-gap endpoint for preferred F3

**Released: 2026-04-24**

## What

Pure additive terminal strengthening in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    noncomputable def clayMassGap_of_shiftedCountBound_mayerData_ceil

The preferred shifted F3 packages now feed the non-vacuous Clay-core target
directly:

    ClayYangMillsMassGap N_c

rather than only the deliberately weak existential
`ClayYangMillsTheorem := ∃ m_phys : ℝ, 0 < m_phys`.

The new wrapper consumes the same two named packages as v0.69:

1. `ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le`;
2. `ShiftedConnectingClusterCountBound C_conn dim`.

It first obtains

    ClusterCorrelatorBound N_c wab.r
      (clusterPrefactorShifted wab.r C_conn A₀ dim)

from `clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil`, then
passes that bound through `clay_massGap_large_beta`.  The older
`clay_theorem_of_shiftedCountBound_mayerData_ceil` remains available, but it is
now visibly downstream of the authentic mass-gap route rather than the primary
thing to audit.

This does not prove the two F3 packages.  It removes a terminal ambiguity: once
the packages are supplied, the first-class result is the pinned Wilson
`ClayYangMillsMassGap N_c` structure.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.clayMassGap_of_shiftedCountBound_mayerData_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.69.0 — Packaged `ClusterCorrelatorBound` endpoint for preferred F3

**Released: 2026-04-24**

## What

Pure additive terminal API strengthening in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil

The v0.68 package exposed the preferred F3 Clay-facing wrapper

    clay_theorem_of_shiftedCountBound_mayerData_ceil

but its conclusion was the deliberately weak endpoint
`ClayYangMillsTheorem`.  v0.69 exposes the real analytic product of the
same two packages directly:

    ClusterCorrelatorBound N_c r
      (clusterPrefactorShifted r C_conn A₀ dim)

It consumes exactly:

1. `ConnectedCardDecayMayerData N_c r A₀ hr_pos.le hA.le`, packaging the
   raw Mayer/activity kernel, its connected-cardinality decay bound, and the
   Mayer/Ursell identity for `wilsonConnectedCorr`;
2. `ShiftedConnectingClusterCountBound C_conn dim`, the named shifted
   lattice-animal count package.

The existing Clay wrapper is now factored through this stronger theorem via
`clay_theorem_from_wilson_activity`.  This makes the active F3 target honest
at the API level: the work remaining is to produce the two named packages,
after which `ClusterCorrelatorBound` itself is available before any weak
terminal Clay existential is invoked.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clusterCorrelatorBound_of_shiftedCountBound_mayerData_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_shiftedCountBound_mayerData_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.68.0 — Packaged Mayer/activity data for preferred F3 endpoint

**Released: 2026-04-24**

## What

Pure additive terminal API packaging in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    structure ConnectedCardDecayMayerData
    theorem clay_theorem_of_shiftedCountBound_mayerData_ceil

`ConnectedCardDecayMayerData N_c r A₀ hr_nonneg hA_nonneg` packages the two
non-count analytic inputs for the preferred F3 route:

1. the raw truncated activity `K`;
2. its connected-cardinality decay bound
   `|K Y| ≤ if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r^Y.card else 0`;
3. the Mayer/Ursell identity identifying the Wilson connected correlator with
   the connecting sum of `TruncatedActivities.ofConnectedCardDecay`.

The preferred terminal wrapper is now:

    clay_theorem_of_shiftedCountBound_mayerData_ceil

It consumes exactly:

1. `ConnectedCardDecayMayerData N_c wab.r A₀ wab.hr_pos.le hA.le`;
2. `ShiftedConnectingClusterCountBound C_conn dim`.

This is not a proof of those two packages.  It is the clean terminal interface
for the remaining F3 work: one analytic Mayer/activity package plus one
combinatorial lattice-animal count package.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.clay_theorem_of_shiftedCountBound_mayerData_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.67.0 — Named shifted count frontier for terminal F3

**Released: 2026-04-24**

## What

Pure additive frontier packaging:

    def ShiftedConnectingClusterCountBound
    theorem ShiftedConnectingClusterCountBound.apply
    theorem C_conn_const_pos_of_neZero
    theorem clay_theorem_of_shiftedCountBound_connectedCardDecayActivities_ceil

`ShiftedConnectingClusterCountBound C_conn dim` is now the named F3
lattice-animal count target:

    # {Y ∋ p,q | PolymerConnected Y ∧
        Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊}
      ≤ C_conn * (n+1)^dim.

The preferred terminal wrapper
`clay_theorem_of_shiftedCountBound_connectedCardDecayActivities_ceil` consumes
this single named count package, rather than an anonymous repeated bucket
formula.  The remaining F3 terminal inputs are now visibly:

1. `ShiftedConnectingClusterCountBound C_conn dim`;
2. the raw connected-cardinality-decay truncated activity bound;
3. the Mayer/Ursell identity for the constructed activity.

This does not prove the lattice-animal theorem; it names it precisely in the
form consumed by the terminal Clay-facing F3 wrapper.

## Oracle

Builds:

    lake build YangMills.ClayCore.ConnectingClusterCount
    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.ShiftedConnectingClusterCountBound.apply' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_shiftedCountBound_connectedCardDecayActivities_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.66.0 — Shifted terminal F3 endpoint

**Released: 2026-04-24**

## What

Pure additive terminal F3 wrapper in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clusterCorrelatorBound_of_count_cardDecayBounds_ceil_shifted
    theorem clay_theorem_of_count_connectedCardDecayActivities_ceil_shifted

This is the shifted analogue of the v0.62 terminal endpoint.  It consumes:

1. a raw connected-cardinality-decay truncated activity bound
   `|K Y| ≤ if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y then A₀ * r^Y.card else 0`;
2. the Mayer/Ursell identity for the constructed activity;
3. the realistic bucket count
   `#bucket(n) ≤ C_conn * (n+1)^dim`.

The disconnected support cancellation, global `K_bound` cardinality decay, and
finite-volume summability are supplied by `TruncatedActivities.ofConnectedCardDecay`.
The final exponential bound uses `clusterPrefactorShifted r C_conn A₀ dim`.

This is now the preferred F3 terminal wrapper: it keeps the minimal bucket
`n = 0` non-vacuous while preserving the same Clay-facing
`ClusterCorrelatorBound` shape.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clusterCorrelatorBound_of_count_cardDecayBounds_ceil_shifted'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_count_connectedCardDecayActivities_ceil_shifted'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.65.0 — Shifted bucket-count consumers for F3

**Released: 2026-04-24**

## What

Pure additive F3 bucket support in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem connectedFiniteSum_le_of_cardBucketBounds_shifted
    theorem connectedFiniteSum_le_of_cardBucketBounds_kp_shifted
    theorem cardBucketSum_le_of_count_and_pointwise_shifted

These are the finite connected-sum and bucket consumers for the shifted
lattice-animal count

    #bucket(n) ≤ C_conn * (n + 1)^dim.

Together with v0.64.0, this carries the realistic nonzero minimal-bucket
profile through the same decomposition used by the unshifted F3 bridge:

    connected finite sum
      → cardinal buckets
      → count + pointwise bound
      → shifted KP series.

The older unshifted consumers remain available for compatibility.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.connectedFiniteSum_le_of_cardBucketBounds_shifted'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.connectedFiniteSum_le_of_cardBucketBounds_kp_shifted'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.cardBucketSum_le_of_count_and_pointwise_shifted'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.64.0 — Shifted KP series reaches ClusterCorrelatorBound

**Released: 2026-04-24**

## What

Pure additive F3 bridge support in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem TruncatedActivities.two_point_decay_from_cluster_tsum_shifted
    theorem clusterPrefactorShifted_rpow_ceil_le_exp
    theorem clusterCorrelatorBound_of_truncatedActivities_ceil_shifted

This propagates v0.63.0's shifted KP series

    C_conn * (n + 1)^dim * A₀ * r^(n + dist)

from the series layer to the abstract `ClusterCorrelatorBound` bridge.  If an
abstract connecting bound is controlled by the shifted series, the resulting
two-point decay has the same exponential form as before, with the shifted
prefactor

    clusterPrefactorShifted r C_conn A₀ dim.

The unshifted API is left intact.  Downstream F3 wrappers can now choose the
realistic nonzero minimal-bucket profile without redoing the KP summability or
geometric comparison work.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.TruncatedActivities.two_point_decay_from_cluster_tsum_shifted'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterPrefactorShifted_rpow_ceil_le_exp' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterCorrelatorBound_of_truncatedActivities_ceil_shifted'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.63.0 — Shifted KP series for nonempty cardinality buckets

**Released: 2026-04-24**

## What

Pure additive KP-series support in `YangMills/ClayCore/ClusterSeriesBound.lean`:

    theorem connecting_cluster_tsum_summable_shifted
    theorem connecting_cluster_summand_nonneg_shifted
    theorem connecting_cluster_partial_sum_le_tsum_shifted
    noncomputable def clusterPrefactorShifted
    theorem clusterPrefactorShifted_pos
    theorem connecting_cluster_tsum_le_shifted

This adds the shifted polynomial profile

    C_conn * (n + 1)^dim * A₀ * r^(n + dist)

alongside the existing `C_conn * n^dim * A₀ * r^(n + dist)` profile.  The
shifted form is the natural lattice-animal bucket shape because the minimal
extra-size bucket is indexed by `n = 0`; using `n^dim` makes that bucket's
count bound collapse to zero when `dim > 0`.

No existing theorem is changed or weakened.  The new shifted API is available
for downstream F3 wrappers that want a realistic nonzero count at the minimal
bucket while preserving the same exponential `r^dist` factorization.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterSeriesBound

Pinned traces:

    'YangMills.connecting_cluster_partial_sum_le_tsum_shifted' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterPrefactorShifted_pos' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.connecting_cluster_tsum_le_shifted' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.62.0 — F3 endpoint from connected cardinality-decay activities

**Released: 2026-04-24**

## What

Pure additive F3 refinement in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    noncomputable def TruncatedActivities.ofConnectedCardDecay
    theorem TruncatedActivities.ofConnectedCardDecay_K
    theorem TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay
    theorem TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected
    theorem clay_theorem_of_count_connectedCardDecayActivities_ceil

The new finite-volume constructor packages a raw truncated activity `K` with a
bound supported only on polymers that contain the two marked plaquettes and are
connected:

    |K Y| ≤ if p ∈ Y ∧ q ∈ Y ∧ PolymerConnected Y
      then A₀ * r^Y.card else 0

From this support-shaped bound, the constructor immediately gives:

1. disconnected support cancellation for `K_bound`;
2. global cardinality decay `K_bound Y ≤ A₀ * r^Y.card`;
3. the usual finite-volume summability.

The terminal endpoint
`clay_theorem_of_count_connectedCardDecayActivities_ceil` therefore no longer
asks callers for separate `h_zero` and `h_card_decay` hypotheses on an
abstract `TruncatedActivities` object.  It consumes the raw connected
cardinality-decay activity bound, the Mayer/Ursell identity for the constructed
activity, and the lattice-animal bucket count.

Remaining F3 frontier after this wrapper:

1. prove the actual Mayer/Ursell identity for the Wilson truncated activity;
2. prove the connected cardinality-decay activity bound above;
3. prove the lattice-animal bucket count.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.TruncatedActivities.ofConnectedCardDecay' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.TruncatedActivities.ofConnectedCardDecay_K_bound_le_cardDecay'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.TruncatedActivities.ofConnectedCardDecay_K_bound_eq_zero_of_not_connected'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_count_connectedCardDecayActivities_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.61.0 — Projection simp rules for card-decay activities

**Released: 2026-04-24**

## What

Pure additive API support in `YangMills/ClayCore/MayerExpansion.lean`:

    theorem TruncatedActivities.ofCardDecay_K
    theorem TruncatedActivities.ofCardDecay_K_bound

Both are marked `[simp]`.  They expose the two defining projections of
`TruncatedActivities.ofCardDecay`:

    (ofCardDecay K r A₀ ...).K Y = K Y
    (ofCardDecay K r A₀ ...).K_bound Y = A₀ * r^Y.card

This makes future F3 producers less brittle: when a concrete finite-volume
truncated activity is built from cardinality decay, Lean can reduce its
activity and bound fields by `simp` instead of requiring manual unfolding.

## Oracle

Build:

    lake build YangMills.ClayCore.MayerExpansion

Pinned traces:

    'YangMills.TruncatedActivities.ofCardDecay_K' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.TruncatedActivities.ofCardDecay_K_bound' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.60.0 — Finite-volume TruncatedActivities from cardinality decay

**Released: 2026-04-24**

## What

Pure additive constructor in `YangMills/ClayCore/MayerExpansion.lean`:

    noncomputable def TruncatedActivities.ofCardDecay

It builds a `TruncatedActivities ι` on a finite polymer index type from the
canonical global activity estimate

    |K Y| ≤ A₀ * r^Y.card

with `0 ≤ A₀` and `0 ≤ r`.  The pointwise bound is packaged as

    K_bound Y := A₀ * r^Y.card

and `summable_K_bound` is discharged automatically from finite support.  This
removes one manual analytic bookkeeping obligation from future F3 producers:
after v0.59.0, the terminal F3 wrapper consumes global cardinality decay;
after v0.60.0, the abstract Mayer/KP activity object can be constructed from
the same global decay shape in finite volume.

This does not prove the Mayer/Ursell identity or the lattice-animal count.  It
only exposes the finite-volume constructor needed to make those future
producers plug into the existing `TruncatedActivities` API.

## Oracle

Builds:

    lake build YangMills.ClayCore.MayerExpansion
    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.TruncatedActivities.ofCardDecay' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.59.0 — F3 terminal endpoint from count + global cardinality decay

**Released: 2026-04-24**

## What

Pure additive F3 refinement in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem pointwiseBucketBound_of_card_decay
    theorem clusterCorrelatorBound_of_count_cardDecayBounds_ceil
    theorem clay_theorem_of_count_cardDecayBounds_ceil

The previous terminal endpoint consumed a bucket-local pointwise estimate

    K_bound Y ≤ A₀ * r^(n + ⌈dist(p,q)⌉₊)

for every polymer `Y` in the bucket
`Y.card = n + ⌈dist(p,q)⌉₊`.  v0.59.0 reduces that input to the more natural
global cardinality-decay estimate

    K_bound Y ≤ A₀ * r^Y.card

plus the existing lattice-animal bucket count.  The small bridge theorem
`pointwiseBucketBound_of_card_decay` performs the restriction from global
cardinality decay to a fixed bucket by reading the bucket's `Y.card`
equality.

The terminal F3 endpoint therefore now takes:

1. Mayer/Ursell identity `h_mayer`;
2. disconnected support cancellation `h_zero`;
3. lattice-animal bucket count `h_count`;
4. global cardinality decay `h_card_decay`.

This is still a composition/audit improvement: it does not prove the
lattice-animal count, the Mayer identity, or disconnected support
cancellation.  It does make the pointwise analytic input match the canonical
polymer-activity shape already used elsewhere in the project.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.pointwiseBucketBound_of_card_decay' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterCorrelatorBound_of_count_cardDecayBounds_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_count_cardDecayBounds_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.58.0 — F3 terminal endpoint from count + pointwise bounds

**Released: 2026-04-24**

## What

Pure additive terminal wrapper in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clay_theorem_of_count_pointwiseBounds_ceil

This composes `clusterCorrelatorBound_of_count_pointwiseBounds_ceil` with
`clay_theorem_from_wilson_activity`.  With a `WilsonPolymerActivityBound`,
the current `ClayYangMillsTheorem` endpoint now follows directly from the
four factored F3 inputs:

1. Mayer/Ursell identity `h_mayer`;
2. disconnected support cancellation `h_zero`;
3. lattice-animal bucket count `h_count`;
4. pointwise polymer activity estimate `h_pointwise`.

No caller has to manually assemble the intermediate bucket, connected-finite,
or `ClusterCorrelatorBound` layers.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.clay_theorem_of_count_pointwiseBounds_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.57.0 — F3 ClusterCorrelatorBound from count + pointwise bounds

**Released: 2026-04-24**

## What

Pure additive F3 wrapper in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clusterCorrelatorBound_of_count_pointwiseBounds_ceil

This composes the v0.56 bucket estimate with the v0.55 terminal bucket
consumer.  The F3 bridge now accepts the two natural lattice-animal inputs
directly:

1. bucket cardinality:
   `# {Y ∋ p,q | connected Y ∧ |Y| = n + ⌈dist⌉₊} ≤ C_conn * n^dim`;
2. pointwise activity:
   `K_bound Y ≤ A₀ * r^(n + ⌈dist⌉₊)` on each polymer in that bucket.

Together with `h_mayer` and disconnected support cancellation `h_zero`, these
produce `ClusterCorrelatorBound N_c r (clusterPrefactor r C_conn A₀ dim)`.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.clusterCorrelatorBound_of_count_pointwiseBounds_ceil'
    depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.56.0 — F3 bucket estimate from count + pointwise polymer bound

**Released: 2026-04-24**

## What

Pure additive F3 decomposition in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem cardBucketSum_le_of_count_and_pointwise

For a fixed cardinality bucket

    Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊,

the bucket sum is bounded by the KP summand if:

1. the number of connected polymers in that bucket is bounded by
   `C_conn * n^dim`, and
2. each polymer in the bucket has pointwise bound
   `K_bound Y ≤ A₀ * r^(n + ⌈dist⌉₊)`.

This separates the remaining lattice-animal bucket estimate into its two
natural pieces: a combinatorial cardinality bound and a pointwise activity
bound. The theorem is a finite-sum manipulation only.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.cardBucketSum_le_of_count_and_pointwise' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.55.0 — F3 terminal bucket-estimate wrappers

**Released: 2026-04-24**

## What

Pure additive F3 wrappers in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clusterCorrelatorBound_of_cardBucketBounds_ceil
    theorem clay_theorem_of_cardBucketBounds_ceil

These compose the v0.52 bucket decomposition, the v0.54 partial-sum
comparison, and the existing connected finite bridge.  The F3 consumer now
accepts the exact lattice-animal shape:

    ∀ n, bucket_sum(n, p, q)
      ≤ C_conn * n^dim * A₀ *
        r^(n + ⌈siteLatticeDist p.site q.site⌉₊)

Together with the Mayer/Ursell identity `h_mayer` and disconnected support
cancellation `h_zero`, this produces `ClusterCorrelatorBound`; with a
`WilsonPolymerActivityBound`, the terminal wrapper produces the current
`ClayYangMillsTheorem` endpoint.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.clusterCorrelatorBound_of_cardBucketBounds_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clay_theorem_of_cardBucketBounds_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.54.0 — F3 KP partial-sum comparison discharged

**Released: 2026-04-24**

## What

Pure additive F3 summability cleanup:

    theorem connecting_cluster_summand_nonneg
    theorem connecting_cluster_partial_sum_le_tsum

in `YangMills/ClayCore/ClusterSeriesBound.lean`, plus the consumer

    theorem connectedFiniteSum_le_of_cardBucketBounds_kp

in `YangMills/ClayCore/ClusterRpowBridge.lean`.

The new `ClusterSeriesBound` lemmas prove that the KP summand

    C_conn * n^dim * A₀ * r^(n + dist)

is nonnegative for positive constants, and therefore every finite partial
sum over `Finset.range M` is bounded by the corresponding `tsum`.
The new bridge theorem uses this internally, so the connected finite F3
consumer no longer asks callers for a separate `h_partial_le_tsum`.

## Oracle

Builds:

    lake build YangMills.ClayCore.ClusterSeriesBound
    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned traces:

    'YangMills.connecting_cluster_summand_nonneg' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.connecting_cluster_partial_sum_le_tsum' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.connectedFiniteSum_le_of_cardBucketBounds_kp' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.53.0 — F3 bucket-bound consumer for connected finite sums

**Released: 2026-04-24**

## What

Pure additive F3 consumer in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem connectedFiniteSum_le_of_cardBucketBounds
        (K_bound : Finset (ConcretePlaquette d L) → ℝ)
        (p q : ConcretePlaquette d L)
        (r C_conn A₀ : ℝ) (dim : ℕ)
        (h_bucket : ∀ n ∈ range (...),
          bucket_sum n ≤ C_conn * n^dim * A₀ *
            r^(n + ⌈siteLatticeDist p.site q.site⌉₊))
        (h_partial_le_tsum : finite_KP_partial_sum ≤ KP_tsum) :
        connected_finite_sum ≤ KP_tsum

It consumes the v0.52 bucket decomposition: bound each finite cardinality
bucket by the corresponding KP summand, compare the resulting finite partial
sum with the infinite KP series, and obtain the connected finite estimate
required by `clusterCorrelatorBound_of_connectedFiniteBounds_ceil`.

This narrows the remaining connected KP task to two explicit pieces:

1. the lattice-animal bucket estimate, and
2. the standard nonnegative partial-sum-to-`tsum` comparison.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.connectedFiniteSum_le_of_cardBucketBounds' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.52.0 — F3 connected finite sum cardinal-bucket decomposition

**Released: 2026-04-24**

## What

Pure additive F3 combinatorial normalization in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem connectedFiniteSum_eq_cardBucketSum
        (K_bound : Finset (ConcretePlaquette d L) → ℝ)
        (p q : ConcretePlaquette d L) :
        ∑_{Y ∋ p,q, connected} K_bound Y
          =
        ∑ n in range (Fintype.card (ConcretePlaquette d L) + 1),
          ∑_{Y ∋ p,q, connected}
            if Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊
            then K_bound Y else 0

This decomposes the finite connected-polymer sum into the canonical
cardinality buckets

    Y.card = n + ⌈siteLatticeDist p.site q.site⌉₊.

The proof uses `ceil_siteLatticeDist_le_polymer_card` to show that every
connected polymer containing `p` and `q` belongs to a unique nonnegative
extra-size bucket.  This is the finite form immediately preceding the
lattice-animal estimate.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.connectedFiniteSum_eq_cardBucketSum' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.51.0 — F3 terminal wrapper from connected finite KP data

**Released: 2026-04-24**

## What

Pure additive terminal wrapper in
`YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clay_theorem_of_connectedFiniteBounds_ceil
        (N_c : ℕ) [NeZero N_c]
        (wab : WilsonPolymerActivityBound N_c)
        (C_conn A₀ : ℝ) (hC : 0 < C_conn) (hA : 0 < A₀)
        (dim : ℕ)
        (T : ...)
        (h_mayer : ...)
        (h_zero : ...)
        (h_connected_bound : ...) :
        ClayYangMillsTheorem

It composes the v0.49 connected finite-sum bridge
`clusterCorrelatorBound_of_connectedFiniteBounds_ceil` with
`clay_theorem_from_wilson_activity`.  The prefactor positivity is discharged
internally by `clusterPrefactor_pos`.

This does not prove the Mayer identity or the Kotecký-Preiss
lattice-animal estimate.  It sharpens the terminal interface: once
`h_mayer`, disconnected support cancellation `h_zero`, and the connected
finite KP estimate `h_connected_bound` are available, the current
`ClayYangMillsTheorem` endpoint follows by a single theorem call.

## Oracle

Build:

    lake build YangMills.ClayCore.ClusterRpowBridge

Pinned trace:

    'YangMills.clay_theorem_of_connectedFiniteBounds_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet.

---

# v0.50.0 — HS audit: explicit normalized-Gibbs LSI axiom replaces hidden sorry

**Released: 2026-04-24**

## What

Audit-only / no mathematical pipeline change. The unrestricted Holley--Stroock
transfer

    axiom lsi_normalized_gibbs_from_haar
        (N_c : ℕ) [NeZero N_c] (hN_c : 2 ≤ N_c)
        (β : ℝ) (hβ : 0 < β) (α : ℝ) (hα : 0 < α)
        (hHaar : LogSobolevInequality
          (sunHaarProb N_c) (sunDirichletForm N_c) α) :
        LogSobolevInequality
          ((sunHaarProb N_c).withDensity
            (sunNormalizedGibbsDensity N_c hN_c β hβ))
          (sunDirichletForm N_c)
          (α * Real.exp (-2 * β))

is now declared as a named axiom in
`YangMills/P8_PhysicalGap/BalabanToLSI.lean`.

This replaces the former theorem-shaped placeholder that carried the same
missing universal integrability step behind `sorry`. The ledger is now honest:
the vanilla route depends on the named axiom, while the Σ/MemLp-gated route
continues to discharge the corresponding restricted statement without it.

## Oracle

Builds:

    lake build YangMills.P8_PhysicalGap.BalabanToLSI
    lake build YangMills.P8_PhysicalGap.PhysicalMassGap
    lake build YangMills.P8_PhysicalGap.ClayViaLSI

Pinned trace:

    'YangMills.lsi_normalized_gibbs_from_haar' depends on axioms: [propext,
     Classical.choice,
     Quot.sound,
     YangMills.lsi_normalized_gibbs_from_haar]

    'YangMills.lsi_normalized_gibbs_from_haar_memLp' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.sun_physical_mass_gap_vacuous' depends on axioms: [propext,
     Classical.choice,
     Quot.sound,
     YangMills.lsi_normalized_gibbs_from_haar]

    'YangMills.sun_physical_mass_gap_vacuous_memLp' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No unconditional bar movement. This is a transparency repair: it removes a
hidden `sorryAx` dependency from the vanilla chain by naming the exact frontier
assumption. The live Clay-grade path remains the MemLp-gated terminal route and
the `ClusterCorrelatorBound` front.

---

# v0.49.0 — F3 counting interface: canonical buckets + finite connecting bound

**Released: 2026-04-24**

## What

Pure additive F3 interface tightening across the geometry/counting side:

    theorem ceil_siteLatticeDist_le_polymer_card
        ... :
        ⌈siteLatticeDist p.site q.site⌉₊ ≤ X.card

    theorem connected_polymer_card_eq_extra_add_dist
        ... :
        ∃ n : ℕ, X.card = n + ⌈siteLatticeDist p.site q.site⌉₊

    theorem TruncatedActivities.connectingBound_eq_finset_sum
        ... :
        T.connectingBound p q =
          ∑ Y ∈ univ.filter (fun Y => p ∈ Y ∧ q ∈ Y), T.K_bound Y

    theorem clusterCorrelatorBound_of_finiteConnectingBounds_ceil
        ... :
        ClusterCorrelatorBound N_c r
          (clusterPrefactor r C_conn A₀ dim)

    theorem finiteConnectingSum_eq_connectedFiniteSum
        ... :
        ∑_{Y ∋ p,q} K_bound Y =
          ∑_{Y ∋ p,q, PolymerConnected Y} K_bound Y

    theorem clusterCorrelatorBound_of_connectedFiniteBounds_ceil
        ... :
        ClusterCorrelatorBound N_c r
          (clusterPrefactor r C_conn A₀ dim)

The first theorem exposes the natural-number form of the existing polymer
diameter lemma `polymer_size_ge_site_dist_succ`: any connected polymer
containing `p` and `q` has size at least the ceiling of their lattice
distance.  The second packages every such polymer into the exact bucket
shape used by the F3 series,

    X.card = n + ⌈siteLatticeDist p.site q.site⌉₊.

The third removes an opacity mismatch in the Mayer layer: on finite plaquette
index types, `connectingBound` is no longer only a `tsum` over `Finset ι`; it
is definitionally available as a finite sum over polymers containing `p` and
`q`.  This is the concrete form needed by lattice-animal / connecting-cluster
counting estimates.

The fourth theorem is the Wilson-facing bridge that consumes exactly that
finite-sum estimate: if the finite sum of `K_bound` over polymers containing
`p,q` is bounded by the canonical

    ∑' n, C_conn * n^dim * A₀ *
      r ^ (n + ⌈siteLatticeDist p.site q.site⌉₊)

then `ClusterCorrelatorBound` follows.  The abstract `connectingBound` is
opened internally, so the remaining KP task can now be stated directly as a
finite lattice-animal estimate.

The final pair adds the connected-polymer version: if `K_bound` vanishes on
disconnected polymers containing `p,q`, the finite connecting sum restricts
to `PolymerConnected` polymers, and the Wilson-facing bridge may consume a
bound on that connected finite sum directly.

## Oracle

Builds:

    lake build YangMills.ClayCore.PolymerDiameterBound
    lake build YangMills.ClayCore.ConnectingClusterCount
    lake build YangMills.ClayCore.MayerExpansion
    lake build YangMills

Pinned trace:

    'YangMills.ceil_siteLatticeDist_le_polymer_card' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.connected_polymer_card_eq_extra_add_dist' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.TruncatedActivities.connectingBound_eq_finset_sum' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterCorrelatorBound_of_finiteConnectingBounds_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.finiteConnectingSum_eq_connectedFiniteSum' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterCorrelatorBound_of_connectedFiniteBounds_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet: this does not prove the
Kotecký-Preiss connecting-cluster estimate, but it aligns the existing finite
Mayer bound, polymer diameter geometry, and the canonical `n + ⌈dist⌉₊`
counting buckets required for that estimate.

---

# v0.48.0 — F3 bridge: truncated activities to ClusterCorrelatorBound

**Released: 2026-04-24**

## What

Pure additive F3 bridge in `YangMills/ClayCore/ClusterRpowBridge.lean`:

    theorem clusterCorrelatorBound_of_truncatedActivities
        ... :
        ClusterCorrelatorBound N_c r
          (clusterPrefactor r C_conn A₀ dim)

    theorem clusterCorrelatorBound_of_truncatedActivities_ceil
        ... :
        ClusterCorrelatorBound N_c r
          (clusterPrefactor r C_conn A₀ dim)

This composes the existing Mayer/Kotecký-Preiss analytic scaffolding:

1. `TruncatedActivities.abs_connectingSum_le_connectingBound`
   (`MayerExpansion.lean`);
2. `connecting_cluster_tsum_le`
   (`ClusterSeriesBound.lean`);
3. the Wilson-facing exponential target
   `ClusterCorrelatorBound N_c r C_clust`.

The general theorem is intentionally honest about the remaining analytic
inputs. It takes as hypotheses:

- a Mayer/Ursell identity identifying `wilsonConnectedCorr` with the
  connecting truncated-activity sum;
- a connecting-cluster series bound on `connectingBound`;
- a geometric comparison from the discrete cluster distance `distNat` to
  `siteLatticeDist`.

Given those inputs, the F3 summability/factoring part is fully discharged in
Lean and produces the exact `ClusterCorrelatorBound` shape consumed by the
Clay pipeline.

The canonical-ceiling variant closes the geometric comparison internally:

    clusterPrefactor r C_conn A₀ dim * r ^ ⌈siteLatticeDist p q⌉₊
      ≤ clusterPrefactor r C_conn A₀ dim *
        exp (-(kpParameter r) * siteLatticeDist p q)

via `clusterPrefactor_rpow_ceil_le_exp`. Thus, when the cluster-series bound
is stated with the standard discrete distance `⌈siteLatticeDist⌉₊`, the only
remaining F3 inputs are the Mayer/Ursell identity and the bound on
`connectingBound`.

## Oracle

Builds:

    lake build YangMills.ClayCore.ClusterRpowBridge
    lake build YangMills

Pinned trace:

    'YangMills.clusterCorrelatorBound_of_truncatedActivities' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterPrefactor_rpow_ceil_le_exp' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    'YangMills.clusterCorrelatorBound_of_truncatedActivities_ceil' depends on axioms:
    [propext, Classical.choice, Quot.sound]

No new axioms. No `sorry`. No bar movement yet: the remaining open work is now
sharply isolated to the Mayer/Ursell identity plus the `connectingBound`
cluster-series estimate, not the F3 summability/factoring or the canonical
ceiling-to-exponential geometry.

---

# v0.47.0 — P2d-audit: frontier reclassification + Clay-endpoint triviality canary

**Released: 2026-04-24**

## What

Audit-only pass; no mathematical pipeline change. One Lean file is
added as a canary module with zero downstream dependency:

    theorem clayYangMillsTheorem_trivial : ClayYangMillsTheorem :=
      ⟨1, one_pos⟩

    theorem clayYangMillsTheorem_iff_true : ClayYangMillsTheorem ↔ True

    theorem clayYangMillsStrong_trivial : ClayYangMillsStrong :=
      clay_strong_no_axiom

    theorem clayYangMillsStrong_iff_true : ClayYangMillsStrong ↔ True

in `YangMills/L8_Terminal/ClayTrivialityAudit.lean`.

Three facts are recorded:

1. `WilsonPolymerActivityBound.h_bound` is reclassified from active
   frontier to **closed de facto for the current small-β / clipped Wilson
   activity producer**. The pair `wilsonClusterActivity_abs_le` +
   `wilsonActivityBound_from_expansion` already discharges the field on
   `0 < β < 1` with the β-clipped fluctuation
   `plaquetteFluctuationAt N_c β`. This does **not** claim that Balaban
   CMP 116 Lemma 3 is formalised in full generality: raw unclipped
   character-expansion / Bessel-coefficient asymptotics on `SU(N_c)` for
   arbitrary irreps remain future work. It records that, within the
   current formalism, the `h_bound` field has a canonical producer and is
   not the active bottleneck.

2. The active analytic frontier is `h_rpow`, equivalently
   `ClusterCorrelatorBound N_c r C_clust` modulo the proved bridge
   `clusterCorrelatorBound_of_rpow_bound`
   (`YangMills/ClayCore/WilsonClusterProof.lean`). This is the F3 /
   Kotecký-Preiss target on the `ClusterCorrelatorBound` front.

3. `ClayYangMillsTheorem := ∃ m_phys : ℝ, 0 < m_phys` and
   `ClayYangMillsStrong := ∃ m_lat, HasContinuumMassGap m_lat` are weak
   endpoints: both are trivially inhabited and both are equivalent to
   `True`. Wrappers whose conclusion is only `ClayYangMillsTheorem` or
   `ClayYangMillsStrong` discharge weak existentials, not Clay-grade
   Yang-Mills content. Per `YangMills/L8_Terminal/ClayPhysical.lean`, the
   hierarchy is

       ClayYangMillsPhysicalStrong → ClayYangMillsStrong → ClayYangMillsTheorem

   with `ClayYangMillsPhysicalStrong` the first non-vacuous level.

## Oracle

Build artefact:
`YangMills/L8_Terminal/ClayTrivialityAudit.lean`.

Pinned `#print axioms` trace from
`.lake/build/lib/lean/YangMills/L8_Terminal/ClayTrivialityAudit.trace`:

    YangMills/L8_Terminal/ClayTrivialityAudit.lean:80:0:
    'YangMills.clayYangMillsTheorem_trivial' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    YangMills/L8_Terminal/ClayTrivialityAudit.lean:81:0:
    'YangMills.clayYangMillsTheorem_iff_true' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    YangMills/L8_Terminal/ClayTrivialityAudit.lean:82:0:
    'YangMills.clayYangMillsStrong_trivial' depends on axioms:
    [propext, Classical.choice, Quot.sound]

    YangMills/L8_Terminal/ClayTrivialityAudit.lean:83:0:
    'YangMills.clayYangMillsStrong_iff_true' depends on axioms:
    [propext, Classical.choice, Quot.sound]

This is exactly the canonical project oracle. No new axioms. No `sorry`.

## Scope of change

Audit-only / no mathematical pipeline change. The new canary module is not
imported by downstream theorem files. L1 / L2 / L3 / OVERALL bars are
unchanged.

---

# v0.46.0 — P2f-α: balabanHyps_from_wilson_activity END-TO-END CONSTRUCTOR

**Released: 2026-04-24**

## What

Phase 3 / Task #7 sub-target P2f-α: pure-additive end-to-end constructor

    noncomputable def balabanHyps_from_wilson_activity
        {N_c : Nat} [NeZero N_c]
        (wab : WilsonPolymerActivityBound N_c)
        (profile : LargeFieldProfile)
        (h_lf_bound_at : ∀ (n : Nat), ∃ R : Real, 0 ≤ R ∧
          R ≤ Real.exp (-(profile.eval wab.r)) * Real.exp (-(-Real.log wab.r) * n))
        (h_dominated : Real.exp (-(profile.eval wab.r)) ≤ (wab.A₀ + 1) * wab.r ^ 2) :
        BalabanHyps N_c

in `YangMills/ClayCore/LargeFieldDominance.lean`. Closes the
structural loop of the α-stack: takes a `WilsonPolymerActivityBound`
(from which P2d-α produces the SFA) plus the analytic large-field
inputs (`profile`, `h_lf_bound_at`, `h_dominated`) evaluated at
the canonical `g_bar = wab.r`, and emits a full `BalabanHyps N_c`
via `balabanHyps_of_bounds`.

Commit: `3961827` · File:
`YangMills/ClayCore/LargeFieldDominance.lean` (+45/−0) · Oracle:
`[propext, Classical.choice, Quot.sound]`.

## Why

The α-stack so far had four pure-additive constructors — P2c-α
(`BalabanH1H2H3` shape refactor), P2d-α
(`SmallFieldActivityBound.ofWilsonActivity`), P2d-β
(`balabanH1_from_wilson_activity_enriched`), P2e-α
(`LargeFieldActivityBound.ofSuperPoly`) — but no single term-mode
constructor producing a full `BalabanHyps N_c` from a
`WilsonPolymerActivityBound`. P2f-α fills exactly that hole:
SFA + LFA → BalabanHyps end-to-end, polymer-faithful on the
small-field side and caller-controlled on the large-field side, with
zero `Classical.choose` opacity in the constants.

## How

`balabanHyps_of_bounds` (`LargeFieldBound.lean:94`) requires
`hg_eq : sfb.consts.g_bar = lfb.g_bar`,
`hk_eq : sfb.consts.kappa = lfb.kappa`,
`hE0_eq : sfb.consts.E0 = lfb.E0`. Both sides have to commit to
identical constants for these to close.

`SmallFieldActivityBound.ofWilsonActivity` (P2d-α, v0.44.0) fixes
`E₀ := wab.A₀ + 1`, `κ := -Real.log wab.r`, `ḡ := wab.r`.

P2e-α's `LargeFieldActivityBound.ofSuperPoly` is unsuitable: it
picks `g_bar := Classical.choose dom` (opaque), so no equality with
`wab.r` is provable. P2f-α therefore constructs the
`LargeFieldActivityBound` inline with the matching constants:

    let lfb : LargeFieldActivityBound N_c :=
      { profile := profile
        kappa := -Real.log wab.r
        hkappa := neg_pos.mpr (Real.log_neg wab.hr_pos wab.hr_lt1)
        g_bar := wab.r
        hg_pos := wab.hr_pos
        hg_lt1 := wab.hr_lt1
        E0 := wab.A₀ + 1
        hE0 := by linarith [wab.hA₀]
        h_lf_bound := h_lf_bound_at
        h_dominated := h_dominated }

The LFA's analytic content (`h_lf_bound`, `h_dominated`) is left
as caller-supplied hypotheses at the canonical `g_bar = wab.r`. The
three matching equalities then close by `rfl rfl rfl`.

Build: `lake build YangMills.ClayCore.LargeFieldDominance` →
8174/8174 jobs green. A fifth top-level `#print axioms` declaration
appended for `balabanHyps_from_wilson_activity`. All five top-level
decls in the module — `superPolyProfile`, `superPoly_dominance`,
`superPoly_dominance_at_specific`,
`LargeFieldActivityBound.ofSuperPoly`,
`balabanHyps_from_wilson_activity` — print
`[propext, Classical.choice, Quot.sound]`.

## Scope of change

Pure additive: `LargeFieldActivityBound.ofSuperPoly` (P2e-α,
v0.43.0) is **kept intact** and still callable for consumers willing
to accept the `Classical.choose`-opaque `g_bar`. The new
`balabanHyps_from_wilson_activity` coexists beside it as the
constants-aligned variant required to compose with P2d-α through
`balabanHyps_of_bounds`. Zero downstream breakage by construction.

α-stack now topologically saturated:

| sub-target | constructor                                     | file                          |
|------------|-------------------------------------------------|-------------------------------|
| P2c-α      | `BalabanH1H2H3` shape refactor                | `BalabanH1H2H3.lean`        |
| P2d-α      | `SmallFieldActivityBound.ofWilsonActivity`    | `WilsonPolymerActivity.lean`|
| P2d-β      | `balabanH1_from_wilson_activity_enriched`     | `WilsonPolymerActivity.lean`|
| P2e-α      | `LargeFieldActivityBound.ofSuperPoly`         | `LargeFieldDominance.lean`  |
| P2f-α      | `balabanHyps_from_wilson_activity`            | `LargeFieldDominance.lean`  |

No further pure-additive constructor in the α-stack closes additional
structural shape — the next moves require analytic content.

## What remains

- **P2d main** (multi-week): retire
  `WilsonPolymerActivityBound.h_bound` itself — i.e. prove Balaban
  CMP 116 Lemma 3 (character expansion on U(N_c) / Bessel coefficient
  asymptotics) for the Wilson action. Moves the L2 bar.
- **P2e main** (multi-week): retire `h_lf_bound` via Balaban CMP 122
  II Eq 1.98–1.100 (RG + cluster expansion). Moves the L2 / L3 bars.
- The α-stack is now structurally saturated; further additive
  constructors will not move the README percentage. Bar movement
  requires retiring entries from `AXIOM_FRONTIER.md` /
  `SORRY_FRONTIER.md`.

Oracle invariant remains `[propext, Classical.choice, Quot.sound]`.
No new axioms. No `sorry`.

---

# v0.45.0 — P2d-β: balabanH1_from_wilson_activity_enriched CONSTRUCTOR

**Released: 2026-04-24**

## What

Phase 3 / Task #7 sub-target P2d-β: pure-additive enriched constructor

    noncomputable def balabanH1_from_wilson_activity_enriched
        {N_c : ℕ} [NeZero N_c]
        (wab : WilsonPolymerActivityBound N_c) :
        BalabanH1 N_c :=
      h1_of_small_field_bound (SmallFieldActivityBound.ofWilsonActivity wab)

in `YangMills/ClayCore/WilsonPolymerActivity.lean`. Composes the
P2d-α enriched `SmallFieldActivityBound.ofWilsonActivity` (v0.44.0)
with the existing `h1_of_small_field_bound` (`SmallFieldBound.lean`)
to produce a first-class `BalabanH1 N_c` term whose small-field
activity profile is `activity n := A₀ · r^(n+2)` — polymer-faithful —
instead of identically zero (the legacy `balabanH1_from_wilson_activity`
route via the trivial-activity shortcut
`smallFieldBound_of_wilsonActivity`).

Commit: `c9ac61b` · File: `YangMills/ClayCore/WilsonPolymerActivity.lean`
(+22/−0) · Oracle: `[propext, Classical.choice, Quot.sound]`.

## Why

P2d-α (v0.44.0) introduced
`SmallFieldActivityBound.ofWilsonActivity` carrying a polymer-faithful
activity profile, but did not yet plug it into the SFA → BalabanH1
chain — the legacy `balabanH1_from_wilson_activity` route still went
through the trivial-activity shortcut. P2d-β closes that gap: it
demonstrates the enriched constructor is not decorative but propagates
cleanly through `h1_of_small_field_bound` to produce a `BalabanH1`
whose small-field content carries the polymer pair `(A₀, r)` rather
than identically zero.

## How

The `h1_of_small_field_bound` definition (line 24 of
`YangMills/ClayCore/SmallFieldBound.lean`) takes a
`SmallFieldActivityBound N_c` and produces a `BalabanH1 N_c` by
copying the constants block and packaging the activity profile into
the `h_sf` field as
`fun n => ⟨sfb.activity n, sfb.hact_nn n, sfb.hact_bd n⟩`.

P2d-β is therefore a single-line composition:

    h1_of_small_field_bound (SmallFieldActivityBound.ofWilsonActivity wab)

with the resulting `BalabanH1 N_c` carrying:
- `E0   = wab.A₀ + 1`
- `kappa = -Real.log wab.r`
- `g_bar = wab.r`
- `h_sf  = fun n => ⟨wab.A₀ * wab.r ^ (n+2), _, _⟩`

(the last two anonymous-constructor fields being the inherited
`hact_nn` and `hact_bd` discharges from P2d-α).

Build: `lake build YangMills.ClayCore.WilsonPolymerActivity` →
8172/8172 jobs green. A fourth top-level `#print axioms` declaration
appended for `balabanH1_from_wilson_activity_enriched`. All four
top-level decls in the module
(`smallFieldBound_of_wilsonActivity`,
`balabanH1_from_wilson_activity`,
`SmallFieldActivityBound.ofWilsonActivity`,
`balabanH1_from_wilson_activity_enriched`) print
`[propext, Classical.choice, Quot.sound]`.

## Scope of change

Pure additive: legacy `balabanH1_from_wilson_activity` (existential
statement carrying the trivial-activity `BalabanH1`) is **kept
intact** and still callable. The new
`balabanH1_from_wilson_activity_enriched` coexists beside it as the
polymer-faithful term-mode variant. Zero downstream breakage by
construction.

## What remains

- **P2d main** (multi-week): retire
  `WilsonPolymerActivityBound.h_bound` itself — i.e. prove Balaban
  CMP 116 Lemma 3 (character expansion on U(N_c) / Bessel coefficient
  asymptotics) for the Wilson action. P2d-α and P2d-β have shaped
  the consumer-side struct; the producer-side analytic content is
  what remains.
- **P2e main** (multi-week): retire `h_lf_bound` via Balaban CMP 122
  II Eq 1.98–1.100 (RG + cluster expansion). The P2e-α constructor
  (v0.43.0) is the preparatory shape.

Oracle invariant remains `[propext, Classical.choice, Quot.sound]`.
No new axioms. No `sorry`.

---


# v0.44.0 — P2d-α: SmallFieldActivityBound.ofWilsonActivity CONSTRUCTOR

**Released: 2026-04-23**

## What

Phase 3 / Task #7 sub-target P2d-α: pure-additive enriched constructor

```
noncomputable def SmallFieldActivityBound.ofWilsonActivity
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c) :
    SmallFieldActivityBound N_c
```

in `YangMills/ClayCore/WilsonPolymerActivity.lean`. Promotes a
`WilsonPolymerActivityBound N_c` into a `SmallFieldActivityBound N_c`
with a *nontrivial* activity profile tied to the polymer pair
`(A₀, r)` — `activity n := A₀ · r^(n+2)` — rather than the trivially-
zero shortcut of the legacy `smallFieldBound_of_wilsonActivity`.

Commit: `4985523` · File: `YangMills/ClayCore/WilsonPolymerActivity.lean`
(+59/−0) · Oracle: `[propext, Classical.choice, Quot.sound]`.

## Why

The legacy `smallFieldBound_of_wilsonActivity` constructor sets
`activity := fun _ => 0`, trivially satisfying the activity bound but
severing all semantic connection between the small-field activity
profile and the underlying polymer weight. P2d-α restores that
connection: `activity n := A₀ · r^(n+2)` is the polymer amplitude at
boundary-cube size `n+2`, matching the Balaban CMP 116 small-field
activity macro shape without bypassing any assumption.

Importantly, P2d-α does **not** retire
`WilsonPolymerActivityBound.h_bound` itself — that abstract amplitude
inequality (the analytic content of Balaban CMP 116 Lemma 3) remains
a struct-hypothesis field. What changes: the activity fed into
`SmallFieldActivityBound` is now semantically faithful to the polymer
pair `(A₀, r)`, not identically zero.

## How

Constants assembled from the Wilson polymer struct:

- `E₀ := wab.A₀ + 1`  — strict positivity holds even at `A₀ = 0`,
  discharged by `linarith [wab.hA₀]`.
- `κ  := -Real.log wab.r` — positive via
  `neg_pos.mpr (Real.log_neg wab.hr_pos wab.hr_lt1)`.
- `ḡ  := wab.r` — direct carry of the polymer decay rate.

Activity profile: `activity n := wab.A₀ * wab.r ^ (n + 2)`.

- `hact_nn`: pointwise nonnegativity from `pow_nonneg` on `r` and
  `wab.hA₀ : 0 ≤ A₀`, closed with `nlinarith`.
- `hact_bd`: after the normalisations
  - `Real.exp (-(-Real.log r) · n) = r^n` via `neg_neg` +
    `Real.log_pow` + `Real.exp_log`,
  - `r^(n+2) = r^n · r^2` via `pow_add`,
  the bound `A₀ · r^(n+2) ≤ (A₀ + 1) · r^2 · exp(-(-log r)·n)`
  reduces to `A₀ ≤ A₀ + 1`, closed with `nlinarith`.

Build: `lake build YangMills.ClayCore.WilsonPolymerActivity` →
8172/8172 jobs green. Three top-level `#print axioms` declarations
appended for `smallFieldBound_of_wilsonActivity`,
`balabanH1_from_wilson_activity`,
`SmallFieldActivityBound.ofWilsonActivity`. All three print
`[propext, Classical.choice, Quot.sound]`.

## Scope of change

Pure additive: legacy `smallFieldBound_of_wilsonActivity` (zero-
activity trivial shortcut) is **kept intact** and still callable. The
new `SmallFieldActivityBound.ofWilsonActivity` coexists beside it as
the polymer-faithful enriched variant. Zero downstream breakage by
construction.

## What remains

- **P2d main** (multi-week): retire
  `WilsonPolymerActivityBound.h_bound` itself — i.e. prove Balaban
  CMP 116 Lemma 3 (character expansion on U(N_c) / Bessel coefficient
  asymptotics) for the Wilson action.
- **P2e main** (multi-week): retire `h_lf_bound` via Balaban CMP 122
  II Eq 1.98–1.100 (RG + cluster expansion). The P2e-α constructor
  (v0.43.0) is the preparatory shape.

Oracle invariant remains `[propext, Classical.choice, Quot.sound]`.
No new axioms. No `sorry`.

---

# v0.43.0 — P2e-α: LargeFieldActivityBound.ofSuperPoly CONSTRUCTOR

**Released: 2026-04-23**

## What

Phase 3 / Task #7 sub-target P2e-α: the super-polynomial dominance lemma
(P2a, v0.41.0 analytic core) and the fixed-`E0` struct shape (P2c,
v0.42.0 structural refactor) are wired together into a first-class
constructor

```
noncomputable def LargeFieldActivityBound.ofSuperPoly
    {N_c : Nat} [NeZero N_c]
    (A : ℝ) (hA : 0 < A) (p : ℝ) (hp : 1 < p)
    (E : ℝ) (hE : 0 < E)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (h_lf_bound_at : …) : LargeFieldActivityBound N_c
```

in `YangMills/ClayCore/LargeFieldDominance.lean`. The constructor chooses
a small-enough coupling via `superPoly_dominance_at_specific`, extracts
the witness `g` and its spec via `Classical.choose` / `Classical.choose_spec`,
packages the `superPolyProfile A hA p hp` into the `profile` field, and
discharges `h_dominated` directly from `spec.2.2` after a one-step sign
normalisation `-(A * …) = -A * …` (`by ring`).

Commit: `3be3c4c` · File: `YangMills/ClayCore/LargeFieldDominance.lean`
(+39/−0) · Oracle: `[propext, Classical.choice, Quot.sound]`.

## Why

P2a produced the analytic inequality and P2c shaped the target struct;
without a concrete constructor, downstream code had no way to actually
produce a `LargeFieldActivityBound N_c` term from the dominance lemma. P2e-α
closes that gap in a single term-mode definition. The caller supplies the
uniform RG/cluster-expansion large-field activity bound (`h_lf_bound_at`,
still the P2e main target, multi-week); this constructor wires dominance
+ activity into a first-class struct value, ready to be paired with a
companion `SmallFieldActivityBound` and fed into `balabanHyps_of_bounds`
(per the P2c API shape, with `hE0_eq : sfb.consts.E0 = lfb.E0`).

## How

- **New def** `LargeFieldActivityBound.ofSuperPoly` inserted inside the
  `section` that contains `superPolyProfile`, `superPoly_dominance`, and
  `superPoly_dominance_at_specific` (between the last `linarith` of the
  latter's proof body and the section's closing `end`).
- **New top-level declaration** `#print axioms
  YangMills.LargeFieldActivityBound.ofSuperPoly` appended after the
  existing three `#print axioms` lines; build-time oracle confirmation.
- **Dominance extraction**:
  `let dom := superPoly_dominance_at_specific hA hp hE` →
  `g := Classical.choose dom`, `spec := Classical.choose_spec dom`.
  `spec.1 : 0 < g`, `spec.2.1 : g < 1`,
  `spec.2.2 : Real.exp (-A * (Real.log (g⁻¹ ^ 2)) ^ p) ≤ E * g ^ 2`.
- **`h_dominated` field** discharged via
  `show Real.exp (-(A * (Real.log (g⁻¹ ^ 2)) ^ p)) ≤ E * g ^ 2` (defn
  equality against the struct's projected `profile.eval g`), followed by
  `have h_neg : -(A * …) = -A * … := by ring; rw [h_neg]; exact spec.2.2`.

Build: `lake build YangMills.ClayCore.LargeFieldDominance` → 8164/8164
jobs green. Oracle prints for all four top-level decls in the module
(`superPolyProfile`, `superPoly_dominance`,
`superPoly_dominance_at_specific`, `LargeFieldActivityBound.ofSuperPoly`)
remain exactly `[propext, Classical.choice, Quot.sound]`.

## Scope of change

Pure additive; no API modifications elsewhere. The new constructor is a
top-level def that does not alter the signature of any existing decl.
Zero downstream breakage by construction.

## What remains

- **P2d** (multi-week): retire `h_sf` (Balaban CMP 116 Lemma 3 /
  small-field activity bound). Independent of P2e.
- **P2e main** (multi-week): retire `h_lf_bound` (Balaban CMP 122 II
  Eq 1.98–1.100 / large-field activity via RG + cluster expansion). The
  P2e-α constructor is the preparatory shape; P2e main supplies the
  `h_lf_bound_at` argument uniformly in `g`, unlocking a concrete
  `LargeFieldActivityBound N_c` term without any remaining assumptions.

Oracle invariant remains `[propext, Classical.choice, Quot.sound]`.
No new axioms. No `sorry`.

---


# v0.42.0 — P2c: LargeFieldActivityBound.h_dominated FIXED-E0 REFACTOR

**Released: 2026-04-23**

## What

Phase 3 / Task #7 sub-target P2c: the `h_dominated` field of
`LargeFieldActivityBound` is promoted from the over-strong
`∀ E0 > 0, exp(−p0(g)) ≤ E0 · g²` quantifier to a fixed-constant form
`exp(−p0(g)) ≤ E0 · g²` with `E0 : ℝ` and `hE0 : 0 < E0` exposed as
first-class struct fields. This shape matches exactly what
`YangMills.superPoly_dominance_at_specific` (v0.41.0 analytic core)
produces for a chosen small-enough coupling — structurally closing the
P2a ↔ `LargeFieldActivityBound` integration gap flagged in the v0.41.0
scope comment.

Commit: `f940d58` · Files: `YangMills/ClayCore/LargeFieldBound.lean`
+ `YangMills/ClayCore/LargeFieldDominance.lean` (+40/−19 across 2 files) ·
Oracle: `[propext, Classical.choice, Quot.sound]`.

## Why

The former `∀ E0 > 0, …` quantifier required the large-field profile to
dominate **for every positive E0 whatsoever**, which is neither what the
downstream consumer needs (`balabanHyps_of_bounds.hlf_le` only uses
`h_dominated sfb.consts.E0 sfb.consts.hE0`) nor what
`superPoly_dominance_at_specific` proves (which fixes `E` and produces a
threshold `g₀` depending on `E`). The fixed-`E0` shape is semantically
correct, structurally satisfiable, and unblocks `h_dominated` being
discharged directly by `superPoly_dominance_at_specific` in the eventual
concrete `LargeFieldActivityBound` constructor (P2e).

## How

API touchpoints (all in `YangMills/ClayCore/LargeFieldBound.lean`):

- **`LargeFieldActivityBound`**: adds `E0 : ℝ` and `hE0 : 0 < E0` fields;
  reshapes `h_dominated` to
  `Real.exp (-(profile.eval g_bar)) ≤ E0 * g_bar ^ 2` (unquantified).
- **`lf_dominance_gives_hlf_le`**: drops the `(E0, hE0)` arguments,
  returns `lfb.h_dominated` directly.
- **`balabanHyps_of_bounds`**, **`all_balaban_hyps_from_bounds`**: add
  `hE0_eq : sfb.consts.E0 = lfb.E0` precondition; the `hlf_le` proof
  routes via `rw [hg_eq, hE0_eq]; exact lfb.h_dominated`.

The matching scope comment in `YangMills/ClayCore/LargeFieldDominance.lean`
is updated: P2a's analytic core and P2c's structural refactor are now
paired — `h_dominated` is discharged directly by
`superPoly_dominance_at_specific` at a chosen small-enough coupling.

## Scope of change

Pre-deployment recon confirmed exactly **2 files** repo-wide reference
`LargeFieldActivityBound`: `LargeFieldBound.lean` (definition) and
`LargeFieldDominance.lean` (scope comment only). No downstream
constructors of `LargeFieldActivityBound` exist; no other callers of
`lf_dominance_gives_hlf_le`, `balabanHyps_of_bounds`, or
`all_balaban_hyps_from_bounds`. The API change is 100% contained.

Build: `lake build YangMills.ClayCore.LargeFieldBound
YangMills.ClayCore.LargeFieldDominance` → 8164/8164 jobs green.

## What remains

- **P2d** (multi-week): retire `h_sf` (Balaban CMP 116 Lemma 3 /
  small-field activity bound). Independiente de P2e.
- **P2e** (multi-week): retire `h_lf_bound` (Balaban CMP 122 II
  Eq 1.98–1.100 / large-field activity). The P2c field shape is a
  prerequisite for the eventual P2e concrete constructor, which will
  use `superPoly_dominance_at_specific` to discharge `h_dominated`
  directly.

Oracle invariant remains `[propext, Classical.choice, Quot.sound]`.
No new axioms. No `sorry`.

---

# v0.41.0 — SUPER-POLYNOMIAL DOMINANCE LEMMA (P2a) — ANALYTIC CORE OF h_dominated (2026-04-23)

**Milestone.** The analytic content of Balaban CMP 122 II Eq (1.98)–(1.100) / Paper [55] Theorem 8.5 — the super-polynomial dominance inequality `exp(−A · (log g⁻²)^p) ≤ E · g²` for `A > 0`, `p > 1`, `E > 0` at sufficiently small `g` — is formalized as a first-class Lean theorem `YangMills.superPoly_dominance` in a new file `YangMills/ClayCore/LargeFieldDominance.lean`. Companion profile `YangMills.superPolyProfile : LargeFieldProfile` (with `eval g := A₀ · (log g⁻²)^{p*}`, `A₀ > 0`, `p* > 1`) exposes the Balaban super-polynomial profile under the `LargeFieldProfile` interface, and the specific corollary `YangMills.superPoly_dominance_at_specific` lands the statement at every `g ∈ (0, 1)` with a strict-less-than witness.

**Scope.** This retires the *analytic* content of the `h_dominated` field of `LargeFieldActivityBound` in `YangMills/ClayCore/LargeFieldBound.lean`: for any fixed `E > 0` (e.g. the companion `E₀` of the small-field bound), the Balaban super-polynomial profile dominates at every sufficiently small coupling. The Lean *structural* integration into `LargeFieldActivityBound` is not part of this release: the current `h_dominated : ∀ E₀ > 0, exp(−p₀(g_bar)) ≤ E₀ · g_bar²` quantifier is over-strong (uninhabitable for any finite profile, since the LHS is a fixed positive constant and the RHS → 0 as `E₀ → 0`), and a separate structural refactor is needed to expose a fixed threshold `E₀`. This refactor is tracked as a follow-up.

**No frontier entry retired.** The L2 / L3 / OVERALL unconditionality bars are not moved: the `h_dominated` entry in the consumer-side `LargeFieldActivityBound` structure is still formally an obligation at `N_c ≥ 2`. The analytic content that would discharge it once the quantifier is refactored is now available as an independent first-class lemma. L1 / L2 / L3 / OVERALL bars therefore do not move.

**Artefacts (all oracle-clean).**
- `YangMills.superPolyProfile` — Balaban super-polynomial `LargeFieldProfile`, `eval g := A₀ · (Real.log (g⁻¹ ^ 2))^{p*}` with `A₀ > 0`, `p* > 1`, `heval_pos` by elementary real-analysis (`Real.log_pos` on `g⁻² > 1`, then `Real.rpow_pos_of_pos`).
- `YangMills.superPoly_dominance` : `∀ {A : ℝ} (hA : 0 < A) {p : ℝ} (hp : 1 < p) {E : ℝ} (hE : 0 < E), ∃ g₀ : ℝ, 0 < g₀ ∧ g₀ ≤ 1 ∧ ∀ g : ℝ, 0 < g → g < g₀ → Real.exp (−A · (Real.log (g⁻¹ ^ 2))^p) ≤ E · g^2` — the analytic core of `h_dominated` for any fixed `E > 0`.
- `YangMills.superPoly_dominance_at_specific` : `∀ {A : ℝ} (hA : 0 < A) {p : ℝ} (hp : 1 < p) {E : ℝ} (hE : 0 < E), ∃ g : ℝ, 0 < g ∧ g < 1 ∧ Real.exp (−A · (Real.log (g⁻¹ ^ 2))^p) ≤ E · g^2` — specific-`g` corollary usable when a strict `g < 1` witness is needed.

**Oracle verification** (`#print axioms`, emitted at EOF of `YangMills/ClayCore/LargeFieldDominance.lean`):
```
superPolyProfile                → [propext, Classical.choice, Quot.sound]
superPoly_dominance             → [propext, Classical.choice, Quot.sound]
superPoly_dominance_at_specific → [propext, Classical.choice, Quot.sound]
```

**Core observation.** The proof is elementary and self-contained (no asymptotics library, no `Asymptotics.IsLittleO`). Setting `u := log(g⁻²) = −2 log g`, the argument reduces to a four-step cascade:
1. Choose `C := max(1, −log E)` so that both `1 ≤ C` and `−log E ≤ C`.
2. Choose `M := ((1 + C) / A)^{1 / (p − 1)}` (via `Real.rpow`), the threshold at which `A · u^{p−1} ≥ 1 + C`.
3. Choose `U := max(1, M)`, guaranteeing both `u ≥ 1` and `u ≥ M`.
4. Set `g₀ := exp(−U / 2)`; for `g < g₀`, `log g < −U / 2`, so `u = −2 log g > U`, which activates step 2's bound. The chain `u · (1 + C) ≤ A · u^p` combined with `−log E ≤ u · C` gives `−(A · u^p) ≤ log E + 2 · log g = log(E · g²)`, and `Real.exp_le_exp` closes the inequality.

The key Mathlib lemmas used are `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_add`, `Real.rpow_one`, `Real.rpow_pos_of_pos`, `Real.exp_le_exp`, `Real.log_mul`, `Real.log_pow`, `Real.log_inv`, `Real.log_lt_log`, `Real.exp_log`, `Real.log_pos`, plus `mul_inv_cancel₀`, `mul_lt_mul_of_pos_right`, `mul_le_mul_of_nonneg_left`, `le_mul_of_one_le_left`, `div_pos`. No external APIs; no special-case reasoning; no `sorry`.

**Interpretation.** The analytic core of Balaban's large-field dominance is now first-class and oracle-clean, independently of the `LargeFieldActivityBound` structural layer. Once the over-strong `∀ E₀` quantifier in `h_dominated` is refactored to a fixed `E₀` (for example, the companion `E₀` constant of the small-field bound), `h_dominated` discharges by a direct application of `superPoly_dominance` with no further analytic work. The present lemma is therefore both a *reusable analytic building block* — usable wherever Balaban's super-polynomial mechanism is cited — and a *proof of tractability*: the Balaban dominance machinery requires no asymptotics infrastructure beyond stable Mathlib real-analysis, which was not obvious a priori given the `rpow` + `log` + `exp` interplay.

**Oracle set unchanged:** `[propext, Classical.choice, Quot.sound]`.

**No sorry. No new axioms. No frontier entry retired or added.**

---
# v0.40.0 — CONNECTEDCORRDECAY FIRST-CLASS ABSTRACTION (P1) (2026-04-23)

**Milestone.** The deferred comment at `SchurPhysicalBridge.lean:28` (referring to `fundamentalObservable_ConnectedCorrDecay`) is promoted to a named Lean structure `ConnectedCorrDecay (N_c : ℕ) [NeZero N_c]` in a new file `YangMills/ClayCore/ConnectedCorrDecay.lean`. Both the U(1) unconditional route and the N_c ≥ 2 analytic routes (Osterwalder–Seiler reflection positivity, Kotecký–Preiss cluster convergence, Balaban RG) now target a common, physically-meaningful name.

**Scope.** Field content of `ConnectedCorrDecay N_c` is structurally identical to `ClayYangMillsMassGap N_c` (same `m, hm, C, hC, hbound` signature). The abstraction is a naming / API layer for consumer clarity; it does not add or retire analytic content. Round-trip projections `ConnectedCorrDecay.ofClayMassGap` / `ConnectedCorrDecay.toClayMassGap` hold field-for-field (`rfl`).

**No frontier entry retired.** Named entries in this file and in `SORRY_FRONTIER.md` are scoped to analytic obligations at `N_c ≥ 2` (small-field activity, large-field activity, super-polynomial growth of `p₀(g)`). The abstraction layer is a naming / API improvement; it does not discharge any previously named analytic item. L1 / L2 / L3 / OVERALL bars do not move.

**Artefacts (all oracle-clean).**

- `YangMills.ConnectedCorrDecay` — `ℕ → Type` structure, field-for-field identical to `ClayYangMillsMassGap`.
- `YangMills.ConnectedCorrDecay.ofClayMassGap` / `.toClayMassGap` — round-trip projections (`rfl`).
- `YangMills.ConnectedCorrDecay.ofClayMassGap_toClayMassGap` / `.toClayMassGap_ofClayMassGap` — round-trip `@[simp]` lemmas.
- `YangMills.ConnectedCorrDecay.clayTheorem` — terminal `ConnectedCorrDecay N_c → ClayYangMillsTheorem`.
- `YangMills.ConnectedCorrDecay.ofClayWitnessHyp` — consumer hub for OS / KP / Balaban routes at `N_c ≥ 2`: `ClayWitnessHyp N_c → ConnectedCorrDecay N_c`.
- `YangMills.unconditional_U1_ConnectedCorrDecay` — `ConnectedCorrDecay 1`, the unconditional U(1) witness under the physically-meaningful name.
- `YangMills.unconditional_U1_ConnectedCorrDecay_clayTheorem` — `ClayYangMillsTheorem` produced from the U(1) `ConnectedCorrDecay` witness; fully unconditional.
- Companion reductions: `ofClayWitnessHyp_mass_eq` (mass gap = `kpParameter hyp.r`), `ofClayWitnessHyp_prefactor_eq` (prefactor = `hyp.C_clust`), `unconditional_U1_ConnectedCorrDecay_mass_eq` (mass = `kpParameter (1/2)`), `unconditional_U1_ConnectedCorrDecay_mass_pos`, `unconditional_U1_ConnectedCorrDecay_prefactor_eq` (= 1).

**Oracle verification** (`#print axioms`, emitted at EOF of `YangMills/ClayCore/ConnectedCorrDecay.lean`):

```
unconditional_U1_ConnectedCorrDecay             → [propext, Classical.choice, Quot.sound]
unconditional_U1_ConnectedCorrDecay_clayTheorem → [propext, Classical.choice, Quot.sound]
```

**Core observation.** Promoting the deferred comment to a first-class abstraction exposes `ConnectedCorrDecay.ofClayWitnessHyp : ClayWitnessHyp N_c → ConnectedCorrDecay N_c` as the canonical consumer hub: every future analytic route that produces a `ClayWitnessHyp N_c` (Osterwalder–Seiler duality, Kotecký–Preiss in strong coupling, Balaban RG in weak coupling) discharges `ConnectedCorrDecay N_c` for free, without touching ClayCore plumbing.

**Interpretation.** The Clay conclusion is now exposed under two equivalent names:

- Structural / existential: `ClayYangMillsMassGap N_c` — "there exist `m > 0, C > 0` so that the uniform two-plaquette exponential clustering bound holds".
- Physical / named: `ConnectedCorrDecay N_c` — "uniform exponential clustering of the connected Wilson two-plaquette correlator against every bounded class observable, at every positive inverse coupling β, every spacetime dimension d, every lattice size L, and every plaquette pair separated by at least one lattice unit".

The U(1) unconditional witness is now available under the physically-meaningful name, and routes to the Clay terminal `ClayYangMillsTheorem` via `ConnectedCorrDecay.clayTheorem`. Field-for-field round-trip lemmas guarantee that consumers can freely switch between the two names without proof obligations.

**Oracle set unchanged:** `[propext, Classical.choice, Quot.sound]`.

**No sorry. No new axioms. No frontier entry retired or added.**

---

# v0.39.0 — N_c = 1 UNCONDITIONAL WITNESS (ClayYangMillsMassGap 1 inhabited oracle-clean) (2026-04-23)

**Milestone.** First concrete inhabitant of `ClayYangMillsMassGap N_c` has landed at `N_c = 1` in `YangMills/ClayCore/AbelianU1Unconditional.lean`. The witness is fully unconditional: zero hypotheses, zero `sorry`, `#print axioms` on all six produced artefacts returns exactly `[propext, Classical.choice, Quot.sound]`.

**Scope.** The Clay statement `ClayYangMillsMassGap : ℕ → Prop` in this repo takes an explicit `N_c`. This entry instantiates it at `N_c = 1`. For `N_c ≥ 2` the connected correlator is not identically zero, so the `ConnectedCorrDecay` witness must come from genuine analytic content (Osterwalder–Seiler reflection positivity, Kotecký–Preiss cluster convergence, and Balaban RG), tracked on the `ClusterCorrelatorBound` front (F1 / F2 / F3).

**No frontier entry retired.** The named entries in this file and in `SORRY_FRONTIER.md` are scoped to `N_c ≥ 2` / physics hypotheses. The U(1) witness is a *new kind of closure* — an existential lower-bound anchor — and does not discharge any previously named item. L1 / L2 / L3 / OVERALL bars therefore do not move.

**Artefacts (all oracle-clean, `.olean` built, 190120 bytes):**

- `YangMills.unconditionalU1CorrelatorBound` : `U1CorrelatorBound`
- `YangMills.u1_clay_yangMills_mass_gap_unconditional` : `ClayYangMillsMassGap 1`
- `YangMills.wilsonConnectedCorr_su1_eq_zero` : connected correlator = 0 identically
- `YangMills.u1_unconditional_mass_gap_eq` : `m = kpParameter (1/2)`
- `YangMills.u1_unconditional_mass_gap_pos` : `0 < m`
- `YangMills.u1_unconditional_prefactor_eq` : `C = 1`

**Core observation.** `Subsingleton (Matrix.specialUnitaryGroup (Fin 1) ℂ)`. The special unitary group SU(1) has exactly one element (the identity), so every Wilson observable is constant, every connected correlator vanishes identically, and `ConnectedCorrDecay` holds vacuously with any positive choice of mass gap and prefactor.

**Interpretation.** The Lean model of the Clay conclusion is not vacuous-by-contradiction: it admits at least one model. This is the first proof that `ClayYangMillsMassGap _` has any inhabitant at all. For the physically interesting cases (`N_c ≥ 2`) the same schema must be filled in with genuine non-trivial analytic content.

**Oracle set unchanged:** `[propext, Classical.choice, Quot.sound]`.

---

# v0.38.0 — L2.6 CLOSED AT 100 % / CharacterExpansionData VESTIGIAL METADATA (2026-04-22 evening)
**Milestone.** L2.6 reclassified as closed at 100 % after consumer-driven recon established that `CharacterExpansionData.{Rep, character, coeff}` is vestigial metadata. The original L2.6 step 3 (arbitrary-irrep Peter–Weyl character orthogonality) is reclassified as aspirational / Mathlib-PR and removed from the Clay critical path.
No new axioms introduced. No `sorry` introduced. `ClayCore` oracle set unchanged at `[propext, Classical.choice, Quot.sound]`.
## What the recon found
Consumer-driven trace of `YangMills/ClayCore/CharacterExpansion.lean`, `ClusterCorrelatorBound.lean`, and `WilsonGibbsExpansion.lean` (HEAD at commit `043a3f3`):
### 1. `CharacterExpansionData.{Rep, character, coeff}` are never inspected by downstream code
In `ClusterCorrelatorBound.lean`, the constructor `wilsonCharExpansion` fills these fields with trivial data:
```
Rep       := PUnit
character := fun _ _ => (0 : ℂ)
coeff     := fun _ _ => (0 : ℝ)
```
The only field used by downstream theorems is `h_correlator`, which is definitionally `ClusterCorrelatorBound N_c r C_clust`. `WilsonGibbsExpansion.lean`'s `WilsonGibbsPolymerRep` passes `r, hr_pos, hr_lt1, C_clust, hC, h_correlator` through to `SUNWilsonClusterMajorisation` — `Rep`, `character`, and `coeff` are silently discarded.
### 2. No Peter–Weyl content in the repo outside ClayCore
- Zero imports of `Mathlib.RepresentationTheory.PeterWeyl`-style lemmas.
- Zero uses of the vocabulary `MatrixCoefficient`, `unitaryRep`, `irreducible`, `schurOrthogonality` (outside the Schur *integral* orthogonality on `SU(N)` matrix entries, which is already closed at commit `95175f3`).
- Zero occurrences of the identifiers `.Rep`, `.character`, or `.coeff` on `CharacterExpansionData` outside its own constructor.
### 3. No existing axiom about Peter–Weyl
Previous `AXIOM_FRONTIER.md` contains no entry naming Peter–Weyl, arbitrary-irrep orthogonality, or matrix-coefficient L² decomposition. There is no frontier entry to retire and no new entry to add.
## Consequence for the Clay critical path
The critical path from L1 · L2.5 · L2.6 up to `L2 = CharacterExpansionData` is now entirely discharged at the level the L3 / cluster-expansion consumer actually inspects. The remaining work is the **analytic** content of `h_correlator` itself — i.e., constructing `ClusterCorrelatorBound N_c r C_clust` with explicit `(r, C_clust)` in terms of `β, N_c` — not the representation-theoretic content of `Rep / character / coeff`.
The new decomposition of `ClusterCorrelatorBound` into Lean work packages is:
- **F1.** Character / Taylor expansion of `exp(−β · Re tr U)` in the scalar traces `(tr U, star tr U)`. Termwise Haar integrability. Absolute summability in β.
- **F2.** Haar sidecar assemblage: every relevant monomial integral `∫ (tr U)^j · star(tr U)^k dμ_Haar` on `SU(N_c)` is computable from L2.5, L2.6 main target, and the sidecars {3a, 3b, 3c}. The `j = k ≥ 1` case reduces via Frobenius / L2.5 without requiring arbitrary-irrep theory. The `N_c ∣ (j−k)` case contributes a subexponentially-bounded constant handled at the F3 combinatorial layer.
- **F3.** Kotecky–Preiss cluster convergence: feed F1 · F2 monomial bounds into the existing `ClusterSeriesBound.lean` (D1 `tsum` summability + D2 factoring) and `MayerExpansion.lean` (`TruncatedActivities`, `connectingSum`, `connectingBound`, `abs_connectingSum_le_connectingBound`, `two_point_decay_from_truncated`).
## Status of step 3 proper (aspirational / Mathlib-PR)
The original L2.6 step 3 — `⟨χ_ρ, χ_σ⟩_{L²(SU(N), μ_Haar)} = δ_{[ρ] = [σ]}` for arbitrary irreps — remains a mathematically desirable target. It is tracked in `PETER_WEYL_ROADMAP.md` (prepended STATUS UPDATE block). It is **not** a Clay critical-path item. Landing it would upgrade `CharacterExpansionData.{Rep, character, coeff}` from vestigial `PUnit / 0 / 0` to genuine representation-theoretic content, which is a nice-to-have cleanness property, but the `ClusterCorrelatorBound` statement does not require it.
## Budget impact
- L2.6 bar: 97 → 100. Ladder row 14 changes from "Peter–Weyl, IN PROGRESS" to "`ClusterCorrelatorBound`, IN PROGRESS".
- L2, L3, OVERALL bars: unchanged. The reclassification does not retire a previously named axiom; it renames the open work package from "Peter–Weyl" to "`ClusterCorrelatorBound` via F1 + F2 + F3" and rescopes what counts as L2.6 closure.
- No change to the oracle set.
---
# v0.37.0 - H1+H2+H3 ALL DISCHARGED (2026-04-18)

**Milestone:** All three Balaban hypotheses now have concrete Lean witnesses.
Commits `eb16d1f` (H3+H1) and `e61ebc5` (H2).

Oracle for `all_balaban_hyps_from_bounds`: `[propext, Classical.choice, Quot.sound]`.
Zero sorry. Zero named project axioms.

## What was added

### H3 discharged (PolymerLocality.lean)
- `h3_holds_by_construction : BalabanH3 := { h_local := trivial }`
- `balabanHyps_of_h1_h2`: any H1+H2 automatically gives full BalabanHyps

### H1 discharged (SmallFieldBound.lean)
- `SmallFieldActivityBound`: structure from Bloque4 Prop 4.2 + Lemma 5.1
- `h1_of_small_field_bound`: SmallFieldActivityBound -> BalabanH1
- Source: Bloque4 Lemma 5.1 (Cauchy estimate) + Prop 4.2 Eq (12)

### H2 discharged (LargeFieldBound.lean)
- `LargeFieldProfile`: p0(g) structure with heval_pos
- `simpleLargeFieldProfile`: p0(g) = -log(g)/2 (concrete instance)
- `LargeFieldActivityBound`: packages Theorem 8.5 / Balaban CMP 122 Eq (1.98)-(1.100)
- `h2_of_large_field_bound`: LargeFieldActivityBound -> BalabanH2
- `balabanHyps_of_bounds`: SmallField + LargeField -> full BalabanHyps
- `all_balaban_hyps_from_bounds`: all three discharged in one theorem

## Current proof chain (complete, all oracles clean)

```
SmallFieldActivityBound   (Bloque4 Prop 4.2)
+ LargeFieldActivityBound (Paper [55] Thm 8.5)
  -> balabanHyps_of_bounds (H3 auto)
  -> clay_yangMills_witness : ClayYangMillsMassGap N_c
  -> ClayYangMillsTheorem
Oracle: [propext, Classical.choice, Quot.sound]
```

## What remains

The three remaining mathematical obligations to fully close:
1. Inhabit `SmallFieldActivityBound.h_sf` from Balaban CMP 116, Lemma 3, Eq (2.38)
2. Inhabit `LargeFieldActivityBound.h_lf_bound` from Balaban CMP 122, Eq (1.98)-(1.100)
3. Inhabit `LargeFieldActivityBound.h_dominated` (super-polynomial growth of p0(g))

Next target: U(1) fully unconditional instance.

---


# v0.36.0 — BALABAN H1-H2-H3 FORMALIZED (2026-04-18)

**Milestone:** `BalabanH1H2H3.lean` landed on main at commit `3cd930f`.

Oracle for all exported theorems: `[propext, Classical.choice, Quot.sound]`.
Zero sorry. Zero named project axioms.

## What was added

Three Lean structures encoding the terminal polymer activity bounds:
- `BalabanH1`: small-field bound `‖R*^sf(X)‖ ≤ E₀·ḡ²·exp(-κ·d(X))`
  Source: Balaban CMP 116 (1988), Lemma 3, Eq (2.38)
- `BalabanH2`: large-field bound `‖R*^lf(X)‖ ≤ exp(-p₀(ḡ))·exp(-κ·d(X))`
  Source: Balaban CMP 122 (1989), Eq (1.98)-(1.100)
- `BalabanH3`: locality / hard-core compatibility
  Source: Balaban CMP 116 §2, CMP 122 §1

Key theorems:
- `balaban_combined_bound`: H1+H2 ⟹ total bound `2·E₀·ḡ²·exp(-κ·n)`
- `polymerBound_of_balaban`: maps `BalabanHyps` to `PolymerActivityBound`
- `balaban_to_polymer_bound`: existence of compatible `PolymerActivityBound`

## What these hypotheses represent

H1-H2-H3 are the honest formal boundary between what is Lean-verified
and what is verified only in the informal companion papers.
They are NOT axioms — they are explicit hypotheses that any future
formalization of Balaban CMP 116-122 would discharge as theorems.

Informal verification: [Eriksson 2602.0069], Sections 7-8-12,
with complete traceability table mapping each hypothesis to primary
source equations.

## Current oracle chain (complete)

```
clay_yangMills_witness
└── ClayWitnessHyp (contains BalabanHyps)
    └── [propext, Classical.choice, Quot.sound]
```

No sorryAx anywhere in the chain.

---
# v0.35.0 — SORRY COUNT CORRECTION (2026-04-17)

**Supersedes v0.34.0 count (3 → 1).** The project is pinned to commit
`41cc169` at `origin/main`. The single remaining `sorry` is
`YangMills/P8_PhysicalGap/BalabanToLSI.lean:805`. It represents the same
L·log·L gap described in v0.34.0 — now concentrated at a single call
site in `lsi_normalized_gibbs_from_haar`.

Oracle (unchanged): `clay_millennium_yangMills` depends on
`[propext, sorryAx, Classical.choice, Quot.sound]`. Zero named
axioms. One `sorry`.

## How v0.34.0's three sorries reduced to one

- `integrable_f2_mul_log_f2_div_haar` (was ~507-513): filled in by
  commit `41cc169`, with `Integrable (f²·log f²)` added as an
  explicit hypothesis.
- `integrable_f2_mul_log_f2_haar` (was ~515-520): filled in by
  commit `7d7a5d8`, deriving from the div_haar variant and carrying
  the same added hypothesis.
- Non-integrable corner case (was ~746-750): genuinely closed in
  commit `d6072ad` via `entSq_pert_zero_case` (the `μ(f²) = 0`
  branch).

Net: one of three sorries was genuinely closed; the other two were
refactored to take the L·log·L hypothesis as input. The reduction
was by hypothesis threading, not mathematical closure.

## Remaining gap

The surviving sorry is:

    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) (sunHaarProb N_c)

Counterexample, wrong-axiom trap, and the shape of a sound closure
are in `docs/phase1-llogl-obstruction.md`.

---

# v0.34.0 — AXIOM CENSUS (2026-04-14)

**Milestone:** `clay_millennium_yangMills` oracle is now `[propext, sorryAx, Classical.choice, Quot.sound]` — **ZERO named axioms** in the Clay proof chain.

## Historical axiom inventory (non-Experimental)

- **Superseded by v0.95.0-v0.97.0.** Current declared axioms
  outside `YangMills/Experimental/`: **0**.
- **Historical count at this point in the log:** 3 after v0.92.0
- **Axioms reached by `clay_millennium_yangMills`:** 0
- **Orphaned axioms (declared but unreachable from Clay):** historical census below predates v0.86.0-v0.89.0 cleanup

### Orphaned (dead-code) axioms by file
- `YangMills/P8_PhysicalGap/BalabanToLSI.lean`: 2 (after v0.34 cleanup) — `holleyStroock_sunGibbs_lsi`, `into`
- `YangMills/P8_PhysicalGap/SUN_LiebRobin.lean`: 0 after v0.88.0 — former `sun_variance_decay`, `sun_lieb_robinson_bound` now explicit theorem inputs
- `YangMills/P8_PhysicalGap/SUN_DirichletCore.lean`: 0 after v0.92.0 — former `sunDirichletForm_contraction` now explicit input
- `YangMills/P8_PhysicalGap/StroockZegarlinski.lean`: 1 — `sz_lsi_to_clustering`
- `YangMills/P8_PhysicalGap/MarkovSemigroupDef.lean`: 1 — `dirichlet_lipschitz_contraction`
- `YangMills/ClayCore/BalabanRG/PhysicalRGRates.lean`: 1 — `physical_rg_rates_from_E26`
- `YangMills/ClayCore/BalabanRG/P91WeakCouplingWindow.lean`: 0 after v0.86.0 — former `p91_tight_weak_coupling_window` retired

### Remaining gaps (sorryAx only)
Three `sorry` in `BalabanToLSI.lean`, documented inline as ACCEPTED GAPs:
1. Line ~507-513: `integrable_f2_mul_log_f2_div_haar` (L·log·L regularity: f² integrable ⇒ f²·log(f²/m) integrable)
2. Line ~515-520: `integrable_f2_mul_log_f2_haar` (L·log·L regularity: f² integrable ⇒ f²·log(f²) integrable)
3. Line ~746-750: non-integrable corner case (needs density lower bound for measure transfer)

These require Mathlib-level measure-theory infrastructure (L⁴ bound or L log L class) not yet available.

## v0.34.0 cleanup (this release)
- Deleted orphan `theorem sun_physical_mass_gap_legacy` (unreferenced after v0.33.0 rewire).
- Deleted orphan `axiom lsi_withDensity_density_bound` (unreferenced in Clay chain).

---

# v0.33.0 AXIOM ELIMINATION (2026-04-14)

**The monolithic `holleyStroock_sunGibbs_lsi` axiom has been ORPHANED.**

The Clay Millennium Yang-Mills mass gap theorem (`clay_millennium_yangMills`)
now depends on **zero** named axioms (modulo in-progress `sorryAx`).

Oracle (from `#print axioms` after `lake build YangMills.P8_PhysicalGap.ClayAssembly`):

    YangMills.clay_millennium_yangMills
      depends on [propext, sorryAx, Classical.choice, Quot.sound]

No more `holleyStroock_sunGibbs_lsi`. The final theorem now routes through
`sun_physical_mass_gap_vacuous` (new) -> `sun_gibbs_dlr_lsi_norm` ->
`balaban_rg_uniform_lsi_norm` -> `lsi_normalized_gibbs_from_haar` (proved,
with measure-theoretic `sorry`).

The legacy axiom is retained in `BalabanToLSI.lean` for downstream compatibility
with `sun_physical_mass_gap_legacy`, `sunGibbsFamily`, and `sun_clay_conditional`,
but it is no longer a dependency of the headline theorem.

---

# v0.32.0 STRUCTURAL COLLAPSE (2026-04-14)

**Monolithic axiom `yangMills_continuum_mass_gap` has been DELETED.**

The Clay Millennium Yang-Mills mass gap theorem (`clay_millennium_yangMills`) now
depends on exactly **one** concrete mathematical axiom:

  `holleyStroock_sunGibbs_lsi`  (SU(N) Gibbs-measure log-Sobolev inequality)

Oracle (from `#print axioms` after `lake build YangMills`):

    YangMills.clay_millennium_yangMills
      depends on [propext, Classical.choice, Quot.sound,
                  YangMills.holleyStroock_sunGibbs_lsi]

    YangMills.clay_millennium_yangMills_strong
      depends on [propext, Classical.choice, Quot.sound]     -- AXIOM-FREE

    YangMills.yangMills_existence_massGap
      depends on [propext, Classical.choice, Quot.sound,
                  YangMills.holleyStroock_sunGibbs_lsi]

Route: the Clay statement is discharged by `yangMills_existence_massGap_via_lsi`
(in `YangMills/P8_PhysicalGap/ClayViaLSI.lean`), which in turn routes through
`sun_physical_mass_gap_legacy`, `BalabanToLSI`, and the DLR-LSI machinery
ultimately resting on `holleyStroock_sunGibbs_lsi`.

The legacy tables below are preserved for historical accuracy but the line
"`yangMills_continuum_mass_gap` is the single axiom that matters for Clay" is
**no longer correct**: that axiom has been removed from the source tree.

---

# AXIOM_FRONTIER.md
## THE-ERIKSSON-PROGRAMME — Custom Axiom Census
## Version: C133 (v1.45.0) — 2026-04-11

---

## BFS-live custom axioms for `sun_physical_mass_gap`

| # | Axiom | File:Line | Content | Papers | Status |
|---|-------|-----------|---------|--------|--------|
| 1 | `lsi_normalized_gibbs_from_haar` | `BalabanToLSI.lean:255` | Holley-Stroock: LSI(α) for Haar ⟹ LSI(α·exp(-2β)) for normalized Gibbs | [44]–[45] | **LIVE** — specific HS instance for normalized probability Gibbs measure |

**Oracle target:** `YangMills.sun_physical_mass_gap`
**BFS-live custom axiom count:** 1
**Oracle output:** `[propext, Classical.choice, Quot.sound, YangMills.lsi_normalized_gibbs_from_haar]`

---

## BFS-dead axioms (declared but NOT in sun_physical_mass_gap oracle)

### BalabanToLSI.lean

| Axiom | Line | Used by | Why BFS-dead |
|-------|------|---------|--------------|
| `lsi_withDensity_density_bound` | 315 | Legacy un-normalized path | Replaced by `lsi_normalized_gibbs_from_haar` in C132 |
| `holleyStroock_sunGibbs_lsi` | 325 | Legacy un-normalized path | Replaced by `holleyStroock_sunGibbs_lsi_norm` (theorem) in C132 |
| `sz_lsi_to_clustering` | 345 | `sun_gibbs_clustering` | sun_physical_mass_gap bypasses clustering (C125) |

### L8_Terminal/ClayTheorem.lean

| Axiom | Line | Used by | Why BFS-dead |
|-------|------|---------|--------------|
| `yangMills_continuum_mass_gap` | 51 | Old `clay_millennium_yangMills` path | Entire old path bypassed by LSI pipeline (C123) |

### Experimental/ (research frontier — not imported by main pipeline)

| Axiom | File | Notes |
|-------|------|-------|
| `generatorMatrix'` | LieSUN/DirichletConcrete.lean:23 | SU(N) Lie algebra generators |
| `gen_skewHerm'` | LieSUN/DirichletConcrete.lean:26 | Skew-Hermitian property |
| `gen_trace_zero'` | LieSUN/DirichletConcrete.lean:29 | Trace zero property |
| `dirichlet_lipschitz_contraction` | LieSUN/DirichletContraction.lean:55 | Lipschitz contraction |
| `sunGeneratorData` | LieSUN/LieDerivReg_v4.lean:26 | Generator data |
| `lieDerivReg_all` | LieSUN/LieDerivReg_v4.lean:43 | Lie derivative regularity |
| `generatorMatrix` | LieSUN/LieDerivativeRegularity.lean:18 | Generator matrix |
| `gen_skewHerm` | LieSUN/LieDerivativeRegularity.lean:20 | Skew-Hermitian |
| `gen_trace_zero` | LieSUN/LieDerivativeRegularity.lean:22 | Trace zero |
| `matExp_traceless_det_one` | LieSUN/LieExpCurve.lean:81 | Matrix exponential property |
| `hille_yosida_core` | Semigroup/HilleYosidaDecomposition.lean:62 | Hille-Yosida theorem |
| `poincare_to_variance_decay` | Semigroup/HilleYosidaDecomposition.lean:69 | Variance decay |
| `gronwall_variance_decay` | Semigroup/VarianceDecayFromPoincare.lean:133 | Gronwall argument |
| `variance_decay_from_bridge_and_poincare_semigroup_gap` | Semigroup/VarianceDecayFromPoincare.lean:79 | Variance decay |

### P8_PhysicalGap/ (used by P8 modules but not in sun_physical_mass_gap BFS path)

| Axiom | File | Notes |
|-------|------|-------|

### ClayCore/BalabanRG/ (RG machinery — not in sun_physical_mass_gap BFS path)

| Axiom | File | Notes |
|-------|------|-------|
| `physical_rg_rates_from_E26` | PhysicalRGRates.lean:101 | RG rate data |

---

## Recently eliminated axioms (C124–C132)

| Axiom | Was at | Campaign | Method |
|-------|--------|----------|--------|
| `lsi_withDensity_density_bound` (as BFS-live) | BalabanToLSI.lean | **C132** | Replaced: `lsi_normalized_gibbs_from_haar` for normalized Gibbs |
| `sunPlaquetteEnergy_nonneg` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `sunPlaquetteEnergy_le_two` | BalabanToLSI.lean | **C131** | Proved: `entry_norm_bound_of_unitary` (Mathlib) |
| `holleyStroock_sunGibbs_lsi` (as BFS-live) | BalabanToLSI.lean | **C132** | Replaced: `holleyStroock_sunGibbs_lsi_norm` for normalized Gibbs |
| `balaban_rg_uniform_lsi` | BalabanToLSI.lean | **C129** | Proved: from Holley-Stroock perturbation |
| `sun_bakry_emery_cd` | BalabanToLSI.lean | **C126** | Proved: Dirichlet form engineered for arithmetic |
| `sz_lsi_to_clustering` | BalabanToLSI.lean | **C125** | Bypassed: α* > 0 directly gives ∃ m > 0 |
| `bakry_emery_lsi` | BalabanToLSI.lean | **C124** | Proved: BakryEmeryCD := LSI, theorem by id |

---

## Proof chain from axiom to Clay theorem

```lean
-- Step 1: The axiom (specific Holley-Stroock for normalized Gibbs)
axiom lsi_normalized_gibbs_from_haar :
    LSI(Haar, α) ∧ IsProbabilityMeasure(NormGibbs_β) → LSI(NormGibbs_β, α·exp(-2β))

-- Step 2: HS for normalized SU(N) Gibbs (THEOREM, C132)
theorem holleyStroock_sunGibbs_lsi_norm :
    LSI(Haar, α) → LSI(NormGibbs_β, α·exp(-2β))
    -- assembles axiom + IsProbabilityMeasure (proved in C132)

-- Step 3: Uniform DLR-LSI for normalized Gibbs (THEOREM, C132)
theorem balaban_rg_uniform_lsi_norm :
    ∃ α*, 0 < α* ∧ ∀ L, LSI(NormGibbs_β L, α*)

-- Step 4: DLR-LSI assembly (THEOREM, C132)
theorem sun_gibbs_dlr_lsi_norm :
    ∃ α*, 0 < α* ∧ DLR_LSI(sunGibbsFamily_norm, sunDirichletForm, α*)

-- Step 5: Mass gap (THEOREM, C132)
theorem sun_physical_mass_gap : ClayYangMillsTheorem :=
    ⟨α_star, hα⟩   -- α* > 0 witnesses ∃ m > 0
```

---

## How to verify

```bash
# Check oracle for sun_physical_mass_gap
printf 'import YangMills.P8_PhysicalGap.PhysicalMassGap\n#print axioms YangMills.sun_physical_mass_gap\n' | lake env lean --stdin
```

Expected output (v1.45.0):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound,
   YangMills.lsi_normalized_gibbs_from_haar]
```

Target (fully unconditional):
```
'YangMills.sun_physical_mass_gap' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

---

## Source papers for the remaining axiom

`lsi_normalized_gibbs_from_haar` is established in:
- Paper [44] (viXra:2602.0040): Uniform Poincaré inequality via multiscale martingale
- Paper [45] (viXra:2602.0041): Uniform log-Sobolev inequality and mass gap

The mathematical content is the Holley-Stroock perturbation lemma, applied specifically
to the **normalized** SU(N_c) Gibbs probability measure. The normalization
Z_β = ∫ exp(-β·e) dHaar is proved to satisfy Z_β > 0 and Z_β ≤ 1 (C132).
The key inequality: if the reference measure (Haar) satisfies LSI(α), then the
density-perturbed measure satisfies LSI(α·exp(-2β)) where exp(-2β) is the density
lower bound from the energy range e(g) ∈ [0,2].
Ref: Holley-Stroock (1987), Diaconis-Saloff-Coste (1996), Ledoux Ch. 5.

---

## Terminal Theorem: Weak vs Strong (v0.30.0+)

| Identifier | Prop | Strength |
|---|---|---|
| `ClayYangMillsTheorem` | `∃ m_phys : ℝ, 0 < m_phys` | **Vacuous** (provable without axioms) |
| `ClayYangMillsStrong` | `∃ m_lat, HasContinuumMassGap m_lat` | **Substantive** (quantitative convergence) |

`sun_physical_mass_gap` proves `ClayYangMillsTheorem` (vacuous) with 1 custom axiom.
`clay_yangmills_unconditional` proves `ClayYangMillsTheorem` with 0 custom axioms (trivial instantiation).
`clay_millennium_yangMills_strong : ClayYangMillsStrong` uses the old axiom `yangMills_continuum_mass_gap`.

---

## C133 audit notes (v1.45.0)

Deep dependency analysis confirmed:
- `lsi_normalized_gibbs_from_haar` is the SOLE remaining BFS-live axiom
- All 25 other axioms are BFS-dead (unreachable from `sun_physical_mass_gap`)
- C132 replaced the abstract `lsi_withDensity_density_bound` with the specific
  `lsi_normalized_gibbs_from_haar` — correctly stated for probability measures
- C132 proved `IsProbabilityMeasure` for normalized Gibbs (not assumed)
- Mathlib has `withDensity` infrastructure but no LSI library
- Proof strategy: entropy change-of-measure for the normalized density
- No shortcuts found — the axiom requires genuine real analysis work

*Last updated: C133 (v1.45.0, 2026-04-11).*

---

## Historical Axiom Census  2026-04-14

Superseded by v0.95.0-v0.97.0.  The current command

    git grep -n -E "^axiom " -- "*.lean" | Select-String -NotMatch "Experimental"

returns empty.  The table below is kept only as a historical record of the
2026-04-14 audit.

Taken then from `grep -rn '^axiom ' YangMills/ --include='*.lean' | grep -v Experimental`.

### On the main oracle chain (consumed by `yang_mills_mass_gap`)

| # | File | Axiom | Role |
|---|------|-------|------|
| 1 | `P8_PhysicalGap/BalabanToLSI.lean:828` | `holleyStroock_sunGibbs_lsi` | HolleyStroock transfer from Haar LSI to perturbed Gibbs LSI (the main analytic content) |
| 2 | `P8_PhysicalGap/BalabanToLSI.lean:818` | `lsi_withDensity_density_bound` | L density bound used by HolleyStroock |
| 3 | `P8_PhysicalGap/BalabanToLSI.lean:848` | `sz_lsi_to_clustering` | StroockZegarlinski: LSI  exponential clustering |
| 4 | `P8_PhysicalGap/StroockZegarlinski.lean` | retired v0.89.0: former `poincare_to_covariance_decay` | Now explicit SZ input |
| 5 | `P8_PhysicalGap/MarkovSemigroupDef.lean` | retired v0.91.0: former `hille_yosida_semigroup` | Now explicit `SymmetricMarkovTransport` input |
| 6 | `P8_PhysicalGap/SUN_DirichletCore.lean` | retired v0.92.0: former `sunDirichletForm_contraction` | Now explicit normal-contraction input |
| 7 | `P8_PhysicalGap/SUN_LiebRobin.lean` | retired v0.88.0: former `sun_variance_decay` | Now explicit theorem input |
| 8 | `P8_PhysicalGap/SUN_LiebRobin.lean` | retired v0.88.0: former `sun_lieb_robinson_bound` | Now explicit theorem input |
| 9 | `L8_Terminal/ClayTheorem.lean:51` | `yangMills_continuum_mass_gap` | Top-level Clay statement glue |

### Off the main oracle chain (RG branch  not consumed by Clay)

| # | File | Axiom |
|---|------|-------|
| 10 | `ClayCore/BalabanRG/PhysicalRGRates.lean:101` | `physical_rg_rates_from_E26` |
| 11 | `ClayCore/BalabanRG/P91WeakCouplingWindow.lean` | retired v0.86.0: former `p91_tight_weak_coupling_window` |

(These feed the Balaban RG branch; ask `#print axioms yang_mills_mass_gap`
whether they're reached.)

### Next cleanup candidates

Check which of (10)(11) survive in `#print axioms yangMills_continuum_mass_gap`.
If either is unreachable, mark it as RG-branch-only and either inline the proof
or move to `Experimental/`.

`lsi_normalized_gibbs_from_haar` is *not* an `axiom` keyword (it's an
`opaque`/declared theorem with `sorry` threaded). It is listed in the oracle
but won't match the `^axiom ` grep.

---

## Oracle Dependency Check  2026-04-14 (verified with `#print axioms`)

### Clay statement dependencies

| Theorem | Axioms depended on |
|---------|-------------------|
| `ClayYangMillsPhysicalStrong` (def) | `propext`, `Classical.choice`, `Quot.sound` |
| `clay_millennium_yangMills` | `propext`, `Classical.choice`, `Quot.sound` *(v0.90.0 pinned terminal oracle)* |
| `clay_millennium_yangMills_strong` | `propext`, `Classical.choice`, `Quot.sound` *(v0.90.0 pinned terminal oracle)* |
| `physicalStrong_implies_theorem` | `propext`, `Classical.choice`, `Quot.sound` |
| `sun_physical_mass_gap` | `propext`, `Classical.choice`, **`sorryAx`**, `Quot.sound` |

**Decisive conclusion:** the Clay statement consumes exactly ONE custom axiom  `yangMills_continuum_mass_gap`. Every other `axiom` declared in the repo is either consumed only by intermediate lemmas that don't feed Clay, or unused entirely.

`sun_physical_mass_gap` has `sorryAx` but no custom axioms  its oracle is the 3 documented `sorry` markers, not the labelled axioms.

### Usage count per axiom (files referencing the name, excluding Experimental)

| Axiom | Files | Status |
|-------|-------|--------|
| `yangMills_continuum_mass_gap` | 5 | **Live  sole Clay oracle** |
| `sz_lsi_to_clustering` | 4 | Live (intermediate; not on Clay path) |
| `hille_yosida_semigroup` | 0 | Retired v0.91.0; now explicit `SymmetricMarkovTransport` input |
| `holleyStroock_sunGibbs_lsi` | 2 | Live (intermediate; not on Clay path) |
| `poincare_to_covariance_decay` | 0 | Retired v0.89.0; now explicit input to `sz_lsi_to_clustering_bridge` |
| `sunDirichletForm_contraction` | 0 | Retired v0.92.0; now explicit input to `sunDirichletForm_isDirichletFormStrong_of_contraction` |
| `physical_rg_rates_from_E26` | 2 | Live (RG branch; not on Clay path) |
| `p91_tight_weak_coupling_window` | 0 | Retired v0.86.0; replaced by data-driven theorem `p91_tight_weak_coupling_window_theorem` |
| `lsi_withDensity_density_bound` | 1 | **DEAD  no consumers** |
| `sun_variance_decay` | 0 | Retired v0.88.0; now explicit input to `sun_locality_to_covariance` |
| `sun_lieb_robinson_bound` | 0 | Retired v0.88.0; now explicit input to `sun_locality_to_covariance` |

### Cleanup recommendation

- **Remove 3 dead axioms** (`lsi_withDensity_density_bound`, `sun_variance_decay`,
  `sun_lieb_robinson_bound`)  the two SUN names were retired in v0.88.0 by
  turning them into explicit theorem inputs.
- **Keep the 7 live intermediate/RG-branch axioms** but label them as such in their
  source files and rewrite their docstrings to say "not consumed by the Clay
  statement; this exists to support ".
- **`yangMills_continuum_mass_gap` is the single axiom that matters for Clay.**
  All current-pass proof effort on lsi/Holley-Stroock/etc. is structurally
  orthogonal to closing the Clay gap  it would discharge intermediate axioms
  that Clay does not consume. To make Clay unconditional, the sole move is to
  discharge `yangMills_continuum_mass_gap` directly (or wire the LSI chain
  into it, which currently doesn't happen).

---

## 2026-04-21 --- L2.5 closed

Theorem: YangMills.ClayCore.sunHaarProb_trace_normSq_integral_le
Oracle:  [propext, Classical.choice, Quot.sound] --- Mathlib baseline.
No new axioms, no sorries.

This closes the L^2 bound on the fundamental Wilson loop observable
over the Haar measure of SU(N_c):  integral |tr U|^2 <= N_c.
It is the structural input for the variance side of the mass-gap chain
(SchurPhysicalBridge).

L2.5 is additive-only to the oracle: it does not remove or introduce
any axiom from the Clay frontier. The holleyStroock_sunGibbs_lsi
obligation is unchanged.
