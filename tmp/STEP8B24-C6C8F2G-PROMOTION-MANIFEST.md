# Step 8b.24 / C6c.8f2g PRE-VALIDATION promotion manifest

Status: **scratch only; not compiler-verified**.

This manifest records the written chain f2g.0--f2g.5.  It must not be
promoted, imported by `YangMillsCore`, or described as sealed before it is
elaborated with the complete scratch dependency overlay and its axiom audit
passes in the sanctioned heavy environment.

## Files

| eventual tracked path | scratch source | SHA-256 |
|---|---|---|
| `YangMills/RG/BalabanCMP99SourceRetainedCarrierEndpointGeometry.lean` | `tmp/BalabanCMP99SourceRetainedCarrierEndpointGeometry.draft.lean` | `3641D88103557D1D43A40DBEC3CF1962C0C2AAB2128C41B3E312DB4D6B1FF1AF` |
| `YangMills/RG/BalabanCMP99SourceRetainedCarrierEndpointGeometryAudit.lean` | `tmp/BalabanCMP99SourceRetainedCarrierEndpointGeometryAudit.draft.lean` | `5AC9DACF229E274B3FF870BF4A0077F45CA881C337A5C3C1A2EB9C25F5C02B08` |
| `YangMills/RG/BalabanCMP99Eq335SourceRegionDictionary.lean` | `tmp/BalabanCMP99Eq335SourceRegionDictionary.draft.lean` | `74DE39D22423FFE4169ABC16085AAE3F678B4E67F2E6436F928BB6AD5AF08A64` |
| `YangMills/RG/BalabanCMP99Eq335SourceRegionDictionaryAudit.lean` | `tmp/BalabanCMP99Eq335SourceRegionDictionaryAudit.draft.lean` | `0EA35D15DC77EB92D3A01D6A2EC8D196DF2038578CB1B00013B0141343B5702E` |

## Contract measured statically

- `CMP99PhysicalBondEndpointsIn` records source and positive-shift target.
- Its lattice size is an explicit polymorphic parameter, so the recursive tail
  does not have to unify an arbitrary size with one fixed syntactic product.
- Negative literal edges swap `srcV` and `dstV` explicitly; orientation is not
  erased by name or inferred from self-adjointness.
- The `M`-step straight path is assigned to the source/one-forward-block union
  by a literal `k < M` edge index and a separate periodic-wrap branch.  This
  proof is written but remains unelaborated.
- The transported-average theorem derives its block carrier internally from
  `cmp99BlockContainedContourSystem_staysIn` and
  `mem_cmp99ActiveCoarseRegion_sites_iff`.
- Gamma3 is handled by an explicit `StaysIn` reversal theorem; source and
  target are swapped through `src_reverse`/`dst_reverse`, not identified.
- The one-bond and selected-family Ubar theorems consume both active coarse
  endpoints, eliminate Gamma3's totalized off-source branch using the actual
  block membership, and construct all fine endpoint inclusions internally.
- The recursive induction consumes its own tail endpoint theorem to feed the
  selected-family Ubar pullback.  It accepts no free carrier map or inclusion.
- The final source dictionary exposes `OmegaPrime0` in its type and keeps the
  head-region equality distinct from the printed
  `OmegaPrime0.sites subset regular cube` premise.  The retained carrier/cube
  conclusion is proved by composition and is not stored in the dictionary.
- No source/cube inclusion, straight-path containment, recursive retained
  containment, small-field premise or operator equality is accepted from the
  caller.
- The endpoint pair has ten declarations/ten audit commands; the source-region
  pair has two declarations/two audit commands.  All four files contain no
  `sorry`, `admit` or axiom declaration and keep all imports before the module
  docstring.  This is a textual check only.

## Required scratch overlay closure

A lightweight import walk resolves the two f2g source roots to 18 scratch
source modules, each with a matching audit draft: 36 files in total.  The
topological source order is:

1. `BalabanCMP99SourceUbarExactReadCarrier`
2. `BalabanCMP99SourceTransportedAverageExactReadCarrier`
3. `BalabanCMP99SourceRetainedExactReadCarrier`
4. `BalabanCMP99SourceRetainedCarrierEndpointGeometry`
5. `BalabanCMP99Eq335PhysicalForwardDerivative`
6. `BalabanCMP99SourceRegularCube`
7. `BalabanCMP99Eq335PhysicalRegularityWitness`
8. `BalabanCMP99Eq335PhysicalRegularityLaplacianLocality`
9. `BalabanCMP99SourceUbarLocalDeviationBound`
10. `BalabanCMP99SourceSelectedNextBackgroundLocality`
11. `BalabanCMP99SourceLocalizedNextBackground`
12. `BalabanCMP99SourceLocalizedWeightedQprimeTower`
13. `BalabanCMP99SourceRetainedQprimeLocality`
14. `BalabanCMP99SourceLocalizedTowerCanonicalExtension`
15. `BalabanCMP99SourceRetainedFineExtension`
16. `BalabanCMP99SourceLocalizedRetainedTower`
17. `BalabanCMP99Eq335PhysicalRetainedNearIdentity`
18. `BalabanCMP99Eq335SourceRegionDictionary`

Promotion and validation must materialize this closure atomically.  Testing
only the final two modules against absent or stale `.olean` files would not be
evidence for f2g.

After the current Step8b22 terminal run has been classified and sealed, the
prepared stop-on-first-error focal order is:

1. materialize the 36-file overlay and verify every promoted blob hash;
2. `lake build YangMills.RG.BalabanCMP99SourceRetainedCarrierEndpointGeometry`;
3. `lake env lean YangMills/RG/BalabanCMP99SourceRetainedCarrierEndpointGeometryAudit.lean`;
4. `lake build YangMills.RG.BalabanCMP99Eq335SourceRegionDictionary`;
5. `lake env lean YangMills/RG/BalabanCMP99Eq335SourceRegionDictionaryAudit.lean`;
6. require exactly the declared ten-plus-two axiom headers and only the
   permitted axiom set before any PRE-VALIDATION removal.

This is a focal brick.  No root build, publication, or new terminal CI is
authorized merely by the static manifest.

## Open continuation

The four-file overlay writes all of C6c.8f2g but does not close it: no theorem
has yet been elaborated or oracle-checked.  The next admissible step is a focal
overlay validation after the current Step8b22 terminal verdict.  Until that
passes, f4's `hinside` remains open and no PRE-VALIDATION mark may be removed.
