# v3 post-integration update brief

This v3 pack assumes the repository has already integrated v2 under
`docs/idea-db/ym-creative-expansion/` and that Batch 002/003 source-db indices now
exist. The role of this pack is therefore not to add more creative material, but
to turn the integrated idea database into a commit discipline focused on live
source-hypothesis removal.

## Observed repository update

- `CURRENT-STATE.md` now records Batch 002 operational crosswalks and Batch 003
  proof-obligation indices.
- The creative expansion pack is explicitly staged as an experimental idea DB.
  It must not be imported into `YangMillsCore` or cited as source proof.
- The LLM fast context ranks Eq. (2.31) P-family dictionary first, then Eq. (2.29),
  Eq. (2.37), activity/termwise, Gaussian/root/Hessian, CMP119/CMP122, and flow/IR.
- `BalabanCMP116Eq231.lean` now exposes a source package with exactly three
  fields: `mem_iff_source`, `source_subset_gapCarrier`, and
  `admissible_iff_source`.

## v3 strategic pivot

The v2 pack was an idea expansion. The v3 pack is a proof-obligation compressor:

```text
one source package field, one commit, one measurable hypothesis reduction
```

Recommended first target:

```text
cmp116Eq231_source_subset_gapCarrier_of_bond_fst_mem_gapCubes
```

because it reduces the carrier field to the source-shaped statement

```text
sourceAdmissible Z D P -> forall b in P, b.1 in gapCubes Z D
```

This is narrower than the full P-family membership iff and should be attacked
from the CMP116/CMP109 windows before touching Eq. (2.37) or Eq. (2.29).
