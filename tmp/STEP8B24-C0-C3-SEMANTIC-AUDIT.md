# Step 8b.24 C0–C3 — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope: bricks 30–34 in `STEP8B24_BRICK_SCHEDULE`.

## Gate C0 — one fixed target/source endpoint

**PASS (static).**

For one coarse Fourier mode, the generated `G Q'^*` output is first written
as the complete finite sum of transposed physical Green terms. Dividing by
the same coarse character at one fixed source site converts those terms into
the sealed row-oriented endpoint samples, whose complete-fibre sum is the
literal CMP89 stabilized endpoint integrand.

The coarse mode `ell`, fine target `x`, coarse source `y`, and Lie vector `v`
remain fixed throughout. No target-dependent readout family is accepted.

## Gate C1 — point source is reconstructed internally

**PASS (static).**

The neutral finite layer proves product-character orthogonality in the
required orientation and reconstructs the literal complex-fibre point source
with exact inverse-volume normalization. An arbitrary continuous-linear map
then consumes that proved reconstruction.

Specializing the map to the generated Green endpoint produces one normalized
finite sum of literal CMP89 endpoint values. The target and source remain in
one common scope; neither a point-source expansion nor a Green response
family is a hypothesis.

## Gate C2 — zero-residue selector uses exact finite reindexings

**PASS (static).**

- Periodic Fourier negation is proved involutive through the literal
  `FinBox`/`ZMod` equivalence.
- The finite sum is reindexed first by that involution and then by the exact
  `FinBox`/`ZMod` equivalence.
- Physical finite-grid aliasing is specialized at residue zero.
- The stabilizing coefficient is the internally generated physical
  coefficient; only the named common-radius scalar windows remain inputs.

No Fourier reconstruction, inverse, coefficient bound, or Green family is
accepted at this endpoint.

## Gate C3 — common scalar target is preserved under recombination

**PASS (static).**

C3 composes the C1 point-source equality with the C2 scalar zero-residue
identity and moves the resulting scalar through the same fixed Lie vector.
The public displacement is the literal negative fine-to-coarse endpoint
displacement from C0/C1; no second target or independently chosen readout is
introduced.

## Delimitation

C0–C3 identify the generated point-source column with the physical
zero-residue Green series. They do not bound that series, transport it to the
independent source owner, produce regional `B0`, attain window 15, or close a
terminal field.

## Static verdict

All C0–C3 gates pass statically. The common-target gate and exact normalization
are explicit, and the point-source/Fourier identities are built internally.
Promotion remains blocked on Lean elaboration and axiom audit in the
sanctioned remote validation path.

