# Step 8b.24 C4a–C6b — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope: bricks 35–39 in `STEP8B24_BRICK_SCHEDULE`.

## Gate C4 — centered endpoint reaches the independent source owner

**PASS (static).**

The literal negative fine-to-coarse displacement and the shortest periodic
displacement need not agree as signed vectors at an antipodal seam. C4a
proves equality only of their centered `l1` lengths through the common
`ZMod` residue, which is exactly what the exponential weight consumes. The
diagonal Unit-F estimate then transports to the actual coarse source `y`.

C4b specializes this at
`Kfine = L^(depth+1)` and `N = 2*(K*Q)`, retaining separately the physical
amplitude, periodic geometric factor, boundary factor, owner exponential and
`norm v`. No diagonal `K=L` identification remains in the conclusion.

## Gate C5 — source-localization owner is a theorem, not a readout

**PASS (static).**

The flat fine target is evaluated at the sealed source-separated site
equivalence, and its block owner rewrites to the literal CMP99 (3.89)
`cmp99Eq389SourceLocalizationOwner`. No separately chosen readout,
cardinality equivalence or owner hypothesis is accepted.

## Gate C6a — the named coefficient is only point-source `B0`

**PASS after a static documentation correction.**

The named coefficient is exactly the coefficient already displayed by C5,
and its nonnegativity is derived from the physical Green majorant and scalar
strip window. The point-source endpoint is merely restated in this exact
normal form.

The coefficient depends explicitly on `depth` through the generated
physical `a`. No theorem in this block proves a uniform-in-depth bound. A
scratch docstring that called it “depth-independent” was therefore corrected
before promotion; no declaration or proof changed. At fixed `L`, `depth` and
`rho`, it is uniform in `K`, `Q`, and the target/source sites.

## Gate C6b — localized source field without a cardinality factor

**PASS (static).**

On the coarse source carrier the owner map is literally the identity. A
field supported in one owner fibre is therefore proved equal to the literal
point source carrying its value at that owner. C6a then upgrades to the
localized-field/sup-norm quantifier, using the existing evaluation-to-sup
bound and introducing no source-cardinality factor.

## Delimitation

The conclusion still controls the ambient complex operator `G Q'^*`. It is
not the canonical real regional Dirichlet Green, does not provide its three
derivative actions, does not prove uniformity in `depth`, and does not attain
window 15 or any terminal field. Calling this coefficient the regional
`B0` would rename three open obligations.

## Static verdict

C4a–C6b pass statically with one repaired prose overclaim. The scale and
owner dictionaries are explicit, and the surviving frontier is accurately
localized at C6c. Promotion remains blocked on Lean elaboration and axiom
audit in the sanctioned remote validation path.

