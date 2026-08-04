# lean-os-positivity M1 interface digest

Date: 2026-07-03.

Satellite repository: <https://github.com/lluiseriksson/lean-os-positivity>.

This digest is for the mother repository only.  It records the exact Lean API
published by the satellite branch `push/m1-rp-core` and the non-consumable
frontier branch `frontier/M1`.  It does not import the satellite and it does
not change any theorem of `THE-ERIKSSON-PROGRAMME`.

## Verified branch

- Branch: `push/m1-rp-core`.
- Commit: `7a7946611c251f2dcf26bf6fcc5b43d31c870e42`.
- CI: green on 2026-07-03,
  <https://github.com/lluiseriksson/lean-os-positivity/actions/runs/28657163752>.
- Local checks reported by the satellite pass:
  `lake build Interfaces`, `lake build OSPositivity`, and no `sorry`/`axiom`
  grep over the exported core.

## Consumption rule

The stable contract root remains unchanged:

```lean
import Interfaces
```

The M1 branch adds implementation modules through the satellite barrel
`OSPositivity.lean`, but `Interfaces.lean` is not widened.  A mother-side
consumer should therefore treat the modules below as candidate implementation
inputs, not as a breaking-change-stable contract, until the satellite promotes
them through `INTERFACES.md`.

Candidate imports on the satellite branch:

```lean
import OSPositivity.PairingForm
import OSPositivity.BondModel
```

## Pairing-form API

File: `OSPositivity/PairingForm.lean`.

Main declarations:

- `OSPositivity.WeightFunction`
- `OSPositivity.WeightFunction.toExpectation`
- `OSPositivity.FiniteProbability.toWeightFunction`
- `OSPositivity.FiniteProbability.toWeightFunction_toExpectation`
- `OSPositivity.WeightFunction.pairingForm`
- `OSPositivity.WeightFunction.reflectionForm_eq_pairingForm`
- `OSPositivity.WeightFunction.pairingForm_add_left`
- `OSPositivity.WeightFunction.pairingForm_add_right`
- `OSPositivity.WeightFunction.pairingForm_smul_left`
- `OSPositivity.WeightFunction.pairingForm_smul_right`
- `OSPositivity.WeightFunction.pairingForm_conj_symm`
- `OSPositivity.WeightFunction.reflectionForm_im_eq_zero`
- `OSPositivity.WeightFunction.pairingForm_expand`
- `OSPositivity.WeightFunction.normSq_pairingForm_le`

Mathematical scope: finite, unnormalized weights; reflection-invariant
involution; reflection Cauchy-Schwarz for observables whose complex span is
reflection-positive.  The key hypothesis is explicit as
`hspan : forall b : Complex, ComplexNonnegative
  (Expectation.reflectionForm ... (F + b • G))`.

No GNS quotient is constructed on this branch.

## Bond-model API

File: `OSPositivity/BondModel.lean`.

Main declarations:

- `OSPositivity.LatticeReflection.DependsOnlyOn.add`
- `OSPositivity.LatticeReflection.DependsOnlyOn.smul`
- `OSPositivity.bondReflection`
- `OSPositivity.bondWeight`
- `OSPositivity.eval_of_dependsOnlyOn_true`
- `OSPositivity.bondQuadForm_re`
- `OSPositivity.bondQuadForm_im`
- `OSPositivity.complexNonnegative_bondForm_of_psd`
- `OSPositivity.bond_reflectionForm_eq`
- `OSPositivity.bond_reflectionPositive`
- `OSPositivity.psd_of_bond_reflectionPositive`
- `OSPositivity.ferromagneticKernel`
- `OSPositivity.ferromagneticKernel_nonneg`
- `OSPositivity.ferromagneticKernel_symm`
- `OSPositivity.ferromagneticKernel_psd`
- `OSPositivity.isingBond_reflectionPositive`

Mathematical scope: the two-site reflected lattice `Bool`, positive side
`{true}`, finite spin space, and an unnormalized nonnegative bond kernel.  The
closed theorem is the finite bond equivalence:

- real symmetric PSD kernel implies reflection positivity;
- reflection positivity of the bond model implies PSD of the kernel.

The instance `isingBond_reflectionPositive` proves reflection positivity for
the zero-field ferromagnetic Ising/Potts bond for every finite spin space and
every `0 <= beta`.

## Frontier branch

- Branch: `frontier/M1`.
- Commit: `26e8b7fc775b440b1e41c90ab387a151aa48b0c4`.
- CI: red by design in the no-sorry step,
  <https://github.com/lluiseriksson/lean-os-positivity/actions/runs/28657325409>.

Do not consume this branch from the mother repository.  It contains four
statement-first obligations in `OSPositivity/Frontier/GNSChain.lean`:

- `OSPositivity.WeightFunction.pairingForm_eq_zero_of_null`
- `OSPositivity.WeightFunction.gnsSeminorm_add_le`
- `OSPositivity.WeightFunction.exists_gnsReconstruction`
- `OSPositivity.multiBond_reflectionPositive`

These names are useful as future interface targets only.  They are not proved
and must not be counted as progress.

## Mother-side impact

No current `THE-ERIKSSON-PROGRAMME` theorem depends on this satellite branch.
The digest is an integration note for future OS/RP wiring after the satellite
promotes a stable interface.  It makes no continuum, OS/Wightman
reconstruction, or mass-gap claim.
