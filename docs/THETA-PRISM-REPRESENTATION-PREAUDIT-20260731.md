# Theta-prism SU(2) representation pre-audit — 2026-07-31

## Status and scope

**Independent, read-only algebra audits: PASS.**  A representation specialist
passed claims 3--7, and a separate full-paper-calculation auditor passed all
eight registered claims.  Together with the independent geometry audit, these
are three PASS reports on the abstract object.  This is evidence about an
abstract product-Haar calculation,
not a Lean theorem, a physical `GaugeConfig` cell, a `ReflectionSplitting`
instance, reflection positivity, or SU(2) Gate 7.

The representation auditor arrived cold and used the raw repository object
`a66b1c7da3c7441e06864e327b5c4efa43e9c79d` only for conventions.  Resolving
the separately supplied annotated tag exposed a verdict-bearing tag message;
the resulting procedural contamination is recorded below.  The auditor states
that it did not use that message in the derivations.  The full-calculation
auditor independently disclosed a second, non-material contamination: an
overbroad search in the authorized tree printed unrelated reports under
`outputs/`.  It states that none was used in the derivation.

Let `G=SU(2)` with normalized Haar measure, `chi=Tr` in the fundamental
representation, and

```text
F(U,V) = chi(U) chi(V) - (1/2) chi(U V^-1).
alpha_j(beta) = integral exp((beta/2) chi(g)) chi_j(g) dg.
```

## Adversarial verdicts

| Claim | Verdict | Exact content checked |
|---|---|---|
| 3. Invariance and removal of one-cycle components | **PASS** | `F` is nonzero and invariant under simultaneous conjugation.  Its conditional expectations given `U`, `V`, or `UV^-1` vanish identically, hence it is orthogonal to the full three subspaces, not merely to their central characters. |
| 4. Norm | **PASS** | `||F||^2 = 3/4`. |
| 5. Representation sector | **PASS** | On three parallel links the subtraction removes exactly the `j0=0` channel, leaving the multiplicity-one sector `(j0,j1,j2)=(1,1/2,1/2)`.  The attempted residual one-cycle attack failed. |
| 6. Central multiplier and pairing | **PASS** | The multiplier on spin `j` is `alpha_j/(2j+1)`, and the pairing is `alpha_1 alpha_(1/2)^2 / 16`; independent Peter--Weyl and tensor-product calculations found no missing dimension or conjugation factor. |
| 7. Pre-registered lower bound | **PASS** | For `0<beta<=1`, nonnegative tensor multiplicities give `alpha_(1/2)>=beta/2`, `alpha_1>=beta^2/8`, hence the pairing is at least `beta^4/512`. |

The coefficient that makes the projection exact was independently rederived:

```text
integral chi(W A1) chi(W A2) dW = (1/2) chi(A2^-1 A1).
```

Consequently the subtracted term is precisely the singlet component.  The
auditor also obtained the explicit absolute bound

```text
|conj(F(g)) F(g') product_r k_beta(g_r g'_r^-1)| <= 25 exp(3 |beta|),
```

on normalized Haar measure, which justifies the Fubini rearrangements used in
the abstract calculation.

The full-calculation auditor reached the same coefficient by a fourth route,
distinct from the matrix-coefficient and singlet-projector calculations:
substitute `Z=W A1`, use `chi(Z C)=chi(Z^-1 C^-1)`, and apply the character
convolution identity `chi*chi=chi/2`.  It again gives
`(1/2) chi(A2^-1 A1)`.

## Endpoint and sign discipline

At `beta=0`, `F` remains nonzero and sector-pure but its pairing is zero.

The following statement is deliberately indivisible: **for `beta<0`, this
specific witness still has positive pairing
`alpha_1 alpha_(1/2)^2/16` and satisfies the numerical lower bound
`beta^4/512`, but this is not reflection positivity, because the one-link
operator has negative half-integer eigenvalues and the full form is not
positive semidefinite in that regime.**

The registered gate was only the inequality for `0<beta<=1`.  Its extension
to all `beta>0`, and the preceding witness-specific observation for `beta<0`,
are **post-hoc strengthenings** and were not part of the pre-registered gate.

Deleting `A2`, `B2`, and the third plaquette kills the specific theta sector
`(1,1/2,1/2)`, **not every one-cycle sector**.  No front door may paraphrase
this as collapse to the zero space.

## Failed attacks

1. A residual component in `L^2(U)`, `L^2(V)`, or `L^2(UV^-1)` was sought.
   All three conditional expectations vanish against arbitrary `L^2`
   functions.
2. A hidden factor of `2j+1` or orientation conjugation was sought by two
   independent conventions.  Both gave the multiplier
   `alpha_j/(2j+1)` and final factor `1/16`.
3. Reversing the inverse in the two-character integral was tested.  Matrix
   coefficient orthogonality fixes the result as
   `(1/2) chi(A2^-1 A1)`.

## Procedural incidents: references and broad reads leak context

An annotated tag can expose its message merely when an auditor resolves the
reference.  Here the supplied tag message contained a prior verdict, so the
audit cannot be described as perfectly blind even though the algebra was
derived independently.

Rule purchased on 2026-07-31: **blind-audit instructions must identify the
object by raw commit SHA only, never by an annotated tag; tag messages must not
contain verdicts.  An anchor identifies an object, it does not adjudicate it.**

The second incident shows that a raw SHA is necessary but not sufficient.  A
repository tree can itself contain reports from other lanes, and a broad `rg`
can print them even when the auditor never seeks them.  Additional rule
purchased on 2026-07-31: **a blind-audit contract must enumerate the readable
files; read-only access to an entire tree is not a blind boundary.**  Both
auditors self-declared their exposures and judged them immaterial, but future
contracts must prevent the mechanism rather than rely on disclosure.

## Remaining gates

- Realize the abstract cell as an honest physical lattice object and bridge it
  to `GaugeConfig`.
- Derive the required splitting/reflection-positive pairing rather than
  importing the continuous `ReflectionSplitting` result by analogy.
- Formalize the construction in Lean, certify its exact object, and obtain the
  separately contracted terminal audit.

No paper, merge, Gate 7 claim, or physical Yang--Mills conclusion is licensed
by this algebraic PASS.
