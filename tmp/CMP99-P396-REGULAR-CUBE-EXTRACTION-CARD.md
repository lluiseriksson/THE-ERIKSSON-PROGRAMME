# CMP99 printed p. 396: regular-cube extraction card

Status: SOURCE-VERIFIED / PRE-VALIDATION-SCRATCH-MATERIALIZED.  This card is
scratch evidence only.  The printed regular-cube clause has been read from a
primary p. 396 render and represented by a source-fixed draft; neither the
draft nor its audit has been compiled.

## Evidence currently available

- Primary article: T. Balaban, *Propagators for Lattice Gauge Theories in a
  Background Field*, CMP 99 (1985), 389--434, Project Euclid
  `cmp/1103942769`.
- `tmp/pdfs/cmp99-p396.png` is the primary visual render of printed p. 396,
  SHA-256
  `15BDDA14DBE560AFE172128D4FDF5234E9B0D6F652F8B811B072A878179F452E`.
- `tmp/pdfs/cmp99-p396-regular-cube-crop.png` isolates the definition,
  SHA-256
  `DBDEE9CEA9FDAB6FD0BE91909DA9906E1FF27F695B7077F6F8BABA047A04E824`.
- `tmp/pdfs/cmp99-source.txt`, lines 353--374, is the companion OCR window
  spanning the definition, (3.35) and (3.36); it is not the authority for the
  damaged superscripts or the `O(1)` convention.
- `tmp/cmp99-p397.png` is a primary visual render of the next printed page.
  It confirms the continuation after (3.38) and, independently, fixes (3.39)
  as the full tensor norm
  `max_(mu,nu) sup_x |(D^U_mu A_nu)(x)|`.
- `tmp/pdfs/cmp99-p393-05.png` supplies the preceding primary definition
  `Lambda_j = Omega_j^(j) \\ Omega_(j+1)^(j)` and
  `Omega_(k+1) = empty`.

## Source facts fixed by the primary render

For every cube in the source class:

1. there is a unique index `j`, with `0 <= j <= k`;
2. the cube is contained in
   `B^j(Lambda_j) union B^(j+1)(Lambda_(j+1))`;
3. it meets `B^j(Lambda_j)` nontrivially;
4. it is a union of several big blocks at the printed scale;
5. its fine-lattice size is `O(1) * M * L^j * eta`, with the printed
   convention **`O(1) >= 10`**;
6. on the cube there is a gauge `u` with `U^u = exp(i * eta * A)`;
7. (3.35) bounds `A` by `O(1) M alpha0 (L^j eta)^-1` and the ordinary
   fine-lattice first-difference tensor `nabla^eta A` by
   `O(1) M alpha0 (L^j eta)^-2`;
8. the article explicitly says that (3.35) imposes no condition outside
   `Omega_0`.

Items 6--8 are not fields of the cube geometry itself; they belong to the
later local-gauge witness C6c.8f1.

The covariant tensor norm `max_(mu,nu) sup_x |D^U_mu A_nu(x)|` on p. 397,
(3.39), is a separate norm for the propagator estimates.  It must not be
identified with `nabla^eta A` in (3.35).  The rejected identification and its
never-compiled hashes are preserved in
`tmp/C6C8F0A-COVARIANT-DERIVATIVE-RETRACTION.md`.

## Resolved type-level design

The neighboring-stratum formulas are no longer visually gated.  Their
faithful tree representation at `j = k` uses the fact that p. 393 defines
`Omega_(k+1) = empty`, while the existing `global.stratum` is indexed only by
`Fin n`.  The draft's derived extended lifted-stratum operation returns the
literal terminal region at the terminal index and proves it empty from
`global.final_empty`.  It accepts no free `Lambda_(k+1)` or arbitrary
`domainOf` map.

The antecedent CMP96 p. 224, (2.3), defines its last source stratum as the
last region (`Lambda_k = Omega_k`), equivalently subtraction of a terminal
empty region.  It does not print a further independent `Lambda_(k+1)`.
Accordingly the value needed by the p. 396 formula at maximal `j` must be
recorded as a **terminal empty completion** of the adjacent-stratum notation,
not attributed to the paper as another freely defined stratum.  The accepted
Lean shape is a derived function on `Fin (n+1)` which agrees with
`global.stratum` below the terminal index and is theorem-proved empty at the
terminal index.

The literal cube/large-block geometry is represented by a periodic axis cube
generated from a base scale site and side `geometryFactor * M`, with
`10 <= geometryFactor`.  Its fine carrier is definitionally the `biUnion` of
those blocks under the existing dependent `fineBlock`.  The carrier is not a
field and cannot be chosen independently.  A separate law makes the printed
uniqueness of the scale index explicit.

## Existing tree objects that the final dictionary must reuse

- `CMP99SourceGlobalStratification.stratum` already defines
  `Lambda_j = Omega_j \\ Omega_(j+1)` and proves unique stratum membership.
- `CMP99SourceScaledStratification` already supplies the dependent scale site
  type, `fineBlock`, `strata` and
  `lift_stratum : biUnion (fineBlock j) (strata j) = global.stratum j`.
- Therefore C6c.8f0b must add only the cube-specific data and laws; it must not
  introduce a second free global stratification or a free `domainOf` map.

## Minimum final C6c.8f0b contract after visual extraction

The final source dictionary should contain, at minimum:

```text
scaleIndex        : Fin n
carrier           : Finset FineSite
carrier_nonempty  : carrier.Nonempty
meets_own_stratum : (carrier inter global.stratum scaleIndex).Nonempty
carrier_lies_in_adjacent_lifts : <exact p. 396 formula>
bigBlocks         : Finset (ScaleSite scaleIndex)
carrier_eq_blocks : carrier = bigBlocks.biUnion (fineBlock scaleIndex)
    geometryConstant        : real
    geometryConstant_ge_ten : 10 <= geometryConstant
    side_length_eq_or_bound : <tree cube-size realization of O(1) M L^j eta>
```

Only the exact orientation (`=` versus an upper/lower size bound) remains to
be matched to the repository's cube-size notion; the source's `O(1)` notation
must not be silently converted into a sharp equality.  The terminal-index
operation must be derived from the stratification rather than stored as a
field of each cube.

## Acceptance gate

C6c.8f0b is materialized in scratch as
`tmp/BalabanCMP99SourceRegularCube.draft.lean` and its seven-readout audit.
Current hashes are:

```text
99D178132F3869215529C8EC09C980BB2F06112B825A0860F4B442521790527B  source
433DE67E650961C902F62B26B12A5EE6646C33B5DBC73C1E3FC42102B6514966  audit
```

The exact two-file overlay passes the lightweight delimiter/namespace and
`sorry`/`admit` gate.  This is syntax evidence only.  The eventual seal must
cite the p. 396 artifact hash and the exact two stratum formulas.  Until a
remote elaboration and axiom audit pass:

- C6c.8f0a and C6c.8f0b remain PRE-VALIDATION scratch;
- C6c.8f1 remains absent;
- no terminal counter moves;
- `TermSource` remains uninhabited.
