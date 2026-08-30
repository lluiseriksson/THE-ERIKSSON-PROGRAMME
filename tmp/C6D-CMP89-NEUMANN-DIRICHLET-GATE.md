# C6d source gate: CMP89 Neumann Green versus the current Dirichlet compression

Status: **OPEN SOURCE DICTIONARY / PHYSICAL IDENTIFICATION PROHIBITED**.

This note records a source-level mismatch found before constructing the
uniform regional `B0`/`delta0` producer.  It does not retract the already
proved Dirichlet algebra.  It prevents that algebra from being cited as the
local Green estimate printed in CMP89 until an exact boundary-condition and
carrier dictionary has been supplied.

## Primary-source evidence

- CMP89 printed p. 572 defines `-Delta_{A,Omega}^{eta,N}` with **Neumann
  boundary conditions** on `partial Omega`; its quadratic form sums bonds
  whose two endpoints lie in `Omega`.  The local Green is
  `G_k(Omega,A) = (-Delta_{A,Omega}^{eta,N} + m^2 + a P_k(A))^{-1}`.
- CMP89 Lemma 2.4, printed p. 582, gives the uniform local Green bounds used
  downstream.
- CMP89 Eq. (2.42), printed p. 584, represents the rectangular-box Green by
  **positive multiple reflections** of the full-lattice propagator.  This is
  the image formula for the printed free/Neumann boundary problem.
- On that page the rectangle is written literally as
  `box = {x in xi Z^d : 0 <= x_mu <= M_mu}`, with `xi = L^(-j)`.  The first
  reflected coordinates printed in (2.42) are `-x'_mu-xi` and
  `2 M_mu-xi-x'_mu`.  Thus the source-facing rectangle must expose the scaled
  integer lattice and the physical endpoint parameters `M_mu`; an arbitrary
  finite-site carrier is not the printed object.
- CMP96 Eq. (2.40) allows a local inverse with specified boundary conditions
  and names Neumann boundary conditions as the source example.  It does not
  identify a zero-extension Dirichlet compression with the CMP89 operator.

Local visual evidence used for this reading:

- `tmp/cmp89-p-02.png` (printed p. 572)
- `tmp/cmp89-p-12.png` (printed p. 582)
- `tmp/cmp89-p-14.png` (printed p. 584)
- `tmp/cmp96-primary.txt` (the local-Green discussion surrounding Eq. (2.40))

No OCR-only constant or boundary-condition reading is accepted here.

## Current Lean object

`BalabanCMP99SourceRegionalGreenNeumann.lean` defines

```lean
cmp99RegionalDirichletPrecision Omega K =
  restrictZeroCLM Omega ∘L K ∘L extendZeroZeroCLM Omega
```

This is compression by zero extension.  Boundary-crossing bonds of the
ambient operator see zero outside the carrier, so the operator is not the
printed Neumann quadratic form that simply omits bonds leaving `Omega`.

`BalabanCMP96SourceSeparatedRegionalPrefixGreen.lean` then defines
`cmp96SourceSeparatedRegionalCell` as the finite-range thickening of a cutoff
support and constructs its local Green as the inverse of that Dirichlet
compression.  Two independent dictionaries are therefore open:

1. **boundary condition:** printed Neumann/free operator versus zero-extension
   Dirichlet compression;
2. **carrier:** printed rectangular parallelepiped/cube versus an arbitrary
   support thickening, for which no rectangle equality is currently proved.
3. **measure convention:** CMP89 (1.3) uses the common lattice factor `eta^d`
   in the site/bond quadratic form, while the present `PiLp` spaces use
   counting measure.  Prove the common-factor cancellation for the induced
   normalized operator and track its effect on every norm before calling the
   objects identical.

The file name `BalabanCMP99SourceRegionalGreenNeumann.lean` does not discharge
either dictionary: its implemented operator is Dirichlet.

## Semantic no-go to seal

On a proper region with a boundary, a constant field has zero energy for the
internal-bond Neumann Laplacian, while zero extension generally creates
nonzero boundary-edge energy for the Dirichlet compression.  Therefore the
two Laplacians are not definitionally equal and cannot be identified merely
by reindexing or inverse uniqueness.

Acceptance test for the no-go brick:

- choose one explicit nonempty proper region with a boundary edge;
- choose a nonzero constant regional zero-cochain;
- prove the internal-bond Neumann Laplacian/energy vanishes;
- prove the zero-extension Dirichlet Laplacian/energy does not vanish;
- keep the conclusion at the exact level proved (operator/energy inequality,
  not a claim about every region).

### Derivative-level prefix now prepared

`BalabanCMP89NeumannDirichletBoundaryNoGo.lean` is a PRE-VALIDATION prefix
to this acceptance test.  On a witnessed boundary-crossing bond it proves
that the internal-bond Neumann derivative, after ambient extension, is zero,
whereas the trivial-background zero-extension Dirichlet derivative is
`spacing⁻¹ • phi(x)` and hence nonzero when the endpoint value and spacing
are nonzero.  This is already enough to prohibit identifying the two
derivatives.

It is deliberately not yet the full no-go above: it does not prove that a
single explicit constant regional field has zero Neumann *energy* and
positive Dirichlet *energy*, nor does it compare the Laplacians or their
Greens.  A future hot PASS of that prefix remains diagnostic evidence only;
the four-item acceptance test stays open until the energy-level witness is
sealed.

## Source-faithful repair (preferred)

1. Define the rectangular active region used by CMP89/CMP96, with its side
   lengths and block units explicit.
2. Prove the `eta^d` weighted-to-counting normalization dictionary, including
   which operator and kernel norms are invariant and which amplitudes rescale.
3. Define the Neumann/free regional precision by the internal-bond quadratic
   form, not by zero extension.
4. Add the positive term `m^2 + a P_k` (or the exact source specialization)
   and prove the resulting regional precision coercive.  The Neumann
   Laplacian alone has constant modes and must not be declared coercive.
5. Construct its inverse internally.
6. Formalize the positive multiple-reflection representation of CMP89
   Eq. (2.42), including the infinite continuation denoted by the printed
   `+ ...`; it is not a finite `2^d` image sum.
7. Transfer the already proved full-lattice analytic bound to the rectangular
   box, proving summability of the reflected image lattice and keeping its
   geometric-series constant and the distance comparison explicit.  No
   finite reflection multiplicity may be substituted for that series.  This
   is the producer of a regional value bound.  Reuse the already cold-sealed
   `BalabanCMP89SignedLatticeL1TotalSum`: it evaluates the full signed `Int^d`
   exponential sum with the exact product constant.  The cold-sealed
   `BalabanCMP89CenteredPeriodicL1ResidueSum` additionally retains decay in a
   centered residue representative, which is the right substrate for each
   image branch.  The remaining work is the centering/distance dictionary
   from reflection images to the physical source separation, not a new
   summability theorem.

   In lattice units, one coordinate of the printed reflection orbit has the
   two branches

   ```text
   2*k*m + x'              and              2*k*m - x' - 1,
   k : Int.
   ```

   The `-1` is the printed `-xi` after rescaling by `xi`.  Thus there are
   `2^d` parity branches, but every branch still contains an infinite
   `Int^d` translation sum.  A valid endpoint is a `2^d` factor multiplying
   the sealed signed-lattice geometric sum (or a sharper disjoint-orbit
   theorem); `2^d` alone is not the image-series cost.  The odd/even identity
   in the cross-branch equation is the natural duplicate guard.
8. Derive the three action bounds and the common Eq. (3.42) certificate from
   that one value bound.
9. Supply an exact carrier dictionary from the source rectangles/cubes to the
   cells used by the CMP96 parametrix.  If the current support thickening is
   retained, prove a comparison theorem; do not call it a rectangle by name.

Only after steps 1--9 may CMP89 Lemma 2.4 or Eq. (2.42) feed the physical
regional certificate.

A repository search at the 2026-08-30 checkpoint found no existing
source-facing CMP89 rectangular active-region type: the current occurrences
of `rectangle` concern unrelated rectangular linear maps or potentials.
Consequently step 1 is a real construction task, not an adapter waiting to be
discovered.  The construction must expose coordinate intervals and block
units; an arbitrary equivalence onto `ActiveGaugeRegion.Site` is not an
acceptable rectangle dictionary.

The endpoint convention is fixed by the same primary source, not by memory.
CMP89 Eq. (1.1), printed page 572, defines every unit block by
`y_mu <= x_mu < y_mu+1`; the large blocks are defined identically with `M`
in place of one.  Thus a rectangle built of unit blocks has lattice sites
`0 <= n_mu < m_mu`, while the inclusive typography on page 584 is the
geometric envelope.  This agrees with the printed images `-n-1` and
`2*m-1-n` and fixes the translation period at `2*m`, without an `m+1` site.

### Exact PRE-VALIDATION source gate now present

The following modules were added without claiming compiler verification:

- `BalabanCMP89NeumannReflectionOrbitAlgebra` records the two printed integer
  reflections, their two parity branches, and the exact alternating
  translation laws;
- `BalabanCMP89NeumannReflectionScaleDictionary` proves that, under the
  visible dictionaries `x'=xi*n` and `M=xi*m`, those maps are exactly
  `-x'-xi` and `2*M-xi-x'`; it keeps the printed inclusive envelope separate
  from the source-faithful half-open block carrier and proves their inclusion;
- `BalabanCMP89NeumannReflectionRepresentation` defines the infinite
  `Int^d x Bool^d` image series and packages precisely two obligations:
  summability and equality with the explicitly parameterized regional Green;
  positive side lengths are a third, geometric field and construct an
  explicit zero-site witness, so the two analytic obligations cannot be
  discharged over an empty rectangle.

The endpoint convention is therefore no longer open at this layer.  The
remaining source gate is analytic: prove summability and the exact regional
Green equality for the half-open block carrier, then transport its distance
and constants to the later physical region.

### Exact residue bridge after the representation gate

For one coordinate with `0 <= x,n < m`, subtracting a reflection image from
the observation point gives exactly two affine residue fibres of period
`2*m`:

```text
x - (2*k*m + n)       = (x-n)   + 2*m*(-k)
x - (2*k*m - n - 1)  = (x+n+1) + 2*m*(-k).
```

The direct residue `x-n` is already centered.  The centered magnitude of the
reflected residue is

```text
min (x+n+1) (2*m-x-n-1),
```

and both entries are at least `|x-n|` on the half-open carrier.  Therefore
every reflection-parity branch retains the same decay in the physical
endpoint separation.  Summing the branches costs exactly the already named
`2^d` budget, with no rectangle-cardinality factor and no extra `exp rho`
loss.  The next analytic brick should instantiate the existing centered
periodic endpoint/carry machinery coordinatewise at period `2*m_mu`, prove
these two inequalities, and only then consume the full-lattice Green bound.

This is a design derivation, not compiler evidence.  It neither proves the
multiple-reflection identity nor produces uniform `B0`/`delta0`.

## Alternative repair (new analysis, not source transcription)

A Dirichlet route remains possible only by proving an independent estimate
for the zero-extension compression, for example an alternating-image or
killed-Green representation with its own constants.  Such a theorem may not
cite the positive-reflection formula (2.42) as though it were the same
operator.  It must be labelled as a new analytic result.

## Accounting

- The running C6d cold gate, if green, certifies per-depth Dirichlet
  four-action/certificate **infrastructure only**.
- It does not produce uniform `B0`, uniform `delta0`, the physical CMP89 local
  Green, or attainment of window 15.
- Counters remain `20/41`; `TermSource = 0`; window 15 remains compatible but
  not attained.
