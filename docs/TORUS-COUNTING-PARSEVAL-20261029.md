# Counting Parseval and energy for actual finite Fourier combinations

This continues the existing flat-obstruction dossier; it is not a separate
paper or a new Fourier-analysis priority claim. Formal source:
`09f56788669f1f6aba94b7e5548b2a1a941c79ce`, based on main
`f99fdbb6cb4624ea706ccde7b3aba21279b66a25` after integration of PR89.

For a finite abelian group G and actual complex additive characters chi,psi,
the module derives the counting Gram sum

    sum_x conjugate(chi(x))*psi(x) = |G| if chi=psi, and 0 otherwise.

The proof identifies the summand with the character psi-chi, using the
derived unit norm of finite-group character values. Mathlib's finite-character
sum then proves orthogonality; no Gram or inner-product hypothesis is supplied.

For an injective family chi_i and F(x)=sum_i c_i chi_i(x), the resulting
pairing identity gives the actual counting-measure Parseval formula

    sum_x ||F(x)||^2 = |G| sum_i ||c_i||^2.

The family used on the centered torus cube is explicitly constructed, and its
injectivity follows from the previously proved no-aliasing result when2R<n.
Thus the concrete specialization has factor n^d, not an assumed norm constant.
This concerns complex-valued profiles (two real internal coordinates), and
does not double-count a real scalar Fourier basis.

The derivative is the synthesis with coefficients c_i*(chi_i(a)-1). Applying
the derived Parseval formula to those coefficients proves

    Eplus(F,a) = |G| sum_i ||c_i||^2 ||chi_i(a)-1||^2.

Summing over steps and using the established backward/forward reindexing gives
the exact one-component scalar-stencil energy for all these combinations.
The torus-cube endpoint uses the actual coordinate unit steps. The ambient
Pi infinity norm is never substituted for counting L2. This removes the
single-character restriction of the preceding module.

The coefficient presentation is explicit. Connecting it to every member of
the old `centeredFourierBand` submodule, the quantitative multiplier bound,
the real internal-plane embedding and the actual physical cochain operator
remain integration obligations. Naming the scalar stencil similarly to a
physical energy does not prove their equality. No hRpoly source or physical
mass gap follows; PR29 stays20/41 and TermSource=0.

## Why the physical-spacing exception matters constructively

The following is a companion **on-paper** consequence, not a Lean claim about
PhysicalGaugeCochains. Use the same periodic flat Hodge symbol derived in
`FLAT-COARSE-RANK-OBSTRUCTION-20261029.md`, with q=d*m real components,
n=L*Nprime, L,Nprime>=1. At physical spacing eta=1/L the energy is L^2 times
the unit-spacing energy. Its nonconstant eigenvalues are bounded below by

    g = 16/(Nprime^2), independently of L.

For n>=2, any nonzero frequency has a coordinate of centered residue magnitude
between1 and n/2. Its sine magnitude is at least sin(pi/n)>=2/n, from the chord
bound sin(t)>=2t/pi on[0,pi/2]. Consequently
4L^2 sum_j sin^2(pi*k_j/n)>=16L^2/n^2=g. This is a finite-volume bound; no
large-volume limit was taken. For n=1 there are no nonconstant modes.

Let P0 be the orthogonal projection to the q-dimensional constant-field space.
It is possible to choose a rank-q measurement C into the usual coarse output
of dimension q*(Nprime)^d with

    ||C A||^2 = ||P0 A||^2.

Explicitly, identify the components at each site with R^q, let
v=n^(-d/2) sum_x A(x), and map v isometrically to the constant coarse fields
by giving each coarse-site component the value v/(Nprime)^(d/2). The coarse
counting norm is ||v||, while ||v||^2 is exactly the norm square of P0 A.
This map is allowed here because we are designing an arbitrary measurement;
no claim of locality or equality to the existing block average is made.

Constants have zero flat energy. Orthogonality of P0 and its complement now
gives, for every real field A,

    <A,L^2 K_unit A> + g ||C A||^2 >= g ||A||^2.

For n=1 the measurement repairs the entire constant field and the same
inequality holds. If q=0 the field space is zero and the inequality is vacuous.
Thus the fixed-output-dimension obstruction at unit spacing cannot be
promoted to an impossibility theorem at fixed physical volume: there is this
explicit small-rank repair in the unrestricted flat periodic model. Its
constant decays like Nprime^-2 when the physical volume grows; it proves no
infinite-volume Yang-Mills gap. Background fields and restricted domains require
their own proofs. This observation reinforces the existing exception rather
than contradicting the correctly scoped unit-spacing no-go.

The finite-torus spectrum is classical; a primary reference is Lin, Wan and
Zhang, [arXiv:2403.06105v1](https://arxiv.org/html/2403.06105v1). The repository's
one-cochain symbol calculation is the needed specialization; a scalar graph
spectrum alone is not an identification of the physical cochain operator.

## Model assessments and review context

Run018 failed at sourceac04a95c: automatic sum expansion reversed the two
coefficient indices, and uncontrolled simplification obscured the Gram sum.
The equality condition in the character-sum formula also needed explicit
handling. Run019 atd7ce00a1 fixed the sum-order issues; rewriting the condition
inside an if-expression failed because its concrete Decidable instance depends
on the original proposition. The final candidate splits the equality cases
and simplifies each original branch. The mathematical statements and six-report
oracle criterion remained unchanged. Both failed complete packages are retained.

Source/verification status must be read from the exact run records below;
failed builds do not certify individual downstream declarations. This same
Codex chat supplied the proof and checks; no independent model assessment,
human peer review, score, acceptance or new publication is claimed.

Run020 verified the exact source09f56788669f1f6aba94b7e5548b2a1a941c79ce
in a fresh own Colab CPU/high-RAM clone,19:51:56.674664-19:54:54.033737 UTC
on29October2026. All nine steps exited zero. Six direct oracle reports contain
exactly `propext`, `Classical.choice` and `Quot.sound`; the pairing theorem is
also checked as their dependency. Complete ZIP SHA256:
`4bb251476a49a21cbe7df1f37166896fda2a62bbfb58b750981ffe94ab40a796`.
All twelve manifest entries, two source hashes, nine child exits and six
reports were checked. Target `.olean` SHA256:
`8a4946f81d52ccfca6edcf6540c89934edc3ff8299248e62932eb42b98af204e`;
raw oracle log SHA256:
`9adfd237fb435476ab0c4314ad06f22397735246712c21a859a9e727da2da111`.
The runtime released automatically and reconnect was observed. No GPU,
Windows Lean/Lake or shared runtime was used. Compute units and the additional
allocation duration were not measured.

The complete first package was preserved before requesting a second fresh
same-SHA reproduction. Separate run records determine whether the two-clone
reproduction condition is closed; it is not implied by one successful build.

Run020b executed the unchanged prepared notebook in a newly allocated own
CPU/high-RAM runtime,19:55:56.723081-19:58:36.607366 UTC. Its full ZIP SHA256 is
`45874010ee2862bd819101fde449cf6c95877d0af2fe1b7389366c8f2faba705`.
All nine steps and six reports passed; twelve manifest entries and both source
hashes were checked. Source SHA, target `.olean`, raw oracle log and source
manifest hashes match020 exactly. Thus the two-fresh-clone requirement is
closed for this exact module at09f56788. The second runtime released and
reconnect was observed. This remains execution reproducibility, not independent
scientific review or a terminal audit of the whole repository. The companion
physical-volume repair above remains an on-paper argument, not an endpoint
proved in this Lean module.
