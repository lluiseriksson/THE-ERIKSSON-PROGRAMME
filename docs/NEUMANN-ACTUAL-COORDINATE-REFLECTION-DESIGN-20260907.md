# Actual full-Green coordinate reflection: finite design gate

STATIC DERIVATION ONLY, not compiler evidence. Source context327a79d3e;
the common-block translation diagnostic is running separately. No new Lean
source is shipped by this note, and no counter or production label changes.

## Why the existing reflection theorem is not the endpoint

BalabanCMP89Eq246FullEndpointReflection fixes depth1, negates every momentum
coordinate and exchanges the two endpoints through the transposed solver.
It is not the required arbitrary-depth, one-coordinate, common half-cell
reflection of the literal non-transpose Green. Keep that theorem unchanged.

The inspected actual precision is diag(fine)+a*column*row, with column
u(q), row u(-q), and u_N(q) the normalized finite negative-exponential
average. The checked diagnostic1182 states u_N(-q)=D(q)*u_N(q),
where D(q)=exp(i*q*(N-1)/N), including the central mode and N=1.
For a coordinate reflection, D uses that coordinate only, not a product
over coordinates that were not reflected.

## Fix the physical scale before the permutation

Set N=L^j>0. The alias carrier is definitionally the centered vectors for
N; use the existing centered-vector Pi equivalence and the scalar residue
reflection on one coordinate. Do not use literal negation on the half-open
even carrier. The reflected alias represents -m modulo N in that coordinate
and m elsewhere. Its associated fine momentum is -q modulo2*pi*N there.
Every factor consuming this congruence needs its own period theorem.

## Six finite outputs to construct, in order

R1. A one-coordinate alias permutation, with unchanged-coordinate and
reflected-residue equations, involution and preservation of the central
alias. At arbitrary j, pin carrier and fibre explicitly; do not identify
the depth-one API with it by unproved definitional reduction.

R2. Literal symbol identities under simultaneous coordinate momentum and
alias reflection: fine'=fine, column'=D*column, row'=D^-1*row.
The half-cell finite-average phase supplies the reflected factor; the
other product factors are unchanged. Period2*pi*N handles wrapped aliases.
D is a concrete exponential and never zero. This gives entrywise
A'[P m,P n]=D_m*A[m,n]*D_n^-1, not an assumed Green covariance.

R3. Transport the solution of the literal alias equation through that
diagonal phase and permutation. Use the already constructed full-solver
domain at both momenta and the literal full-solution equation. Establish
uniqueness from its square finite matrix, not a supplied inverse identity.
The required theorem ALREADY EXISTS:
cmp89Eq246EntireAliasPrecisionMatrix_mulVec_injective, in
BalabanCMP89Eq246AliasPrecisionUniqueness. It takes exactly fine,
stabilized and row nonvanishing; surjectivity is constructed from the
literal solver and finite dimensionality gives injectivity. Its selective
cold seal is1bda3dd70, ledger1056. Do not duplicate this theorem or add a
new uniqueness hypothesis. FinePointSourceSolutionCycle demonstrates its
existing use after transporting an actual source equation; reflection
needs the additional diagonal phases, not a new uniqueness principle.

R4. Reflect both fine integer endpoints about the block centre:
S_N(x)_mu=N-1-x_mu in the selected coordinate, unchanged elsewhere.
After reindexing aliases and negating that momentum coordinate, the target
phase is target*D^-1 and the source phase is D*source. R3 cancels them
termwise. This is a two-endpoint identity for the non-transpose integrand,
not the displacement-only (2.48) kernel and not endpoint exchange.

R5. Integrate the signed momentum change over the symmetric Brillouin cube
with the literal normalization. Supply the actual change-of-variables
lemma and its measure/integrability requirements, rather than assuming
the integral invariant. The complete solver domains must come from the
same common-polistrip hypotheses on both signed slices.

R6. The required lower half-cell reflection is S_0(x)=-x-1 in that
coordinate. It equals S_N(x)-N. Apply the common BLOCK translation theorem
to BOTH reflected endpoints with integer shift -1 in that coordinate.
This is exactly where the pending five-lemma translation consumer enters.
Upper half-cell reflection then differs by an integer block translation
when the physical side is N times its block count. Cite that dictionary.

## Acceptance boundaries

The phase accounting above is a checked-on-paper algebraic design, not a
Lean theorem. It must survive R1-R6 without replacing the actual operator.
N=1, central aliases and full-period carrier sides are not removed.
Neither source-image summability nor a permutation of source images proves
the target Neumann seam. That seam and the image-series precision equation
remain M4 in NEUMANN-MIXED-BOUNDARY-CANDIDATE-20260907.md. The normalized
fine-density-to-counting factor N^-4 must still be installed exactly once.

20/41; TermSource=0; window15 compatible, not attained.

## Bounded R1 scratch preparation while translation compiles

tmp/NeumannCoordinateAliasReflectionDraft.lean constructs the one-coordinate
permutation from already sealed scalar-reflection and product-equivalence
modules; it does not import the pending translation draft. Six audit targets
cover the two product-coordinate equations, unchanged integer coordinates,
selected-coordinate residue negation, involution and finite-sum reindexing.
Explicit central-alias preservation and specialization N=L^j remain to add.
Nothing from this draft is in the running queue. Text guard only: exit0,
0.0855034s,15273984bytes observed peak RSS; compiler status NOT CHECKED.
Two local invocation mistakes (missing manifest argument, then str instead
of Path in the direct checker call) were corrected without any Colab run.
