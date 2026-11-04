# Two weak neighbours obstruct the supplied-cube decomposition

Unit118, 4 November2026. Companion to units116-117 in the critical
rectangular-mean dossier. Analytic counterexample to the proposed
coefficient decomposition, with a successful actual rectangular partition
for the SAME family. No separate paper or new PDF/assessment.

## 1. Exact profile, fixed critical moment

Fix D>=3, c>0, beta>=1, p=D/2, Nc>=2 and h=D(Nc^2-1).
For arbitrarily large integer n>=3 take m=n on X=(Z/nZ)^D.
Let z=0, let W={e_1,-e_1}, f=2/n^D, and set

    a(x)=1  for x in W,
    a(x)=A=(n-f)/(1-f) otherwise.                  (1)

The two weak vertices are distinct, neither equals z. Since f<1/2,
n<A<=2n: the upper inequality is equivalent to
f(2n-1)<=n, which follows from f<1/2. Hence 1<=a<=2m and
f+(1-f)A=n exactly. Moreover

    mean((m/a)^p)
      = f n^p + (1-f)(n/A)^p
      < 2 n^(-p)+1-f <= 2.                       (2)

The last inequality holds for n>=3,D>=3. Thus the original critical
class has fixed M=2, uniformly in n. No executable arithmetic is needed.

Choose n also so large that

    n>beta, n>8 beta/c, n>1+8/c, n>=c.           (3)

These conditions are compatible for every fixed c,beta. Since
c n(n-1)/4>2n>=A, ALL vertices have coefficient strictly less than
the strong-complement threshold in units116-117.

## 2. No allowed supplied-cube family exists

Suppose that some disjoint nonwrapping integer cubes S_k, in ANY one
translated coordinate root, satisfy the unit116-117 conditions

    c L_k(L_k-1)/4 <= a(x) <= beta L_k^2 (x in S_k),
    a(x)>=c n(n-1)/4                   (outside their union).

By (3) their union must cover X, in particular z. Consider a cube S
containing z and let its integer side be L.

If L=1, its upper scale condition requires A<=beta, contradicting
A>n>beta. If L>=2, the coordinate interval in direction1 containing z
also contains at least one of its two torus neighbours e_1,-e_1.
Indeed an interval of consecutive residues of length>=2 has a neighbour
of every contained residue on at least one side. This remains true when
z is at an endpoint of the chosen root, and when L=n. Because S is a
Cartesian product, keep all other coordinates equal to those of z; the
corresponding weak neighbour lies in S. Thus its lower scale condition
implies c L(L-1)/4<=1. For L>=2, L(L-1)>=L^2/2, so L^2<=8/c.
Applying the upper scale condition at z yields

    A <= beta L^2 <= 8 beta/c < n < A,

a contradiction. No cube containing z is admissible, even without
disjointness. Thus overlap, cube order, number of cubes, stopping rule,
or translation of the common root cannot repair this decomposition.

For every fixed beta the obstruction holds for arbitrarily large n with
the SAME fixed moment bound2. Allowing beta to grow with n would change
the theorem's uniform constants and does not eliminate the hypothesis.
The failed implication is from the original moment to the simultaneous
pointwise upper/lower cube scales AND the n-scale strong complement.
Neither the BSP geometry of117 nor its conditional theorem is refuted.

## 3. The original rectangular target succeeds on this family

It is essential not to mistake section2 for an all-partition obstruction.
Here is an actual partition with the original target order and fixed
penalty K=c. Let

    ell=min(n, floor(2 sqrt(A/c))).

By (3), A>=c, hence ell>=1. Split every coordinate into consecutive
integer intervals of length<=ell. There are ceil(n/ell)^D grid boxes.
For each of the two vertices in W, refine its current box to its singleton
plus at most2D rectangles, assigning all other points by their first
coordinate differing from that vertex. Delete empty rectangles. This is
an actual disjoint partition; each isolation increases the leaf count
by at most2D. Keep earlier singletons when performing the second cut.
Every nonsingleton output box now has a=A everywhere and maximal side
<=ell. Thus

    N <= ceil(n/ell)^D + 4D.                     (4)

On every strong output rectangle R, the unit116 path/product variance
bound gives

    c Var_R(u) <= [c ell(ell-1)/(4A)] E_(a,R)(u)
               <= E_(a,R)(u).

Weak singleton residuals are zero. Summing disjoint retained original
edges and the exact normalized-mean decomposition gives, for ALL cochains,

    c ||U||^2 <= E_a(U)+c ||C_P U||^2,
    (C_P U)_(R,j)=sqrt(|R|)mean_R U_j, dim F=hN. (5)

No kernel-only shortcut or divergence-preservation assumption is used.

If ell=n, the grid count is1. Otherwise, because A/c>=1,
floor(2 sqrt(A/c))>=sqrt(A/c), whence

    ceil(n/ell)^D <= (1+sqrt(c)n/sqrt(A))^D
      <= (1+sqrt(c))^D max(1,n^D/A^p)
      <= (1+sqrt(c))^D max(1,n^D/m^p).

The same final bound covers ell=n. Combining (4), m>=1 and
m^(-p)<=2^p(1+m)^(-p), with T=max(1,n^D/(1+m)^p), gives

    dim F <= h [2^p(1+sqrt(c))^D+4D] T.         (6)

This is the requested order for this particular family with fixed M=2.
Here a global threshold works because only TWO weak vertices are excised;
the all-threshold growing-cluster obstruction of115 remains valid for
its different family. Neither construction is a general algorithm proof.

## 4. Verification, provenance and route decision

Analytic audit: exact mean and cap; fixed critical moment; simultaneous
large-n conditions; both torus neighbours and arbitrary root; singleton
versus L>=2 cases; no hidden disjointness dependence; all vertices below
complement threshold; actual box isolation and count; strong internal
starting-edge weights; zero weak-singleton variance; positive omitted
wrap/parallel edges; global normalized means; ell capped atn; mto1+m.
No Lean/numerical execution, Colab allocation or local mathematical script.

Primary context checked4November2026: Andres, Deuschel and Slowik,
*Harnack inequalities on weighted graphs and some applications to the
random conductance model*, https://arxiv.org/abs/1312.5473 . Its weighted
Sobolev/moment setting is background, not a citation proving the finite
profile, the cube impossibility or (4)-(6). Those are derived above using
the dossier's actual path variance. No exhaustive priority search or
originality finding; no independent AI/human review or new numeric grade.
Same preparing Codex agent, served backend/effort unexposed. No inherited
PDF assessment, new publication, deposit or acceptance.

This closes the proposed UNIVERSAL supplied-cube decomposition route by
an explicit counterexample, after three substantive scaled-cluster units.
Keep the conditional116-117 theorem. Stop trying to derive its exact
pointwise scales/strong complement from the original moment alone.
There remains ONE active original critical rectangular question; it is
neither proved nor refuted. Old stopped mass-only/Schur/global-threshold
routes and their counters are unchanged. PR29 stays20/41,TermSource=0;
the interacting/continuum physical gap is open.

Next bounded route: investigate local blocks allowing small internal
defect sets, with actual edge-energy control and a shared critical-mass
charge across scales. Any claimed method must handle BOTH this two-neighbour
family and115's growing weak cube, without assuming a rank/Poincare
certificate or paying separately for every weak point in the latter.
An original-target falsifier must still defeat EVERY allowed partition.
