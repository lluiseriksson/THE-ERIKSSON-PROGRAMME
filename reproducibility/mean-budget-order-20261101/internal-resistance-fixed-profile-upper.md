# Internal resistance budgets imply the block-observation upper bound

Unit097,2026-11-02. Analytic positive counterpart to the period-two refutation, inside the same existing mean-budget dossier. Base d4ee549d4e76359e8cf6487fa6038c4cfddedc3f. This is a derived coefficient-to-Poincare implication, not an assumed Poincare certificate or a new Lean endpoint. No PDF/publication claim.

## One-dimensional coefficient theorem

Let l>=2, u_0,...,u_(l-1) belong to a finite real Hilbert space, and a_s>0 be the actual conductance of the internal edge s to s+1,0<=s<l-1. Write r_s=1/a_s and S=sum_s r_s. Weighted Cauchy-Schwarz on the unique internal path gives, for a<b,

 ||u_b-u_a||^2 <= (sum_(s=a)^(b-1) r_s)
                          *(sum_(s=a)^(b-1) a_s||u_(s+1)-u_s||^2).

For vector values this follows by the triangle inequality and scalar Cauchy-Schwarz applied to sqrt(r_s) and sqrt(a_s)||diff_s u||; r_s*a_s=1. The exact counting variance identity is

 sum_a||u_a-mean(u)||^2=(1/l)sum_(a<b)||u_b-u_a||^2.

After substituting the path inequality, the coefficient of the weighted energy on edge p-1 to p is

 H_p=(1/l)sum_(a<p<=b) sum_(s=a)^(b-1) r_s,

where1<=p<=l-1. Each path resistance is at most S, there are exactly p(l-p) crossing pairs, and p(l-p)<=l^2/4. Therefore

 H_p <= p(l-p)S/l <= l*S/4.

It follows that

 sum_a||u_a-mean(u)||^2 <= (l*S/4)sum_s a_s||diff_s u||^2.     (1)

In particular the explicit coefficient condition

 sum_s 1/a_s <= rho*l/m,     rho>0,m>0,                     (IR)

gives the proved constant rho*l^2/(4m). For l=1 the residual is zero and no coefficient condition is required. For l=2 the exact constant is1/(2a_0): our l*S/4=S/2 agrees with it. Constant coefficients a_s=m give the safe bound l(l-1)/(4m); the earlier sharper constant floor(l^2/4)/(2m) is not claimed here. This loss does not change the observation order.

## Tensorization and the actual finite flat operator

Fix D>=2,Nc>=2,c>0,m>=1,rho>0 and h=D(Nc^2-1). Total actual coefficients a_(i,x,j)=1+w_(i,x,j) are strictly positive. Negative repair values w are allowed provided a>0; if the dossier additionally requires w>=0, impose a>=1 explicitly. No upper arithmetic-mean hypothesis is needed for the following implication; if upper means<=m are also required, the proof still applies to that subclass.

Partition each cyclic coordinate of Z/n into consecutive intervals of length at most l. Product boxes B have side lengths l_i<=l, including short final intervals. For EVERY box, derivative direction i, component j and fixed other coordinates in B, require (IR) for the actual internal i-directed fibre edges when l_i>=2, with the SAME rho,m. No wrap edge between boxes occurs in this condition. For l=n the final cyclic wrap edge is still omitted from the interval path; its positive energy may be discarded.

Uniform product-measure variance tensorization gives

 sum_(x inB)||U_j(x)-mean_B U_j||^2
 <= sum_i sum_(othercoordinates) sum_(x_i)
               ||U_j(x)-mean_(x_i)U_j||^2.

One elementary proof is induction on the coordinate count: split variance into expected fibre variance and variance of the fibre mean, apply induction to the latter, then apply Jensen to its remaining-coordinate differences. The law-of-total-variance and conditional Jensen step produce the displayed original-fibre variances; no averaging of heterogeneous weights is substituted. Apply(1)/(IR) separately to each original fibre BEFORE summing, obtaining

 sum_B sum_j residual_(B,j)^2
 <= rho*l^2/(4m) * sum_(internal actual edges i,x,j)
                                      a_(i,x,j)||diff_i U_j(x)||^2
 <= rho*l^2/(4m) Q_w(U).                                    (2)

The last equality/comparison uses the existing actual componentwise finite flat Hodge identity, formally established at dfd49d0b0730a4d36f58a4cbb7a17d6a41fb60bc, and positivity on omitted edges. This NEW path/tensorization/observation adapter has not been Lean-compiled. The theorem applies to every cochain, hence also to actual divergence-zero fields. Hilbert-valued application covers all adjoint coordinates without multiplying the constant by h or D.

Define C(U)_(B,j)=sqrt(|B|)*mean_B U_j, retaining each actual adjoint coordinate in an ordinary Euclidean output. Its dimension is

 q=h*ceil(n/l)^D.

Exact orthogonal decomposition is ||U||^2=sum_B,j residual^2+||C(U)||^2. If

 c*rho*l^2 <=4m,                                            (3)

then(2) proves c||U||^2<=Q_w(U)+c||C(U)||^2 globally. Thus linear C, Phi(y)=c||y||^2,K=c supply the ORIGINAL nonlinear local data, with any positive neighbourhood radii, rather than assuming them. For l=1 the residual is exactly zero, so the same conclusion holds without(3).

## Explicit mean-budget order, conditional on actual fibre coefficients

Set t=2sqrt(m/(rho*c)) and l=max(1,min(n,floor(t))). The coefficients must satisfy(IR) on the partition just specified; this is an explicit sufficient hypothesis, not something inferred from arithmetic means. For t<1 use the singleton identity. For t>=1, floor(t)>=t/2. If l=n then q=h. If l<n then

 ceil(n/l)<=1+2n/t=1+sqrt(rho*c)*n/sqrt(m)
                         <=1+sqrt(2rho*c)*n/sqrt(1+m),

since m>=1. For t<1, m<rho*c/4 and

 q=h*n^D <=h*(1+rho*c/4)^(D/2)*(n/sqrt(1+m))^D.

Because sqrt(1+rho*c/4)<=1+sqrt(2rho*c), all cases yield

 q <= h*(1+sqrt(2rho*c))^D
                    *max(1,(n/sqrt(1+m))^D).                (4)

At n=1 only singletons occur; the same bound holds and no fibre edge is tested. Short final intervals use their own l_i in(IR), bounded by l in(2). No divisibility assumption is concealed in(4).

## Strict weakening and relation to the refutation

Pointwise relative ellipticity a>=alpha*m implies(IR) with rho=1/alpha, because a fibre has l_i-1 edges. The converse fails uniformly over growing boxes, even with nonnegative repairs and exact arithmetic directional means m.

For an explicit family let l>=3, L=l-1, n a multiple of l. In every length-l coordinate interval choose one internal edge a=m/L and the other L-1 internal edges a=m*(L+1)/L. Assign each boundary edge a=m, for every derivative direction and field component, with coefficients depending on the corresponding coordinate modulo l. Internal edge arithmetic sum is m/L+(L-1)m*(L+1)/L=mL, so the full periodic directional arithmetic mean, including one boundary edge per period, is exactly m. Every fibre in this aligned partition has

 S=L/m+(L-1)*L/[m*(L+1)]<2L/m<2l/m.

Thus rho=2 works. The relative minimum is1/L, tending to0 as l grows; no fixed alpha>0 is implied. Taking m=c*l^2 ensures(3) for rho=2, and for sufficiently large l ensures m/L>=1, so w>=0 also holds. The chosen l here is any admissible block size satisfying(3), not necessarily the optimized floor(t) partition in(4); the example establishes strict weakness of the coefficient criterion, without asserting it meets every other partition. No unsupported equivalence is claimed.

Conversely the period-two profile of unit096 has at least floor((l_i-1)/2) internal unit-conductance edges on a long fibre in direction1, so S>=floor((l_i-1)/2). For a block scale l_i comparable to sqrt(m), it cannot satisfy(IR) for fixed rho as m grows. The pathological slow pair-constant modes are therefore excluded for a proved reason: their series resistance is too large. Microscopic l_i=2 can accidentally align with heavy edges and meet(IR), but then rho*l_i^2/(4m) controls ONLY residuals inside those tiny blocks; observation rank remains large. No contradiction with unit096 follows from choosing such a partition.

## Primary-source comparison and next falsifier

Doyle and Snell, Random walks and electric networks, author-hosted2006version derived from their1984Carus monograph, https://math.dartmouth.edu/~doyle/docs/walks/walks.pdf , section1.3.4, PDFpage43/printed43: series resistances add; inspected directly. Chihao Zhang, AA2025Lecture8, Theorem1 and proof, https://chihaozhang.com/teaching/AA2025/lectures/lec8/lec8.html : classical variance tensorization; inspected directly. These sources supply classical context, not a priority claim for this note. The explicit counting constants, component-dependent fibre condition, actual field adapter and original nonlinear observation witness are derived above. No independent/new homogenization result is advertised. No source prose or figures are reproduced.

One active question remains the same coefficient-to-Poincare route: can the internal-resistance condition be formally realized for the actual directional/component indices and a nondivisible partition, without assuming an abstract certificate? Hypotheses: actual positive coefficients and explicitly summed(IR) on the chosen partition. Mechanism: prove(1), tensorization, exact normalized means and dimension count, then adapt the actual Hodge identity. Falsifier: normalization/short interval or component-dependent weight counterexample to(2); especially a hidden change of partition between(IR) and(4). Abandon after three substantive units without a proof/new useful falsifier; current analytic implication is substantive, but formal implementation remains blocked by own Colab access and must not be called verified.

## Model assessments and review context

FIRST exact-note source assessment6/10 by the same preparing Codex agent. Actual served backend identity and effort unexposed. No independent review, human peer review, acceptance, PDF score or inherited grade. Qualitative rubric0-10: derivation7, originality3, dossier relevance7, verification maturity4; overall6 is a judgement, not a calibrated probability or average. Proof audit: vector Cauchy-Schwarz, exact crossing-pair count, l1/l2, counting/product factors, coefficient-dependent fibre placement, omitted-edge positivity, normalized means, c*rho*l^2<=4m, floor/singleton/n1/short blocks, exact-mean strict-weakness example and partition distinction. No numerical/oracle run.

O1. New path, partition, real output count and field adapters are analytic, not Lean-compiled.
O2. Series-resistance/Cauchy-Schwarz/tensorization are classical; independent publication novelty unestablished.
O3. (IR) is an additional sufficient coefficient condition, not a hypothesis eliminated from the original mean-only claim or a necessary condition.
O4. The same partition must be used for coefficient tests and output dimension; the weakening example is an admissible-partition example, not proof for every optimized partition.
O5. Constants are safe and not sharp; the condition is imposed on every original fibre/component and may be costly to establish in an interacting model.
O6. Exact-source self-assessment supplies no independent validation, new PDF review or editorial acceptance.
O7. Finite flat componentwise energy only; no physical interacting/continuum mass gap. PR29 remains20/41,TermSource=0; no new paper/deposit.