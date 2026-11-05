# Cycle obstructions inside the actual divergence-zero flat family

This analytic bridge closes the explicitly retained limitation of the existing four-cycle counterexample: that earlier finite result had not been embedded into the actual physical divergence-zero domain. It does not refute the existence of other rectangular partitions or the original optimal-rank question. No original Schur-complement principle, interacting/continuum gap, new paper or inherited review is claimed.

## Exact transport, with constructed maps

Let D>=3, Nc>=2, n>=3, X=(Z/nZ)^D and h=D(Nc^2-1). Choose a unit vector T in the real internal Hilbert space (dimension Nc^2-1) and the physical component j=2, distinct from coordinate1. For a real cyclic vector u=(u_t), define the ACTUAL cochain

    (J u)_2(x)=u_(x1) T; all other components zero.

This is an injective real-linear map. Its actual backward divergence is zero: the only possibly nonzero term differentiates component2 in coordinate2, where it is constant. No divergence-free comparison space is assumed. The norm is n^(D-1) sum_t u_t^2.

For any positive cyclic alpha_t, set the original componentwise repair weights w(i,x,l)=alpha_(x1)-1 for ALL derivative and physical-component indices. The existing actualTotalStiffness_energy identity (YangMills/RG/ActualPacketSupportEnvelope.lean:33) identifies the actual flat Hodge plus repair form with

    E_a(A)=sum_(x,i,l) alpha_(x1) ||A_l(x+e_i)-A_l(x)||^2.

Consequently E_a(Ju)=n^(D-1) sum_t alpha_t (u_(t+1)-u_t)^2. This uses the actual shared scalar total coefficient family; it makes no assertion about an interacting Hessian. No new Lean execution is claimed.

Given a partition I_1,...,I_r of the first cyclic coordinate into intervals, construct rectangles B_(b,y)=I_b x {y}, for every transverse y in (Z/nZ)^(D-1). These actual nonempty disjoint rectangles cover X. For each physical/internal scalar coordinate take the normalized mean on every B. The output dimension is h r n^(D-1); we do NOT claim this is an optimal observation or a rank obstruction against all partitions. Direct summation gives

    ||C_P Ju||^2 = n^(D-1) sum_b (sum_(t in I_b) u_t)^2/|I_b|.

In particular J transports the actual cycle block kernel into the actual physical divergence-zero block kernel.

There is also an all-field converse for quadratic inequalities. If the cyclic block-kernel inequality E_alpha(v)>=c||v||^2 holds, apply it separately to EVERY transverse fibre and internal/physical scalar coordinate of A in ker C_P. The remaining transverse edges are nonnegative. Hence E_a(A)>=c||A||^2 on the entire cochain kernel. Conversely any such bound on the physical divergence-zero kernel applies to Ju. The same fibrewise argument proves equivalence of the cyclic and all-cochain inequalities E+K||C||^2>=c||.||^2, while the physical inequality implies the cyclic one by J. Thus the kernel bound and the fixed-map quadratic-penalty obstruction transport exactly, rather than merely by a dimensional analogy. Transverse singleton factors are essential to this fibrewise proof; no claim is made for full transverse blocks.

## Actual admissible four-cycle and strict fixed-penalty failure

Take n=4, alpha=(1,6,4,1), I_1={0,1}, I_2={2,3}. The spatial mean is mu=3, 1<=a<=2mu, and for p=D/2 the ORIGINAL normalized moment is exactly

    M_D = (2*3^p + (1/2)^p + (3/4)^p)/4 < infinity.

Thus the example belongs to the stated bounded critical-moment scalar class (for M>=M_D). These are actual coefficients, not an assumed moment or a changed energy. Its fixed finite size does not disprove an asymptotic rank order.

For v=(x,-x,y,-y), direct expansion gives

    E_alpha(v)=11x^2+14xy+23y^2,  ||v||^2=2x^2+2y^2,
    E_alpha(v)-(19/5)||v||^2
      =(17/5)(x+(35/17)y)^2+(84/85)y^2 >=0.

Transport proves this kernel bound on ALL actual cochains, hence also on the physical divergence-zero kernel. For u=(19,-9,-5,-5)/14, exact evaluation gives

    E_alpha(u)=52/7, ||u||^2=123/49, ||C_I u||^2=25/49,
    E_alpha(u)+(19/5)||C_I u||^2-(19/5)||u||^2=-6/35.

Therefore the constructed divergence-zero field Ju has defect -(6/35)4^(D-1)<0 for the actual normalized rectangular mean map. A kernel lower bound does not imply the SAME fixed penalty, even in this actual bounded-moment physical family. All relations above are exact, not spectral numerics.

## At the sharp kernel endpoint, no finite quadratic penalty repairs this map

Put s=sqrt(85), c_*=(17-s)/2. Since 9<s<10, c_*>0 and 13-s>0. For every kernel vector the defect is

    E_alpha(v)-c_*||v||^2 = (s-6)(x+7y/(s-6))^2 >=0.

The nonzero kernel vector v_*=(7,-7,6-s,s-6) attains equality. The transport establishes the sharp endpoint on the full actual kernel as well as the physical divergence-zero kernel. This is not a strict-margin theorem.

For p_delta=(delta/2,delta/2,-delta/2,-delta/2), v_* is orthogonal to p_delta, C_I v_*=0, and ||C_I p_delta||^2=||p_delta||^2=delta^2. Edgewise expansion yields for every finite K>=0

    E_alpha(v_*+p_delta)+K||C_I(v_*+p_delta)||^2
       -c_*||v_*+p_delta||^2
       =(7+K-c_*)delta^2-10(13-s)delta.

The denominator q_K=7+K-c_* is positive. Choosing delta=5(13-s)/q_K gives the STRICT negative value -25(13-s)^2/q_K. Lift this ACTUAL vector by J: divergence remains exactly zero, and the complete defect is multiplied by4^(D-1). Thus no finite K works for this SAME map at this sharp kernel endpoint, despite kernel coercivity on every physical zero-block field.

It also defeats a penalty Phi satisfying Phi(z)<=K||z||^2 only near zero. Fix the negative witness for K and scale it by any sufficiently small nonzero real t. The divergence-zero condition is unchanged, C is linear, and the upper quadratic defect is t^2 times the same strictly negative number. Both the field-radius and observation-radius conditions can be met by scaling. If an upper-bound constant was negative, replacing it by max(K,0) only makes the bound weaker, so K>=0 loses no case. This does not rule out a different observation map, a strict-margin construction with larger penalty, or the original coefficient-adapted optimal-rank problem.

## What has actually changed

The scalar square identities and negative vectors were already preserved in research-consolidation/critical-inverse-moment-appendix.tex, including its analytic equality example. The new work is the explicit physical embedding, observation transport, all-kernel fibre proof and original coefficient/moment audit. The earlier ten Lean cycle endpoints remain evidence for their own scalar statements only; this new lift is analytic, not Lean certified. The earlier report's historical limitation must remain verbatim for its exact PDF. This source provides later evidence; it does not rewrite that report or transfer its rating. Frozen reviewed PDF eb4df3 and the11-page companion6fcb0a are unchanged.

Classical algebraic context: Carlson, Haynsworth and Markham, A Generalization of the Schur Complement by Means of the Moore-Penrose Inverse, SIAM J. Appl. Math.26(1),169-175(1974), DOI10.1137/0126013. The publisher abstract and bibliography were inspected; the full paywalled article was not read. Its classical context is not a priority claim for this explicit embedding. The direct finite proof above is provided in full. An exhaustive novelty determination has not been made. The rejected alternative of repeating separated-defect/weak-line detours was found already closed in units124/125/130 before any new result was claimed.

## Model assessments and review context

Prepared and analytically self-audited by this ongoing GPT-6-based Codex agent, with extensive previous participation. Actual served backend identifier/reasoning setting is unexposed. No independent, external or human assessment, numerical score, new PDF or new Lean proof is claimed. Any subsequent finite diagnostics apply only to their exact source and listed dimensions, not to the universal embedding theorem by themselves.

The original single active critical-rectangle question remains open. This unit closes one physical-domain counterexample bridge. It does not restart the stopped common-refinement route, alter PR29's20/41 or TermSource0, or eliminate a substantive interacting coefficient hypothesis.

## Exact finite diagnostics at the stated source

Source9596d5a9e60b60f0b25409532aae3562df79bb89 ran only in this chat's exclusive Colab Linux CPU/high-RAM runtime. For D3 and D4 it evaluated the actual cochain values at every vertex, ALL original forward edge/component occurrences, every backward divergence and every actual rectangular normalized-mean squared norm. The fixed19/5 defects are exactly -96/35 and -384/35, with divergence identically zero. At the sharp endpoint it checked K=0,1,100 in each dimension using exact rational-pair arithmetic in Q(sqrt85); all six defects equal the derived strictly negative expressions. Both modes accepted all8 cases, detected2 actually changed fields by their nonzero divergence, exited0 and produced byte-identical JSON. Zero assert nodes; real decimal exit sentinels retained. No local Windows computation. This is same-author finite diagnostics, not independent reproduction or the universal proof. Runtime disconnected after full recovery. Archive7685bytes, SHA256f06b55dc5e6615ec645092bf58a1e4a62564fa396ba100f18007b1b6aa562148.

## First formal lift stage, with explicit remaining obligations

Unit143 compiled PhysicalCycleLift.lean at784236ea24a74728b49516cf5acfdf03aad45c8e in a fresh exclusive Colab clone. Five endpoints certify the constructed lift's divergence zero, injectivity, counting mass, physical norm and selected-coordinate normalized fibre mean, with only standard propext/Classical.choice/Quot.sound dependencies. Actual oracle validators passed in normal/optimized modes and each rejected3 changed oracle outputs. This is one successful clone; paired terminal reproduction is pending. The actual energy transport, FULL observation squared-norm identity and final physical negative-defect theorem are still analytic, not Lean verified. See FORMAL-STAGE143.md and the complete evidence package. This does not change any exact-PDF review or assessment.

## Paired reproduction of the first five lift endpoints

Unit144 completed the required second fresh Colab clone at the SAME784236ea24a74728b49516cf5acfdf03aad45c8e source. Actual recovered source/olean/oracle/validator hashes match across both separate sessions. Thus terminal paired reproduction is complete for those5 partial lift endpoints only. Full actual energy transport, entire observation squared norm and final physical penalty-counterexample theorem remain analytic. This milestone is not an independent review or an assessment of either PDF. See FORMAL-PAIRED144.md and paired-lift144.json. No third identical run is needed.
