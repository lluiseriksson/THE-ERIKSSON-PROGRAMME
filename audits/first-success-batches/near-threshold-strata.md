# A band of success-count strata with a uniform bias sign

In the common-cap setting of profile-transport.md put \(T=mn,\ k=m+h\), where \(h\ge1\). All probability comparisons in the proof use the uniform labelled \(k\)-subset law \(F\) and the probability law \(Q\) obtained by weighting this law by the canonical first-hit score. The homogeneous unbiasedness identity gives \(E_F Z=1\) on this stratum. Neither auxiliary law depends on the heterogeneous parameters.

**Theorem (a positive-width interval at fixed cap).** Fix \(n\ge2\). For all sufficiently large \(m\), for every integer
\[
 0\le h\le \frac{m}{16 n^n(4n-3)\log 2}
\]
and every vector of true task probabilities in \([0,1]^m\),
\[
 E[Z\,1_{\{S=m+h\}}]\le\Pr(S=m+h).
\]
A finite sufficient condition for \(h\ge1\) is
\(h\le\min(m/8,m/(2n^n))\) and
\((mn+1)\exp[-m/(8n^n)]\le 2^{-(4n-3)h}\).
The constants give a conservative interval and do not locate a transition. The conclusion holds on each stratum and after summation over any subset of the certified band. It leaves open the contribution of the other strata to the full tail.

**1. Sufficient comparison.** Suppose \(h\le m\). The most balanced profile at total \(k\) consists of \(h\) twos and \(m-h\) ones; denote it by \(B\). It is majorized by every profile. Every profile under \(Q\) has all counts positive. Any source profile having at least \(h\) saturated tasks (count \(n\) on each) majorizes *every* such positive profile. For prefix lengths \(l\le h\) its top \(l\) counts are maximal. For \(l\ge h\), its top \(l\) counts sum to at least \(l+h\): the cumulative excess over \(l\) is concave in \(l\), is at least \(h\) at \(l=h\), and equals \(h\) at \(l=m\). A positive target profile has at most \(h\) excess at any prefix. Consequently, if \(F(X<h)\le Q(B)\), where \(X\) counts saturated tasks, the high-saturation mass under \(F\) can supply all non-\(B\) demand; the remaining source mass supplies \(B\). Under a coupling supported on majorization, the symmetric means of the heterogeneous odds give the desired comparison (and continuity handles the endpoints).

**2. The full-law exceptional probability.** In a homogeneous full experiment at \(p=k/T\), \(S\) is binomial with mode \(k\), so its atom there is at least \(1/(T+1)\). Prior to conditioning, \(X\) is binomial with mean \(\mu=mp^n\ge m/n^n\). If \(h\le m/(2n^n)\), then
\[
 F(X<h)\le(T+1)e^{-\mu/8}\le(T+1)e^{-m/(8n^n)} .
\]
For instance, apply Markov to \(2^{-X}\) at \(\mu/2\): \(E2^{-X}\le e^{-\mu/2}\) and \((1-\log2)/2>1/8\).

**3. The weighted-law balanced mass.** At total wait \(s\) let \(R=m(n-1)-s\). Every successful wait vector of that sum has \(\binom Rh\) completions and receives the same score. As a result,
\[
 Q(s)=\binom{m+s-1}{s}\binom Rh/\binom Tk.
\]
This is also the probability that position \(m+s\) is the \(m\)-th selected slot in a uniform \(k\)-subset of \(T\) ordered slots. Conditional on the waits under \(Q\), the \(h\) extra successes form a uniform subset of the \(R\) unseen slots; each task contributes at most \(n-1\) unseen slots. Put \(L=2(n-1)h\). Under the ordered-slot representation the event that the last \(L\) slots are unselected ensures \(R\ge L\). Its probability is at least \(4^{-L}\): throughout the sequential inspection the fraction of remaining unselected slots is at least \((T-k-L+1)/T\ge1/4\) for \(h\le m/8\), \(n\ge2\). On \(R\ge L\), even after any \(j<h\) different tasks have been used for extra successes, at least \(R-j(n-1)\ge R/2\) slots belong to unused tasks. Thus the probability the extras all occupy different tasks is at least \(2^{-h}\). This is precisely the required profile \(B\). We obtain \(Q(B)\ge 2^{-(4n-3)h}\). Combining the bounds proves the finite criterion. In the asserted band, \(2^{-(4n-3)h}\ge e^{-m/(16n^n)}\), and \(mn+1\le e^{m/(16n^n)}\) eventually for fixed \(n\). The case \(h=0\) follows directly by the unique all-hit profile.

**A cap-uniform result for a fixed surplus.** For every fixed \(h\ge1\) a finite \(M(h)\) suffices simultaneously for all caps \(n\ge2\). Put \(d=\min(n,h+1)\) and \(c_h=1/[3(h+1)^{h+1}]\). It suffices that
\[
 m\ge\max\{h,\,2h(h-1),\,\max(2h,8)/c_h\}.
\]
Under \(F\), count tasks with at least \(d\) successes. If \(n\le h+1\), each saturates with probability \((k)_n/(T)_n\ge n^{-n}\). If \(n>h+1\), prescribe \(d=h+1\) slots on one task and exclude its others from the remaining \(m-1\) selections. Summing disjoint exact-\(d\) cases gives at least \(\binom nd n^{-d}(1-1/m)^{m-1}\ge c_h\), since \(\binom nd\ge(n/d)^d\). In both cases the count \(Y\) has mean at least \(mc_h\) and variance at most its mean by conditional negative covariance of threshold indicators. Chebyshev gives \(F(Y<h)\le4/(mc_h)\le1/2\). Any profile with \(h\) entries at least \(d\) majorizes every all-positive profile: use the prefix argument from step 1, observing that no positive target count exceeds \(d\). Under \(Q\), the probability of any collision among the \(h\) extras is at most \(\binom h2\,2/(m+1)\) by a union bound and the bounded-composition pair estimate in two-extra-successes.md. Hence \(Q(B)\ge1/2\); the same matching proves the cap-uniform statement. For \(h=1\) the profile is already unique. The explicit \(M(h)\) also certifies \(h\le(1-\epsilon)\log m/\log\log m\) for sufficiently large \(m\), any fixed \(0<\epsilon<1\), uniformly in the cap.

The probability model assumes independent attempts within and across tasks, with a fixed probability per task. The band gives a theoretical statement in that experiment. No inference about an observed model or literature priority is made.
