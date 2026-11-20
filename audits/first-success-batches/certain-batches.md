# Removing batches that succeed with certainty

The common cap is $n\ge2$. Append $r\ge1$ batches with success probability one to a design with $k\ge1$ batches of arbitrary success probabilities. The full target changes from at least $k$ successes to at least $k+r$. Nevertheless **the deficit between the full target probability and the mean stopped score cannot decrease**. More precisely, if $S$ counts full-budget successes in the original $kn$ trials,
$$
D_{k+r}-D_k\ \ge\ \Pr\{k-r(n-1)\le S<k\}.
$$
Here $D_j$ is the full-budget target minus the mean stopped score for the corresponding $j$-batch design. In particular the lower bound can be used directly if $D_k$ is zero or has been bounded below. The claim is comparative and does not presume $D_k\ge0$.

**Combinatorial proof.** Given total failures $s$ before the first hits, the homogeneous score $w_j(s)$ for $j$ batches is the reciprocal of the fraction of weak compositions of $s$ into $j$ parts whose largest part is at most $n-1$. This follows by counting the compositions. In a uniform word consisting of $s$ stars and $j-1$ bars, insert a bar into a uniformly selected one of its $s+j$ insertion positions. Every resulting word has exactly $j$ preimages counted with the marked inserted bar, so the new composition is uniform. Insertion only splits a part. The fraction of compositions satisfying the cap therefore increases weakly, and $w_{j+1}(s)\le w_j(s)$ wherever the old score is defined. The added certain batches always record a first-trial hit. On each old record with any missing hit both scores are zero; otherwise $s$ is unchanged and the new score is at most the old one. In the full experiment the certain batches supply $rn$ successes. The difference of the two full target probabilities is precisely the displayed probability. Subtract the mean scores to finish.

**Consequences.** If the uncertain batches have the same interior probability, $D_k=0$ by the homogeneous negative-binomial identity, for every $k,n$. Adding any certain batch then gives a strictly positive deficit, since $S=k-1$ has positive probability. For at most two uncertain batches at distinct interior probabilities, the arbitrary-depth two-batch bound gives the same conclusion. A single batch has score equal to its observed hit indicator. More generally any certified lower-dimensional sign region lifts to higher dimensions this way. A batch with probability zero makes the whole stopped score zero regardless of the other batches.

**Stability for nearly certain additions.** Suppose the added batches instead have probabilities $1-e_j$. Couple each of their potential trials to the certain version using the same independent uniforms. The probability that the full records differ is at most $1-\prod_j(1-e_j)^n$. The full indicator has range one and the stopped score is in $[0,M]$, with $M=\binom{(k+r)n-1}{k+r-1}$ a valid upper bound since each bounded-composition denominator is at least one. Thus
$$
D_{k+r}(\text{actual})\ge D_k+\Pr\{k-r(n-1)\le S<k\}-(1+M)\left[1-\prod_j(1-e_j)^n\right].
$$
This is a sufficient sign certificate that can cover middle-range success rates among the original batches even as every added success probability moves below one. It does not apply indiscriminately when the right-hand side is negative.
