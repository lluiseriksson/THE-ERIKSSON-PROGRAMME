# A material-selection bound uniform in observability

With the model assumptions and notation in low-observation.md, let d=min(T-R,P-S)>0 and K=R-P>0. For every interior population share, every type-homogeneous equilibrium, and every 0<rho<=1,

    F_selfish - F_conditional >= [d^2/(d+K)] y.

To prove this, let m be the conditional type's adoption probability, z=1-m, and y=xm. Every selfish individual uses discretionary A. Denote by g its equilibrium advantage of A over a deviation to M. Couple the two potential opponent responses using the same type, device, observation event, and private randomization. A change in the opponent's action is possible only if the opponent is conditional, discretionary, and observes the player's device. This event has probability rho x z. Elsewhere the material payoff advantage of defecting with A over cooperating with M is at least d. Even on that event the payoff advantage is at least P-R=-K. Therefore g>=max(0,d-(d+K)rho xz).

The selfish type also weakly outperforms the conditional type conditional on both using A. With probability rho y an A user sees a committed device; in that event the conditional user voluntarily cooperates and forgoes T-R>=d. The two types induce the same opponent behavior when choosing A. Conditional on choosing M they obtain identical material payoffs. Thus F_selfish-F_conditional >= m g + z rho y d. If y=0 imitation alone suffices. Otherwise divide by y and use x<=1 to obtain

    (F_selfish-F_conditional)/y >= max(0,d-(d+K)t) + d t,   t=rho z.

For t<=d/(d+K) the right side is d-Kt, and for t>=d/(d+K) it is dt. Both attain their minimum d^2/(d+K) at the common endpoint. No sharpness claim is made for the payoff constant across actual equilibria.

Under realized-fitness replicator selection, d(log(x/(1-x)))/dt=F_conditional-F_selfish almost everywhere along any interior absolutely continuous solution. In the low-observation regime x is bounded below by min(x0,k)>0, because below k the only outcome is full defection and the derivative is zero. The integral over all time of y is bounded by [(d+K)/d^2] times the difference between the initial log-odds and the log-odds at min(x0,k). Long-run average adoption therefore vanishes, even for a measurable varying equilibrium selection. If a pointwise limit exists, it is zero. Under the weaker all-equilibrium sign restriction of Definition 1, stationary positive adoption remains possible. This comparison identifies the dynamic condition responsible for the different predictions.

Boundary check: at rho=1/4,x=3/5 in the example, d=1,K=2 give y/3=2/15, strictly below the verified material disadvantage 9/10. The inequality uses independent observation and one-on-one simultaneous actions; a repeated-interaction game requires a fresh argument.