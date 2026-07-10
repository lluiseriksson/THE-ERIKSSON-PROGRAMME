"""HOLONOMIC INSURANCE (lane C, dead-hours job): derive the exact linear
recurrence with polynomial coefficients for b_m = m I_m(beta)^4 via the
Sym^4 companion structure (verified rounds ago: quartic monomials
propagate exactly).

Output: the order-<=5 recurrence sum_k p_k(m, x) b_{m+k} = 0 with
polynomial p_k, saved to holonomic_recurrence.txt. This is the input
for certified Taylor/ODE continuation if the exp-integrator's scaling
surprises — a policy, contracted before any fire.
"""
import sympy as sp

m, x = sp.symbols('m x')
# companion: v_m = (I_m, I_{m-1}); v_{m+1} = M(m) v_m,
# M = [[-2m/x, 1], [1, 0]]
M = sp.Matrix([[-2*m/x, 1], [1, 0]])

# quartic monomial vector w = (a^4, a^3 b, a^2 b^2, a b^3, b^4),
# (a, b) -> (Ma), build Sym^4(M) symbolically
a1, b1 = sp.symbols('a1 b1')
anew = M[0, 0]*a1 + M[0, 1]*b1
bnew = M[1, 0]*a1 + M[1, 1]*b1
mons = [a1**(4-i)*b1**i for i in range(5)]
S = sp.zeros(5, 5)
for i in range(5):
    expr = sp.expand(anew**(4-i)*bnew**i)
    for j in range(5):
        S[i, j] = expr.coeff(mons[j]) if True else 0
        expr2 = expr
    # extract coefficients properly
for i in range(5):
    expr = sp.Poly(sp.expand(anew**(4-i)*bnew**i), a1, b1)
    for j in range(5):
        S[i, j] = expr.coeff_monomial(a1**(4-j)*b1**j)

print("Sym4 matrix built", flush=True)

# w_{m+1} = S(m) w_m ; the first component q_m := I_m^4 satisfies a
# linear recurrence of order <= 5: find rational-function coefficients
# c_0..c_5 (not all zero) with sum_k c_k(m) q_{m+k} = 0.
# Build q_{m+k} as rows in terms of w_m: q_{m+k} = e1^T S(m+k-1)...S(m) w_m.
rows = []
prod = sp.eye(5)
rows.append(sp.Matrix([[1, 0, 0, 0, 0]]))            # q_m
for k in range(1, 6):
    prod = (S.subs(m, m + k - 1)) * prod
    rows.append(prod[0, :])                          # q_{m+k}
A = sp.Matrix.vstack(*rows)                          # 6 x 5
print("stacked 6x5; solving nullspace over Q(m,x)...", flush=True)
ns = A.T.nullspace()
assert ns, "no recurrence found (unexpected)"
c = ns[0]
c = c * sp.lcm([sp.denom(sp.together(ci)) for ci in c])
c = sp.Matrix([sp.expand(sp.simplify(ci)) for ci in c])
print("recurrence for I_m^4 found; adapting to b_m = m I_m^4", flush=True)
# b_{m+k} = (m+k) q_{m+k}  =>  coefficients c_k(m)/(m+k)
out = []
for k in range(6):
    out.append(sp.simplify(c[k] / (m + k)))
L = sp.lcm([sp.denom(sp.together(o)) for o in out])
out = [sp.expand(sp.simplify(o * L)) for o in out]

with open("holonomic_recurrence.txt", "w") as f:
    f.write("recurrence: sum_{k=0}^{5} p_k(m, x) * b_{m+k} = 0, "
            "b_m = m I_m(x)^4\n\n")
    for k, o in enumerate(out):
        f.write("p_%d = %s\n\n" % (k, sp.sstr(o)))
print("saved holonomic_recurrence.txt", flush=True)

# numeric sanity at (m, x) = (7, 3.2)
import mpmath as mp
mp.mp.dps = 40
resid = sum(float(sp.N(out[k].subs([(m, 7), (x, sp.Rational(16, 5))])))
            * float((7 + k) * mp.besseli(7 + k, mp.mpf(16) / 5) ** 4)
            for k in range(6))
scale = float((7) * mp.besseli(7, mp.mpf(16) / 5) ** 4)
print("sanity residual (relative):", abs(resid / scale), flush=True)
