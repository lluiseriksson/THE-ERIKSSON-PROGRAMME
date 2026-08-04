import time
import exp_integrator_arb as m

D = m.D
pt = m.V2((15, 10), (8, 1), prec=90)
print("V2 ok", flush=True)

X = m.hull(m.arb(0)/D, m.arb(D)/D)
print("X hull ok:", X.str(5), flush=True)
S = pt.PI*X
print("S ok:", S.str(5), flush=True)
t0 = time.time()
P = (S/2).sin()**2
print("P ok %.2fs:" % (time.time()-t0), P.str(5), flush=True)
Y = m.hull(m.arb(0)/D, m.arb(D)/D)
A = pt.PI*Y
Q = (A/2).sin()**2
print("Q ok:", Q.str(5), flush=True)
t0 = time.time()
R2 = m.clip0(4*(pt.c0**2*(1-P-Q) + P*Q))
print("R2 ok %.2fs:" % (time.time()-t0), R2.str(5), flush=True)
t0 = time.time()
z2 = m.clip0(4*pt.B**2*R2)
print("z2 ok %.2fs:" % (time.time()-t0), z2.str(5), flush=True)
t0 = time.time()
z = m.safe_sqrt(z2)
print("safe_sqrt ok %.2fs:" % (time.time()-t0), z.str(5), flush=True)
t0 = time.time()
zl = float(m.ball_lo(z)); zh = float(m.ball_hi(z))
print("floats ok %.2fs: [%.3f, %.3f]" % (time.time()-t0, zl, zh), flush=True)
# end-to-end: the module's own geometry on the full-domain cell
t0 = time.time()
S2, A2, P2, Q2, R2b, zb = pt.geom(X, Y)
zl2 = float(m.ball_lo(zb)); zh2 = float(m.ball_hi(zb))
print("module geom ok %.2fs: z = [%.3f, %.3f]" % (time.time()-t0, zl2, zh2), flush=True)
# and a real point certification smoke test
t0 = time.time()
ok = m.certify_point((15, 10), (8, 1), prec=90, tag="smoke ")
print("certify_point smoke %.2fs: ok=%s" % (time.time()-t0, ok), flush=True)
