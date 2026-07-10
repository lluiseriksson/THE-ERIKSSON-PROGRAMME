"""High-precision sanity of the derived recurrence (the float64 check in
the derivation was inadequate for a 17-order term spread)."""
import re
import mpmath as mp

mp.mp.dps = 60
txt = open('holonomic_recurrence.txt').read()
polys = {}
for k in range(6):
    mtch = re.search(r'p_%d = (.+)' % k, txt)
    polys[k] = mtch.group(1)

m_val = 7
x_val = mp.mpf(16)/5
env = {'m': mp.mpf(m_val), 'x': x_val}
resid = mp.mpf(0)
mx = mp.mpf(0)
for k in range(6):
    pk = eval(polys[k].replace('**', '^').replace('^', '**'), {}, env)
    bk = (m_val+k)*mp.besseli(m_val+k, x_val)**4
    term = pk*bk
    resid += term
    mx = max(mx, abs(term))
print("max term:", mp.nstr(mx, 6))
print("residual:", mp.nstr(resid, 6))
print("relative residual:", mp.nstr(abs(resid)/mx, 6))
print("EXACT (rel < 1e-40):", abs(resid)/mx < mp.mpf('1e-40'))
