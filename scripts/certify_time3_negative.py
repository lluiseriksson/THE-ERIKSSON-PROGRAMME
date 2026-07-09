from mpmath import iv
from math import factorial

# CERTIFIED (interval arithmetic, outward rounding, mpmath.iv, prec=350):
# time-3 marginal tail difference at beta=20, a=4802/10^4, t1=29621/10^4,
# t2=30070/10^4 is STRICTLY NEGATIVE.
iv.prec = 350
M = 120          # series cutoff in both indices
X = iv.mpf(10)   # beta/2 = 10, exact

def besseli_iv(m):
    # I_m(20) = sum_j 10^(m+2j)/(j!(m+j)!), positive terms; geometric tail
    s = iv.mpf(0); j = 0
    while True:
        t = X**(m+2*j) / (iv.mpf(factorial(j)) * iv.mpf(factorial(m+j)))
        s += t
        ratio_hi = 100.0/((j+1)*(m+j+1))
        if ratio_hi < 0.5 and float(t.b) < 1e-120*float(s.a if s.a > 0 else 1):
            # tail <= t*ratio/(1-ratio) <= 2*t*ratio  (ratio<1/2)
            r = iv.mpf(100) / (iv.mpf(j+1)*iv.mpf(m+j+1))
            s += iv.mpf([0,1]) * (t*r/(1-r))
            return s
        j += 1

I = [besseli_iv(m) for m in range(0, M+1)]
A  = iv.mpf(4802)/iv.mpf(10000)
T1 = iv.mpf(29621)/iv.mpf(10000)
T2 = iv.mpf(30070)/iv.mpf(10000)
sa  = [iv.sin(iv.mpf(k)*A) for k in range(0, 2*M+1)]
s1v = [iv.sin(iv.mpf(n)*T1) for n in range(0, M+1)]
s2v = [iv.sin(iv.mpf(n)*T2) for n in range(0, M+1)]
PI = iv.pi

def assemble(sv):
    TN = iv.mpf(0); D = iv.mpf(0)
    for m in range(1, M+1):
        cm = iv.mpf(m)*I[m]**3
        row = iv.mpf(0)
        for n in range(1, M+1):
            if m == n:
                J = (PI-A)/2 + sa[2*m]/(iv.mpf(4)*iv.mpf(m))
            else:
                J = -(sa[abs(m-n)]*(1 if m>n else -1)/(iv.mpf(2)*iv.mpf(m-n if m>n else n-m))*(1 if m>n else 1))
                # careful: sin((m-n)a) = sign(m-n)*sin(|m-n|a)
                sgn = 1 if m > n else -1
                J = -(iv.mpf(sgn)*sa[abs(m-n)]/(iv.mpf(2*(m-n))*iv.mpf(sgn)) - sa[m+n]/(iv.mpf(2*(m+n))))
                # simplify: sin((m-n)a)/(2(m-n)) is even in swap; just:
                J = -(iv.mpf(sgn)*sa[abs(m-n)]/(iv.mpf(2)*iv.mpf(m-n)) - sa[m+n]/(iv.mpf(2)*iv.mpf(m+n)))
            row += iv.mpf(4)*I[n]*sv[n]*J
        TN += cm*row
        D  += cm*iv.mpf(4)*I[m]*sv[m]*(PI/2)
    return TN, D

# truncation tails (both sums), crude but rigorous:
# I_m(20) <= 10^m e^100 / m!  ;  sum_{n>M} I_n <= B_{M+1}/(1-10/(M+2))
E100 = iv.exp(iv.mpf(100))
BM1 = X**(M+1)*E100/iv.mpf(factorial(M+1))
tailI = BM1/(1 - iv.mpf(10)/iv.mpf(M+2))                     # sum_{n>M} I_n
sumI  = sum(I[n] for n in range(1, M+1)) + tailI             # sum_{n>=1} I_n
summ3 = sum(iv.mpf(m)*I[m]**3 for m in range(1, M+1))
tailm3 = iv.mpf(M+1)*BM1**3*iv.mpf(2)                        # crude: sum_{m>M} m B_m^3 <= 2(M+1)B_{M+1}^3
eps = iv.mpf(4)*PI*(tailm3*sumI + summ3*iv.mpf(4)*tailI*PI)  # generous
ERR = iv.mpf([-1,1])*eps

TN1, D1 = assemble(s1v); TN2, D2 = assemble(s2v)
TN1 += ERR; TN2 += ERR; D1 += ERR; D2 += ERR

print("D1 > 0:", D1 > 0, "   D2 > 0:", D2 > 0)
R = TN2*D1 - TN1*D2
print("R interval:", R)
print("CERTIFIED R < 0:", R < 0)
diff = R/(D1*D2)
print("diff enclosure:", diff)
print("CERTIFIED diff < 0:", diff < 0)
