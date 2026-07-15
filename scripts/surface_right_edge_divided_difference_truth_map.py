"""Multiprecision point oracle for the divided-difference G5 target.

This is deliberately not a certificate.  It evaluates the five regular
families U, U_y, U_yy, V_y, V_yy from their Fourier series after the common
exp(-4 beta) scaling and reports the cancellation-free numerator P.
"""

import argparse
import hashlib
from pathlib import Path
import platform

import mpmath as mp


def scaled_bessel_row(beta, cutoff):
    scale = mp.exp(-beta)
    return [scale*mp.besseli(m, beta) for m in range(cutoff + 2)]


def regular_families(beta, lam, values):
    x = lam/(2*beta)
    s_terms = []
    sx_terms = []
    sxx_terms = []
    tp_terms = []
    tpp_terms = []
    for n in range(len(values)-1):
        k = 2*n+1
        coefficient = (-1)**n*(values[n]*values[n+1])**2
        s_terms.append(coefficient*mp.sin(k*x))
        sx_terms.append(coefficient*k*mp.cos(k*x))
        sxx_terms.append(-coefficient*k*k*mp.sin(k*x))
    for m in range(1, len(values)-1):
        coefficient = (-1)**m*values[m]**4
        tp_terms.append(-2*m*coefficient*mp.sin(2*m*x))
        tpp_terms.append(-4*m*m*coefficient*mp.cos(2*m*x))
    shifted = mp.fsum(s_terms)
    shifted_x = mp.fsum(sx_terms)
    shifted_xx = mp.fsum(sxx_terms)
    t_x = mp.fsum(tp_terms)
    t_xx = mp.fsum(tpp_terms)
    U = shifted/x
    Uy = (x*shifted_x-shifted)/(2*x**3)
    Uyy = (x*x*shifted_xx-3*x*shifted_x+3*shifted)/(4*x**5)
    b = t_x/(2*x)
    by = (x*t_xx-t_x)/(4*x**3)
    return U, Uy, Uyy, b, by


def target(beta, lam, values):
    x = lam/(2*beta)
    U, Uy, Uyy, b, by = regular_families(beta, lam, values)
    sinc = mp.sin(x)/x
    defect = (mp.sin(x)-x*mp.cos(x))/x**3
    sinc_y = (x*mp.cos(x)-mp.sin(x))/(2*x**3)
    defect_y = (mp.sin(x)/(2*x**3)
                - 3*(mp.sin(x)-x*mp.cos(x))/(2*x**5))
    a = defect*U+2*sinc*Uy
    ay = defect_y*U+(defect+2*sinc_y)*Uy+2*sinc*Uyy
    P = a*b+x*x*(ay*b-a*by)
    H = P/(4*beta*b*b)
    # The Fourier coefficients above use exp(-beta) I_m, hence every one of
    # the five families is exp(-4 beta) times its unscaled value.  Convert to
    # the exact saddle/polynomial normalization of the companion note.
    amplifier = mp.exp((4-2*mp.sqrt(2))*beta)
    U0 = amplifier*mp.sqrt(beta)*U
    U1 = amplifier*beta**(-mp.mpf("1.5"))*Uy
    U2 = amplifier*beta**(-mp.mpf("3.5"))*Uyy
    B0 = amplifier*beta**(-mp.mpf("0.5"))*b
    B1 = amplifier*beta**(-mp.mpf("2.5"))*by
    P0 = amplifier**2*beta**-2*P
    assert mp.almosteq(H, P0/(4*B0**2))
    return U0, U1, U2, B0, B1, P0, H


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--betas", default="125,250,500")
    parser.add_argument("--lambdas", default="0.01,0.05,0.1,0.25,0.5,1,1.5")
    parser.add_argument(
        "--dps", type=int, default=0,
        help="decimal precision; zero chooses a beta-dependent safe value")
    parser.add_argument("--sigma-cutoff", type=int, default=16)
    args = parser.parse_args()
    betas = [mp.mpf(item) for item in args.betas.split(",")]
    lambdas = [mp.mpf(item) for item in args.lambdas.split(",")]
    path = Path(__file__).resolve()
    print("PROVENANCE script_sha256", hashlib.sha256(path.read_bytes()).hexdigest())
    print("PROVENANCE python", platform.python_version(), "mpmath", mp.__version__)
    worst = None
    for beta in betas:
        lost_digits = (4-2*mp.sqrt(2))*beta/mp.log(10)
        mp.mp.dps = args.dps or int(mp.ceil(lost_digits+100))
        cutoff = int(mp.ceil(args.sigma_cutoff*mp.sqrt(beta)+20))
        values = scaled_bessel_row(beta, cutoff)
        for lam in lambdas:
            row = target(beta, lam, values)
            P0, H = row[-2:]
            print("beta", mp.nstr(beta, 8), "lambda", mp.nstr(lam, 8),
                  "dps", mp.mp.dps, "cutoff", cutoff,
                  "P0", mp.nstr(P0, 30), "H", mp.nstr(H, 30),
                  "B0", mp.nstr(row[3], 20),
                  flush=True)
            if worst is None or H < worst[0]:
                worst = (H, beta, lam)
    print("DIVIDED-DIFFERENCE TRUTH MAP VERIFIED POINTS ONLY",
          "min_H", mp.nstr(worst[0], 30), "at_beta", worst[1],
          "lambda", worst[2], "G5 REMAINS OPEN", flush=True)


if __name__ == "__main__":
    main()
