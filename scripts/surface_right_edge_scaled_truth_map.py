"""Multiprecision point map for the scaled G5 target; never a certificate."""

import argparse
import hashlib
from pathlib import Path
import platform

import mpmath as mp


def coefficients(beta, cutoff):
    values = [mp.besseli(m, beta) for m in range(cutoff + 2)]
    a = [mp.mpf(0)] * (cutoff + 1)
    b = [mp.mpf(0)] * (cutoff + 1)
    for m in range(1, cutoff + 1):
        a[m] = values[m]**2 * (
            (m-1)*values[m-1]**2 + (m+1)*values[m+1]**2)
        b[m] = m*values[m]**4
    return a, b


def target(beta, lam, a, b):
    d = lam/beta
    t = mp.pi-d
    indices = range(1, len(a))
    fa = mp.fsum(a[m]*mp.sin(m*t) for m in indices)
    fb = mp.fsum(b[m]*mp.sin(m*t) for m in indices)
    fap = mp.fsum(m*a[m]*mp.cos(m*t) for m in indices)
    fbp = mp.fsum(m*b[m]*mp.cos(m*t) for m in indices)
    w = 2*(fap*fb-fa*fbp)
    q_lambda = -w/(4*fb**2)
    return q_lambda/lam, q_lambda, fa/(2*fb)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--beta", type=int, default=125)
    parser.add_argument("--dps", type=int, default=140)
    parser.add_argument("--extra", type=int, default=100)
    args = parser.parse_args()
    mp.mp.dps = args.dps
    beta = mp.mpf(args.beta)
    cutoff = args.beta + args.extra
    path = Path(__file__).resolve()
    print("PROVENANCE script_sha256", hashlib.sha256(path.read_bytes()).hexdigest())
    print("PROVENANCE python", platform.python_version(), "mpmath", mp.__version__)
    print("CONFIG beta", args.beta, "dps", args.dps, "cutoff", cutoff)
    a, b = coefficients(beta, cutoff)
    values = []
    for numerator in range(1, 16):
        lam = mp.mpf(numerator)/10
        h, q_lambda, e = target(beta, lam, a, b)
        values.append(h)
        print("lambda", mp.nstr(lam, 4), "H", mp.nstr(h, 30),
              "Q_lambda", mp.nstr(q_lambda, 30), "E", mp.nstr(e, 30),
              flush=True)
    print("SCALED TRUTH MAP VERIFIED POINTS ONLY: min_H",
          mp.nstr(min(values), 30), "G5 REMAINS OPEN", flush=True)


if __name__ == "__main__":
    main()
