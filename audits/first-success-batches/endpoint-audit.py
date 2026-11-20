"""Exact spot checks of the polynomial loss and the centered inverse odds tilt."""
from fractions import Fraction as F
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib
import json


def check_profiles():
    counts = [0, 0]
    for n in range(2, 11):
        for x in (F(1, 100), F(1, 5), F(1), F(5), F(100)):
            weights = [x**j for j in range(n)]
            rho = sum(j * w for j, w in enumerate(weights)) / sum(weights)
            v = rho / (1 + rho)
            c = x / v

            def profile(q):
                return (1 - q) * sum((c * q)**j for j in range(n))

            for q in [F(i, 16) for i in range(17)] + [v, v / 2, (1 + v) / 2]:
                bound = (q + v)**(n - 2) * (q - v)**2 / (8 * 2**(n - 2))
                assert 1 - profile(q) / profile(v) >= bound
                counts[0] += 1
        for v in (F(0), F(n - 1, n)):
            for q in (F(i, 16) for i in range(17)):
                value = 1-q**n if v == 0 else (1-q)*q**(n-1)/((1-v)*v**(n-1))
                assert 1-value >= (q+v)**(n-2)*(q-v)**2/(8*2**(n-2))
                counts[1] += 1
    return counts


def check_inverse():
    count = 0
    for n in range(2, 11):
        t = F(1, n)
        for lam in (1, 2, 17, 10**7):
            def g(y):
                return y / (lam - (lam - 1) * y)
            for y in (F(i, 64) for i in range(65)):
                assert (1-t)*abs(g(y)-g(t)) <= abs(y-t)
                count += 1
    return count


if __name__ == "__main__":
    inside, endpoints = check_profiles()
    result = dict(interior_profile=inside, endpoint_profile=endpoints, anchored_tilt=check_inverse())
    packet = Path("/content/archive.zip")
    with ZipFile(packet, "w", ZIP_DEFLATED) as z:
        z.writestr("endpoint-audit.json", json.dumps(result, sort_keys=True))
    print("archive_sha256", hashlib.sha256(packet.read_bytes()).hexdigest())
