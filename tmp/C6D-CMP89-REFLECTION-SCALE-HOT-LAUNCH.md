# Retained-runtime diagnostic: CMP89 reflection scale dictionary

Run only after the active cold C6d gate and its evidence verification, after
the reflection-branch and reflection-orbit hot diagnostics. This is hot
diagnostic evidence and cannot retire PRE-VALIDATION.

```text
cold base source: 77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
scale overlay: afae28a60fdedc960b4a284b1781f2ba292464f3
runner object: 46273b1824bb7a9d045edccebf7a33edb751dff4
runner SHA-256: 407d728b59e9f2e2f0cf5a34e2a478f4b09a752206158b9069049806d447d901
sentinel: HOT_C6D_CMP89_REFLECTION_SCALE_PASS
```

This supersedes runner `f443e7145fbbb004de236993c5e298ea176eba0c`
and SHA-256
`e81d19d273edf5f3876a15d2178ce26cd0f92a3c8943f0edc136393d10c64190`,
which predated the half-open block-carrier correction.

Execute exactly once in a new cell:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "46273b1824bb7a9d045edccebf7a33edb751dff4/"
    "tmp/run_c6d_cmp89_reflection_scale_hot.py"
)
expected = "407d728b59e9f2e2f0cf5a34e2a478f4b09a752206158b9069049806d447d901"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on first error. PASS verifies only the exact lattice-spacing dictionary
for the two first reflected coordinates, the half-open block carrier fixed by
CMP89 (1.1), and its inclusion in the printed geometric envelope. It does not
prove the Green image-series identity, produce uniform `B0`/`delta0`, or
attain window 15.
