# Retained-runtime diagnostic: CMP89 reflection representation interface

Run only after the active cold C6d gate and evidence verification, after the
reflection branch, orbit, and scale diagnostics. Hot evidence cannot retire
PRE-VALIDATION.

```text
cold base: 77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
overlay: afae28a60fdedc960b4a284b1781f2ba292464f3
runner: 46273b1824bb7a9d045edccebf7a33edb751dff4
runner SHA-256: 4661fc67d222de5d72605c857f3e055ec3e0df8481c0befe0e221657ac61dadd
sentinel: HOT_C6D_CMP89_REFLECTION_REPRESENTATION_PASS
```

This supersedes runner `9e936ef29cbcca1ebbb8668845180a65917e3d34`
and SHA-256
`ff3f5462e1ce0057ad555e221c4484c054fdb4fa3732c645c613a29770d1ba8f`,
whose point subtype still used the printed inclusive envelope.

Execute exactly once:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "46273b1824bb7a9d045edccebf7a33edb751dff4/"
    "tmp/run_c6d_cmp89_reflection_representation_hot.py"
)
expected = "4661fc67d222de5d72605c857f3e055ec3e0df8481c0befe0e221657ac61dadd"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on first error. PASS verifies only the type-level source gate and its
explicit series. Summability and equality with the physical regional Green
remain obligations; no `B0`, `delta0`, or window 15 is produced.
