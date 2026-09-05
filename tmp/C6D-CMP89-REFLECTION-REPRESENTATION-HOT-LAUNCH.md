# Retained-runtime diagnostic: CMP89 reflection representation interface

Run only after the active cold C6d gate and evidence verification, after the
reflection branch, orbit, and scale diagnostics. Hot evidence cannot retire
PRE-VALIDATION.

```text
cold base: 77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
overlay: f3550512d25ad7a76071a38c421a8c0863986624
runner: 8323dc229d7b2c8169b85a0b134844fb1e3d0025
runner SHA-256: f4f5e577a13ffd3dfe6ae2a024429455509a9151c89e6671fe50f7e82e73af49
sentinel: HOT_C6D_CMP89_REFLECTION_REPRESENTATION_PASS
```

This supersedes runners `9e936ef29cbcca1ebbb8668845180a65917e3d34`,
`46273b1824bb7a9d045edccebf7a33edb751dff4`, and
`d2b5912890a0d8f099778a356a0a622e26c14d34`. The current contract also
requires positive side lengths and derives carrier nonemptiness.

Execute exactly once:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "8323dc229d7b2c8169b85a0b134844fb1e3d0025/"
    "tmp/run_c6d_cmp89_reflection_representation_hot.py"
)
expected = "f4f5e577a13ffd3dfe6ae2a024429455509a9151c89e6671fe50f7e82e73af49"
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
