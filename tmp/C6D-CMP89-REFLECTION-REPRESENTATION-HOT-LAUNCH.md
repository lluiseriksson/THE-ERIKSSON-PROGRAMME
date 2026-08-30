# Retained-runtime diagnostic: CMP89 reflection representation interface

Run only after the active cold C6d gate and evidence verification, after the
reflection branch, orbit, and scale diagnostics. Hot evidence cannot retire
PRE-VALIDATION.

```text
cold base: 77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
overlay: 2a3b3ddcf1d69a77b4844c0e3f9c3d9e901b71a4
runner: d2b5912890a0d8f099778a356a0a622e26c14d34
runner SHA-256: 5103fe04ea947f0ac3516ab157bc5ad41e5bf0c0406069b89768fac757836c28
sentinel: HOT_C6D_CMP89_REFLECTION_REPRESENTATION_PASS
```

This supersedes runners `9e936ef29cbcca1ebbb8668845180a65917e3d34`
and `46273b1824bb7a9d045edccebf7a33edb751dff4`. The first still used the
printed inclusive envelope; the second predated the final header correction
that states the half-open carrier without leaving a false site-count debt.

Execute exactly once:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "d2b5912890a0d8f099778a356a0a622e26c14d34/"
    "tmp/run_c6d_cmp89_reflection_representation_hot.py"
)
expected = "5103fe04ea947f0ac3516ab157bc5ad41e5bf0c0406069b89768fac757836c28"
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
