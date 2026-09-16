# Retained-runtime diagnostic: CMP89 reflection branch budget

Run only after the active C6d Green-owner-prefix gate has emitted a terminal
verdict and, on PASS, its archive and executed notebook have been downloaded
and hash-verified.  This diagnostic mutates the retained checkout and is hot
evidence only; it cannot retire PRE-VALIDATION.

Pinned objects:

```text
cold base source:
  77d9f4b4d923ab1c804ca9dd6679ea304a9d3a92
reflection overlay source:
  d39ba71cde7bca6aef127fce833925b719a70967
runner object:
  3a40b6819a32aa940eaf6e1e316aac765d596b55
runner blob SHA-256:
  ee476352a1773520f6bc911173223479b63543435b39c3ce1e153a87391c2c8e
success sentinel:
  HOT_C6D_CMP89_REFLECTION_BRANCH_PASS
```

Execute exactly once in a new cell of the retained runtime:

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "3a40b6819a32aa940eaf6e1e316aac765d596b55/"
    "tmp/run_c6d_cmp89_reflection_branch_hot.py"
)
expected = "ee476352a1773520f6bc911173223479b63543435b39c3ce1e153a87391c2c8e"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

Stop on the first error.  A PASS verifies only the `2^d` parity-branch
multiplicity separated from the finite signed-translation box and its
geometric majorant.  It does not prove CMP89 (2.42), the infinite reflection
representation, an image-orbit injection, a distance comparison, the
rectangle/carrier dictionary, a regional Green bound, uniform `B0`/`delta0`,
or window 15.
