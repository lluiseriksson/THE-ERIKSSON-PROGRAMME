# C6d retained-runtime hot diagnostic suite

Run only after `FINAL_STATUS=PASS` for the active cold gate and after its
archive plus executed notebook have been downloaded and hash-verified. Use
one new cell exactly once. The suite fetches every child runner by exact Git
object and SHA-256, runs them in dependency order, and stops on first error.
Hot evidence cannot retire PRE-VALIDATION.

```text
suite runner object: a273c601e197622ecdf5f660839e03a51dda5dcb
suite runner SHA-256: 2586a378285e5a559978da0548c48869965ae7dc31c1d18852c3334ae6a27a84
success sentinel: HOT_C6D_POST_COLD_DIAGNOSTIC_SUITE_PASS
```

This supersedes suite object `01fc252a068b76aae94e7d7beb45cc089b5eb69d`
and SHA-256
`c8baf4f4f86b44c7043d26e3585ecd26fa5e28e362f12c8ee47ea9776a8c51e7`;
the superseded suite used the pre-correction reflection-scale and
representation runners.

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "a273c601e197622ecdf5f660839e03a51dda5dcb/"
    "tmp/run_c6d_post_cold_hot_suite.py"
)
expected = "2586a378285e5a559978da0548c48869965ae7dc31c1d18852c3334ae6a27a84"
with urllib.request.urlopen(url) as response:
    payload = response.read()
actual = hashlib.sha256(payload).hexdigest()
print("HOT_SUITE_TRANSPORT_SHA256=" + actual, flush=True)
if actual != expected:
    raise RuntimeError("HOT_SUITE_TRANSPORT_HASH_MISMATCH")
exec(compile(payload, url, "exec"), {"__name__": "__main__"})
```

The suite covers the uniform-certificate adapter, normalized Neumann
precision, reflection branch budget, derivative-level Neumann/Dirichlet
no-go, reflection orbit algebra, source scale dictionary, and representation
interface. Even a full PASS is diagnostic only: it does not prove the Green
image-series equality, uniform `B0`/`delta0`, or window 15.
