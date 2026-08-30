# C6d retained-runtime hot diagnostic suite

Run only after `FINAL_STATUS=PASS` for the active cold gate and after its
archive plus executed notebook have been downloaded and hash-verified. Use
one new cell exactly once. The suite fetches every child runner by exact Git
object and SHA-256, runs them in dependency order, and stops on first error.
Hot evidence cannot retire PRE-VALIDATION.

```text
suite runner object: 47f7c82da0427b3b098b7b1b90ded151538e6908
suite runner SHA-256: 3d67f003422a3c26ee3e74aa3ca445137b9bfa26ed40ea122433056b969e53f3
success sentinel: HOT_C6D_POST_COLD_DIAGNOSTIC_SUITE_PASS
```

This supersedes suite objects `7ff3c5e47e96adc2bfd6ac3ceff92efc0eb4beee`,
`415a19f4d42336c6bd1310081abe82a2ad41a937`,
`01fc252a068b76aae94e7d7beb45cc089b5eb69d`,
`a273c601e197622ecdf5f660839e03a51dda5dcb`, and
`18bb269ce3dcfb5d3e14919791ebef1040b29190`, and
`f698d7a67de8ec402c2a66992689e1f62c740a0d`, and
`37640a20c256a267eb625d235a9f5ce4af6e2362`. The current suite is the first
one whose representation contract is both half-open and nonvacuous and whose
axiom parser accepts both pure and permitted-axiom declarations without
depending on line wrapping. It also carries the exact rectangular
reflection-residue dictionary as the final diagnostic stage.

```python
import hashlib, urllib.request

url = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "47f7c82da0427b3b098b7b1b90ded151538e6908/"
    "tmp/run_c6d_post_cold_hot_suite.py"
)
expected = "3d67f003422a3c26ee3e74aa3ca445137b9bfa26ed40ea122433056b969e53f3"
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
interface, followed by the exact rectangular reflection residues. Even a full
PASS is diagnostic only: it does not prove the Green image-series equality,
uniform `B0`/`delta0`, or window 15.
