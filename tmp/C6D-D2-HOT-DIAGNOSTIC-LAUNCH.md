# C6d D2 retained-runtime hot diagnostic launch

Use this only after the running cold D2 gate has emitted literal
`FINAL_STATUS=PASS` and its cold archive plus executed notebook have been
downloaded.  The retained checkout is intentionally older than the diagnostic,
so do not invoke a path from that checkout.  Insert one new Colab cell and run
the following transport exactly once:

The published raw URL was fetched independently on 2026-08-29: 5711 bytes,
SHA-256 `B62BF2946229E5A13DCEA667141102DD3082C3449F0D5E93F751C6B350436F3B`.

```python
import hashlib, sys, urllib.request

SOURCE_SHA = "c5a8738d044fd9dd1c5120b2b355c723de6dc6ff"
RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/" + SOURCE_SHA +
    "/tmp/c6d_eq389_physical_spacing_hot_diagnostic.py"
)
RUNNER_SHA256 = "b62bf2946229e5a13dcea667141102dd3082c3449f0d5e93f751c6b350436f3b"

with urllib.request.urlopen(RUNNER_URL) as response:
    runner_source = response.read()
measured = hashlib.sha256(runner_source).hexdigest()
print("HOT_RUNNER_TRANSPORT_SHA256=" + measured, flush=True)
if measured != RUNNER_SHA256:
    raise RuntimeError("HOT_RUNNER_TRANSPORT_HASH_MISMATCH")

sys.argv = [
    RUNNER_URL,
    "--source-sha", SOURCE_SHA,
    "--root", "/content/hrpoly-c6d-d2-owner-rescaling",
]
exec(compile(runner_source, RUNNER_URL, "exec"), {"__name__": "__main__"})
```

Acceptance is the first literal `FINAL_STATUS=PASS` or `FINAL_STATUS=FAIL`
from this cell.  This is hot diagnostic evidence only: it does not seal any
module, move `20/41`, attain Window 15 or instantiate `TermSource`.
