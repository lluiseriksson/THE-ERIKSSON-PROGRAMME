#!/usr/bin/env python3
"""Colab diagnostic gate for the cross-fibre alias quotient transport.

The immutable mathematical source is ``SOURCE_SHA``.  This runner reuses the
fresh-clone transport, exact pin gates, robust axiom parser, evidence archive,
and runtime release protocol.  A Mathlib-only reproduction checks the complex
field normalization behind the transported coarse base momentum before the
expensive project focal.

Honest scope: this validates the nonzero-coarse-fibre row-to-column quotient
transport through periodic Fourier negation and the physical stabilized
specialization.  It does not reindex the complete finite alias sum, handle the
zero coarse fibre, identify a Brillouin integral, construct regional ``B0``,
attain window 15, discharge a terminal field or inhabit ``TermSource``.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import urllib.request


HERE = Path("/content")
BASE_RUNNER = HERE / "colab_qprime_row_validation.py"
BASE_RUNNER_URL = (
    "https://raw.githubusercontent.com/lluiseriksson/"
    "THE-ERIKSSON-PROGRAMME/"
    "bcc852cee5e709bff91fad7de26fa21cff754e1f/"
    "scripts/colab_qprime_row_validation.py"
)
BASE_RUNNER_SHA256 = (
    "d06b8a186c9fcefb54d6e21264d2467b6fb723b337be092d4c3380b875e47cee"
)
with urllib.request.urlopen(BASE_RUNNER_URL) as response:
    base_runner_source = response.read()
base_runner_hash = hashlib.sha256(base_runner_source).hexdigest()
print("BASE_RUNNER_TRANSPORT_SHA256=" + base_runner_hash, flush=True)
if base_runner_hash != BASE_RUNNER_SHA256:
    raise RuntimeError("BASE_RUNNER_TRANSPORT_HASH_MISMATCH")
BASE_RUNNER.write_bytes(base_runner_source)
SPEC = importlib.util.spec_from_file_location(
    "cmp99_cross_fibre_alias_quotient_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-cross-fibre-alias-quotient-v3"
runner.SOURCE_SHA = "da7eed698c279304d24fb7f7a5f64278cbededf0"
runner.ROOT = Path("/content/hrpoly-cmp99-cross-fibre-alias-quotient")
runner.EVIDENCE = Path(
    "/content/hrpoly-cmp99-cross-fibre-alias-quotient-evidence"
)
runner.ARCHIVE = Path(
    "/content/hrpoly-cmp99-cross-fibre-alias-quotient-evidence.tar.gz"
)
runner.PATH_MANIFEST = Path(
    "/content/hrpoly-cmp99-cross-fibre-alias-quotient-paths.txt"
)

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCrossFibreAliasQuotient.lean":
        "8b6f5296d06ab284a1bc15313797bd995a92d136791d3d0b4cbae492e89e0897",
    "YangMills/RG/BalabanCMP99SourceFlatQprimeCrossFibreAliasQuotientAudit.lean":
        "1d3235c0b6f26445dd7e84184b0b1a0ebb95602b924ea2014c027965433142b7",
}

REPRO = HERE / "cmp99_cross_fibre_alias_quotient_repro.lean"
REPRO.write_text(
    """import Mathlib

example (N l : ℕ) (hle : l ≤ N) :
    -(((N - l : ℕ) : ℂ)) = (l : ℂ) - (N : ℂ) := by
  rw [Nat.cast_sub hle]
  ring

example {d : ℕ} : -(fun _ : Fin d => (0 : ℤ)) = fun _ => 0 := by
  funext mu
  simp
""",
    encoding="utf-8",
)

runner.QUEUE = [
    (
        "cmp99_cross_fibre_alias_quotient_repro",
        ["lake", "env", "lean", str(REPRO)],
        None,
    ),
    (
        "cmp99_cross_fibre_alias_quotient_focal",
        [
            "lake",
            "build",
            "YangMills.RG."
            "BalabanCMP99SourceFlatQprimeCrossFibreAliasQuotient",
        ],
        None,
    ),
    (
        "cmp99_cross_fibre_alias_quotient_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/"
            "BalabanCMP99SourceFlatQprimeCrossFibreAliasQuotientAudit.lean",
        ],
        8,
    ),
]


if __name__ == "__main__":
    try:
        from google.colab import runtime

        runtime.unassign = lambda: print(
            "RUNTIME_UNASSIGN_DEFERRED_TO_LAUNCHER=1", flush=True
        )
    except ImportError:
        pass
    raise SystemExit(runner.main())
