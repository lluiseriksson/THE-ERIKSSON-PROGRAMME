#!/usr/bin/env python3
"""Colab diagnostic gate for centered-alias residue reflection.

The immutable mathematical source is ``SOURCE_SHA``.  This runner-only child
reuses the established fresh-clone transport, exact pin gates, robust axiom
parser, evidence archive, and runtime release protocol.  Its queue contains
only the alias-carrier reflection and its five-declaration audit.

Honest scope: this does not assert physical reflection inside a fixed coarse
fibre.  The cross-fibre negation, endpoint phase, finite-to-continuous
periodization, regional ``B0`` and window 15 remain open.
"""

from __future__ import annotations

import importlib.util
import hashlib
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
    "centered_alias_reflection_base_runner", BASE_RUNNER
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)

runner.RUNNER_REV = "cmp99-centered-alias-reflection-v2"
runner.SOURCE_SHA = "3bf925319be2b09c6d77706be64913e9817eb3b4"
runner.ROOT = Path("/content/hrpoly-centered-alias-reflection")
runner.EVIDENCE = Path("/content/hrpoly-centered-alias-reflection-evidence")
runner.ARCHIVE = Path("/content/hrpoly-centered-alias-reflection-evidence.tar.gz")
runner.PATH_MANIFEST = Path("/content/hrpoly-centered-alias-reflection-paths.txt")

runner.SOURCE_BLOBS = {
    "YangMills/RG/BalabanCMP99SourceCenteredAliasReflection.lean":
        "50a27bed81d489105ba1df211823e1d999b5ac4b20df45b4a88a72ee694c3b58",
    "YangMills/RG/BalabanCMP99SourceCenteredAliasReflectionAudit.lean":
        "b934a5e4618844cc747e70e40971e9057f5f3b66a7356ba015d3651648007082",
}

runner.QUEUE = [
    (
        "centered_alias_reflection_focal",
        [
            "lake",
            "build",
            "YangMills.RG.BalabanCMP99SourceCenteredAliasReflection",
        ],
        None,
    ),
    (
        "centered_alias_reflection_audit",
        [
            "lake",
            "env",
            "lean",
            "YangMills/RG/BalabanCMP99SourceCenteredAliasReflectionAudit.lean",
        ],
        5,
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
