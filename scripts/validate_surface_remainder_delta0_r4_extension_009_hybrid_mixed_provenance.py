"""Validate the complete K2 hybrid009 lane with explicit mixed provenance.

The canonical production directory currently contains 156 units from the
historical source head ``027885a6`` and two replacement units from
``2627288a``.  This audit accepts that split only when every dependency hash,
unit row, strict margin, and deterministic replay field agrees.  It strips
only the provenance-head line and wall-clock duration when comparing with the
independent replay directory; all mathematical transcript fields remain exact.
No G2, K4, S1'''/S2''', or G6 promotion follows.
"""

from collections import Counter
import json
import re
from pathlib import Path

from flint import arb

import certify_surface_remainder_delta0_r4_extension_009_hybrid as cert
import surface_remainder_delta0_r4_extension_009_hybrid_contract as hybrid
from surface_eol_hashes import validate_recorded_dependencies


ROOT = Path(__file__).resolve().parents[1]
PRODUCTION = ROOT / "scripts"
REPLAY = ROOT / "replay-hybrid009-027885a6"
PREFIX = "certify_surface_remainder_delta0_r4_extension_009_hybrid_"
HEAD_HISTORICAL = "027885a6b9c052cd518787f70d41617ad3aa6ab8"
HEAD_REPLACEMENT = "2627288a79efe0dd2ab067e2822dbeaa0a3bd6fe"
ELAPSED = re.compile(r"(elapsed_seconds\s+)[^\s]+$")


def normalized(lines):
    out = []
    for line in lines:
        if line.startswith("PROVENANCE git_head "):
            line = "PROVENANCE git_head <provenance-normalized>"
        if line.startswith("CERTIFIED UNIT "):
            line = ELAPSED.sub(r"\1<wall-clock>", line)
        out.append(line)
    return out


def dependency_map(lines):
    return {
        line.split()[1]: line.split()[2]
        for line in lines if line.startswith("DEPENDENCY ")
    }


def main() -> int:
    expected = {u.slug: u for u in hybrid.regular_units()}
    heads = Counter()
    for slug, unit in expected.items():
        prod = PRODUCTION / f"{PREFIX}{slug}.txt"
        replay = REPLAY / prod.name
        assert prod.is_file() and replay.is_file(), f"missing {slug}"
        plines = prod.read_text(encoding="utf-8").splitlines()
        rlines = replay.read_text(encoding="utf-8").splitlines()
        head_lines = [x for x in plines if x.startswith("PROVENANCE git_head ")]
        assert len(head_lines) == 1, f"provenance count {slug}"
        head = head_lines[0].split()[-1]
        heads[head] += 1
        assert head in {HEAD_HISTORICAL, HEAD_REPLACEMENT}, f"unexpected head {slug}"
        if slug in {"parent_000", "parent_001"}:
            assert head == HEAD_REPLACEMENT, f"replacement head missing {slug}"
        else:
            assert head == HEAD_HISTORICAL, f"historical head drift {slug}"
        validate_recorded_dependencies(
            dependency_map(plines), cert.DEPENDENCIES, ROOT
        )
        assert normalized(plines) == normalized(rlines), f"replay mismatch {slug}"
        row_lines = [x for x in plines if x.startswith("ROW ")]
        assert len(row_lines) == 1, f"row count {slug}"
        row = json.loads(row_lines[0][4:])
        assert row["slug"] == slug and arb(row["margin_lower"]) > 0
    assert heads == Counter({HEAD_HISTORICAL: 156, HEAD_REPLACEMENT: 2})
    assert hybrid.edge_starts_no_later_than_cut()
    print(
        "K2 HYBRID009 MIXED-PROVENANCE VALIDATION PASS: 158 units; "
        "156 historical + 2 replacement heads; deterministic replay exact "
        "after provenance/wall-clock normalization; all margins positive"
    )
    print("SCOPE K2 regular lane only; no G2/K4/S1'''/S2'''/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
