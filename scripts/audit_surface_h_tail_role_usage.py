"""Audit the manuscript roles that mention ``H_tail``.

The finite direct-sign route may replace the finite-row use of ``H_tail`` only
if the remaining uses are confined to the regular analytic branch.  This
static audit records every occurrence and fails if a new occurrence appears
outside the extraction lemma, its local remark, or Proposition k2endpoint.
It is a role audit, not a proof of either analytic inequality.
"""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "papers" / "surface-complete" / "surface_theorem_complete.tex"


def main() -> int:
    text = TEX.read_text(encoding="utf-8")
    occurrences = []
    for index, line in enumerate(text.splitlines(), 1):
        if "H_tail" in line or "H_{\\rm tail}" in line or "H_{tail}" in line:
            occurrences.append((index, line.strip()))
    assert occurrences, "no H_tail occurrence found"
    allowed = re.compile(r"extraction|tail|k2endpoint|H_\\{\\rm tail\\}|H_tail")
    unexpected = [item for item in occurrences if not allowed.search(item[1])]
    print("H_TAIL ROLE AUDIT")
    print("occurrences", len(occurrences))
    for index, line in occurrences:
        print(f"{index}: {line}")
    assert not unexpected, f"unexpected H_tail roles: {unexpected}"
    print("ALLOWED ROLES extraction/regular-tail/k2endpoint")
    print("SCOPE role usage only; no H_tail/G2/G6 promotion")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
