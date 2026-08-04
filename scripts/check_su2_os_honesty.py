"""Regression canary for the SU(2) Wilson/Haar lane's repaired scope labels.

This is deliberately a documentary check, not a mathematical proof.  It
prevents the specific pre-audit failures repaired in this lane from silently
returning:

* the old theorem name that advertised a derived geometric factorization;
* the old "final physical endpoint" front-door labels; and
* a front door that postpones the gauge-pure `Cross` limitation until after
  its title.

Run from the repository root:

    python scripts/check_su2_os_honesty.py
"""

from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent

FILES = [
    Path("YangMills/OS/SU2WilsonReflectionKernel.lean"),
    Path("YangMills/OS/SU2WilsonReflectionGeometry.lean"),
    Path("YangMills/OS/SU2WilsonReflectionSharp.lean"),
    Path("YangMills/OS/SU2WilsonReflectionEndpoint.lean"),
    Path("docs/su2-os/CONTRACT.md"),
    Path("docs/su2-os/SHARP-GATE.md"),
    Path("docs/su2-os/CERTIFICATION.md"),
    Path("docs/su2-os/INTEGRATION-NOTE.md"),
    Path("docs/su2-os/AUDIT.md"),
    Path("docs/su2-os/DEPENDENCY-MAP.md"),
    Path("docs/su2-os/SU2OSOracle.lean"),
]

FRONT_DOORS = [
    Path("YangMills/OS/SU2WilsonReflectionGeometry.lean"),
    Path("YangMills/OS/SU2WilsonReflectionEndpoint.lean"),
    Path("docs/su2-os/CONTRACT.md"),
    Path("docs/su2-os/CERTIFICATION.md"),
    Path("docs/su2-os/INTEGRATION-NOTE.md"),
    Path("docs/su2-os/AUDIT.md"),
]

FORBIDDEN = [
    "su2OnePlaquetteCutWeight_" + "splitting",
    "su2OnePlaquette_trace_reflection_positive_" + "sharp",
    "Final SU(2)/Wilson endpoint",
    "Non-vacuous finite SU(2) Wilson reflection-positivity endpoint",
    "splitting identity",
    "algebraic splitting identity",
    "Gate (4)",
]


def normalized(text: str) -> str:
    return re.sub(r"\s+", " ", text)


def prefix_before_title(path: Path, text: str) -> str:
    if path.suffix == ".lean":
        start = text.find("/-!")
        title = text.find("#", start + 3)
        return text[start:title] if start >= 0 and title >= 0 else ""
    title = text.find("\n# ")
    return text[:title] if title >= 0 else ""


def main() -> int:
    failures = []
    contents = {}

    for rel in FILES:
        path = ROOT / rel
        if not path.is_file():
            failures.append(f"{rel}: missing required canary input")
            continue
        contents[rel] = path.read_text(encoding="utf-8")

    for rel, text in contents.items():
        folded = text.casefold()
        for phrase in FORBIDDEN:
            if phrase.casefold() in folded:
                failures.append(f"{rel}: forbidden repaired label {phrase!r}")

    for rel in FRONT_DOORS:
        text = contents.get(rel)
        if text is None:
            continue
        prefix = normalized(prefix_before_title(rel, text)).casefold()
        if "scope limitation" not in prefix:
            failures.append(f"{rel}: no scope limitation before the title")
        if "does not participate" not in prefix:
            failures.append(
                f"{rel}: front door does not say Cross does not participate"
            )
        if "not exercised" not in prefix:
            failures.append(
                f"{rel}: front door does not say inversion is not exercised"
            )
        if "every continuous" not in prefix or "β/4" not in prefix:
            failures.append(
                f"{rel}: front door does not preserve the analytic Haar/β/4 scope"
            )

    for failure in failures:
        print(f"FAIL: {failure}")
    print(f"files checked: {len(FILES)}  failures: {len(failures)}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
