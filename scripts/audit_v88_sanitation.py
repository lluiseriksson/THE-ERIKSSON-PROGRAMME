"""Independent executable audit of the committed v88 sanitation evidence."""

from __future__ import annotations

import ast
import hashlib
import re
import sys
from decimal import Decimal
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
PAIRS = (
    (
        "cascade3b_judges_transcript_SUPERSEDED_nonmonotone.txt",
        "cascade3b_judges_transcript.txt",
        "cascade3b_judges.py",
    ),
    (
        "cascade1_signed_minoration_transcript_SUPERSEDED_nonmonotone.txt",
        "cascade1_signed_minoration_transcript.txt",
        "cascade1_signed_minoration.py",
    ),
    (
        "cascade2_step0_eps_transcript_SUPERSEDED_nonmonotone.txt",
        "cascade2_step0_eps_transcript.txt",
        "cascade2_step0_eps.py",
    ),
    (
        "cascade3_mirror_extraction_transcript_SUPERSEDED_nonmonotone.txt",
        "cascade3_mirror_extraction_transcript.txt",
        "cascade3_mirror_extraction.py",
    ),
    (
        "cascade3c_buckets_transcript_SUPERSEDED_nonmonotone.txt",
        "cascade3c_buckets_transcript.txt",
        "cascade3c_buckets.py",
    ),
)
NUMBER = re.compile(
    r"(?<![A-Za-z0-9_])[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?"
)
SCRIPT_HASH = re.compile(r"^script sha256\s*:\s*([0-9a-f]{64})$", re.MULTILINE)
TIME_FIELD = re.compile(r"\(\d+s(?: total)?\)")
ALLOWED_ARB_IMPORTS = {
    "datetime",
    "flint",
    "fractions",
    "hashlib",
    "math",
    "sys",
    "time",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_lf(path: Path) -> str:
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def provenance_hashes(text: str, script_name: str) -> tuple[str, str] | None:
    match = re.search(
        rf"^## {re.escape(script_name)}\n"
        rf"- executed bytes \(EOL: (?:CRLF|LF)\): ([0-9a-f]{{64}})\n"
        rf"- LF-normalized:\s+([0-9a-f]{{64}})$",
        text,
        re.MULTILINE,
    )
    return (match.group(1), match.group(2)) if match else None


def canonical_transcript(text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines():
        if line.startswith("script sha256"):
            continue
        lines.append(TIME_FIELD.sub("(TIME)", line))
    return "\n".join(lines)


def _imports(path: Path) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names.update(alias.name.split(".", 1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            names.add(node.module.split(".", 1)[0])
    return names


def audit(root: Path = ROOT) -> tuple[list[str], dict[str, Any]]:
    scripts = root / "scripts"
    errors: list[str] = []
    metrics: dict[str, Any] = {
        "pairs": 0,
        "numbers_compared": 0,
        "max_absolute_difference": Decimal(0),
        "richardson_rows": 0,
        "mirror_drift_rows": 0,
        "domination_rows": 0,
        "m_sharp": None,
        "arb_files": 0,
        "independent_rerun_matches": 0,
    }
    provenance = (scripts / "PROVENANCE-HASHES.md").read_text(encoding="utf-8")

    # T2/T3: current script hashes and complete nonvolatile transcript equality.
    for old_name, new_name, script_name in PAIRS:
        old_path, new_path = scripts / old_name, scripts / new_name
        script_path = scripts / script_name
        for path in (old_path, new_path, script_path):
            if not path.is_file():
                errors.append(f"missing required v88 artifact: {path.relative_to(root)}")
        if not all(path.is_file() for path in (old_path, new_path, script_path)):
            continue
        new_text = new_path.read_text(encoding="utf-8")
        match = SCRIPT_HASH.search(new_text)
        recorded = provenance_hashes(provenance, script_name)
        if match is None:
            errors.append(f"{new_name}: missing script sha256 header")
        elif recorded is None:
            errors.append(f"{script_name}: missing dual hashes in PROVENANCE-HASHES.md")
        elif match.group(1) != recorded[0]:
            errors.append(
                f"{new_name}: executed hash disagrees with provenance "
                f"({match.group(1)} != {recorded[0]})"
            )
        elif sha256_lf(script_path) != recorded[1]:
            errors.append(f"{script_name}: LF-normalized hash mismatch")
        header = "\n".join(new_text.splitlines()[:4])
        if "python " not in header or not any(
            library in header for library in ("mpmath", "sympy", "python-flint")
        ):
            errors.append(f"{new_name}: incomplete Python/library version header")

        old_clean = canonical_transcript(old_path.read_text(encoding="utf-8"))
        new_clean = canonical_transcript(new_text)
        old_numbers = [Decimal(value) for value in NUMBER.findall(old_clean)]
        new_numbers = [Decimal(value) for value in NUMBER.findall(new_clean)]
        if len(old_numbers) != len(new_numbers):
            errors.append(
                f"{new_name}: numeric count changed ({len(old_numbers)} != {len(new_numbers)})"
            )
        else:
            differences = [abs(old - new) for old, new in zip(old_numbers, new_numbers)]
            metrics["numbers_compared"] += len(differences)
            metrics["max_absolute_difference"] = max(
                metrics["max_absolute_difference"], max(differences, default=Decimal(0))
            )
        if old_clean != new_clean:
            errors.append(f"{new_name}: nonvolatile transcript content changed")
        independent_name = new_name.replace(
            ".txt", "_independent_20260711.txt"
        )
        independent_path = scripts / independent_name
        if not independent_path.is_file():
            errors.append(f"{new_name}: independent rerun transcript missing")
        else:
            independent_clean = canonical_transcript(
                independent_path.read_text(encoding="utf-8")
            )
            if independent_clean != new_clean:
                errors.append(
                    f"{new_name}: independent rerun differs after removing "
                    "only script-hash/timing volatility"
                )
            else:
                metrics["independent_rerun_matches"] += 1
        metrics["pairs"] += 1

    # T4: pre-registered closed-form and drift gates recorded in the transcripts.
    judges = (scripts / "cascade3b_judges_transcript.txt").read_text(encoding="utf-8")
    richardson = re.findall(
        r"^\s+(?:0\.5|1\.5|2\.9)\s+(?:muF|nuD|nuF)\s+\|\s+"
        r"[-+0-9.]+\s+([-+0-9.]+)\s+([-+0-9.]+)\s+rel\s+([0-9.]+)\s+OK$",
        judges,
        re.MULTILINE,
    )
    metrics["richardson_rows"] = len(richardson)
    if len(richardson) != 9:
        errors.append(f"T4: expected 9 Richardson rows, found {len(richardson)}")
    for measured, closed, printed_rel in richardson:
        absolute = abs(Decimal(measured) - Decimal(closed))
        relative = absolute / abs(Decimal(closed))
        if relative >= Decimal("0.03") or Decimal(printed_rel) >= Decimal("0.03"):
            errors.append("T4: Richardson row exceeds the pre-registered 3% gate")

    mirror = (scripts / "cascade3_mirror_extraction_transcript.txt").read_text(
        encoding="utf-8"
    )
    drift_rows = re.findall(r"^\s+t=(?:2\.2|2\.6|2\.9)\s+\w+:.+\sOK$", mirror, re.MULTILINE)
    metrics["mirror_drift_rows"] = len(drift_rows)
    for marker in (
        "MARK M-A PASSES",
        "MARK M-B PASSES",
        "MARK M-C PASSES",
        "MARK M-D PASSES",
    ):
        if marker not in mirror:
            errors.append(f"T4: missing {marker}")
    if len(drift_rows) != 12:
        errors.append(f"T4: expected 12 mirror drift rows, found {len(drift_rows)}")

    cascade1 = (scripts / "cascade1_signed_minoration_transcript.txt").read_text(
        encoding="utf-8"
    )
    if "19/19 checks PASS" not in cascade1 or "VERDICT: ALL PASS" not in cascade1:
        errors.append("T4: cascade1 transcript lacks its 19/19 passing verdict")
    cascade2 = (scripts / "cascade2_step0_eps_transcript.txt").read_text(
        encoding="utf-8"
    )
    if "VERDICT (floor of the claim): CERTIFIED" not in cascade2:
        errors.append("T4: cascade2 transcript lacks its certified verdict")

    # T5: all measured bucket dominations and the registered M_sharp window.
    buckets = (scripts / "cascade3c_buckets_transcript.txt").read_text(encoding="utf-8")
    metrics["domination_rows"] = len(re.findall(r"dominated \(B2 =", buckets))
    if metrics["domination_rows"] != 17 or "BUCKET DOMINATION: PASS" not in buckets:
        errors.append(
            f"T5: expected 17 passing domination rows, found {metrics['domination_rows']}"
        )
    m_sharp_match = re.search(r"M_sharp\(2\.9,15\) = ([0-9.]+)", buckets)
    if m_sharp_match is None:
        errors.append("T5: M_sharp stress-cell value missing")
    else:
        metrics["m_sharp"] = Decimal(m_sharp_match.group(1))
        if not Decimal("0.0733") < metrics["m_sharp"] < Decimal("0.7"):
            errors.append("T5: M_sharp lies outside the registered window")

    # T6: exact reciprocal human manifest and no live references to old evidence.
    manifest_path = scripts / "SUPERSESSION-MANIFEST.md"
    manifest = manifest_path.read_text(encoding="utf-8")
    for old_name, new_name, _ in PAIRS:
        if old_name not in manifest or new_name not in manifest:
            errors.append(f"T6: supersession pair missing for {old_name}")
    allowed_reference_files = {
        manifest_path.resolve(),
        (root / "docs" / "SURFACE-CLOSURE-NOTES.md").resolve(),
        (root / "docs" / "incidents" / "INC-T1-ZERO-SCAN.md").resolve(),
        Path(__file__).resolve(),
    }
    for path in root.rglob("*"):
        if not path.is_file() or path.resolve() in allowed_reference_files:
            continue
        if path.suffix.lower() not in {".md", ".py", ".tex", ".txt", ".json", ".yml", ".yaml"}:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        if "SUPERSEDED_nonmonotone" in text:
            errors.append(f"T6: live reference to superseded evidence in {path.relative_to(root)}")

    # T7: Arb certificate imports are stdlib plus python-flint only.
    arb_files = sorted(scripts.glob("*_arb.py"))
    metrics["arb_files"] = len(arb_files)
    if not arb_files:
        errors.append("T7: no Arb certificate files found")
    for path in arb_files:
        unexpected = _imports(path) - ALLOWED_ARB_IMPORTS
        if unexpected:
            errors.append(
                f"T7: {path.name} imports unexpected dependencies {sorted(unexpected)}"
            )

    return sorted(set(errors)), metrics


def main() -> int:
    errors, metrics = audit()
    print(
        "v88 audit: pairs={pairs}, numbers={numbers_compared}, max_abs_diff={max_absolute_difference}, "
        "Richardson={richardson_rows}, mirror_drifts={mirror_drift_rows}, "
        "dominations={domination_rows}, M_sharp={m_sharp}, arb_files={arb_files}".format(
            **metrics
        )
    )
    print(
        "independent canonical rerun matches: "
        f"{metrics['independent_rerun_matches']}/5"
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("v88 sanitation evidence audit OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
