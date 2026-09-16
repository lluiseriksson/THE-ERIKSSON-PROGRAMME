#!/usr/bin/env python3
"""Prepare the PRE-VALIDATION H1--H2d3 promotion overlay.

This is a deterministic mechanical staging step. It does not invoke Lean,
Lake, GitHub or any network service. Public declarations are obtained by
removing the scratch-only ``_draft`` suffix from the source drafts; the
audit drafts already name that public surface.
"""

from __future__ import annotations

import hashlib
import json
import re
import shutil
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
OUT = TMP / "step8b24-c6c1-h1-h2b-overlay"
MANIFEST = TMP / "STEP8B24-C6C1-H1-H2B-OVERLAY-MANIFEST.json"

MODULES = (
    "BalabanCMP89Eq249PhysicalFineHolderPhaseQuotient",
    "BalabanCMP89Eq249ComplexStripHolderPhaseQuotient",
    "BalabanCMP89Eq251AliasWeightExponentMonotonicity",
    "BalabanCMP89Eq249PhysicalFineComplexHolderPhaseQuotient",
    "BalabanCMP89Eq249ComplexHolderRadialRedistribution",
    "BalabanCMP89Eq249ComplexHolderAliasSummation",
    "BalabanCMP89Eq249PhysicalFineComplexHolderPhasedNoncentralSum",
    "BalabanCMP89Eq249PhysicalFineComplexHolderCentralBranch",
    "BalabanCMP89Eq249PhysicalFineComplexHolderStabilizedBound",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def import_target(line: str) -> str | None:
    match = re.fullmatch(r"import\s+([A-Za-z0-9_.]+)\s*", line)
    return None if match is None else match.group(1)


def module_path(name: str) -> Path:
    return Path(*name.split(".")).with_suffix(".lean")


def validate_imports(path: Path, overlay_paths: set[Path]) -> None:
    for line in path.read_text(encoding="utf-8").splitlines():
        name = import_target(line)
        if name is None:
            continue
        rel = module_path(name)
        if rel in overlay_paths or (ROOT / rel).is_file():
            continue
        raise SystemExit(f"unresolved import in {path.name}: {name}")


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)

    records: list[dict[str, object]] = []
    overlay_paths: set[Path] = set()

    for module in MODULES:
        for audit in (False, True):
            suffix = "Audit" if audit else ""
            draft = TMP / f"{module}{suffix}.draft.lean"
            if not draft.is_file():
                raise SystemExit(f"missing draft: {draft}")

            target = Path("YangMills") / "RG" / f"{module}{suffix}.lean"
            overlay_paths.add(target)
            data = draft.read_text(encoding="utf-8").replace("_draft", "")
            if re.search(r"\b(?:sorry|admit)\b", data, flags=re.IGNORECASE):
                raise SystemExit(f"forbidden proof placeholder: {draft.name}")
            if "_draft" in data:
                raise SystemExit(f"scratch suffix survived: {draft.name}")
            if data.count("PRE-VALIDATION:") != 1:
                raise SystemExit(
                    f"expected exactly one PRE-VALIDATION marker: {draft.name}"
                )

            out = OUT / target
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(data, encoding="utf-8", newline="\n")
            records.append(
                {
                    "draft": str(draft.relative_to(ROOT)).replace("\\", "/"),
                    "path": str(target).replace("\\", "/"),
                    "sha256": sha256(data.encode("utf-8")),
                    "bytes": len(data.encode("utf-8")),
                }
            )

    for record in records:
        validate_imports(OUT / str(record["path"]), overlay_paths)

    order = {Path(str(record["path"])): index for index, record in enumerate(records)}
    internal_edges = 0
    for index, record in enumerate(records):
        path = OUT / str(record["path"])
        for line in path.read_text(encoding="utf-8").splitlines():
            name = import_target(line)
            if name is None:
                continue
            dependency = module_path(name)
            if dependency not in order:
                continue
            internal_edges += 1
            if order[dependency] >= index:
                raise SystemExit(
                    f"non-topological overlay import in {path.name}: {name}"
                )

    sources = [OUT / str(r["path"]) for r in records if not str(r["path"]).endswith("Audit.lean")]
    audits = [OUT / str(r["path"]) for r in records if str(r["path"]).endswith("Audit.lean")]
    declarations = sum(
        len(re.findall(r"(?m)^\s*(?:theorem|lemma|def|structure)\s+(?:\n\s*)?[A-Za-z0-9_]", p.read_text(encoding="utf-8")))
        for p in sources
    )
    prints = sum(
        len(re.findall(r"(?m)^#print axioms\s+", p.read_text(encoding="utf-8")))
        for p in audits
    )
    if declarations != prints:
        raise SystemExit(f"audit mismatch: declarations={declarations}, prints={prints}")

    payload = {
        "status": "PRE-VALIDATION",
        "compiler_verified": False,
        "source_head": None,
        "files": records,
        "declarations": declarations,
        "axiom_prints": prints,
        "internal_import_edges": internal_edges,
    }
    MANIFEST.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(
        json.dumps(
            {
                "status": "PASS-STATIC-STAGING",
                "files": len(records),
                "declarations": declarations,
                "axiom_prints": prints,
                "internal_import_edges": internal_edges,
                "manifest_sha256": sha256(MANIFEST.read_bytes()),
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
