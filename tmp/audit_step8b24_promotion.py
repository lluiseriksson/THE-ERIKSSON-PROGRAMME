#!/usr/bin/env python3
"""Read-only whole-schedule audit for the Step 8b.24 promotion frontier.

This proves only mechanical/static properties: exact scope, source/audit
coverage, declaration ownership, resolvable imports, and acyclicity of the
scratch dependency graph.  It is not Lean evidence.
"""

from __future__ import annotations

import re
import hashlib
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TMP = ROOT / "tmp"
PRE_UNIT_E = (
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreen",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalAmbientGreenComplexification",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bPrecisionDictionary",
    "BalabanCMP99SourceFlatQprimePhysicalFineSymbolMassZeroNoncentral",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenIdentification",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalGreenFourierEndpoint",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalEndpointIntegrand",
    "BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction",
    "BalabanCMP99SourceSeparatedGeneratedFlatPhysicalPointSourceEndpoint",
)
TAIL_LISTS = (
    "STEP8B24-C2-PATHS.txt",
    "STEP8B24-C3-PATHS.txt",
    "STEP8B24-C4A-PATHS.txt",
    "STEP8B24-C4B-PATHS.txt",
    "STEP8B24-C5-PATHS.txt",
    "STEP8B24-C6A-PATHS.txt",
    "STEP8B24-C6B-PATHS.txt",
)
INDEPENDENT = {
    "tmp/BalabanCMP89CenteredBrillouinAffineSlice.draft.lean",
    "tmp/BalabanCMP89CenteredBrillouinAffineSliceAudit.draft.lean",
}
OWNERSHIP_MOVE = "cmp99SourceFlatQprimePhysicalFineSymbol_massZero_ne_zero_noncentral"
OWNERSHIP_ORIGIN = "YangMills/RG/BalabanCMP99SourceGeneratedFlatPhysicalGreenIdentification.lean"

DECL = re.compile(
    r"(?m)^(?:(?:noncomputable|protected)\s+)?"
    r"(?:def|abbrev|theorem|lemma|structure|class)\s+([A-Za-z0-9_.'’]+)"
)
PRINT = re.compile(r"(?m)^#print axioms YangMills\.RG\.([A-Za-z0-9_.'’]+)")
IMPORT = re.compile(r"(?m)^import\s+([^\s]+)")
COMMENT_IMPORT = re.compile(r"(?m)^--\s*import\s+([^\s]+)")


def listed(path: Path) -> list[str]:
    return [
        line.strip()
        for line in path.read_text(encoding="utf-8-sig").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]


def pair(name: str) -> list[str]:
    return [f"tmp/{name}.draft.lean", f"tmp/{name}Audit.draft.lean"]


def source_module(path: Path) -> str:
    return "YangMills.RG." + path.name.removesuffix(".draft.lean")


def visit(
    node: str,
    edges: dict[str, set[str]],
    state: dict[str, int],
    stack: list[str],
    failures: list[str],
) -> None:
    mark = state.get(node, 0)
    if mark == 2:
        return
    if mark == 1:
        start = stack.index(node)
        failures.append("scratch import cycle: " + " -> ".join(stack[start:] + [node]))
        return
    state[node] = 1
    stack.append(node)
    for dependency in sorted(edges[node]):
        visit(dependency, edges, state, stack, failures)
    stack.pop()
    state[node] = 2


def main() -> int:
    failures: list[str] = []
    pre = [item for name in PRE_UNIT_E for item in pair(name)]
    step8b23 = listed(TMP / "STEP8B23-ALL-PATHS.txt")
    shared = [item for item in step8b23 if item not in INDEPENDENT]
    tail = [item for name in TAIL_LISTS for item in listed(TMP / name)]
    dependency = pre + shared + tail
    full = step8b23 + pre + tail
    recorded_full = listed(TMP / "STEP8B24-ALL-PATHS.txt")

    expected_counts = (("pre", pre, 20), ("shared", shared, 42), ("tail", tail, 14),
                       ("dependency", dependency, 76), ("full", full, 78))
    for label, values, expected in expected_counts:
        if len(values) != expected or len(set(values)) != expected:
            failures.append(
                f"{label} scope {len(values)} files/{len(set(values))} unique; "
                f"expected {expected}/{expected}"
            )
    if recorded_full != full:
        failures.append("STEP8B24-ALL-PATHS.txt differs from the derived full schedule")

    paths = [ROOT / item for item in full]
    missing_paths = [path.relative_to(ROOT).as_posix() for path in paths if not path.is_file()]
    if missing_paths:
        failures.extend(f"missing path: {item}" for item in missing_paths)

    sources = [path for path in paths if not path.name.endswith("Audit.draft.lean")]
    audits = [path for path in paths if path.name.endswith("Audit.draft.lean")]
    if len(sources) != 39 or len(audits) != 39:
        failures.append(f"pair count source={len(sources)} audit={len(audits)}; expected 39/39")

    source_modules = {source_module(path): path for path in sources}
    scratch_modules = {
        "tmp." + path.name.removesuffix(".draft.lean"): path for path in sources
    }
    all_draft_modules = source_modules | scratch_modules

    tracked_names: dict[str, list[str]] = defaultdict(list)
    for path in (ROOT / "YangMills").rglob("*.lean"):
        for name in DECL.findall(path.read_text(encoding="utf-8-sig")):
            tracked_names[name].append(path.relative_to(ROOT).as_posix())

    total_declarations = 0
    total_prints = 0
    source_promotion_imports = 0
    all_names: dict[str, str] = {}
    edges: dict[str, set[str]] = {source_module(path): set() for path in sources}

    for source in sources:
        module = source_module(source)
        audit = TMP / source.name.replace(".draft.lean", "Audit.draft.lean")
        target = ROOT / "YangMills" / "RG" / source.name.replace(".draft.lean", ".lean")
        if target.exists():
            failures.append(f"tracked target already exists: {target.relative_to(ROOT)}")
        if audit not in audits:
            failures.append(f"missing scoped sibling audit: {audit.relative_to(ROOT)}")
            continue

        source_text = source.read_text(encoding="utf-8-sig")
        audit_text = audit.read_text(encoding="utf-8-sig")
        declarations = DECL.findall(source_text)
        prints = PRINT.findall(audit_text)
        total_declarations += len(declarations)
        total_prints += len(prints)
        missing = [name for name in declarations if name not in prints]
        extra = [name for name in prints if name not in declarations]
        if missing:
            failures.append(f"audit missing {source.name}: {', '.join(missing)}")
        if extra:
            failures.append(f"audit extra {source.name}: {', '.join(extra)}")

        for name in declarations:
            prior = all_names.get(name)
            if prior is not None:
                failures.append(f"duplicate draft declaration: {name} ({prior}, {source.name})")
            all_names[name] = source.name
            collisions = tracked_names.get(name, [])
            if not collisions:
                continue
            if name == OWNERSHIP_MOVE and collisions == [OWNERSHIP_ORIGIN]:
                continue
            failures.extend(f"tracked declaration collision: {name} in {item}" for item in collisions)

        expected_audit_import = module
        active_audit_imports = IMPORT.findall(audit_text)
        commented_audit_imports = COMMENT_IMPORT.findall(audit_text)
        if active_audit_imports not in ([], [expected_audit_import]) or (
            expected_audit_import not in active_audit_imports + commented_audit_imports
        ):
            failures.append(
                f"audit import mismatch {audit.name}: expected [{expected_audit_import}] "
                f"active={active_audit_imports} commented={commented_audit_imports}"
            )

        active_source_imports = IMPORT.findall(source_text)
        commented_source_imports = COMMENT_IMPORT.findall(source_text)
        source_promotion_imports += len(commented_source_imports)
        for imported in active_source_imports + commented_source_imports:
            dependency_path = all_draft_modules.get(imported)
            if dependency_path is not None:
                edges[module].add(source_module(dependency_path))
                continue
            if imported.startswith("tmp."):
                failures.append(f"unresolved scratch import {source.name}: {imported}")
                continue
            if imported.startswith("Mathlib"):
                continue
            tracked = ROOT / (imported.replace(".", "/") + ".lean")
            if not tracked.is_file():
                failures.append(f"unresolved tracked import {source.name}: {imported}")

    state: dict[str, int] = {}
    for module in sorted(edges):
        visit(module, edges, state, [], failures)

    if failures:
        print("STEP8B24_PROMOTION_STATIC_FAIL")
        for failure in failures:
            print(f"- {failure}")
        return 1

    byte_manifest = "".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT).as_posix()}\n"
        for path in paths
    ).encode("utf-8")
    content_manifest_sha256 = hashlib.sha256(byte_manifest).hexdigest().upper()

    print(
        "STEP8B24_PROMOTION_STATIC_OK "
        f"files={len(paths)} sources={len(sources)} audits={len(audits)} "
        f"declarations={total_declarations} prints={total_prints} "
        f"dependency_edges={sum(map(len, edges.values()))} "
        f"source_promotion_imports={source_promotion_imports} ownership_moves=1 "
        f"content_manifest_sha256={content_manifest_sha256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
