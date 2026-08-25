#!/usr/bin/env python3
"""Require one ``#print axioms`` readout for every public Lean declaration.

The input is an exact newline-delimited manifest containing source modules and
their audit modules.  This is deliberately a textual, lightweight gate: it
does not run Lean and it does not claim that the readouts themselves are
acceptable.  It only prevents a remote queue from silently auditing a strict
subset of the public declarations it ships.
"""

from __future__ import annotations

import argparse
import importlib.util
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OVERLAY_GUARD = ROOT / "scripts" / "check_lean_overlay_text.py"
DECLARATION = re.compile(
    r"(?m)^(?:@\[[^\]\n]+\]\s*)*"
    r"(?:(?:noncomputable|protected)\s+)*"
    r"(?:def|theorem|lemma|structure|class|inductive|abbrev|opaque)\s+"
    r"([^\s(:]+)"
)
READOUT = re.compile(
    r"(?m)^\s*#print\s+axioms\s+(?:YangMills\.RG\.)?([^\s]+)\s*$"
)


def load_visible_lines():
    spec = importlib.util.spec_from_file_location("check_lean_overlay_text", OVERLAY_GUARD)
    if spec is None or spec.loader is None:
        raise RuntimeError("LEAN_OVERLAY_GUARD_IMPORT_FAILED")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.visible_lines


VISIBLE_LINES = load_visible_lines()


def listed_paths(root: Path, manifest: Path) -> list[Path]:
    paths: list[Path] = []
    for raw in manifest.read_text(encoding="utf-8-sig").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        path = Path(line)
        if not path.is_absolute():
            path = root / path
        if path.suffix != ".lean":
            raise ValueError(f"NON_LEAN_PATH={line}")
        paths.append(path)
    if not paths:
        raise ValueError("EMPTY_PATH_MANIFEST")
    if len(paths) != len(set(paths)):
        raise ValueError("DUPLICATE_PATH_IN_MANIFEST")
    return paths


def is_audit(path: Path) -> bool:
    return path.name.endswith("Audit.lean") or path.name.endswith("Audit.draft.lean")


def visible_text(path: Path) -> str:
    text = path.read_text(encoding="utf-8-sig")
    return "\n".join(VISIBLE_LINES(text))


def declaration_names(paths: list[Path]) -> list[str]:
    names: list[str] = []
    for path in paths:
        if not path.is_file():
            raise ValueError(f"MISSING_PATH={path}")
        names.extend(DECLARATION.findall(visible_text(path)))
    return names


def readout_names(paths: list[Path]) -> list[str]:
    names: list[str] = []
    for path in paths:
        if not path.is_file():
            raise ValueError(f"MISSING_PATH={path}")
        names.extend(READOUT.findall(visible_text(path)))
    return names


def coverage_failures(paths: list[Path]) -> list[str]:
    sources = [path for path in paths if not is_audit(path)]
    audits = [path for path in paths if is_audit(path)]
    if not sources:
        return ["NO_SOURCE_FILES"]
    if not audits:
        return ["NO_AUDIT_FILES"]

    declarations = declaration_names(sources)
    readouts = readout_names(audits)
    failures: list[str] = []
    duplicate_declarations = sorted(
        name for name in set(declarations) if declarations.count(name) != 1
    )
    duplicate_readouts = sorted(name for name in set(readouts) if readouts.count(name) != 1)
    missing = sorted(set(declarations) - set(readouts))
    unknown = sorted(set(readouts) - set(declarations))
    if duplicate_declarations:
        failures.append(f"DUPLICATE_DECLARATIONS={duplicate_declarations!r}")
    if duplicate_readouts:
        failures.append(f"DUPLICATE_READOUTS={duplicate_readouts!r}")
    if missing:
        failures.append(f"MISSING_READOUTS={missing!r}")
    if unknown:
        failures.append(f"UNKNOWN_READOUTS={unknown!r}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--paths-from", type=Path, required=True)
    args = parser.parse_args()
    try:
        paths = listed_paths(ROOT, args.paths_from)
        failures = coverage_failures(paths)
    except (OSError, UnicodeError, ValueError, RuntimeError) as exc:
        print(f"LEAN_AXIOM_READOUT_COVERAGE_FAIL {exc}")
        return 1
    if failures:
        for failure in failures:
            print(f"LEAN_AXIOM_READOUT_COVERAGE_FAIL {failure}")
        return 1
    declarations = declaration_names([path for path in paths if not is_audit(path)])
    print(
        "LEAN_AXIOM_READOUT_COVERAGE_OK "
        f"files={len(paths)} declarations={len(declarations)} readouts={len(declarations)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
