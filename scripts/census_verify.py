#!/usr/bin/env python3
"""
census_verify.py — Authoritative axiom census for THE-ERIKSSON-PROGRAMME.

⚠ DOCSTRING POSSIBLY STALE — references v0.15.0 expected output.
   Current state (v1.89.0, 2026-04-25): axiom count outside
   YangMills/Experimental/ is **0**. Total Experimental axioms
   are **14** (per EXPERIMENTAL_AXIOMS_AUDIT.md). The script
   may still execute correctly but its expected-output comments
   below will not match current reality.

   For current axiom census, see AXIOM_FRONTIER.md (live ledger)
   and EXPERIMENTAL_AXIOMS_AUDIT.md (classification by
   retire-ability). For the dual-governance dead-weight
   discussion, see COWORK_FINDINGS.md Finding 007 and
   REPO_INFRASTRUCTURE_AUDIT.md §3.

Run this in Colab AFTER cloning/updating the repo:

    !git -C /content/THE-ERIKSSON-PROGRAMME pull --ff-only
    !python census_verify.py

Expected output (v0.15.0 — STALE; will not match current state):
    Total unique Lean axiom declaration names: 26
    Distinct mathematical gaps:                26
      Clay-core (open):          3
      Clay-core (unconnected):   1
      ClayCore/BalabanRG:        4
      P8 Mathlib-gap:            7
      LieSUN Mathlib-gap:        7
      Semigroup Mathlib-gap:     4

    NOTE (C3 not committed):
      generatorMatrix, gen_skewHerm, gen_trace_zero each appear in two files.
      They are counted once (26 unique names).
      Fix: remove duplicates from DirichletConcrete.lean (run elimination_structural_v1.py).

If the counts differ, the discrepancy must be documented in AXIOM_FRONTIER.md.
"""
import os
import re
import sys
from pathlib import Path


def _repo_root() -> Path:
    try:
        candidate = Path(__file__).resolve().parent.parent
        if (candidate / "lakefile.lean").exists():
            return candidate
    except NameError:
        pass
    env = os.environ.get("ERIKSSON_REPO_ROOT")
    if env:
        return Path(env).resolve()
    cwd = Path.cwd().resolve()
    for ancestor in [cwd, *cwd.parents]:
        if (ancestor / "lakefile.lean").exists():
            return ancestor
    sibling = cwd / "THE-ERIKSSON-PROGRAMME"
    if (sibling / "lakefile.lean").exists():
        return sibling
    for ancestor in [cwd, *cwd.parents]:
        if (ancestor / "YangMills").is_dir():
            return ancestor
    return cwd


def strip_block_comments(text: str) -> str:
    result: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0:
            if text[i:i+2] == '/-':
                depth += 1; result.append('  '); i += 2
            else:
                result.append(text[i]); i += 1
        else:
            if text[i:i+2] == '/-':
                depth += 1; result.append('  '); i += 2
            elif text[i:i+2] == '-/':
                depth -= 1; result.append('  '); i += 2
            elif text[i] == '\n':
                result.append('\n'); i += 1
            else:
                result.append(' '); i += 1
    return ''.join(result)


_AXIOM_NAME_RE = re.compile(r'\baxiom\s+(\w+)')
_SORRY_RE = re.compile(r'\bsorry\b')


def collect_axioms(root: Path) -> dict[str, list[tuple[str, int]]]:
    """Return dict: axiom_name -> [(file_rel_path, line_no), ...]"""
    yang_mills = root / "YangMills"
    if not yang_mills.is_dir():
        print(f"ERROR: YangMills/ not found under {root}", file=sys.stderr)
        sys.exit(1)
    result: dict[str, list[tuple[str, int]]] = {}
    for p in sorted(yang_mills.rglob("*.lean")):
        try:
            text = p.read_text(encoding="utf-8")
        except OSError as e:
            print(f"WARNING: cannot read {p}: {e}", file=sys.stderr)
            continue
        cleaned = strip_block_comments(text)
        for line_no, line in enumerate(cleaned.splitlines(), 1):
            comment_pos = line.find("--")
            code = line[:comment_pos] if comment_pos != -1 else line
            for m in _AXIOM_NAME_RE.finditer(code):
                name = m.group(1)
                rel = str(p.relative_to(root))
                result.setdefault(name, []).append((rel, line_no))
    return result


def collect_sorry(root: Path) -> list[tuple[str, int]]:
    yang_mills = root / "YangMills"
    hits = []
    for p in sorted(yang_mills.rglob("*.lean")):
        try:
            text = p.read_text(encoding="utf-8")
        except OSError:
            continue
        cleaned = strip_block_comments(text)
        for line_no, line in enumerate(cleaned.splitlines(), 1):
            comment_pos = line.find("--")
            code = line[:comment_pos] if comment_pos != -1 else line
            if _SORRY_RE.search(code):
                hits.append((str(p.relative_to(root)), line_no))
    return hits


def main():
    root = _repo_root()
    print(f"Repo root: {root}")
    print(f"YangMills/: {root / 'YangMills'}")
    print()

    # Sorry check
    sorry_hits = collect_sorry(root)
    if sorry_hits:
        print(f"\u26a0\ufe0f  SORRY DETECTED ({len(sorry_hits)} occurrence(s)):")
        for f, ln in sorry_hits:
            print(f"   {f}:{ln}")
    else:
        print("\u2705 Zero sorry in YangMills/ source")
    print()

    # Axiom census
    axioms = collect_axioms(root)
    print(f"Total unique Lean axiom declaration names: {len(axioms)}")
    print()

    # Group by file for reporting
    by_file: dict[str, list[str]] = {}
    for name, locs in sorted(axioms.items()):
        for f, ln in locs:
            by_file.setdefault(f, []).append(f"{name} (line {ln})")

    for f in sorted(by_file):
        print(f"  {f}:")
        for entry in by_file[f]:
            print(f"    axiom {entry}")
    print()

    # Duplicate detection
    duplicates = {n: locs for n, locs in axioms.items() if len(locs) > 1}
    if duplicates:
        print(f"\u26a0\ufe0f  DUPLICATE AXIOM NAMES ({len(duplicates)} name(s) declared in >1 file):")
        for name, locs in duplicates.items():
            for f, ln in locs:
                print(f"   {name}  \u2190  {f}:{ln}")
        print()
    else:
        print("\u2705 No duplicate axiom names across files")
        print()

    # Expected names (from AXIOM_FRONTIER.md v0.15.0)
    EXPECTED_NAMES = {
        "sun_bakry_emery_cd", "balaban_rg_uniform_lsi", "sun_lieb_robinson_bound",
        "sz_lsi_to_clustering",
        "blockFinset", "blockFinset_spec",
        "p91_tight_weak_coupling_window", "physical_rg_rates_from_E26",
        "bakry_emery_lsi", "instIsProbabilityMeasure_sunHaarProb",
        "instIsTopologicalGroupSUN", "sunDirichletForm_contraction",
        "hille_yosida_semigroup", "poincare_to_covariance_decay", "sun_variance_decay",
        "sunGeneratorData", "lieDerivReg_all",
        "generatorMatrix", "gen_skewHerm", "gen_trace_zero",
        "matExp_traceless_det_one", "dirichlet_lipschitz_contraction",
        "hille_yosida_core", "poincare_to_variance_decay",
        "variance_decay_from_bridge_and_poincare_semigroup_gap", "gronwall_variance_decay",
    }

    found = set(axioms.keys())
    missing = EXPECTED_NAMES - found
    extra   = found - EXPECTED_NAMES

    if missing:
        print(f"\u26a0\ufe0f  EXPECTED axioms NOT FOUND ({len(missing)}):")
        for n in sorted(missing):
            print(f"   {n}")
        print()
    else:
        print("\u2705 All 26 expected axiom names found")
        print()

    if extra:
        print(f"\u2139\ufe0f  UNEXPECTED axioms found ({len(extra)}) — new eliminations or spurious:")
        for n in sorted(extra):
            locs = axioms[n]
            print(f"   {n}  ({', '.join(f'{f}:{ln}' for f, ln in locs)})")
        print()

    # Summary
    print("=" * 60)
    print("CENSUS SUMMARY")
    print("=" * 60)
    print(f"  Total unique Lean axiom declaration names : {len(found)}")
    if duplicates:
        print(f"  \u26a0 Duplicate names (>1 file)            : {len(duplicates)}")
        print(f"    These will cause Lean redeclaration errors!")
        print(f"    Fix: run elimination_structural_v1.py (C3 fix)")
    print(f"  Distinct mathematical gaps (unique names) : {len(found)}")
    print(f"  Zero sorry                                : {'YES' if not sorry_hits else 'NO (' + str(len(sorry_hits)) + ' hits)'}")
    print()
    expected_count = len(EXPECTED_NAMES)
    if not sorry_hits and len(found) == expected_count and not missing:
        print(f"\u2705 Census matches AXIOM_FRONTIER.md v0.15.0")
        print(f"   {expected_count} mathematical gaps (unique declaration names)")
    elif len(found) < expected_count and not missing:
        eliminated = expected_count - len(found)
        print(f"\U0001f389 Census shows {eliminated} axiom(s) ELIMINATED vs v0.15.0 baseline!")
        print(f"   Update AXIOM_FRONTIER.md to reflect new count: {len(found)}")
    else:
        print(f"\u274c Census does NOT match AXIOM_FRONTIER.md v0.15.0")
        print(f"   Expected: {expected_count}  Found: {len(found)}")
        print(f"   Update AXIOM_FRONTIER.md before next push.")


if __name__ == "__main__":
    main()
