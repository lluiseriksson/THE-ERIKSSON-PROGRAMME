#!/usr/bin/env python3
"""Local Gemma4/Ollama mathematical-discovery sidecar.

This runner keeps Gemma4 useful but non-authoritative. It reads a bounded
manifest of project context, asks the local Ollama model for candidate
mathematical ideas, and writes auditable artifacts. It never edits Lean, never
moves percentages, and never upgrades ledger status.
"""

from __future__ import annotations

import argparse
import json
import sys
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(r"C:\Users\lluis\.gemini\antigravity\scratch\THE-ERIKSSON-PROGRAMME")
STATE_FILE = REPO_ROOT / "registry" / "gemma4_state.json"
RUN_LOG = REPO_ROOT / "registry" / "gemma4_discovery_runs.jsonl"
LATEST_OUTPUT = REPO_ROOT / "dashboard" / "gemma4_math_discovery_latest.md"
OLLAMA_URL = "http://127.0.0.1:11434/api/generate"
DEFAULT_MODEL = "gemma4:e2b"

CONTEXT_FILES = [
    "JOINT_AGENT_PLANNER.md",
    "UNCONDITIONALITY_LEDGER.md",
    "AXIOM_FRONTIER.md",
    "F3_COUNT_DEPENDENCY_MAP.md",
    "dashboard/f3_decoder_iteration_scope.md",
    "dashboard/simplegraph_non_cut_vertex_codex_inventory.md",
    "AGENT_BUS.md",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def read_text_limited(path: Path, limit: int) -> str:
    if not path.exists():
        return f"[MISSING: {path}]"
    text = path.read_text(encoding="utf-8", errors="replace")
    if len(text) <= limit:
        return text
    return text[: limit // 2] + "\n\n[...TRUNCATED...]\n\n" + text[-limit // 2 :]


def load_state() -> dict[str, Any]:
    if not STATE_FILE.exists():
        return {}
    return json.loads(STATE_FILE.read_text(encoding="utf-8"))


def save_state(state: dict[str, Any]) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    STATE_FILE.write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def append_log(event: dict[str, Any]) -> None:
    RUN_LOG.parent.mkdir(parents=True, exist_ok=True)
    with RUN_LOG.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(event, ensure_ascii=False, sort_keys=True) + "\n")


def ollama_generate(model: str, prompt: str, num_predict: int, timeout: int) -> dict[str, Any]:
    payload = {
        "model": model,
        "prompt": prompt,
        "stream": False,
        "think": False,
        "options": {
            "temperature": 0.35,
            "top_p": 0.9,
            "num_predict": num_predict,
        },
    }
    data = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        OLLAMA_URL,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return json.loads(response.read().decode("utf-8", errors="replace"))
    except urllib.error.URLError as exc:
        raise RuntimeError(f"Ollama API unavailable at {OLLAMA_URL}: {exc}") from exc


def build_context(limit_per_file: int) -> tuple[str, list[str]]:
    chunks: list[str] = []
    manifest: list[str] = []
    for rel in CONTEXT_FILES:
        path = REPO_ROOT / rel
        manifest.append(rel)
        chunks.append(f"\n\n===== {rel} =====\n{read_text_limited(path, limit_per_file)}")
    return "\n".join(chunks), manifest


def build_prompt(focus: str, context: str) -> str:
    return f"""You are Gemma4-MathDiscovery, a local HEURISTIC_ONLY sidecar for THE-ERIKSSON-PROGRAMME.

Hard rules:
- Do not claim the Clay Yang-Mills problem is solved.
- Do not move any project percentage or ledger status.
- Treat every idea as HEURISTIC unless it is later formalized in Lean and audited.
- Prefer exact formalization targets over prose.
- Every candidate must include a falsification test.

Current requested focus:
{focus}

Project context:
{context}

Your output will be rejected if it is generic. Do not summarize the project.
Do not write "Analysis and Recommendation". Do not say "derive the missing
theorem" without naming the theorem shape.

Write a compact Markdown report with exactly these headings and fill every
field. If the context is insufficient, say exactly which file or identifier is
missing in the relevant field.

## Status
Say whether this is heuristic-only.

## Smallest Live Blocker
Name the smallest blocker visible from the context.

## Candidate Ideas
Give 3 candidates. For each:
- Label: HEURISTIC or FORMALIZATION_TARGET
- Target statement:
- Existing identifiers/files:
- Why it might help:
- Falsification test:
- Lean route:
- Cowork audit question:

## Recommended Next Codex Task
One precise task only.

## Risks
List overclaiming or invalidity risks.
"""


def assess_output(response: str) -> str:
    required = [
        "## Status",
        "## Smallest Live Blocker",
        "## Candidate Ideas",
        "## Recommended Next Codex Task",
        "## Risks",
        "Falsification test:",
        "Cowork audit question:",
    ]
    missing = [item for item in required if item not in response]
    if missing:
        return "WEAK_OUTPUT_MISSING_" + ",".join(missing)
    generic_phrases = [
        "derive the necessary structural theorem",
        "specific mathematical result",
        "main objective",
    ]
    if any(phrase in response.lower() for phrase in generic_phrases):
        return "WEAK_OUTPUT_GENERIC"
    return "STRUCTURED_HEURISTIC_OUTPUT"


def write_report(model: str, focus: str, manifest: list[str], response: str, meta: dict[str, Any]) -> None:
    now = utc_now()
    report = "\n".join(
        [
            "# Gemma4 Math Discovery Latest",
            "",
            f"- generated_at: `{now}`",
            f"- model: `{model}`",
            "- authority: `HEURISTIC_ONLY`",
            f"- output_assessment: `{assess_output(response)}`",
            "- ledger_status_change: `NONE`",
            "- percentage_change: `NONE`",
            "",
            "## Focus",
            "",
            focus,
            "",
            "## Context Manifest",
            "",
            *[f"- `{item}`" for item in manifest],
            "",
            "## Gemma Output",
            "",
            response.strip(),
            "",
            "## Runner Metadata",
            "",
            "```json",
            json.dumps(meta, indent=2, ensure_ascii=False),
            "```",
            "",
        ]
    )
    LATEST_OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    LATEST_OUTPUT.write_text(report, encoding="utf-8")


def cmd_status(args: argparse.Namespace) -> int:
    state = load_state()
    print(json.dumps(state, indent=2, ensure_ascii=False))
    return 0


def cmd_probe(args: argparse.Namespace) -> int:
    result = ollama_generate(args.model, "Reply with exactly GEMMA4_SIDEcar_READY", 20, args.timeout)
    response = (result.get("response") or "").strip()
    state = load_state()
    state.update(
        {
            "status": "AVAILABLE" if "GEMMA4_SIDEcar_READY" in response else "UNEXPECTED_RESPONSE",
            "model": args.model,
            "last_probe": utc_now(),
            "last_probe_response": response,
        }
    )
    save_state(state)
    append_log({"time": utc_now(), "event": "probe", "model": args.model, "response": response})
    print(response)
    return 0


def cmd_run(args: argparse.Namespace) -> int:
    context, manifest = build_context(args.limit_per_file)
    prompt = build_prompt(args.focus, context)
    result = ollama_generate(args.model, prompt, args.num_predict, args.timeout)
    response = (result.get("response") or "").strip()
    assessment = assess_output(response)
    meta = {
        "done": result.get("done"),
        "done_reason": result.get("done_reason"),
        "total_duration": result.get("total_duration"),
        "prompt_eval_count": result.get("prompt_eval_count"),
        "eval_count": result.get("eval_count"),
        "output_assessment": assessment,
    }
    write_report(args.model, args.focus, manifest, response, meta)
    state = load_state()
    state.update(
        {
            "status": "RAN_DISCOVERY_PASS",
            "model": args.model,
            "last_run": utc_now(),
            "latest_output": str(LATEST_OUTPUT.relative_to(REPO_ROOT)),
            "authority": "HEURISTIC_ONLY",
            "may_move_ledger_status": False,
            "may_move_percentages": False,
            "last_output_assessment": assessment,
        }
    )
    save_state(state)
    append_log(
        {
            "time": utc_now(),
            "event": "discovery_run",
            "model": args.model,
            "focus": args.focus,
            "context_manifest": manifest,
            "output": str(LATEST_OUTPUT.relative_to(REPO_ROOT)),
            "metadata": meta,
            "assessment": assessment,
        }
    )
    print(f"Wrote {LATEST_OUTPUT}")
    return 0


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    status = sub.add_parser("status")
    status.set_defaults(func=cmd_status)

    probe = sub.add_parser("probe")
    probe.add_argument("--model", default=DEFAULT_MODEL)
    probe.add_argument("--timeout", type=int, default=45)
    probe.set_defaults(func=cmd_probe)

    run = sub.add_parser("run")
    run.add_argument("--model", default=DEFAULT_MODEL)
    run.add_argument(
        "--focus",
        default=(
            "Find non-overclaiming candidate routes for the B.2 anchored word "
            "decoder / recursive parent-map after v2.63 safe deletion."
        ),
    )
    run.add_argument("--limit-per-file", type=int, default=2500)
    run.add_argument("--num-predict", type=int, default=900)
    run.add_argument("--timeout", type=int, default=180)
    run.set_defaults(func=cmd_run)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
