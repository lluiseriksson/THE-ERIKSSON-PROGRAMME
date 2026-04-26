from __future__ import annotations

import json
import sys
from pathlib import Path

try:
    import yaml
except ImportError as exc:  # pragma: no cover - environment diagnostic
    raise SystemExit("PyYAML is required for joint_planner_report.py") from exc


REPO_ROOT = Path(__file__).resolve().parents[1]
METRICS_FILE = REPO_ROOT / "registry" / "progress_metrics.yaml"


def load_metrics() -> dict:
    with METRICS_FILE.open("r", encoding="utf-8") as handle:
        data = yaml.safe_load(handle) or {}
    if not isinstance(data, dict):
        raise ValueError(f"{METRICS_FILE} must contain a YAML mapping")
    return data


def validate(data: dict) -> list[str]:
    errors: list[str] = []
    metrics = data.get("metrics", {})
    required = ["clay_as_stated", "lattice_small_beta", "named_frontier_retirement"]
    for key in required:
        if key not in metrics:
            errors.append(f"missing metric: {key}")
        elif "percent" not in metrics[key]:
            errors.append(f"metric {key} has no percent")

    components = data.get("components", [])
    if not isinstance(components, list):
        errors.append("components must be a list")
    else:
        contribution = sum(float(item.get("contribution_percent", 0)) for item in components)
        lattice = float(metrics.get("lattice_small_beta", {}).get("percent", 0))
        if abs(contribution - lattice) > 0.75:
            errors.append(
                f"lattice component contributions sum to {contribution}, expected about {lattice}"
            )

    if data.get("global_status") != "NOT_ESTABLISHED":
        errors.append("global_status must remain NOT_ESTABLISHED without complete formal evidence")
    return errors


def render_markdown(data: dict) -> str:
    metrics = data["metrics"]
    lines = [
        "## Joint Planner Snapshot",
        "",
        f"Updated: `{data.get('updated_at', 'unknown')}`",
        "",
        "| Metric | Percent | Status |",
        "|---|---:|---|",
    ]
    for key in ["clay_as_stated", "lattice_small_beta", "named_frontier_retirement"]:
        item = metrics[key]
        lines.append(f"| {item['title']} | {item['percent']}% | {item['status']} |")
    discount = metrics["lattice_small_beta"].get("honest_discounted_percent_range")
    if discount:
        lines.append(f"| Honest lattice discount | {discount}% | Caveat on vacuous/low-content retirements |")
    lines.extend(["", "Critical path:"])
    for item in data.get("critical_path", []):
        lines.append(f"{item['order']}. `{item['id']}` - {item['description']}")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    mode = argv[1] if len(argv) > 1 else "markdown"
    data = load_metrics()
    errors = validate(data)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    if mode == "json":
        print(json.dumps(data, indent=2, ensure_ascii=False))
    elif mode == "validate":
        print("joint planner metrics: OK")
    else:
        print(render_markdown(data))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
