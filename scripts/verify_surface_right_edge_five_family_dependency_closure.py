"""Static closure check for the half-line five-family dependency ledger."""

import ast
from pathlib import Path

import surface_right_edge_five_family_cover_design as cover


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
ENTRY = "surface_right_edge_five_family_cover_design"


def local_imports(module):
    path = SCRIPTS / f"{module}.py"
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    found = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            names = (alias.name.split(".")[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            names = (node.module.split(".")[0],)
        else:
            continue
        for name in names:
            if (SCRIPTS / f"{name}.py").is_file():
                found.add(name)
    return found


def transitive_local_dependencies(entry=ENTRY):
    pending = [entry]
    reached = set()
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        pending.extend(sorted(local_imports(module) - reached))
    return reached


def verify():
    declared = {
        Path(relative).stem for relative in cover.DEPENDENCIES
        if relative.startswith("scripts/")
    }
    reached = transitive_local_dependencies()
    assert reached <= declared, (
        "undeclared transitive dependencies: " + ", ".join(sorted(reached-declared))
    )
    assert declared == reached, (
        "stale dependency entries: " + ", ".join(sorted(declared-reached))
    )
    return reached


if __name__ == "__main__":
    modules = verify()
    print("FIVE-FAMILY DEPENDENCY CLOSURE PASS", len(modules), "modules")
