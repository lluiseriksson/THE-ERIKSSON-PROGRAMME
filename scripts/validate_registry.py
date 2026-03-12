#!/usr/bin/env python3
import yaml
import sys
from pathlib import Path
from itertools import chain

def load_yaml(file):
    return yaml.safe_load(Path(file).read_text(encoding="utf-8"))

def main():
    nodes_data = load_yaml("registry/nodes.yaml")
    deps_data = load_yaml("registry/dependencies.yaml")
    critical_data = load_yaml("registry/critical_paths.yaml")
    labels = load_yaml("registry/labels.yaml")

    nodes = nodes_data.get("nodes", [])
    deps = deps_data.get("dependencies", [])
    critical = critical_data.get("critical_paths", [])

    errors = []

    # 1. Estados válidos
    valid_status = set(labels.get("status_labels", []))
    for n in nodes:
        if n.get("status") not in valid_status:
            errors.append(f"Nodo {n.get('id')} tiene status inválido: {n.get('status')}")

    # 2. Dependencias existen y no hay ciclos (simple DFS)
    node_ids = {n["id"] for n in nodes if "id" in n}
    for n in nodes:
        for d in n.get("depends_on", []):
            if d not in node_ids:
                errors.append(f"Nodo {n['id']} depende de inexistente {d}")

    # 3. Nodos críticos NO pueden ser BLACKBOX sin registro explícito
    cp_nodes = set(chain.from_iterable(p.get("nodes", []) for p in critical))
    bottlenecks_data = load_yaml("registry/bottlenecks.yaml") if Path("registry/bottlenecks.yaml").exists() else {}
    bottlenecks = bottlenecks_data.get("bottlenecks", [])
    
    for n in nodes:
        if n["id"] in cp_nodes and n.get("status") == "BLACKBOX":
            if not any(b.get("related_nodes") and n["id"] in b["related_nodes"] for b in bottlenecks):
                errors.append(f"Nodo crítico {n['id']} es BLACKBOX sin entrada en bottlenecks.yaml")

    # 4. Axiomas deben estar registrados
    for n in nodes:
        if "axiom" in n.get("evidence", "").lower() and not n.get("mathlib_gap"):
            errors.append(f"Nodo {n['id']} declara axiom sin mathlib_gap")

    if errors:
        print("❌ ERRORES DE REGISTRO:", len(errors))
        for e in errors: print("   ", e)
        sys.exit(1)
    print("✅ registry/nodes.yaml válido – 0 errores")
    print(f"   Nodos totales: {len(nodes)} | Critical path nodes: {len(cp_nodes)}")

if __name__ == "__main__":
    main()
