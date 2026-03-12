#!/usr/bin/env python3
import re
import sys
from pathlib import Path
from itertools import chain

LEAN_DIRS = ["YangMills", "Lean"]
FORBIDDEN = ["sorry", "axiom ", "placeholder", "default", "rfl", "exact ⟨"]

def scan():
    errors = []
    # Usar el directorio de trabajo actual
    root_dir = Path(".")
    
    for ext in (".lean", ".Lean"):
        for d in LEAN_DIRS:
            dir_path = root_dir / d
            if dir_path.exists() and dir_path.is_dir():
                for p in dir_path.rglob(f"*{ext}"):
                    text = p.read_text(encoding="utf-8")
                    for line_no, line in enumerate(text.splitlines(), 1):
                        if any(f in line for f in FORBIDDEN):
                            errors.append(f"{p}:{line_no} → {line.strip()}")
                            
    if errors:
        print("❌ PROHIBIDO EN MAIN BRANCH:", len(errors))
        for e in errors[:10]: print("   ", e)
        sys.exit(1)
    print("✅ No se detectaron sorry/axiom/placeholders en Lean files")
    print("   (todos los nodos críticos siguen limpios)")

if __name__ == "__main__":
    scan()
