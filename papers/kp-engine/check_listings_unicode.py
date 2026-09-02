"""Report every non-ASCII character in main.tex and whether the listings
`literate` table declares it (pdflatex + listings needs every non-ASCII
character inside a listing to be declared)."""
import re, sys, pathlib, collections
if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
src = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else 'main.tex').read_text(encoding='utf-8')
lit = re.search(r'literate=(.*?)\}\s*\n\s*\n', src, re.S)
keys = set()
if lit:
    for m in re.finditer(r'\{([^{}]+)\}\{\{', lit.group(1)):
        keys.add(m.group(1))
counts = collections.Counter(ch for ch in src if ord(ch) > 127)
bad = 0
for ch, n in sorted(counts.items()):
    ok = ch in keys or any(ch in k for k in keys)
    print(f"U+{ord(ch):04X} {ch!r} x{n} {'literate' if ok else 'NOT IN LITERATE TABLE'}")
    bad += (not ok)
print("undeclared non-ASCII characters:", bad)
