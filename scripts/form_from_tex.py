"""Derive the submission form's abstract FROM the paper, instead of retyping it.

The form carried a hand-typed parallel copy of the abstract.  It drifted: the
sentence "the same weight that destroys uniformity leaves positivity exactly
where it was" was retracted from the paper in v1.1 and purged from the module in
v1.2, and was still alive here in v1.4 --- in the one artefact that actually
leaves the building.

Same lesson as the counter row: a text that no process derives from the source
is not a copy, it is a fork.
"""
import io
import re

TEX = r"C:\Users\lluis\AppData\Local\Temp\eriksson-push2\papers\spatial-reflection\spatial_reflection.tex"
FORM = r"C:\Users\lluis\Desktop\YangMills\ENVIAR-AHORA\FORMULARIO-spatial-reflection.txt"

tex = io.open(TEX, encoding="utf-8", newline="").read()
abs_tex = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", tex, re.S).group(1)

MATH = {
    r"\beta\ge0": "beta >= 0", r"\beta<0": "beta < 0", r"\beta": "beta",
    r"\langle v, K^{N} v\rangle": "<v, K^N v>",
    r"\langle K^{m}v, K K^{m} v\rangle": "<K^m v, K K^m v>",
    r"2(e^{\beta}-e^{-\beta})^{N}": "2(e^beta - e^-beta)^N",
    r"\mathrm{specGap}<\lambda": "specGap < lambda",
    r"\mathrm{specRatio}(L)": "specRatio(L)",
    r"\sqrt{w}": "sqrt(w)", r"w(\varnothing)": "w(empty)",
    r"\SU(N)": "SU(N)", r"L=0": "L = 0", r"\beta=0": "beta = 0",
    r"N": "N", r"K": "K", r"w": "w",
    r"1": "1", r"v": "v",
}


def demath(m):
    body = m.group(1)
    if body in MATH:
        return MATH[body]
    raise SystemExit("unhandled math in abstract: $" + body + "$")


t = abs_tex
t = re.sub(r"\\textbf\{([^{}]*)\}", lambda m: m.group(1).upper(), t)
t = re.sub(r"\\emph\{([^{}]*)\}", lambda m: m.group(1).upper(), t)
t = re.sub(r"\\cite\{[^{}]*\}", "", t)
SECTIONS = {"sec:scope": "the scope section", "sec:gates": "the gates section"}
t = re.sub(r"\\S\\ref\{([^{}]*)\}", lambda m: SECTIONS[m.group(1)], t)
t = re.sub(r"\\ref\{[^{}]*\}", "", t)
t = re.sub(r"\$([^$]*)\$", demath, t)
t = re.sub(r"(?i)(osterwalder|yang)--", lambda m: m.group(1) + "-", t)
t = t.replace("---", "--")
t = t.replace("~", " ")
t = re.sub(r"[ \t]+", " ", t)
t = re.sub(r"[ \t]*\n?[ \t]*([.,;:])", r"\1", t)   # \cite removal leaves a gap
t = re.sub(r"\n{3,}", "\n\n", t).strip()

# rewrap at 78 columns, preserving paragraph breaks
out = []
for para in t.split("\n\n"):
    words, line = para.split(), ""
    for wd in words:
        if len(line) + len(wd) + 1 > 78:
            out.append(line)
            line = wd
        else:
            line = (line + " " + wd).strip()
    out.append(line)
    out.append("")
abstract = "\n".join(out).strip()

RETRACTED = "weight that destroys uniformity leaves positivity"
assert RETRACTED not in abstract, "the retracted sentence is still in the paper!"

f = io.open(FORM, encoding="utf-8", newline="").read()
nl = "\r\n" if "\r\n" in f else "\n"
start = f.index("[4] ABSTRACT")
end = f.index("[5] COMMENTS FIELD")
head = "[4] ABSTRACT (derived from the paper's own abstract -- do not retype)" + nl
head += "-" * 70 + nl + nl
f = f[:start] + head + abstract.replace("\n", nl) + nl + nl + nl + f[end:]
io.open(FORM, "w", encoding="utf-8", newline="").write(f)
print("form abstract regenerated from the .tex (%d chars)" % len(abstract))
