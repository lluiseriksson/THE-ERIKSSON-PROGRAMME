"""Print a paper's abstract as plain text, DERIVED from its .tex.

Retyping an abstract into a submission form creates a fork, and forks drift: the
form for paper 12 still carried a sentence the paper had retracted two versions
earlier, in the one artefact that actually leaves the building.  So the form's
abstract is generated, never typed.

    python scripts/abstract_from_tex.py <tex> [--wrap N]

Fails loudly on any math token it does not recognise rather than guessing, so a
new formula in the paper cannot be silently mangled into the form.
"""
import io
import re
import sys

MATH = {
    r"2m+2": "2m+2",
    r"\mathrm{past}\,X": "past(X)",
    r"\mathrm{rev}\,X": "rev(X)",
    r"L": "L", r"m": "m", r"w": "w", r"X": "X", r"F": "F", r"1": "1",
    r"W": "W", r"K": "K", r"N": "N",
    r"\beta\ge0": "beta >= 0",
    r"\beta": "beta",
    r"L=0": "L = 0",
    r"L\ge1": "L >= 1",
    r"\Z_2": "Z_2",
    r"1/w(\sigma)": "1/w(sigma)",
    r"\sqrt{w}": "sqrt(w)",
    r"\SU(N)": "SU(N)",
    r"\S\ref{sec:open}": "the status table",
}

DISPLAY = {
    r"\sum_{X}\ \overline{F(\mathrm{past}\,X)}\ F(\mathrm{rev}\,X)\ W(X)\ \ge\ 0 ,":
        "    sum over whole paths X of  conj(F(past X)) * F(rev X) * W(X)  >=  0",
}


def demath(m):
    body = m.group(1)
    if body in MATH:
        return MATH[body]
    raise SystemExit("unhandled inline math: $" + body + "$")


def dedisplay(m):
    body = m.group(1).strip()
    if body in DISPLAY:
        return "\n\n" + DISPLAY[body] + "\n"
    raise SystemExit("unhandled display math:\n" + body)


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    tex = io.open(sys.argv[1], encoding="utf-8", newline="").read()
    wrap = 78
    if "--wrap" in sys.argv:
        wrap = int(sys.argv[sys.argv.index("--wrap") + 1])

    m = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", tex, re.S)
    if m is None:
        print("no abstract found in", sys.argv[1])
        return 2
    t = m.group(1)

    # Math FIRST: uppercasing \emph{} before it turns `$\beta$` inside an
    # emphasis into `$\BETA$`, and then the token table rejects a name it wrote
    # itself.  Substituting math first makes the two passes independent.
    t = re.sub(r"\\\[(.*?)\\\]", dedisplay, t, flags=re.S)
    t = re.sub(r"\$([^$]*)\$", demath, t)
    t = re.sub(r"\\textbf\{([^{}]*)\}", lambda x: x.group(1).upper(), t)
    t = re.sub(r"\\emph\{([^{}]*)\}", lambda x: x.group(1).upper(), t)
    t = re.sub(r"\\cite\{[^{}]*\}", "", t)
    t = re.sub(r"\\S\\ref\{[^{}]*\}", "the status table", t)
    t = re.sub(r"(?i)(osterwalder|yang)--", lambda x: x.group(1) + "-", t)
    t = t.replace("---", "--").replace("~", " ")
    t = re.sub(r"[ \t]+", " ", t)
    t = re.sub(r"[ \t]*\n?[ \t]*([.,;:])", r"\1", t)
    t = re.sub(r"\n{3,}", "\n\n", t).strip()

    out = []
    for para in t.split("\n\n"):
        if para.startswith("    "):          # a display: keep it as it is
            out.append(para)
            out.append("")
            continue
        line = ""
        for word in para.split():
            if len(line) + len(word) + 1 > wrap:
                out.append(line)
                line = word
            else:
                line = (line + " " + word).strip()
        out.append(line)
        out.append("")
    print("\n".join(out).strip())
    return 0


if __name__ == "__main__":
    sys.exit(main())
