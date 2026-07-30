from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfbase import pdfmetrics
from reportlab.platypus import (
    KeepTogether,
    PageBreak,
    Paragraph,
    SimpleDocTemplate,
    Spacer,
    Table,
    TableStyle,
)


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / "output" / "pdf"
OUTPUT.mkdir(parents=True, exist_ok=True)
PDF = OUTPUT / "local_gibbs_thermodynamic_limit.pdf"


def register_fonts():
    candidates = [
        (
            Path("C:/Windows/Fonts/cambria.ttc"),
            Path("C:/Windows/Fonts/cambriab.ttf"),
            Path("C:/Windows/Fonts/cambriai.ttf"),
        ),
        (
            Path("C:/Windows/Fonts/georgia.ttf"),
            Path("C:/Windows/Fonts/georgiab.ttf"),
            Path("C:/Windows/Fonts/georgiai.ttf"),
        ),
    ]
    for regular, bold, italic in candidates:
        if regular.exists() and bold.exists() and italic.exists():
            pdfmetrics.registerFont(TTFont("PaperSerif", str(regular), subfontIndex=0))
            pdfmetrics.registerFont(TTFont("PaperSerif-Bold", str(bold)))
            pdfmetrics.registerFont(TTFont("PaperSerif-Italic", str(italic)))
            return
    pdfmetrics.registerFont(TTFont("PaperSerif", "C:/Windows/Fonts/times.ttf"))
    pdfmetrics.registerFont(TTFont("PaperSerif-Bold", "C:/Windows/Fonts/timesbd.ttf"))
    pdfmetrics.registerFont(TTFont("PaperSerif-Italic", "C:/Windows/Fonts/timesi.ttf"))


register_fonts()

BASE = colors.HexColor("#172033")
ACCENT = colors.HexColor("#185A73")
PALE = colors.HexColor("#EAF3F6")
RULE = colors.HexColor("#93A9B3")
LIGHT = colors.HexColor("#F5F7F8")

styles = getSampleStyleSheet()
styles.add(
    ParagraphStyle(
        name="PaperTitle",
        fontName="PaperSerif-Bold",
        fontSize=20,
        leading=24,
        alignment=TA_CENTER,
        textColor=BASE,
        spaceAfter=6 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="PaperAuthor",
        fontName="PaperSerif",
        fontSize=11,
        leading=14,
        alignment=TA_CENTER,
        textColor=ACCENT,
        spaceAfter=2 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="PaperMeta",
        fontName="PaperSerif-Italic",
        fontSize=8.5,
        leading=11,
        alignment=TA_CENTER,
        textColor=colors.HexColor("#4D5966"),
        spaceAfter=8 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="AbstractText",
        fontName="PaperSerif",
        fontSize=9.3,
        leading=13.2,
        alignment=TA_JUSTIFY,
        textColor=BASE,
        leftIndent=7 * mm,
        rightIndent=7 * mm,
        spaceAfter=5 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="SectionHead",
        fontName="PaperSerif-Bold",
        fontSize=14,
        leading=17,
        textColor=ACCENT,
        spaceBefore=4.2 * mm,
        spaceAfter=2.2 * mm,
        keepWithNext=True,
    )
)
styles.add(
    ParagraphStyle(
        name="SubHead",
        fontName="PaperSerif-Bold",
        fontSize=11,
        leading=14,
        textColor=BASE,
        spaceBefore=2.5 * mm,
        spaceAfter=1.2 * mm,
        keepWithNext=True,
    )
)
styles.add(
    ParagraphStyle(
        name="BodyText2",
        fontName="PaperSerif",
        fontSize=9.4,
        leading=12.7,
        alignment=TA_JUSTIFY,
        textColor=BASE,
        spaceAfter=1.8 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="TheoremText",
        fontName="PaperSerif",
        fontSize=9.1,
        leading=12.5,
        textColor=BASE,
        leftIndent=4 * mm,
        rightIndent=4 * mm,
        spaceAfter=1.5 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="CodeText",
        fontName="Courier",
        fontSize=7.7,
        leading=10.4,
        textColor=colors.HexColor("#23303A"),
        leftIndent=5 * mm,
        rightIndent=5 * mm,
        spaceBefore=1.2 * mm,
        spaceAfter=2.5 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="Caption",
        fontName="PaperSerif-Italic",
        fontSize=7.8,
        leading=10,
        textColor=colors.HexColor("#596773"),
        spaceAfter=2 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="Reference",
        fontName="PaperSerif",
        fontSize=7.8,
        leading=9.7,
        textColor=BASE,
        leftIndent=5 * mm,
        firstLineIndent=-5 * mm,
        spaceAfter=0.8 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="ReferenceHead",
        fontName="PaperSerif-Bold",
        fontSize=12,
        leading=14,
        textColor=ACCENT,
        spaceBefore=2 * mm,
        spaceAfter=1 * mm,
        keepWithNext=True,
    )
)


def P(text, style="BodyText2"):
    return Paragraph(text, styles[style])


def theorem(title, body):
    box = Table(
        [[P(f"<b>{title}</b><br/>{body}", "TheoremText")]],
        colWidths=[166 * mm],
        hAlign="CENTER",
    )
    box.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, -1), PALE),
                ("BOX", (0, 0), (-1, -1), 0.7, ACCENT),
                ("LEFTPADDING", (0, 0), (-1, -1), 4 * mm),
                ("RIGHTPADDING", (0, 0), (-1, -1), 4 * mm),
                ("TOPPADDING", (0, 0), (-1, -1), 3 * mm),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 2.5 * mm),
            ]
        )
    )
    return KeepTogether([box, Spacer(1, 2.5 * mm)])


def code(lines):
    escaped = (
        lines.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace("\n", "<br/>")
        .replace(" ", "&nbsp;")
    )
    box = Table([[P(escaped, "CodeText")]], colWidths=[162 * mm], hAlign="CENTER")
    box.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, -1), LIGHT),
                ("BOX", (0, 0), (-1, -1), 0.45, RULE),
                ("LEFTPADDING", (0, 0), (-1, -1), 1.5 * mm),
                ("RIGHTPADDING", (0, 0), (-1, -1), 1.5 * mm),
                ("TOPPADDING", (0, 0), (-1, -1), 1.5 * mm),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 1.5 * mm),
            ]
        )
    )
    return KeepTogether([box, Spacer(1, 2 * mm)])


def header_footer(canvas, doc):
    canvas.saveState()
    width, height = A4
    canvas.setStrokeColor(RULE)
    canvas.setLineWidth(0.35)
    canvas.line(22 * mm, height - 15 * mm, width - 22 * mm, height - 15 * mm)
    canvas.setFont("PaperSerif", 7.5)
    canvas.setFillColor(colors.HexColor("#65737E"))
    canvas.drawString(
        22 * mm,
        height - 11.5 * mm,
        "Machine-checked local Gibbs thermodynamic limit",
    )
    canvas.drawRightString(
        width - 22 * mm,
        12 * mm,
        f"{doc.page}",
    )
    canvas.restoreState()


story = []
story.append(P("A Machine-Checked Thermodynamic Limit for Local Lattice Gauge Gibbs States", "PaperTitle"))
story.append(P("Lluis Eriksson", "PaperAuthor"))
story.append(
    P(
        "THE ERIKSSON PROGRAMME - Lean 4 artifact, branch "
        "<font name='Courier'>codex/thermodynamic-limit-kp</font>, "
        "verified source checkpoint <font name='Courier'>0be45284</font>",
        "PaperMeta",
    )
)

story.append(P("<b>Abstract.</b>", "AbstractText"))
story.append(
    P(
        "We formalize in Lean 4 the thermodynamic limit of bounded local Gibbs "
        "expectations for a periodic lattice gauge model in a uniform "
        "Kotecky-Preiss regime. The proof treats the complete finite-volume "
        "sequence: an exact one-volume marked expansion cancels the extensive "
        "far gas algebraically, common-window terms are transported exactly, "
        "and the remaining boundary contribution is bounded by the existing "
        "volume-uniform pinned cluster tail "
        "<font name='Courier'>connectedLattice_pinned_tail_volumeUniform</font>. "
        "The resulting explicit Cauchy modulus tends to zero, so completeness "
        "constructs an infinite-volume positive normalized real local state. "
        "On the intrinsic integer-coordinate local-observable algebra, the "
        "state carries a genuine additive action of Z^d and is invariant under "
        "every integer translation, including inverses. For SU(2), Haar "
        "probability measure, and the physical Wilson plaquette energy "
        "Re tr(U), the hypotheses are discharged throughout the explicit "
        "punctured intervals <b>0 &lt; |beta| &lt;= 10^-5</b> in d=2 and "
        "<b>0 &lt; |beta| &lt;= 10^-6</b> in the physical lattice dimension "
        "d=4. We also construct "
        "a genuine centered free-boundary exhaustion and prove that its complete "
        "cofinal sequence converges to the same state as periodic boundary "
        "conditions. Finally, the normalized finite-volume two-plaquette "
        "truncated-correlation bound passes unchanged to the state under "
        "explicit eventual realization and separation hypotheses. We do not "
        "claim arbitrary boundary conditions, a C*-algebraic state, a "
        "continuum limit, Osterwalder-Schrader "
        "reconstruction, or progress on the continuum Yang-Mills mass-gap "
        "problem.",
        "AbstractText",
    )
)

story.append(P("1. Introduction", "SectionHead"))
story.append(
    P(
        "Cluster expansions are a standard route from finite-volume polymer "
        "representations to analytic and probabilistic control in regimes of "
        "small activities. The Kotecky-Preiss criterion gives a particularly "
        "useful volume-uniform convergence mechanism for abstract polymer "
        "models [1]. For lattice gauge systems, however, a thermodynamic-limit "
        "argument must still connect the abstract cluster estimates to genuine "
        "normalized Gibbs expectations. This connection is delicate because "
        "the numerator and partition function are both extensive; neither is "
        "expected to converge separately.",
    )
)
story.append(
    P(
        "The underlying strong-coupling existence and clustering statement is "
        "classical; in particular, it belongs to the lattice gauge theory "
        "framework of Osterwalder and Seiler [2]. The contribution claimed here "
        "is not a new analytic thermodynamic-limit theorem, but a mechanically "
        "checked derivation from the finite Gibbs integral through every "
        "marked-expansion, cancellation, tail, and completeness bridge, together "
        "with an explicit proof that the packaged KP hypotheses are inhabited.",
    )
)
story.append(
    P(
        "The formal development studied here closes that connection for local "
        "observables. Its central design rule is to cancel the far gas exactly "
        "before applying estimates. The proof then compares two finite volumes "
        "through a common non-wrapping window. Clusters that remain inside the "
        "window agree term by term, including their Ursell coefficients and "
        "activity monomials. Clusters that leave it are support-pinned boundary "
        "tails, and are controlled uniformly in volume.",
    )
)
story.append(
    P(
        "The output is not an abstract compactness statement. It is a Cauchy "
        "theorem for the complete sequence of genuine Gibbs expectations, "
        "followed by a definition of the limit using completeness. This "
        "distinction is essential: a convergent subsequence would not establish "
        "a unique thermodynamic state or boundary-condition comparison.",
    )
)

story.append(P("2. Formal-design lessons", "SectionHead"))
story.append(
    P(
        "The main formal contribution is not the invention of a new cluster "
        "expansion, but the choice of interfaces that make every analytic "
        "bridge auditable. Several mathematically plausible shortcuts were "
        "rejected because they could support a formally correct endpoint while "
        "leaving the intended Gibbs statement unproved. This section records "
        "the four design decisions that most strongly shaped the development. "
        "They are reusable beyond this model because each concerns the boundary "
        "between an abstract convergence theorem and the concrete object that "
        "is supposed to converge.",
    )
)

story.append(P("2.1. Rejecting a free bulk hypothesis", "SubHead"))
story.append(
    P(
        "A tempting interface is to assume that the normalized expectation has "
        "already been decomposed into a volume-independent bulk term plus a "
        "small boundary correction. Such a theorem can be useful after the "
        "decomposition has been proved, but it cannot itself establish the "
        "thermodynamic limit of the genuine Gibbs integral. If the bulk term is "
        "an unconstrained argument, the caller may instantiate it without any "
        "connection to the numerator or the partition function. The resulting "
        "Cauchy theorem is then conditional on exactly the identity that carries "
        "the mathematical content.",
    )
)
story.append(
    P(
        "The accepted interface therefore starts from "
        "<font name='Courier'>localGibbsExpectation</font> and proves a literal "
        "one-volume identity. The Boltzmann product is expanded into plaquette "
        "subsets, connected components disjoint from the insertion are "
        "factorized as the ordinary gas, and the unique sector touching the "
        "finite support is retained as a marked activity. Only after this exact "
        "factorization is the common far gas cancelled between numerator and "
        "denominator. Thus the later error term is not postulated: it is the "
        "restriction difference left by an algebraic equality. A terminal "
        "theorem is accepted only if its conclusion names the genuine Gibbs "
        "expectation and its hypotheses contain no free bulk or cancellation "
        "oracle.",
    )
)

story.append(P("2.2. Local coordinate charts instead of global volume embeddings", "SubHead"))
story.append(
    P(
        "Comparing torus sizes N and M might suggest constructing a global map "
        "between their edge sets or gauge-configuration spaces. There is no "
        "canonical such map compatible with periodic wraparound: a coordinate "
        "that is local in one torus can cross a seam in another, and a global "
        "configuration map would impose choices irrelevant to a local "
        "observable. Building a universal-cover theory for entire "
        "configurations would also mix the finite product measure with geometry "
        "that is needed only on a bounded window.",
    )
)
story.append(
    P(
        "Instead, an observable stores a finite coordinate chart independent "
        "of the ambient volume. A comparison chooses one non-wrapping window "
        "large enough for the support and for every cluster below the current "
        "size cutoff. Plaquettes, polymer activities, incompatibility, Ursell "
        "coefficients, and the marked integral are transported exactly inside "
        "that window; no map between complete gauge configurations is required. "
        "The residual terms are precisely clusters that leave the chart, so the "
        "geometric failure of transport becomes the event controlled by the "
        "pinned tail.",
    )
)
story.append(
    P(
        "The same principle resolves inverse translations. Natural-number "
        "coordinates support positive shifts but do not form a translation "
        "group with a volume-independent guard. The final observable type uses "
        "coordinates in Z^d and realizes them periodically by integer "
        "remainders. A finite lower shift places any given observable in the "
        "old natural-coordinate chart, and the two realizations agree literally "
        "beyond an explicit bound. This is an eventual chart comparison, not a "
        "volume-dependent simulation of a negative shift by N-1 positive "
        "steps.",
    )
)

story.append(P("2.3. Keeping the rooted multiplicity", "SubHead"))
story.append(
    P(
        "At cluster order n, an Ursell tuple has n+1 polymer coordinates. The "
        "boundary event says that some coordinate meets the marked region and "
        "some coordinate leaves the common window. Existing KP tails are rooted "
        "at coordinate zero. Reindexing an arbitrary witness to zero therefore "
        "introduces a factor n+1. Choosing the first witness does not remove the "
        "factor in general: once the mark is forgotten, as many as n+1 marked "
        "tuples can map to the same unmarked tuple. Without an additional "
        "uniqueness theorem for the touching polymer, the multiplicity is "
        "intrinsic.",
    )
)
story.append(
    P(
        "The development exposes this combinatorial derivative rather than "
        "hiding it in a coarse constant. The factorial normalization obeys "
        "(n+1)/(n+1)! = 1/n!, and the remaining cardinality cost is absorbed by "
        "one unit of activity tilt. Consequently the honest hypothesis is the "
        "KP criterion at t+epsilon+1, not merely at t+epsilon. This stronger "
        "field propagates through the boundary theorem and is visible in the "
        "non-vacuity calculation. Recording the factor at the reindexing site "
        "prevents a downstream estimate from appearing stronger than the "
        "combinatorics justify.",
    )
)

story.append(P("2.4. Treating non-vacuity as part of the API", "SubHead"))
story.append(
    P(
        "A packaged KP theorem may be internally consistent while having no "
        "proved interacting instance. In particular, beta=0 annihilates every "
        "Mayer activity and yields only the free product measure. It is a useful "
        "normalization check, but it does not demonstrate that the simultaneous "
        "radius, smallness, tilted, and marked-radius hypotheses can hold away "
        "from the trivial point. Declaring the abstract structure inhabited only "
        "at beta=0 would therefore make the advertised strong-coupling result "
        "mathematically empty.",
    )
)
story.append(
    P(
        "For this reason the abstract regime and its physical constructor are "
        "separate audited endpoints. The constructor proves measurability, an "
        "explicit activity majorant, all tilted inequalities, and "
        "nonconstancy of the Wilson energy on punctured rational intervals. The "
        "d=2 and d=4 witnesses use conservative constants because their role is "
        "logical: they certify an open interacting range, not an optimized "
        "strong-coupling threshold. This separation also makes future constant "
        "improvements local; they can replace the constructor without changing "
        "the thermodynamic-limit proof.",
    )
)

story.append(P("2.5. A typed chain of evidence", "SubHead"))
story.append(
    P(
        "The proof is deliberately not packaged as one theorem with a large "
        "record of opaque hypotheses. It is a chain of certificates whose "
        "codomain is the next layer's input. Equalities are established in the "
        "finite combinatorial layers; inequalities enter only when the terms "
        "that cross the common window have been isolated. Completeness is used "
        "only after a numerical Cauchy modulus has been produced. This ordering "
        "makes it impossible to replace a missing algebraic bridge by a later "
        "analytic estimate.",
    )
)
bridge_data = [
    [
        P("<b>Interface</b>", "Caption"),
        P("<b>Exported certificate</b>", "Caption"),
        P("<b>Downstream role</b>", "Caption"),
    ],
    [
        P("Gibbs integral / polymer gas", "Caption"),
        P("Exact marked one-volume expansion", "Caption"),
        P("Cancels the far gas without a bulk oracle", "Caption"),
    ],
    [
        P("Two torus volumes", "Caption"),
        P("Common-window equality of local terms", "Caption"),
        P("Identifies every contribution below the cutoff", "Caption"),
    ],
    [
        P("Cluster leaves the window", "Caption"),
        P("Rooted tail at t+epsilon+1", "Caption"),
        P("Gives a bound uniform in both volumes", "Caption"),
    ],
    [
        P("Uniform numerical bound", "Caption"),
        P("Explicit Cauchy modulus tending to zero", "Caption"),
        P("Constructs the complete-sequence limit", "Caption"),
    ],
    [
        P("Signed local coordinates", "Caption"),
        P("Literal Z^d action and eventual chart equality", "Caption"),
        P("Transfers finite covariance, including inverses", "Caption"),
    ],
    [
        P("Centered seam deletion", "Caption"),
        P("Gas restriction plus inclusion-exclusion", "Caption"),
        P("Compares periodic with the proved free exhaustion", "Caption"),
    ],
    [
        P("Finite correlation estimate", "Caption"),
        P("Eventual realization and separation bridge", "Caption"),
        P("Passes the quantitative bound to the state", "Caption"),
    ],
]
bridge_tbl = Table(
    bridge_data,
    colWidths=[48 * mm, 58 * mm, 58 * mm],
    repeatRows=1,
    hAlign="CENTER",
)
bridge_tbl.setStyle(
    TableStyle(
        [
            ("BACKGROUND", (0, 0), (-1, 0), PALE),
            ("GRID", (0, 0), (-1, -1), 0.35, RULE),
            ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("LEFTPADDING", (0, 0), (-1, -1), 2 * mm),
            ("RIGHTPADDING", (0, 0), (-1, -1), 2 * mm),
            ("TOPPADDING", (0, 0), (-1, -1), 1.1 * mm),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 1.1 * mm),
        ]
    )
)
story.append(bridge_tbl)
story.append(Spacer(1, 2.5 * mm))
story.append(
    P(
        "This layering is also a debugging protocol. If a proposed endpoint "
        "mentions a new hypothesis that already states the next row's "
        "certificate, the bridge has been skipped. If a reindexing changes the "
        "summation domain, its multiplicity must appear before a norm bound is "
        "taken. If a cross-volume equality depends on a global configuration "
        "map, the window interface has leaked. These checks forced two early "
        "prototypes to be replaced even though their conditional endpoints "
        "elaborated.",
    )
)
story.append(
    P(
        "The organization keeps claim scope in the types as well. The free "
        "boundary object is one concrete restriction, not a parameter ranging "
        "over unspecified boundary conditions. The infinite functional is "
        "bundled with linearity, order, a unit, and the Z^d action, but not with "
        "a C*-norm that has not been constructed. The correlation consumer asks "
        "for eventual plaquette realization and separation rather than "
        "silently assigning a distance to every abstract observable. The final "
        "paper ledger is therefore derived from available interfaces, not from "
        "the informal theorem one might hope to state.",
    )
)
story.append(
    theorem(
        "Interface discipline.",
        "Every terminal conclusion is connected to the genuine finite Gibbs "
        "integral by exact equalities before estimates are applied; every "
        "multiplicity introduced by rooting is charged explicitly; every "
        "cross-volume comparison is local to a common chart; and the abstract "
        "uniform KP package is accompanied by a nonzero physical instance.",
    )
)
story.append(PageBreak())

story.append(P("3. Finite-volume setting", "SectionHead"))
story.append(
    P(
        "Fix a dimension d, a measurable group G with measurable multiplication "
        "and inversion, a probability measure mu on G, a bounded measurable "
        "plaquette energy pe, and a real coupling beta. At torus extent N, a "
        "gauge configuration assigns an element of G to each positively oriented "
        "edge. The Wilson action is the sum of pe evaluated on oriented "
        "plaquette holonomies, and the Gibbs measure is the normalized tilt of "
        "the product gauge measure.",
    )
)
story.append(
    P(
        "A <i>compatible local observable</i> records a finite support with "
        "coordinates independent of the ambient volume, a measurable bounded "
        "kernel, and a minimum admissible volume. Its realization in each "
        "sufficiently large torus reads exactly those edge coordinates. The "
        "finite Gibbs expectation E_n(O) is the genuine normalized integral of "
        "that realization at extent n+1.",
    )
)
story.append(
    theorem(
        "Finite local substrate.",
        "For every compatible local observable O, its realization is measurable "
        "and bounded; E_n is positive and normalized. Addition, multiplication, "
        "and real scalar multiplication are realized exactly at jointly "
        "admissible volumes.",
    )
)

story.append(P("4. Exact marked expansion and cancellation", "SectionHead"))
story.append(
    P(
        "Expanding each plaquette Boltzmann factor into 1 plus its Mayer "
        "activity gives a finite sum over plaquette subsets. For a local "
        "insertion O, components disjoint from the observable support factor as "
        "the ordinary polymer gas. Components touching the support form a "
        "marked activity. Mayer-Ursell inversion is then applied at one fixed "
        "volume.",
    )
)
story.append(code(
    "E_n(O)\n"
    "  = sum_{marked S0} markedIntegral_n(O,S0)\n"
    "      * exp( clusterSum(P_n restricted to far(S0))\n"
    "             - clusterSum(P_n) )."
))
story.append(
    P(
        "This identity is exact. The extensive contribution has already "
        "cancelled between numerator and partition function. No estimate of "
        "the full partition function, and no free bulk hypothesis, appears in "
        "the thermodynamic comparison.",
    )
)

story.append(P("5. Uniform pinned boundary control", "SectionHead"))
story.append(
    P(
        "For a fixed marked set, the remaining exponent is a restriction "
        "difference. It is reindexed as a series of Ursell tuples that meet the "
        "marked region and leave the common window. Pinning an arbitrary tuple "
        "coordinate at position zero costs its cardinality n+1. The formal "
        "development records this factor explicitly and absorbs it by the "
        "unit-cardinality tilt t+epsilon+1; it is not silently discarded.",
    )
)
story.append(
    theorem(
        "Rooted boundary tail.",
        "The local correction tail is summable uniformly in the torus volume. "
        "Its proof invokes "
        "<font name='Courier'>connectedLattice_pinned_tail_volumeUniform</font> "
        "literally, after the exact rooted reindexing and the honest unit tilt.",
    )
)
story.append(
    P(
        "The outer marked-set sum is controlled separately by decomposing a "
        "marked plaquette set into connected components. Each component is "
        "charged to the finite observable support, and a volume-uniform lattice "
        "animal bound resums the possibilities. Combining the outer tail with "
        "the normalization-correction tail yields the explicit error",
    )
)
story.append(code(
    "Delta_O(q)\n"
    "  = 2 * markedOuterTailBound_O(q)\n"
    "    + markedSmallLayerCauchyBound_O(q,q),\n"
    "Delta_O(q) -> 0 as q -> infinity."
))

story.append(PageBreak())
story.append(P("6. Whole-sequence thermodynamic state", "SectionHead"))
story.append(
    theorem(
        "Complete-sequence Cauchy theorem.",
        "Under a packaged uniform local KP regime, the sequence "
        "n |-> E_n(O) is Cauchy for every compatible local observable O. "
        "For each tolerance, the proof selects one cutoff q with "
        "Delta_O(q) below that tolerance and one explicit volume threshold "
        "above which every pair of volumes is bounded by Delta_O(q).",
    )
)
story.append(
    P(
        "Completeness of the complex numbers supplies the limit. Since every "
        "finite expectation is real, the limit is real. Exact finite-volume "
        "algebra, positivity, normalization, and translation covariance pass "
        "to the limit by uniqueness of limits.",
    )
)
story.append(
    P(
        "To obtain an honest translation group rather than a semigroup of "
        "positive shifts, we introduce local observables whose edge coordinates "
        "lie in Z^d. Periodic realization uses integer remainders and is defined "
        "at every volume. A canonical finite lower shift moves each observable "
        "into the existing natural-coordinate chart; beyond its explicit "
        "coordinate bound the two realizations agree literally. This eventual "
        "equality transfers the complete-sequence Cauchy theorem and its cofinal "
        "uniqueness without introducing a subsequence or a compactness argument.",
    )
)
story.append(
    theorem(
        "Infinite local Gibbs state.",
        "The constructed functional omega_infinity is real linear, positive, "
        "and normalized on the ordered integer-coordinate local-observable "
        "space with unit. For every z in Z^d it satisfies "
        "omega_infinity(z + O)=omega_infinity(O). The acting object is an "
        "additive group, so inverse translations are part of the same literal "
        "action rather than volume-dependent positive words.",
    )
)
story.append(
    P(
        "The domain has an observable product, but no C*-norm or C*-completion "
        "is constructed here. Accordingly the result is described as a "
        "positive normalized local state, not as a C*-algebraic state.",
    )
)

story.append(P("7. Genuine free boundary and uniqueness at the proved scope", "SectionHead"))
story.append(
    P(
        "The periodic torus is cut along a centered seam. Plaquettes crossing "
        "that seam receive zero activity; the resulting polymer gas is proved "
        "literally equal to a restriction of the periodic gas. The observable "
        "is centered so that its support lies in the interior rather than on "
        "the cut.",
    )
)
story.append(
    P(
        "Inclusion-exclusion cancels all clusters except those that meet both "
        "the local marked support and the deleted seam. Short clusters cannot "
        "do so once the common window fits. Long clusters are bounded by the "
        "same support-pinned tail. At a common volume,",
    )
)
story.append(code(
    "| E_n^periodic(O) - E_n^free(centered O) |\n"
    "  <= 2 * markedOuterTailBound_O(q)\n"
    "     + markedSmallLayerCauchyBound_O(q,q)."
))
story.append(
    P(
        "Define the free volume index by the explicit threshold plus q. These "
        "indices are cofinal, so the periodic expectations along them converge "
        "to omega_infinity(O). The displayed difference tends to zero by "
        "squeezing. Therefore the complete explicitly indexed free sequence "
        "converges to the same value.",
    )
)
story.append(
    theorem(
        "Periodic versus centered free boundary.",
        "The full cofinal sequence of genuine centered free-box expectations "
        "converges to the same infinite value as periodic boundary conditions. "
        "This is the boundary independence formalized here; no type or theorem "
        "for arbitrary boundary conditions is asserted.",
    )
)

story.append(P("8. Truncated correlations", "SectionHead"))
story.append(
    P(
        "For local observables O and P, define the finite truncated correlation "
        "as E_n(OP)-E_n(O)E_n(P). The complete finite-volume sequence converges "
        "to the analogous expression in omega_infinity. Hence every eventual "
        "volume-uniform finite bound passes unchanged to the limit.",
    )
)
story.append(
    P(
        "The formalization additionally bridges the existing normalized "
        "two-plaquette theorem to this local-observable definition. If, in all "
        "sufficiently large volumes, O and P realize a bounded measurable "
        "holonomy observable f at distinct plaquettes p_n and q_n with touching "
        "distance at least 2k, the finite normalized estimate gives",
    )
)
story.append(code(
    "| omega_infinity(OP) - omega_infinity(O) omega_infinity(P) |\n"
    "  <= C(d,B,beta,s,t,epsilon) * exp(-epsilon*k)."
))
story.append(
    P(
        "The eventual realization and separation data remain explicit "
        "hypotheses of this bridge. The theorem does not claim that every pair "
        "of abstract local observables is a separated two-plaquette pair.",
    )
)

story.append(P("9. Explicit non-vacuous SU(2) intervals", "SectionHead"))
story.append(
    P(
        "A conditional KP theorem can be mathematically empty if its hypotheses "
        "are never instantiated, and the point beta=0 would describe only the "
        "free product measure. The development therefore constructs a concrete "
        "nonzero interval. For d=2 and SU(2), the physical plaquette energy "
        "Re tr(U) is measurable, bounded by 2, and formally proved nonconstant.",
    )
)
story.append(
    P(
        "The parameters t=epsilon=eta=1/100 are fixed. On "
        "|beta|<=10^-5, the activity is bounded using the quadratic exponential "
        "remainder:",
    )
)
story.append(code(
    "exp(2*|beta|) - 1 <= 2.1*|beta|."
))
story.append(
    P(
        "Elementary rational upper bounds on the remaining exponentials then "
        "discharge the radius, smallness, unit-tilt, and marked-radius fields of "
        "the uniform regime. These constants are deliberately unoptimized: the "
        "certified radii below are far smaller than the order-one "
        "strong-coupling domains customarily obtained by analytic treatments. "
        "They certify non-vacuity of this formal package, not a competitive "
        "estimate of the strong-coupling boundary.",
    )
)
story.append(
    theorem(
        "Concrete two-dimensional strong-coupling regime.",
        "For every real beta with 0<|beta|<=10^-5, the d=2 SU(2) Wilson theory "
        "has the constructed infinite local Gibbs state. Positivity, "
        "normalization, full Z^d-translation invariance, and periodic-versus-"
        "centered-free convergence are therefore non-vacuous physical "
        "statements on an interval.",
    )
)
story.append(
    P(
        "The same rational proof is instantiated separately in the physical "
        "lattice dimension d=4. Here the animal constant grows from "
        "(16*2+1)^2=1089 to (16*4+1)^2=4225 and the smallness prefactor from "
        "32 to 64. A deliberately conservative exponential majorant then "
        "discharges all five fields on 0<|beta|<=10^-6.",
    )
)
story.append(
    theorem(
        "Concrete four-dimensional lattice regime.",
        "For every real beta with 0<|beta|<=10^-6, the d=4 SU(2) Wilson lattice "
        "theory has the constructed infinite local Gibbs state, with the same "
        "positivity, normalization, full Z^d-translation invariance, and "
        "periodic-versus-centered-free convergence conclusions. This is a "
        "four-dimensional lattice statement, not a continuum limit.",
    )
)

story.append(P("10. Formal verification record", "SectionHead"))
data = [
    [P("<b>Endpoint</b>", "Caption"), P("<b>Role</b>", "Caption")],
    [P("connectedLattice_pinned_tail_volumeUniform", "Caption"), P("Banked volume-uniform rooted KP tail", "Caption")],
    [P("cauchySeq_localGibbsExpectation_kpUniform", "Caption"), P("Complete-sequence Cauchy theorem", "Caption")],
    [P("infiniteLocalGibbsState", "Caption"), P("Positive normalized local state", "Caption")],
    [P("integerLocalGibbsExpectation_vadd", "Caption"), P("Exact finite invariance for every z in Z^d", "Caption")],
    [P("integerInfiniteLocalGibbsState", "Caption"), P("Positive normalized state with the full translation action", "Caption")],
    [P("su2InfiniteLocalGibbsStateOnPuncturedInterval", "Caption"), P("Physical nonzero interval", "Caption")],
    [P("su2D4InfiniteLocalGibbsStateOnPuncturedInterval", "Caption"), P("Physical d=4 lattice interval", "Caption")],
    [P("norm_localGibbsExpectation_sub_freeBoundary_le_kpUniform", "Caption"), P("Same-volume periodic/free bound", "Caption")],
    [P("tendsto_freeBoundaryThermodynamicExpectation", "Caption"), P("Complete free sequence has the same limit", "Caption")],
    [P("abs_infiniteLocalGibbsTruncatedCorrelation_le_twoPlaquette", "Caption"), P("Finite normalized bound passes to the state", "Caption")],
]
tbl = Table(data, colWidths=[82 * mm, 82 * mm], repeatRows=1, hAlign="CENTER")
tbl.setStyle(
    TableStyle(
        [
            ("BACKGROUND", (0, 0), (-1, 0), PALE),
            ("GRID", (0, 0), (-1, -1), 0.35, RULE),
            ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("LEFTPADDING", (0, 0), (-1, -1), 2.2 * mm),
            ("RIGHTPADDING", (0, 0), (-1, -1), 2.2 * mm),
            ("TOPPADDING", (0, 0), (-1, -1), 1.0 * mm),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 1.0 * mm),
        ]
    )
)
story.append(tbl)
story.append(Spacer(1, 3 * mm))
story.append(
    P(
        "Direct focal elaboration of all terminal modules and direct "
        "elaboration of the root <font name='Courier'>YangMillsCore.lean</font> "
        "terminated with exit code 0 under Lean 4.29.0-rc6. Twenty headline "
        "<font name='Courier'>#print axioms</font> checks reported exactly "
        "<font name='Courier'>[propext, Classical.choice, Quot.sound]</font>."
        "<br/>All nine dependency HEADs matched the manifest. After supplying "
        "a process-local safe.directory setting for the ownership-mismatched "
        "checkout, the fixed-toolchain canonical root build completed with "
        "empty stderr and the literal final line "
        "<font name='Courier'>Build completed successfully (8460 jobs).</font> "
        "No dependency was deleted or updated and no global Git configuration "
        "was changed.",
    )
)

story.append(P("11. Scope and open directions", "SectionHead"))
scope_rows = [
    [P("<b>Proved here</b>", "Caption"), P("<b>Not proved here</b>", "Caption")],
    [P("Complete periodic expectation sequence is Cauchy", "Caption"), P("Continuum or lattice-spacing limit", "Caption")],
    [P("Positive normalized real local state", "Caption"), P("C*-completion or C*-state", "Caption")],
    [P("Genuine Z^d action, including inverse translations", "Caption"), P("Finite-cutoff covariance of the centered free exhaustion under every z", "Caption")],
    [P("Periodic and one genuine centered free exhaustion", "Caption"), P("Arbitrary boundary conditions", "Caption")],
    [P("Two-plaquette bound passes under explicit geometry", "Caption"), P("Geometry-free clustering for arbitrary local observables", "Caption")],
    [P("d=2 and d=4 SU(2) lattice instances", "Caption"), P("Four-dimensional continuum Yang-Mills or OS reconstruction", "Caption")],
]
scope_tbl = Table(scope_rows, colWidths=[82 * mm, 82 * mm], repeatRows=1, hAlign="CENTER")
scope_tbl.setStyle(
    TableStyle(
        [
            ("BACKGROUND", (0, 0), (-1, 0), PALE),
            ("BACKGROUND", (1, 1), (1, -1), colors.HexColor("#FAF2F0")),
            ("GRID", (0, 0), (-1, -1), 0.35, RULE),
            ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("LEFTPADDING", (0, 0), (-1, -1), 2.2 * mm),
            ("RIGHTPADDING", (0, 0), (-1, -1), 2.2 * mm),
            ("TOPPADDING", (0, 0), (-1, -1), 1.0 * mm),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 1.0 * mm),
        ]
    )
)
story.append(scope_tbl)
story.append(Spacer(1, 3 * mm))
story.append(
    P(
        "The next mathematical extensions are to instantiate the eventual "
        "separated-plaquette geometry for explicit signed translated "
        "observables, and formulate "
        "additional physical boundary conditions as concrete polymer "
        "restrictions. These are separate theorems; none is required for the "
        "whole-sequence periodic and centered-free limits established above.",
    )
)

story.append(P("References", "ReferenceHead"))
refs = [
    (
        "[1] R. Kotecky and D. Preiss, <i>Cluster expansion for abstract "
        "polymer models</i>, Communications in Mathematical Physics 103 "
        "(1986), 491-498. "
        "<link href='https://doi.org/10.1007/BF01211762'>"
        "doi:10.1007/BF01211762</link>."
    ),
    (
        "[2] K. Osterwalder and E. Seiler, <i>Gauge field theories on a "
        "lattice</i>, Annals of Physics 110 (1978), 440-471. "
        "<link href='https://doi.org/10.1016/0003-4916(78)90039-8'>"
        "doi:10.1016/0003-4916(78)90039-8</link>."
    ),
    (
        "[3] L. de Moura and S. Ullrich, <i>The Lean 4 Theorem Prover and "
        "Programming Language</i>, CADE 28, LNCS 12699 (2021), 625-635. "
        "<link href='https://doi.org/10.1007/978-3-030-79876-5_37'>"
        "doi:10.1007/978-3-030-79876-5_37</link>."
    ),
    (
        "[4] The mathlib Community, <i>The Lean mathematical library</i>, "
        "CPP 2020, 367-381. "
        "<link href='https://doi.org/10.1145/3372885.3373824'>"
        "doi:10.1145/3372885.3373824</link>."
    ),
    (
        "[5] L. Eriksson, <i>THE ERIKSSON PROGRAMME</i>, Lean 4 artifact "
        "and verification ledger, "
        "<link href='https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME'>"
        "repository</link>."
    ),
]
for ref in refs:
    story.append(P(ref, "Reference"))

doc = SimpleDocTemplate(
    str(PDF),
    pagesize=A4,
    rightMargin=22 * mm,
    leftMargin=22 * mm,
    topMargin=21 * mm,
    bottomMargin=19 * mm,
    title="A Machine-Checked Thermodynamic Limit for Local Lattice Gauge Gibbs States",
    author="Lluis Eriksson",
    subject="Lean 4 formalization of a local Gibbs thermodynamic limit in a uniform KP regime",
)
doc.build(story, onFirstPage=header_footer, onLaterPages=header_footer)
print(PDF)
