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
        spaceBefore=5 * mm,
        spaceAfter=2.5 * mm,
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
        spaceBefore=3 * mm,
        spaceAfter=1.5 * mm,
        keepWithNext=True,
    )
)
styles.add(
    ParagraphStyle(
        name="BodyText2",
        fontName="PaperSerif",
        fontSize=9.4,
        leading=13.4,
        alignment=TA_JUSTIFY,
        textColor=BASE,
        spaceAfter=2.2 * mm,
    )
)
styles.add(
    ParagraphStyle(
        name="TheoremText",
        fontName="PaperSerif",
        fontSize=9.1,
        leading=13,
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
        fontSize=8.1,
        leading=11,
        textColor=BASE,
        leftIndent=5 * mm,
        firstLineIndent=-5 * mm,
        spaceAfter=1.5 * mm,
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
        "verified source checkpoint <font name='Courier'>ca355eb1</font>",
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
        "The state is invariant under each positive unit translation generator "
        "and every finite word in those generators. For SU(2), Haar "
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
        "claim arbitrary boundary conditions, inverse-translation invariance, "
        "a C*-algebraic state, a continuum limit, Osterwalder-Schrader "
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

story.append(P("2. Finite-volume setting", "SectionHead"))
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

story.append(P("3. Exact marked expansion and cancellation", "SectionHead"))
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

story.append(P("4. Uniform pinned boundary control", "SectionHead"))
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

story.append(P("5. Whole-sequence thermodynamic state", "SectionHead"))
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
    theorem(
        "Infinite local Gibbs state.",
        "The constructed functional omega_infinity is real linear, positive, "
        "and normalized on the ordered local-observable space with unit. It "
        "satisfies omega_infinity(T_i O)=omega_infinity(O) for each positive "
        "unit translation generator i and for every finite word in those "
        "generators.",
    )
)
story.append(
    P(
        "The domain has an observable product, but no C*-norm or C*-completion "
        "is constructed here. Accordingly the result is described as a "
        "positive normalized local state, not as a C*-algebraic state.",
    )
)

story.append(P("6. Genuine free boundary and uniqueness at the proved scope", "SectionHead"))
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

story.append(P("7. Truncated correlations", "SectionHead"))
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

story.append(P("8. Explicit non-vacuous SU(2) intervals", "SectionHead"))
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
        "normalization, generator/finite-word invariance, and periodic-versus-"
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
        "positivity, normalization, generator/finite-word invariance, and "
        "periodic-versus-centered-free convergence conclusions. This is a "
        "four-dimensional lattice statement, not a continuum limit.",
    )
)

story.append(P("9. Formal verification record", "SectionHead"))
data = [
    [P("<b>Endpoint</b>", "Caption"), P("<b>Role</b>", "Caption")],
    [P("connectedLattice_pinned_tail_volumeUniform", "Caption"), P("Banked volume-uniform rooted KP tail", "Caption")],
    [P("cauchySeq_localGibbsExpectation_kpUniform", "Caption"), P("Complete-sequence Cauchy theorem", "Caption")],
    [P("infiniteLocalGibbsState", "Caption"), P("Positive normalized local state", "Caption")],
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
            ("TOPPADDING", (0, 0), (-1, -1), 1.7 * mm),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 1.7 * mm),
        ]
    )
)
story.append(tbl)
story.append(Spacer(1, 3 * mm))
story.append(
    P(
        "Direct focal elaboration of all terminal modules and direct "
        "elaboration of the root <font name='Courier'>YangMillsCore.lean</font> "
        "terminated with exit code 0 under Lean 4.29.0-rc6. Twelve headline "
        "<font name='Courier'>#print axioms</font> checks reported exactly "
        "<font name='Courier'>[propext, Classical.choice, Quot.sound]</font>."
        "<br/>All nine dependency HEADs matched the manifest. After supplying "
        "a process-local safe.directory setting for the ownership-mismatched "
        "checkout, the fixed-toolchain canonical root build completed with "
        "empty stderr and the literal final line "
        "<font name='Courier'>Build completed successfully (8458 jobs).</font> "
        "No dependency was deleted or updated and no global Git configuration "
        "was changed.",
    )
)

story.append(P("10. Scope and open directions", "SectionHead"))
scope_rows = [
    [P("<b>Proved here</b>", "Caption"), P("<b>Not proved here</b>", "Caption")],
    [P("Complete periodic expectation sequence is Cauchy", "Caption"), P("Continuum or lattice-spacing limit", "Caption")],
    [P("Positive normalized real local state", "Caption"), P("C*-completion or C*-state", "Caption")],
    [P("Positive generators and finite words", "Caption"), P("An action of the full translation group with inverses", "Caption")],
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
            ("TOPPADDING", (0, 0), (-1, -1), 1.7 * mm),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 1.7 * mm),
        ]
    )
)
story.append(scope_tbl)
story.append(Spacer(1, 3 * mm))
story.append(
    P(
        "The next mathematical extensions are to package inverse translations "
        "as an honest local action, instantiate the eventual separated-"
        "plaquette geometry for explicit translated observables, and formulate "
        "additional physical boundary conditions as concrete polymer "
        "restrictions. These are separate theorems; none is required for the "
        "whole-sequence periodic and centered-free limits established above.",
    )
)

story.append(P("References", "SectionHead"))
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
        "[5] L. Eriksson, <i>THE ERIKSSON PROGRAMME</i>, Lean 4 source "
        "repository and verification ledger. "
        "<link href='https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME'>"
        "github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME</link>."
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
