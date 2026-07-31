#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from xml.sax.saxutils import escape

from pypdf import PdfReader, PdfWriter
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen import canvas
from reportlab.platypus import PageBreak, Paragraph, SimpleDocTemplate, Spacer


ROOT = Path(__file__).resolve().parents[1]
ART = ROOT / "artifacts"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def register_fonts() -> tuple[str, str]:
    regular_candidates = (
        Path(r"C:\Windows\Fonts\arial.ttf"),
        Path("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf"),
    )
    bold_candidates = (
        Path(r"C:\Windows\Fonts\arialbd.ttf"),
        Path("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"),
    )
    regular = next((p for p in regular_candidates if p.is_file()), None)
    bold = next((p for p in bold_candidates if p.is_file()), None)
    if regular is None or bold is None:
        raise FileNotFoundError("embedded TrueType fonts not found")
    pdfmetrics.registerFont(TTFont("AuditSans", str(regular)))
    pdfmetrics.registerFont(TTFont("AuditSansBold", str(bold)))
    return "AuditSans", "AuditSansBold"


class InvariantCanvas(canvas.Canvas):
    def __init__(self, *args, **kwargs):
        kwargs["invariant"] = 1
        kwargs["initialFontName"] = "AuditSans"
        kwargs["initialFontSize"] = 9
        super().__init__(*args, **kwargs)


def build_notice(cfg: dict[str, object], page_size: tuple[float, float], out: Path) -> None:
    regular, bold = register_fonts()
    styles = getSampleStyleSheet()
    body = ParagraphStyle(
        "AuditBody",
        parent=styles["BodyText"],
        fontName=regular,
        fontSize=9.3,
        leading=12.2,
        spaceAfter=7,
        textColor=colors.HexColor("#172033"),
    )
    heading = ParagraphStyle(
        "AuditHeading",
        parent=body,
        fontName=bold,
        fontSize=11.2,
        leading=14,
        spaceBefore=7,
        spaceAfter=4,
        textColor=colors.HexColor("#15385c"),
    )
    title = ParagraphStyle(
        "AuditTitle",
        parent=body,
        fontName=bold,
        fontSize=15,
        leading=18,
        alignment=TA_CENTER,
        spaceAfter=8,
    )
    banner = ParagraphStyle(
        "AuditBanner",
        parent=body,
        fontName=bold,
        fontSize=13,
        leading=16,
        alignment=TA_CENTER,
        textColor=colors.HexColor("#a51d2d"),
        borderColor=colors.HexColor("#a51d2d"),
        borderWidth=1.2,
        borderPadding=8,
        spaceAfter=12,
    )
    small = ParagraphStyle(
        "AuditSmall",
        parent=body,
        fontSize=8.3,
        leading=10.5,
        textColor=colors.HexColor("#4a5568"),
    )

    def footer(c: canvas.Canvas, doc: SimpleDocTemplate) -> None:
        c.saveState()
        c.setStrokeColor(colors.HexColor("#9aa4b2"))
        c.line(18 * mm, 14 * mm, page_size[0] - 18 * mm, 14 * mm)
        c.setFont(regular, 7.5)
        c.setFillColor(colors.HexColor("#4a5568"))
        c.drawString(18 * mm, 9.5 * mm, f"ai.viXra:{cfg['record']} - version {cfg['new_version']} supersession/correction note")
        c.drawRightString(page_size[0] - 18 * mm, 9.5 * mm, f"notice page {doc.page}")
        c.restoreState()

    doc = SimpleDocTemplate(
        str(out),
        pagesize=page_size,
        leftMargin=19 * mm,
        rightMargin=19 * mm,
        topMargin=17 * mm,
        bottomMargin=19 * mm,
        title=str(cfg["title"]),
        author=str(cfg["author"]),
        subject=str(cfg["headline"]),
    )
    story: list[object] = [
        Paragraph(escape(str(cfg["headline"])), banner),
        Paragraph(escape(str(cfg["title"])), title),
        Paragraph(f"<b>{escape(str(cfg['author']))}</b><br/>Version {escape(str(cfg['new_version']))} - supersession and correction note", ParagraphStyle("Byline", parent=body, alignment=TA_CENTER)),
        Spacer(1, 4),
        Paragraph("Purpose of this replacement", heading),
    ]
    for paragraph in cfg["summary"]:
        story.append(Paragraph(escape(str(paragraph)), body))
    story.extend(
        [
            Paragraph("Citation rule", heading),
            Paragraph(escape(str(cfg["citation_rule"])), body),
            Paragraph("Status boundary", heading),
            Paragraph(escape(str(cfg["status_boundary"])), body),
            Paragraph("The exact claim map and provenance record continue on notice page 2. The historical public manuscript then follows unchanged.", small),
            PageBreak(),
            Paragraph("CORRECTION AND CLAIM MAP", banner),
            Paragraph("Results retained from the historical paper", heading),
        ]
    )
    for item in cfg["retained"]:
        story.append(Paragraph("- " + escape(str(item)), body))
    story.append(Paragraph("Claims superseded or narrowed", heading))
    for item in cfg["superseded"]:
        story.append(Paragraph("- " + escape(str(item)), body))
    story.append(Paragraph("What the successor adds", heading))
    for item in cfg["successor_adds"]:
        story.append(Paragraph("- " + escape(str(item)), body))
    story.extend(
        [
            Paragraph("Evidence classification", heading),
            Paragraph(escape(str(cfg["evidence"])), body),
            Paragraph("Provenance", heading),
            Paragraph(escape(str(cfg["provenance"])), body),
        ]
    )
    doc.build(story, onFirstPage=footer, onLaterPages=footer, canvasmaker=InvariantCanvas)


def main() -> int:
    cfg = json.loads((ROOT / "config.json").read_text(encoding="utf-8"))
    ART.mkdir(parents=True, exist_ok=True)
    historical = ROOT / "inputs" / cfg["historical_pdf"]
    successor = ROOT / "inputs" / cfg["successor_pdf"]
    if sha256(historical) != cfg["historical_sha256"]:
        raise RuntimeError("historical input SHA mismatch")
    if sha256(successor) != cfg["successor_sha256"]:
        raise RuntimeError("successor input SHA mismatch")
    old_reader = PdfReader(str(historical), strict=True)
    if old_reader.is_encrypted or len(old_reader.pages) != cfg["historical_pages"]:
        raise RuntimeError("historical input page/encryption mismatch")
    first = old_reader.pages[0].mediabox
    page_size = (float(first.width), float(first.height))
    notice = ART / "supersession-notice.pdf"
    build_notice(cfg, page_size, notice)
    notice_reader = PdfReader(str(notice), strict=True)
    if len(notice_reader.pages) != 2:
        raise RuntimeError("supersession notice must be exactly two pages")

    final = ART / cfg["final_filename"]
    writer = PdfWriter()
    writer.append(str(notice))
    writer.append(str(historical))
    writer.add_metadata(
        {
            "/Title": cfg["title"],
            "/Author": cfg["author"],
            "/Subject": cfg["headline"],
            "/Keywords": f"superseded by ai.viXra:{cfg['successor_record']}; correction; provenance",
        }
    )
    with final.open("wb") as stream:
        writer.write(stream)

    final_reader = PdfReader(str(final), strict=True)
    result = {
        "status": "BUILT-NOT-INDEPENDENTLY-AUDITED",
        "final_pdf": final.name,
        "final_sha256": sha256(final),
        "final_bytes": final.stat().st_size,
        "final_pages": len(final_reader.pages),
        "notice_pages": len(notice_reader.pages),
        "historical_pdf": cfg["historical_pdf"],
        "historical_sha256": sha256(historical),
        "historical_pages": len(old_reader.pages),
        "successor_pdf": cfg["successor_pdf"],
        "successor_sha256": sha256(successor),
    }
    (ART / "build-result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    (ART / "BUILD-TRANSCRIPT.txt").write_text(
        "SOURCE_DATE_EPOCH=1785614400\n" + json.dumps(result, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    os.environ.setdefault("SOURCE_DATE_EPOCH", "1785614400")
    raise SystemExit(main())
