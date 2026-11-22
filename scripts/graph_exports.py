"""Render the HTML graph's exact nodes, routes, and proof status for GitHub previews."""
import hashlib
import io
import math
import xml.etree.ElementTree as ET
from pathlib import Path

from pypdf import PdfReader, PdfWriter

GOLD, RED, GREEN = "#f6cc55", "#f4b3ac", "#a3dbb3"
PENDING, DONE = "#b33532", "#197146"
INK, MUTED, EDGE = "#192c33", "#475a64", "#586874"
PDF_ORDER = ["defence", *(f"d{i}" for i in range(1, 8)), *map(str, range(1, 8)), "all"]


def add(parent, name, **attrs):
    return ET.SubElement(parent, name, {k.replace("_", "-"): str(v) for k, v in attrs.items()})


def label(parent, x, y, text, size, *, fill=INK, bold=False, middle=False):
    item = add(parent, "text", x=x, y=y, font_size=size, fill=fill,
               font_weight="bold" if bold else "normal", text_anchor="middle" if middle else "start")
    item.text = text


def caption(view, data):
    if view == "all":
        return "Полный граф зависимостей"
    if view == "defence":
        return "Семь положений на защиту и их основания"
    if view.startswith("d"):
        index = int(view[1:])
        return f"Положение {index}. " + data["nodes"][data["defence"][index-1]]["title"]
    return f"Глава {view}. " + data["groups"][view]


def draw_route(group, points, kind):
    def xy(point):
        return f"{point[0]} {point[1]}"

    path = "M " + xy(points[0]) + " C " + " ".join(map(xy, points[1:]))
    dash = {"statement_ref": "2 2", "reconstructed": "6 3"}.get(kind)
    stroke = add(group, "path", d=path, fill="none", stroke=EDGE, stroke_width=1.35)
    if dash:
        stroke.set("stroke-dasharray", dash)
    # Explicit arrowheads also work in PDF renderers without SVG marker support.
    x, y = points[-1]
    prev = next(p for p in reversed(points[:-1]) if p != points[-1])
    dx, dy = x - prev[0], y - prev[1]
    norm = math.hypot(dx, dy)
    ux, uy = dx/norm, dy/norm
    ends = [(x + 7*ux, y + 7*uy), (x - 3*uy, y + 3*ux), (x + 3*uy, y - 3*ux)]
    add(group, "polygon", points=" ".join(f"{a:.2f},{b:.2f}" for a, b in ends), fill=EDGE)


def svg_page(view, data, layouts, proofs):
    drawing = layouts[view]
    w, h = drawing["size"]
    width, height = max(880, w+44), h+156
    title = caption(view, data)
    svg = ET.Element("svg", {"xmlns": "http://www.w3.org/2000/svg", "width": str(width),
                             "height": str(height), "viewBox": f"0 0 {width} {height}",
                             "role": "img", "aria-labelledby": "title desc",
                             "font-family": "DejaVu Sans, sans-serif"})
    add(svg, "title", id="title").text = title
    add(svg, "desc", id="desc").text = "Стрелки идут от оснований к результатам. Статус повторён в легенде и названиях узлов."
    add(svg, "rect", width=width, height=height, fill="white")
    label(svg, 24, 33, title, 22, bold=True)
    ns = drawing["positions"]
    summary = (f"Исправленная редакция   ·   Узлов: {len(ns)}   ·   Связей: {len(drawing['routes'])}"
               f"   ·   Доказано в Lean: {len(ns.keys() & proofs.keys())}")
    label(svg, 24, 55, summary, 12, fill=MUTED)

    legend = [(24, GOLD, PENDING, "На защиту · открыто"), (216, GOLD, DONE, "На защиту · доказано"),
              (420, RED, PENDING, "Открыто"), (541, GREEN, DONE, "Доказано в Lean")]
    for x, fill, stroke, text in legend:
        add(svg, "rect", x=x, y=72, width=18, height=13, rx=2, fill=fill, stroke=stroke, stroke_width=2)
        label(svg, x+25, 83, text, 12)
    label(svg, 24, 106, "Стрелка идёт от основания к результату. Точечная — ссылка в формулировке, штриховая — зависимость по содержанию.", 11, fill=MUTED)
    add(svg, "line", x1=24, x2=width-24, y1=120, y2=120, stroke="#d7dddc")
    graph = add(svg, "g", transform=f"translate({(width-w)/2:g} 132)")
    kinds = {(e["a"], e["b"]): e["kind"] for e in data["edges"]}
    for a, b, points in drawing["routes"]:
        draw_route(graph, points, kinds[a, b])
    for key, (x, y) in ns.items():
        n, done = data["nodes"][key], key in proofs
        node = add(graph, "g", id=key)
        add(node, "title").text = n["short"] + " · " + n["title"] + (" · доказано" if done else " · открыто")
        add(node, "rect", x=x-104, y=y-28, width=208, height=56, rx=7,
            fill=GOLD if n.get("claim") else (GREEN if done else RED),
            stroke=DONE if done else PENDING, stroke_width=4 if n.get("claim") else 1.5)
        lines = [n["short"] + ("  ✓" if done else ""), *n["lines"]]
        for i, line in enumerate(lines):
            label(node, x, round(y+(i-(len(lines)-1)/2)*12+3.8, 2), line, 11,
                  middle=True, bold=i == 0)
    return ET.tostring(svg, encoding="utf-8", xml_declaration=True)


def export_graphs(docs: Path, data, layouts, proofs, check):
    pages = [(caption(v, data), svg_page(v, data, layouts, proofs)) for v in PDF_ORDER]
    # A PDF records the digest of every source drawing, including styles and status.
    digest = hashlib.sha256(b"\0".join(svg for _, svg in pages)).hexdigest()
    svg_path, pdf_path = docs / "dependency_graph.svg", docs / "dependency_graph.pdf"
    if check:
        if not svg_path.exists() or svg_path.read_bytes() != pages[-1][1]:
            raise SystemExit("SVG graph is stale. Run python3 scripts/graph.py")
        pdf = PdfReader(pdf_path)
        if (pdf.metadata.get("/GraphSourceSHA256") != digest or len(pdf.pages) != len(pages)
                or [entry.title for entry in pdf.outline] != [title for title, _ in pages]):
            raise SystemExit("PDF graph is stale. Run python3 scripts/graph.py")
        return

    import cairosvg  # Only needed when exporting, not for the CI check.
    writer = PdfWriter()
    for i, (title, svg) in enumerate(pages):
        page = PdfReader(io.BytesIO(cairosvg.svg2pdf(bytestring=svg))).pages[0]
        writer.add_page(page)
        writer.add_outline_item(title, i)
    writer.add_metadata({"/Title": "Граф зависимостей диссертации",
                         "/Subject": "Исправленная редакция · статус верификации в Lean",
                         "/GraphSourceSHA256": digest})
    writer.compress_identical_objects()
    writer.write(pdf_path)
    svg_path.write_bytes(pages[-1][1])
