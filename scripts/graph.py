"""Publish an offline graph from the corrected edition and the proof registry."""
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import textwrap
from pathlib import Path

from graph_exports import export_graphs

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
HTML = DOCS / "dependency_graph.html"
DEFENCE = ["claim1", "claim2", "claim3", "defence_sigma", "claim5", "claim6", "claim7"]
MODULES = ["Trees"] * 5 + ["Bipartite", "Words"]

# Several captions in the supplied comparison still describe the old edition.
TITLES = {
    "irr_norm": "Определения irr, σ и полной нерегулярности",
    "cortreen1": "Критерий дерева по числу рёбер связного графа",
    "domnumn1": "Нижняя граница числа доминирования по степеням",
    "albstarirr": "Индекс Альбертсона звезды",
    "lem006cyc": "Экстремумы вариации циклической расстановки",
    "lem001starlikerr": "Индекс Альбертсона паука с d ветвями",
    "prop06squeeze": "Критерий локальной оптимальности при двух модификациях",
    "Thm02worksep": "Перебор допустимых параметров глобального максимума",
    "Thm03worksep": "Оптимум внутри семейства по ближайшему целому",
    "thm001global": "Точная конечная редукция глобального максимума при λ ∈ [0,1]",
    "lem003exact": "Точный максимум на допустимой ветви",
    "lem02exponenttransform": "Нижняя граница показателя образа фактора и равенство",
    "thm01slopecf": "Наклон бипериодического слова и его цепная дробь",
}


def read_graph():
    original = (DOCS / "dependency_graph_original.html").read_text()
    data, _ = json.JSONDecoder().raw_decode(original.split("const D=", 1)[1])
    nodes = {}
    for key, versions in data["nodes"].items():
        n = versions["new"]
        if n:
            nodes[key] = {k: n[k] for k in ("short", "title", "page", "chapter", "statement")}
            nodes[key]["title"] = TITLES.get(key, n["title"])
    nodes["problemn2"]["page"] = "47"
    for key, number in [("eqq01def002polarized", "3.4.2"), ("eqq01def002Sp", "3.4.3")]:
        nodes[key]["short"] = "О " + number + " · " + nodes[key]["short"]
    for i, (key, module) in enumerate(zip(DEFENCE, MODULES), 1):
        nodes[key].update(claim=i, spec=f"Thesis.{module}.Claim{i}", module=f"Thesis/{module}.lean")
    edges = [dict(a=e["a"], b=e["b"], kind=e["new"]["kind"], evidence=e["new"]["evidence"])
             for e in data["edges"] if e["new"]]
    # §1.3(7) states the closed form explicitly. Theorem 6.3.2 proves that identity.
    edges.append(dict(a="thm01slopecf", b="claim7", kind="reconstructed",
                      evidence=["Формула наклона в положении 7 совпадает с (6.6), с. 58."]))
    assert all(e["a"] in nodes and e["b"] in nodes for e in edges)
    return dict(nodes=nodes, edges=edges, groups=data["groups"], defence=DEFENCE)


def views(data):
    nodes, edges = data["nodes"], data["edges"]
    sets = {"defence": set(DEFENCE) | {e["a"] for e in edges if e["b"] in DEFENCE}}
    for n, key in enumerate(DEFENCE, 1):
        selected = {key}
        while True:
            expanded = selected | {e["a"] for e in edges if e["b"] in selected}
            if expanded == selected:
                break
            selected = expanded
        sets[f"d{n}"] = selected
    for chapter in data["groups"]:
        sets[chapter] = {k for k, v in nodes.items() if str(v["chapter"]) == chapter}
    sets["all"] = set(nodes)
    return sets


def layout(selected, edges):
    # Use Graphviz for routing only. The browser supplies colours and accessible labels.
    names = sorted(selected)
    ids = {k: f"n{i}" for i, k in enumerate(names)}
    lines = ["digraph {", 'graph [rankdir=LR, nodesep=0.22, ranksep=0.65];',
             'node [shape=box, fixedsize=true, width=2.9, height=0.78, label=""];']
    lines += [f"{ids[k]};" for k in names]
    lines += [f"{ids[e['a']]} -> {ids[e['b']]};" for e in edges
              if e["a"] in selected and e["b"] in selected]
    result = subprocess.run(["dot", "-Tplain"], input="\n".join(lines + ["}"]),
                            text=True, capture_output=True, check=True)
    positions, routes = {}, []
    for line in result.stdout.splitlines():
        item = line.split()
        if item[0] == "graph":
            width, height = map(float, item[2:4])
        elif item[0] == "node":
            positions[names[int(item[1][1:])]] = point(item[2:4], height)
        elif item[0] == "edge":
            a, b = (names[int(s[1:])] for s in item[1:3])
            coords = item[4:4 + 2 * int(item[3])]
            routes.append([a, b, [point(coords[i:i+2], height) for i in range(0, len(coords), 2)]])
    return dict(size=[round(72*width+16), round(72*height+16)], positions=positions, routes=routes)


def point(pair, height):
    x, y = map(float, pair)
    return [round(8 + 72*x, 2), round(8 + 72*(height-y), 2)]


def compact(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).replace("<", r"\u003c")


def element(html, name):
    return re.search(f'<script id="{name}" type="application/json">(.*?)</script>', html, re.S)[1]


def proof_registry(nodes):
    registry = json.loads((DOCS / "proofs.json").read_text())
    for key, proof in registry.items():
        if key not in nodes:
            raise ValueError(f"Unknown graph node: {key}")
        name = proof["theorem"]
        if not re.fullmatch(r"Thesis(?:\.[A-Za-z][A-Za-z0-9_]*)+", name):
            raise ValueError(f"Invalid theorem name: {name}")
        lines = (ROOT / "lean" / proof["file"]).read_text().splitlines()
        bare = re.escape(name.rsplit(".", 1)[1])
        proof["line"] = next(i for i, line in enumerate(lines, 1)
                             if re.match(rf"^theorem {bare}\b", line))
    return registry


def audit(nodes, registry):
    commands = ["import Thesis"]
    for key, proof in registry.items():
        name = proof["theorem"]
        if "spec" in nodes[key]:
            commands.append(f"example : {nodes[key]['spec']} := {name}")
        commands.append(f"#print axioms {name}")
    with tempfile.NamedTemporaryFile(suffix=".lean", mode="w") as script:
        script.write("\n".join(commands) + "\n")
        script.flush()
        run = subprocess.run(["lake", "env", "lean", script.name], cwd=ROOT/"lean",
                             capture_output=True, text=True)
    print(run.stdout + run.stderr, end="")
    if run.returncode or "sorryAx" in run.stdout:
        raise SystemExit("Proof audit failed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--audit", action="store_true", help="type-check registered proofs in Lean")
    args = parser.parse_args()
    data = read_graph()
    sets = views(data)
    proofs = proof_registry(data["nodes"])
    # Preserve layout across Graphviz versions when the topology is unchanged.
    topology = compact([sorted(data["nodes"]), [[e["a"], e["b"]] for e in data["edges"]],
                        {k: sorted(v) for k, v in sets.items()}])
    digest = hashlib.sha256(topology.encode()).hexdigest()
    previous = HTML.read_text() if HTML.exists() else ""
    geometry = json.loads(element(previous, "layout")) if previous else {}
    if geometry.get("digest") != digest:
        if args.check:
            raise SystemExit("Graph topology changed. Run python3 scripts/graph.py")
        geometry = dict(digest=digest, views={k: layout(v, data["edges"]) for k, v in sets.items()})
    for k, group in sets.items():
        view = geometry["views"][k]
        assert set(view["positions"]) == group
        assert {(r[0], r[1]) for r in view["routes"]} == {
            (e["a"], e["b"]) for e in data["edges"] if e["a"] in group and e["b"] in group}
    for v in data["nodes"].values():
        v["lines"] = textwrap.wrap(v["title"], 29, break_long_words=False)[:3]
    output = (ROOT / "scripts" / "graph_template.html").read_text()
    for tag, value in [("DATA", data), ("LAYOUT", geometry), ("PROOFS", proofs)]:
        output = output.replace("{{" + tag + "}}", compact(value))
    if args.check:
        if previous != output:
            raise SystemExit("Graph is stale. Run python3 scripts/graph.py")
    else:
        HTML.write_text(output)
    export_graphs(DOCS, data, geometry["views"], proofs, args.check)
    if args.audit:
        audit(data["nodes"], proofs)


if __name__ == "__main__":
    main()
