"""Exact bounded installation grammar for structural descriptor schemes.

This module belongs to the catalog producer. Native TableGen and Rust admission
check their own representations independently.
"""

import re

MAX_DEPTH = 32
MAX_NODES = 1024
FORMS = ("Append", "Concat", "Replace", "ForgetExtent", "CheckExtent", "Fold")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact(value, fields):
    require(isinstance(value, dict), "expected scheme object")
    require(set(value) == set(fields), "invalid scheme fields")


def index(value):
    require(type(value) is int and 0 <= value <= 1048576, "invalid scheme index")


def pattern(value):
    # Check graph bounds before recursive projection or canonicalization. A
    # repeated object on the active path is a cycle, not a shared subtree.
    pending = [(value, 0, frozenset())]
    nodes = 0
    while pending:
        node, depth, ancestors = pending.pop()
        nodes += 1
        require(nodes <= MAX_NODES and depth <= MAX_DEPTH, "scheme pattern limit")
        require(id(node) not in ancestors, "cyclic scheme pattern")
        require(isinstance(node, dict), "expected scheme pattern")
        tag = node.get("kind")
        ancestors = ancestors | {id(node)}
        if tag == "contract":
            exact(node, ("kind", "variable"))
            index(node["variable"])
        elif tag == "product":
            exact(node, ("kind", "elements"))
            require(isinstance(node["elements"], list) and
                    len(node["elements"]) <= MAX_NODES - nodes - len(pending),
                    "scheme pattern limit")
            pending.extend((child, depth + 1, ancestors) for child in node["elements"])
        elif tag == "sequence":
            exact(node, ("kind", "element", "extent"))
            extent(node["extent"])
            require(nodes + len(pending) < MAX_NODES, "scheme pattern limit")
            pending.append((node["element"], depth + 1, ancestors))
        else:
            raise ValueError("unknown scheme pattern")


def extent(value):
    require(isinstance(value, dict), "expected scheme extent")
    tag = value.get("kind")
    if tag == "unsized":
        exact(value, ("kind",))
    elif tag == "extent":
        exact(value, ("kind", "variable"))
        index(value["variable"])
    elif tag == "static":
        exact(value, ("kind", "index"))
        index(value["index"])
    else:
        raise ValueError("unknown scheme extent")


def port(value, named=False):
    require(isinstance(value, dict), "expected scheme port")
    fields = ("name",) if named else ()
    if named:
        require(isinstance(value.get("name"), str), "invalid scheme port name")
    if value.get("kind") == "descriptor":
        exact(value, fields + ("kind", "contract"))
        pattern(value["contract"])
    elif value.get("kind") == "selectedView":
        exact(value, fields + ("kind", "context", "state"))
        pattern(value["context"])
        pattern(value["state"])
    else:
        raise ValueError("unknown scheme port")


def named_port(value):
    port(value, True)


def shape(value):
    exact(value, ("name", "form", "variables", "statics", "inputs", "output"))
    require(isinstance(value["name"], str) and
            re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", value["name"]), "invalid scheme name")
    require(value["form"] in FORMS, "unknown descriptor scheme form")
    require(isinstance(value["variables"], list) and len(value["variables"]) <= MAX_NODES,
            "scheme variable limit")
    require(all(v in ("Contract", "OptionalExtent") for v in value["variables"]),
            "unknown scheme variable sort")
    require(isinstance(value["statics"], list) and len(value["statics"]) <= MAX_NODES,
            "scheme static limit")
    for static in value["statics"]:
        exact(static, ("kind", "sort"))
        require(static == {"kind": "Nat", "sort": ""}, "invalid scheme static")
    require(isinstance(value["inputs"], list) and len(value["inputs"]) <= MAX_NODES,
            "scheme port limit")
    for value_port in value["inputs"]:
        port(value_port)
    pattern(value["output"])


def canonical(form):
    c = {"kind": "contract", "variable": 0}
    a = {"kind": "contract", "variable": 1}
    unsized = {"kind": "unsized"}
    length = {"kind": "extent", "variable": 1}
    def seq(e):
        return {"kind": "sequence", "element": c, "extent": e}

    def desc(p):
        return {"kind": "descriptor", "contract": p}
    s = seq(unsized)
    variables = ["Contract"]
    statics = []
    if form in ("Replace", "ForgetExtent"):
        variables.append("OptionalExtent")
    if form in ("Replace", "CheckExtent", "Fold"):
        statics = [{"kind": "Nat", "sort": ""}]
    inputs, output = {
        "Append": ([desc(s), desc(c)], s),
        "Concat": ([desc(s), desc(s)], s),
        "Replace": ([desc(seq(length)), desc(c)], seq(length)),
        "ForgetExtent": ([desc(seq(length))], s),
        "CheckExtent": ([desc(s)], seq({"kind": "static", "index": 0})),
        "Fold": ([{"kind": "selectedView", "context": c, "state": a}, desc(c), desc(a)], a),
    }[form]
    if form == "Fold":
        variables.append("Contract")
    return {"variables": variables, "statics": statics, "inputs": inputs, "output": output}


def validate(catalog):
    schemes = {}
    forms = set()
    for row in catalog["frontendSchemes"]:
        shape(row)
        require(row["name"] not in schemes and row["form"] not in forms,
                "duplicate descriptor scheme")
        require({k: row[k] for k in ("variables", "statics", "inputs", "output")} ==
                canonical(row["form"]), "descriptor scheme form mismatch")
        forms.add(row["form"])
        schemes[row["name"]] = row
    require(forms == set(FORMS), "missing descriptor scheme form")
    heads = {row["name"]: row["form"] for row in catalog["frontendConstructors"]}
    used_schemes, used_heads = set(), set()
    for row in catalog["frontendDeclarations"]:
        target = row["association"]["target"]
        if row["kind"] == "ContractConstructor":
            require(heads.get(target) in ("DescriptorProduct", "DescriptorSequence") and
                    target not in used_heads, "invalid contract constructor association")
            used_heads.add(target)
        elif row["kind"] == "View":
            scheme = schemes.get(target)
            require(scheme is not None and target not in used_schemes,
                    "invalid View scheme association")
            require([s["parameter"] for s in row["statics"]] == scheme["statics"] and
                    [{k: v for k, v in p.items() if k != "name"} for p in row["inputs"]] ==
                    scheme["inputs"] and row["output"] == scheme["output"],
                    "View scheme declaration mismatch")
            used_schemes.add(target)
    require(used_schemes == set(schemes), "unreferenced descriptor scheme")
    require(used_heads == {h for h, f in heads.items() if f in
                          ("DescriptorProduct", "DescriptorSequence")},
            "unreferenced contract constructor")
