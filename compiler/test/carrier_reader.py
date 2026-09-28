"""The direct common reader preserves exact records and refuses authored syntax."""

import json

from cases import case
from commands import Commands
from tools import compiler, records


commands = Commands(records())
directory = commands.directory


def run(mode, text, *, refuses=None):
    path = directory / "input.pir"
    path.write_text(text)
    return commands.run([compiler, mode, path], refuses=refuses)


def common(functions=(), *, bindings=(), protocols=(), instances=(), entries=()):
    return [
        "zkc.protocol/1",
        list(bindings),
        list(functions),
        list(protocols),
        list(instances),
        list(entries),
    ]


def library(definitions, configurations=(), concrete=None):
    return [
        "zkc.library/1",
        definitions,
        list(configurations),
        common() if concrete is None else concrete,
    ]


def identity(name, typ="bool", argument="x"):
    return [
        "function",
        name,
        [[argument, typ]],
        [typ],
        [["return", [argument]]],
        [name, []],
    ]


def roundtrip(encoded):
    printed = run("protocol-format", json.dumps(encoded))
    assert printed.startswith("carrier module"), printed
    actual = json.loads(run("protocol-source", printed))
    assert actual == encoded, (actual, encoded, printed)
    assert run("protocol-format", printed) == printed
    return printed


for name in ("F-", "poly.fold", "return", "src_generated"):
    with case(f"exact common name {name}"):
        roundtrip(common([identity(name, argument=name)]))

# Exact text decoding does not broaden common admission's name policy.
for name in ("r#fold", "a b", 'quote"back\\slash', r"literal\u002e"):
    with case(f"quoted data remains subject to common admission {name}"):
        atom = json.dumps(name)
        source = f"carrier module {{ fn {atom}(x: bool) -> bool {{ return x; }} }}"
        assert atom in run("protocol-format", source)
        run("protocol-source", source, refuses="interactive-name")

for binder in ("F-", "koala-bear", "return", "zkc"):
    with case(f"exact static binder {binder}"):
        encoded = library(
            [
                [
                    "generic_function",
                    "Echo",
                    [[binder, "Field"]],
                    [["Field", [binder]]],
                    [["x-", f"field:{binder}"]],
                    [f"field:{binder}"],
                    [["return", ["x-"]]],
                ],
            ]
        )
        roundtrip(encoded)

with case("raw carrier identifiers and escaped strings decode once"):
    source = (
        r'carrier module { fn "\u0072eturn"(r#fold: bool) -> bool { return r#fold; } }'
    )
    assert json.loads(run("protocol-source", source)) == common(
        [
            identity("return", argument="fold"),
        ]
    )

with case("type binder has priority over installed type spelling"):
    roundtrip(
        library(
            [
                [
                    "generic_function",
                    "Echo",
                    [["bool", "Type"]],
                    [],
                    [["x", "bool"]],
                    ["bool"],
                    [["return", ["x"]]],
                ],
            ]
        )
    )

with case("structural types retain exact type and natural binders"):
    roundtrip(
        library(
            [
                [
                    "generic_function",
                    "Echo",
                    [["T-", "Type"], ["N-", "Nat"]],
                    [],
                    [["x", "fixed_vector<T-,N->"]],
                    ["fixed_vector<T-,N->"],
                    [["return", ["x"]]],
                ],
            ]
        )
    )

with case("associated common static paths retain odd binder roots"):
    roundtrip(
        library(
            [
                [
                    "generic_function",
                    "Echo",
                    [["G-", "Group"]],
                    [["ScalarAction", ["G-"]]],
                    [["x", "field:G-.Scalar"]],
                    ["field:G-.Scalar"],
                    [["return", ["x"]]],
                ],
            ]
        )
    )

with case("contract path differs from exact dotted helper"):
    encoded = library(
        [
            [
                "generic_function",
                "poly.fold",
                [["F-", "Field"]],
                [["CommRing", ["F-"]]],
                [["x", "table:F-"]],
                ["table:F-"],
                [["return", ["x"]]],
            ],
            [
                "generic_function",
                "Fold",
                [["F-", "Field"]],
                [["CommRing", ["F-"]]],
                [["a", "table:F-"], ["r", "field:F-"]],
                ["table:F-"],
                [
                    ["op", "operation", "poly.fold", ["F-"], [], ["a", "r"], ["b"]],
                    ["apply", "helper", "poly.fold", ["F-"], ["b"], ["c"]],
                    ["return", ["c"]],
                ],
            ],
        ],
        [
            ["configure", "Partial", "Fold", [], []],
            [
                "configure",
                "Selected",
                "Partial",
                [["F-", "koala-bear"]],
                [["operation", "arkworks/poly.fold"]],
            ],
        ],
    )
    printed = roundtrip(encoded)
    assert "poly::r#fold" in printed, printed
    assert '"poly.fold"::<' in printed, printed
    unqualified = printed.replace("zkc::poly::Table", "Table")
    assert json.loads(run("protocol-source", unqualified)) == encoded

with case("exact predicate and attribute data"):
    encoded = library(
        [
            [
                "generic_function",
                "Observe",
                [["T", "Transcript"], ["E", "Codec"]],
                [["Transcript", ["T"]], ["Encodes.bool", ["E"]]],
                [["s", "transcript:T"], ["x", "bool"]],
                ["transcript:T"],
                [
                    [
                        "op",
                        "observe",
                        "transcript.observe.bool",
                        ["T", "E"],
                        ["N", "message", "schema", "P", "V"],
                        ["s", "x"],
                        ["y"],
                    ],
                    ["return", ["y"]],
                ],
            ],
        ]
    )
    roundtrip(encoded)

with case("metadata type families and structural applications"):
    for typ in (
        "vector:koala-bear",
        "groups:bn254.g1",
        "fixed_vector<bool,2>",
        "index",
        "field:koala-bear",
    ):
        roundtrip(common([identity("Echo", typ)]))

with case("forward binding and concrete helper classification"):
    encoded = common(
        [
            [
                "function",
                "Use",
                [["x", "bool"]],
                ["bool"],
                [
                    ["op", "not", "not-", [], ["x"], ["y"]],
                    ["apply", "helper", "bool.not", [], ["y"], ["z"]],
                    ["return", ["z"]],
                ],
                ["Use", []],
            ],
            identity("bool.not"),
        ],
        bindings=[["not-", "bool.not", [], ""]],
    )
    printed = roundtrip(encoded)
    line = next(line for line in printed.splitlines() if "bind " in line)
    reordered = printed.replace(line + "\n", "")
    closing = reordered.rfind("}")
    reordered = reordered[:closing] + line + "\n" + reordered[closing:]
    assert json.loads(run("protocol-source", reordered)) == encoded
    assert '= "bool.not"(' in printed

with case("structured regions preserve records and sites"):
    roundtrip(
        common(
            [
                [
                    "function",
                    "Choose",
                    [["c", "bool"], ["x", "bool"]],
                    ["bool"],
                    [
                        [
                            "if",
                            "branch-",
                            "c",
                            ["x"],
                            [["yield", ["x"]]],
                            [["yield", ["x"]]],
                            ["y"],
                        ],
                        ["return", ["y"]],
                    ],
                    ["Choose", []],
                ],
                [
                    "function",
                    "Iterate",
                    [["lo", "index"], ["hi", "index"], ["x", "bool"]],
                    ["bool"],
                    [
                        [
                            "for",
                            "for-",
                            "i",
                            "lo",
                            "hi",
                            [["a", "x"]],
                            [],
                            [["yield", ["a"]]],
                            ["r"],
                        ],
                        ["return", ["r"]],
                    ],
                    ["Iterate", []],
                ],
            ]
        )
    )

with case("external declarations and exact origin data"):
    external = identity("External")
    external[4] = "external"
    external[5] = ["origin.name", [["F-", "koala-bear"]]]
    roundtrip(
        common(
            [external],
            protocols=[
                ["protocol", "Outside", ["P"], ["N"], [], [], [], "external"],
            ],
        )
    )

with case("protocol instructions dependencies instances and entries"):
    roundtrip(
        common(
            [identity("Echo")],
            protocols=[
                [
                    "protocol",
                    "Child",
                    ["P", "V"],
                    ["N"],
                    [["x", "P", "bool"]],
                    [["V", "bool"]],
                    [],
                    [
                        ["local", "local-", "P", "Echo", ["x"], ["y"]],
                        ["message", "wire-", "schema-", "P", "V", "y", "z"],
                        ["return", ["z"]],
                    ],
                ],
                [
                    "protocol",
                    "Root",
                    ["P", "V"],
                    ["M"],
                    [["x", "P", "bool"]],
                    [["V", "bool"]],
                    [["child-", "Child", [["N", "M"]]]],
                    [
                        ["call", "invoke-", "child-", ["x"], ["z"]],
                        ["return", ["z"]],
                    ],
                ],
                [
                    "protocol",
                    "Halt",
                    ["P"],
                    [],
                    [],
                    [],
                    [],
                    [["stop", "stop-", "P", "reject"]],
                ],
            ],
            instances=[
                [
                    "instance",
                    "child",
                    "Child",
                    [["N", "1"]],
                    [],
                    [["P", "Alice"], ["V", "Bob"]],
                ],
                [
                    "instance",
                    "root",
                    "Root",
                    [["M", "1"]],
                    [["child-", "child"]],
                    [["P", "Alice"], ["V", "Bob"]],
                ],
            ],
            entries=[["entry", "entry-", "root"]],
        )
    )

with case("constant and parameter loop counts"):
    roundtrip(
        common(
            protocols=[
                [
                    "protocol",
                    "Repeat",
                    ["P"],
                    ["N-"],
                    [["x", "P", "bool"]],
                    [["P", "bool"]],
                    [],
                    [
                        [
                            "loop",
                            "outer",
                            ["parameter", "N-"],
                            [["a", "x"]],
                            [],
                            [
                                [
                                    "loop",
                                    "inner",
                                    ["constant", "1"],
                                    [["b", "a"]],
                                    [],
                                    [["yield", ["b"]]],
                                    ["c"],
                                ],
                                ["yield", ["c"]],
                            ],
                            ["y"],
                        ],
                        ["return", ["y"]],
                    ],
                ],
            ],
            instances=[
                ["instance", "repeat", "Repeat", [["N-", "2"]], [], [["P", "P"]]],
            ],
            entries=[["entry", "main", "repeat"]],
        )
    )

with case("family ingress selectors retain exact names"):
    roundtrip(
        common(
            [
                [
                    "function",
                    "Select-",
                    [["n", "index"]],
                    ["index"],
                    [["return", ["n"]]],
                    ["Select-", []],
                ],
            ],
            protocols=[
                [
                    "protocol",
                    "Repeat",
                    ["P"],
                    ["N"],
                    [["n", "P", "index"]],
                    [["P", "index"]],
                    [],
                    [
                        [
                            "loop",
                            "repeat",
                            ["parameter", "N"],
                            [["i", "n"]],
                            [],
                            [["yield", ["i"]]],
                            ["j"],
                        ],
                        ["return", ["j"]],
                    ],
                ],
            ],
            instances=[
                [
                    "instance",
                    "repeat",
                    "Repeat",
                    [["N", ["ingress", "4", [["P", "Select-", ["n"]]]]]],
                    [],
                    [["P", "P"]],
                ],
            ],
            entries=[["entry", "main", "repeat"]],
        )
    )

for source, diagnostic in (
    ("carrier module {} trailing", "source-syntax"),
    ("carrier module { fn F() -> () {", "source-syntax"),
    ("carrier module { fn F(x: bool) -> bool { return x + x; } }", "source-syntax"),
    (
        "carrier module { fn F(x: bool) -> bool { [s] let y = x.field; return y; } }",
        "source-syntax",
    ),
    ("carrier module { bind b = bool::not(); }", "source-syntax"),
    ("carrier module { fn F<>() -> () { [s] poly::fold(); } }", "source-syntax"),
    (
        "carrier module { fn F<>() -> () { [s] unknown::operation(); } }",
        "source-syntax",
    ),
    ("carrier module { fn F<>() -> () { [s] F<bool>(); } }", "source-syntax"),
    (
        "carrier module { protocol P { roles(P); roles(P); return (); } }",
        "source-duplicate",
    ),
    (
        "carrier module { instance p: P { roles(P=P); roles(P=P); } }",
        "source-duplicate",
    ),
    ("carrier module { fn return(x: bool) -> bool { return x; } }", "source-syntax"),
    ("carrier module { struct Pair { x: bool } }", "source-carrier-authoring"),
    ("carrier module { use zkc::algebra; }", "source-carrier-authoring"),
):
    with case(f"malformed carrier {source}"):
        run("protocol-source", source, refuses=diagnostic)
        run("protocol-format", source, refuses=diagnostic)

with case("carrier type nesting is bounded"):
    typ = "FixedVector<" * 66 + "bool" + ", 1>" * 66
    run(
        "protocol-source",
        f"carrier module {{ fn F(x: {typ}) -> () {{ return (); }} }}",
        refuses="source-depth",
    )

with case("carrier body nesting is bounded"):
    body = "loop [s] 1 carry () -> () {" * 66 + "yield ();" + "}" * 66
    run(
        "protocol-source",
        f"carrier module {{ protocol P {{ roles(P); {body} }} }}",
        refuses="source-depth",
    )

with case("carrier lists are bounded"):
    arguments = ",".join("x" for _ in range(32769))
    run(
        "protocol-source",
        f"carrier module {{ protocol P {{ roles({arguments}); }} }}",
        refuses="source-limit",
    )

with case("carrier input size is bounded"):
    run(
        "protocol-source",
        "carrier module { /*" + "x" * (1024 * 1024) + "*/ }",
        refuses="byte-limit",
    )

with case("unsupported common instructions fail closed when printing"):
    # A canonical one-alternative variant table, with a bool payload.
    table = [
        "zkc.variant/1",
        ["Flag", "On", "bool", ["2"], ["1", "3"], ["4"], ["0", "5"]],
    ]
    typ = "variant:" + json.dumps(table, separators=(",", ":")).encode().hex()
    encoded = common(
        [
            [
                "function",
                "Unwrap",
                [["x", "bool"]],
                ["bool"],
                [
                    ["variant", "construct", typ, "On", ["x"], "v"],
                    [
                        "match",
                        "match",
                        "v",
                        [],
                        [["On", ["payload"], [["yield", ["payload"]]]]],
                        ["r"],
                    ],
                    ["return", ["r"]],
                ],
                ["Unwrap", []],
            ],
        ]
    )
    assert json.loads(run("protocol-source", json.dumps(encoded))) == encoded
    run("protocol-format", json.dumps(encoded), refuses="source-print-loss")

with case("explicit empty library cannot silently lose its envelope"):
    run("protocol-format", json.dumps(library([])), refuses="source-print-loss")

print(f"carrier reader: {commands.save()} checks")
