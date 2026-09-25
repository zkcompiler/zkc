"""Printed common carriers have a public, lossless and closed text boundary."""

import json

from cases import case
from commands import Commands
from tools import ROOT, compiler, records


directory = records()
commands = Commands(directory)


def run(mode, path, *, refuses=None, extra=()):
    return commands.run([compiler, mode, path, *extra], refuses=refuses)


for example, libraries in (
    ("examples/protocols/dleq.pir", ()),
    ("examples/projects/group/main.pir", ("examples/libraries/group/lib.pir",)),
):
    with case(example):
        encoded = run("protocol-source", ROOT / example,
                      extra=tuple(f"--library={ROOT / p}" for p in libraries))
        source = directory / "carrier.json"
        source.write_text(encoded)
        printed = run("protocol-format", source)
        assert printed.startswith("carrier module"), printed
        text = directory / "carrier.pir"
        text.write_text(printed)
        assert json.loads(run("protocol-source", text)) == json.loads(encoded)
        assert run("protocol-format", text) == printed
        run("protocol-admit", text)
        parsed = json.loads(run("protocol-parse", text))
        assert parsed["content"]["carrier"] is True, parsed


for prefix in ("src_", "lib_", "client_", "__library_operation_"):
    with case(f"explicit-carrier-symbol-{prefix}"):
        text = directory / "symbols.pir"
        body = f"module {{ fn {prefix}f(x: bool) -> bool {{ return x; }} }}"
        text.write_text("carrier " + body)
        run("protocol-source", text)
        text.write_text(body)
        run("protocol-source", text, refuses="source-name-reserved")


for declaration in (
    "mod child;",
    'library(namespace="test", name="x", version="1", resolution="r1");',
    'dependency x = library(namespace="test", name="x", version="1", resolution="r1");',
    "use x::F;",
    "interface X { type Value; }",
    "component X: I { type Value = bool; }",
    "link X = Client<Cell>;",
    "struct X { value: bool }",
    "const N: nat = 1;",
    'relation X = r1cs("not-read.json");',
    "pub fn X(x: bool) -> bool { return x; }",
):
    with case(f"closed-carrier-{declaration.split()[0]}"):
        text = directory / "closed.pir"
        text.write_text(f"carrier module {{ {declaration} }}")
        run("protocol-source", text, refuses="source-carrier-authoring")
        run("protocol-format", text, refuses="source-carrier-authoring")

with case("carrier-is-not-a-child-module"):
    child = directory / "child.pir"
    child.write_text("carrier module { fn src_f(x: bool) -> bool { return x; } }")
    app = directory / "app.pir"
    app.write_text("module { mod child; }")
    run("protocol-source", app, refuses="source-carrier-project")

with case("carrier-root-has-no-captured-libraries"):
    text = directory / "standalone.pir"
    text.write_text("carrier module { fn src_f(x: bool) -> bool { return x; } }")
    run("protocol-source", text, refuses="source-carrier-project",
        extra=(f"--library={ROOT / 'examples/libraries/group/lib.pir'}",))

with case("carrier-is-not-a-library-dependency"):
    library = directory / "dependency.pir"
    library.write_text("carrier module { fn src_f(x: bool) -> bool { return x; } }")
    app = directory / "dependency-root.pir"
    app.write_text('module { dependency x = library(namespace="test", '
                   'name="x", version="1", resolution="r1"); }')
    run("protocol-source", app, refuses="source-carrier-project",
        extra=(f"--library={library}",))

with case("carrier-requires-explicit-bindings"):
    text = directory / "profile.pir"
    text.write_text("carrier module Profile { }")
    run("protocol-source", text, refuses="source-carrier-authoring")

with case("carrier-still-checks-types"):
    text = directory / "invalid.pir"
    text.write_text("carrier module { fn src_f(x: bool) -> index { return x; } }")
    run("protocol-source", text, refuses="source-type-mismatch")

# Carrier origins are admitted metadata, not new claims to authored-project
# origins. Names in unrelated namespaces do not identify function coordinates.
for owner in ("protocol", "binding", "instance", "entry"):
    with case(f"carrier-origin-shares-{owner}-name"):
        encoded = [
            "zkc.protocol/1",
            [["G", "bool.not", [], ""]] if owner == "binding" else [],
            [["function", "A", [["x", "bool"]], ["bool"],
              [["return", ["x"]]], ["G", []]]],
            [["protocol", "G", ["P"], [], [], [], [], [["return", []]]]]
            if owner == "protocol" else [], [], [],
        ]
        if owner in ("instance", "entry"):
            instance = "G" if owner == "instance" else "root"
            encoded[3] = [["protocol", "Root", ["P"], [], [], [], [], [["return", []]]]]
            encoded[4] = [["instance", instance, "Root", [], [], [["P", "P"]]]]
            encoded[5] = [["entry", "G" if owner == "entry" else "main", instance]]
        source = directory / f"origin-{owner}.json"
        source.write_text(json.dumps(encoded))
        run("protocol-admit", source)
        printed = run("protocol-format", source)
        text = directory / f"origin-{owner}.pir"
        text.write_text(printed)
        assert json.loads(run("protocol-source", text)) == encoded
