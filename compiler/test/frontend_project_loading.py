"""Explicit filesystem projects, bounded capture, and pure editing/stdin paths."""

import copy
import json
from pathlib import Path
from contextlib import contextmanager
from itertools import count

from cases import case
from commands import Commands
from tools import compiler, records

record_dir = records()
commands = Commands(record_dir)
fixture_ids = count()


@contextmanager
def project_directory():
    path = record_dir / f"project-{next(fixture_ids)}"
    path.mkdir()
    yield path

FIELD = "bls12-381.fr"
RELATION = [
    "zkc.relation.r1cs/1",
    FIELD,
    "4",
    "1",
    "1",
    [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]],
]


def write(root, name, text):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path


def run(mode, path, *options, refuses=None):
    return commands.run([compiler, mode, path, *options], refuses=refuses)


def identity(name):
    return f'library(namespace="loading", name="{name}", version="1", resolution="r1")'


def relation_source(path="data.json"):
    return f'module {{ relation Circuit = r1cs("{path}"); }}'


with case("parse and format do not load modules or assets"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", 'module { mod missing; relation R = r1cs("absent.json"); }')
    json.loads(run("protocol-parse", source))
    formatted = run("protocol-format", source)
    source.write_text(formatted)
    run("protocol-format-check", source)
    for mode in ("protocol-parse", "protocol-format", "protocol-format-check"):
        run(mode, source, "--library=missing.pir", refuses="unsupported-option")

with case("nested modules use root-relative conventional paths"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", '''module {
      mod outer; use outer::inner::Id;
      fn Main(x: bool) -> bool { return Id(x); }
    }''')
    write(root, "outer.pir", "module { pub mod inner; }")
    write(root, "outer/inner.pir", "module { pub fn Id(x: bool) -> bool { return x; } }")
    # A wrong sibling lookup must not succeed by finding a convenient file.
    write(root, "inner.pir", "this is not source")
    json.loads(run("protocol-source", source))
    analysis = json.loads(run("protocol-analyze", source))
    assert analysis["state"] == "source_checked", analysis
    run("protocol-admit", source)

with case("repeat explicit roots and dependency aliases are independent"), project_directory() as tmp:
    root = Path(tmp)
    left = write(root, "left/lib.pir", f'''module {{ {identity("left")};
      pub fn Id(x: bool) -> bool {{ return x; }}
    }}''')
    right = write(root, "right/lib.pir", f'''module {{ {identity("right")};
      pub fn Id(x: bool) -> bool {{ return x; }}
    }}''')
    source = write(root, "app.pir", f'''module {{
      dependency alpha = {identity("left")};
      dependency beta = {identity("right")};
      use alpha::Id as A; use beta::Id as B;
      fn Main(x: bool) -> bool {{ let y = A(x); return B(y); }}
    }}''')
    options = (f"--library={left}", f"--library={right}")
    original = json.loads(run("protocol-source", source, *options))
    source.write_text(source.read_text().replace("alpha", "renamed"))
    assert json.loads(run("protocol-source", source, *options)) == original
    analysis = json.loads(run("protocol-analyze", source, *options))
    assert analysis["state"] == "source_checked", analysis

with case("assets belong to declaring files and frozen snapshots survive deletion"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", "module { mod left; mod right; }")
    write(root, "left.pir", "module { mod leaf; }")
    write(root, "right.pir", "module { mod leaf; }")
    write(root, "left/leaf.pir", relation_source())
    write(root, "right/leaf.pir", relation_source())
    left = write(root, "left/data.json", json.dumps(RELATION))
    other = copy.deepcopy(RELATION)
    other[5][0][0][0][1] = "2"
    right = write(root, "right/data.json", json.dumps(other))
    write(root, "data.json", "wrong declaring-file base")
    frozen = run("protocol-resolve", source)
    snapshot = write(root, "snapshot.json", frozen)
    decoded = json.loads(frozen)
    assert decoded[0] == "zkc.relations/1", decoded
    assert len(decoded[1][0]) == 2, decoded
    assert decoded[1][0][0] != decoded[1][0][1], decoded
    left.unlink()
    right.unlink()
    run("protocol-admit", snapshot)
    run("protocol-resolve", source, refuses="relation-asset-missing")

with case("same relative asset name has independent library owners"), project_directory() as tmp:
    root = Path(tmp)
    libraries = []
    for name, coefficient in (("left", "1"), ("right", "3")):
        libraries.append(write(root, f"{name}/lib.pir", f'''module {{
          {identity(name)}; relation Circuit = r1cs("data.json");
        }}'''))
        relation = copy.deepcopy(RELATION)
        relation[5][0][0][0][1] = coefficient
        write(root, f"{name}/data.json", json.dumps(relation))
    source = write(root, "app.pir", f'''module {{
      dependency a = {identity("left")}; dependency b = {identity("right")};
    }}''')
    frozen = json.loads(run("protocol-resolve", source, *(f"--library={p}" for p in libraries)))
    assert frozen[0] == "zkc.relations/1", frozen
    assert len(frozen[1][0]) == 2, frozen
    assert frozen[1][0][0] != frozen[1][0][1], frozen

with case("file source execution captures relation assets automatically"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", relation_source())
    write(root, "data.json", json.dumps(RELATION))
    assert json.loads(run("protocol-source", source))[0] == "zkc.relations/1"
    run("protocol-admit", source)

for kind in ("missing", "directory", "escape", "traversal", "absolute"):
    with case(f"relation asset refuses {kind}"), project_directory() as tmp:
        root = Path(tmp) / "project"
        root.mkdir()
        outside = write(Path(tmp), "outside.json", json.dumps(RELATION))
        reference = "data.json"
        if kind == "directory":
            (root / reference).mkdir()
        elif kind == "escape":
            (root / reference).symlink_to(outside)
        elif kind == "traversal":
            reference = "../outside.json"
        elif kind == "absolute":
            reference = str(outside)
        source = write(root, "app.pir", relation_source(reference))
        code = "relation-asset-missing" if kind in ("missing", "directory") else "relation-asset-path"
        run("protocol-resolve", source, refuses=code)

for kind in ("missing", "directory", "escape", "cycle"):
    with case(f"module capture refuses {kind}"), project_directory() as tmp:
        root = Path(tmp) / "project"
        root.mkdir()
        source = write(root, "app.pir", "module { mod child; }")
        if kind == "directory":
            (root / "child.pir").mkdir()
        elif kind == "escape":
            outside = write(Path(tmp), "outside.pir", "module {}")
            (root / "child.pir").symlink_to(outside)
        elif kind == "cycle":
            (root / "child.pir").symlink_to(source)
        code = {"escape": "project-source-path", "cycle": "project-module-cycle"}.get(kind, "project-source-missing")
        run("protocol-source", source, refuses=code)

with case("duplicate module declarations refuse before second read"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", "module { mod child; mod child; }")
    write(root, "child.pir", "module {}")
    run("protocol-source", source, refuses="project-module-duplicate")

for metadata in (f"{identity('child')};", f"dependency a = {identity('a')};"):
    with case(f"child cannot own root metadata: {metadata}"), project_directory() as tmp:
        root = Path(tmp)
        source = write(root, "app.pir", "module { mod child; }")
        write(root, "child.pir", f"module {{ {metadata} }}")
        run("protocol-source", source, refuses="project-library-root")

with case("relation dependency count is project-wide including repeated paths"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", "module { mod left; mod right; }")
    write(root, "data.json", json.dumps(RELATION))
    for name, count in (("left", 33), ("right", 32)):
        imports = " ".join(f'relation R{i} = r1cs("data.json");' for i in range(count))
        write(root, f"{name}.pir", f"module {{ {imports} }}")
    run("protocol-resolve", source, refuses="relation-dependency-limit")

for count, size in ((1, 8 * 1024 * 1024 + 1), (17, 8 * 1024 * 1024)):
    with case(f"family and project asset bytes are bounded ({count} imports)"), project_directory() as tmp:
        root = Path(tmp)
        imports = " ".join(f'relation R{i} = air("large.json");' for i in range(count))
        source = write(root, "app.pir", f"module {{ {imports} }}")
        # A sparse file tests capture bounds before decoding. Repeated aliases
        # must count their decoding work even though capture reads bytes once.
        with (root / "large.json").open("wb") as asset:
            asset.truncate(size)
        run("protocol-resolve", source, refuses="byte-limit")

with case("project source count is bounded before extra child reads"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", "module { " + " ".join(f"mod m{i};" for i in range(256)) + " }")
    for i in range(255):
        write(root, f"m{i}.pir", "module {}")
    # The 257th source is deliberately absent: count refusal takes precedence.
    run("protocol-source", source, refuses="project-source-limit")

with case("module depth is bounded"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", "module { mod m; }")
    for depth in range(1, 65):
        write(root, "/".join(["m"] * depth) + ".pir", "module { mod m; }")
    run("protocol-source", source, refuses="project-module-depth")

with case("options are exact and inappropriate combinations refuse"), project_directory() as tmp:
    root = Path(tmp)
    source = write(root, "app.pir", "module {}")
    for option in ("--library", "--library=", "--library=-", "--libraries=x", "extra.pir"):
        run("protocol-source", source, option, refuses="unsupported-option")
    run("protocol-source", source, "--library=x", "--library=x", refuses="duplicate-option")
    run("protocol-source", source, *(f"--library={i}.pir" for i in range(64)), refuses="project-library-limit")
    run("protocol-source", source, "--library=missing.pir", refuses="project-source-missing")
    snapshot = write(root, "source.json", run("protocol-source", source))
    run("protocol-source", snapshot, "--library=missing.pir", refuses="unsupported-option")
    commands.source("protocol-source", "module {}", "--library=missing.pir", refuses="unsupported-option")

with case("source stdin never resolves relation assets from working directory"):
    commands.source("protocol-source", relation_source(), refuses="relation-unresolved")

with case("a root file named like standard input is a file"), project_directory() as tmp:
    # Only standard input itself has no file. A file of that name anchors its
    # project's child modules like any other.
    root = Path(tmp)
    write(root, "<stdin>", "module { mod child; use child::Keep; fn Main(x: bool) -> bool { return Keep(x); } }")
    write(root, "child.pir", "module { pub fn Keep(x: bool) -> bool { return x; } }")
    commands.run([compiler, "protocol-source", "<stdin>"], cwd=root)

with case("a refused name leaves the rest of the project to analysis"), project_directory() as tmp:
    # The declaration a name refusal belongs to, and what calls it, are
    # deferred; unrelated declarations are still checked.
    root = Path(tmp)
    write(root, "inner.pir", "module { pub fn Keep(x: bool) -> bool { return x; } }")
    for refusal, text in (
        ("source-name-reserved", "fn src_f(x: bool) -> bool { return x; } "
                                 "fn Uses(x: bool) -> bool { return src_f(x); }"),
        ("source-name-ambiguous", "mod inner; fn inner.Keep(x: bool) -> bool origin Chosen() { return x; } "
                                  "fn Uses(x: bool) -> bool { return inner.Keep(x); }"),
    ):
        source = write(root, "app.pir", f"module {{ {text} fn Good(x: bool) -> bool {{ return x; }} }}")
        analysis = json.loads(run("protocol-analyze", source))
        assert [d["code"] for d in analysis["diagnostics"]] == [refusal], analysis["diagnostics"]
        states = {d["display_name"]: d["body_state"] for d in analysis["declarations"]}
        assert states["Good"] == "source_checked" and states["Uses"] == "deferred", states

with case("file syntax recovery preserves partial analysis"), project_directory() as tmp:
    source = write(Path(tmp), "app.pir", '''module {
      fn Before(x: bool) -> bool { return x; }
      fn Broken(x: bool) -> bool { let x = ; }
      fn After(x: bool) -> bool { return x; }
    }''')
    analysis = json.loads(run("protocol-analyze", source))
    assert analysis["state"] == "incomplete", analysis
    assert analysis["diagnostics"], analysis
    run("protocol-source", source, refuses="source-syntax")
