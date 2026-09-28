"""Structured declaration paths retain category and visibility authority."""

import json
from itertools import count

from cases import case, counted
from commands import Commands
from tools import compiler, records

root = records()
commands = Commands(root)
ids = count()


def identity(name):
    return f'library(namespace="ambiguity", name="{name}", version="1", resolution="r1")'


def library(body, name="a"):
    return f" {identity(name)}; {body} "


def app(body):
    imports = "use zkc::algebra::Vector;" if "Vector<" in body else ""
    return f" {imports} dependency a = {identity('a')}; {body} "


def run(source, body="", *, libraries=None, files=None, refuses=None, analyze=False, emit=False):
    folder = root / f"project-{next(ids)}"
    folder.mkdir()

    def write(name, text):
        path = folder / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    source = write("app.pir", source)
    libraries = libraries if libraries is not None else {"a/lib.pir": library(body)}
    options = [f"--library={write(name, text)}" for name, text in libraries.items()]
    for name, text in (files or {}).items():
        write(name, text)
    mode = "protocol-analyze" if analyze else "protocol-source" if emit else "protocol-admit"
    result = commands.run(
        [compiler, mode, source, *options],
        refuses=refuses,
    )
    return json.loads(result) if analyze or emit else result


# Ordinary punctuation no longer creates an alternative exact declaration.
# Each category remains an independent refusal, even if the dependency exports
# a declaration with the corresponding path.
CATEGORIES = (
    ("type", "struct a.T { flag: bool }", "pub struct T { other: index }"),
    ("constant", "const a.N: index = 1;", "pub const N: index = 2;"),
    ("predicate", "interface a.I { type Value drop; }", "pub interface I { type Value drop; }"),
    ("call", "fn a.Keep(x: bool) -> bool { return x; }", "pub fn Keep(x: bool) -> bool { return x; }"),
    ("protocol", "protocol a.P { roles(A); return; }", "pub protocol P { roles(A); return; }"),
    ("bundle", "bundle a.B(F) = (Field(F));", "pub bundle B(F) = (Field(F));"),
)
for category, declaration, exported in CATEGORIES:
    for visibility in ("public", "private"):
        with case(f"{category}: dotted declaration refuses with {visibility} dependency"):
            run(app(declaration), exported if visibility == "public" else exported.replace("pub ", ""),
                refuses="source-syntax")
    with case(f"{category}: quoting cannot authorize an ordinary declaration"):
        head, name, tail = declaration.split(" ", 2)
        run(app(f'{head} "{name}" {tail}'), exported, refuses="source-identifier")

for setup, path, files, body in (
    ("", "a::T", {}, "pub struct T { flag: bool }"),
    ("use a as m;", "m::T", {}, "pub struct T { flag: bool }"),
    ("use a::T as Imported;", "Imported", {}, "pub struct T { flag: bool }"),
    ("mod child;", "child::T", {"child.pir": "pub use a::T;"}, "pub struct T { flag: bool }"),
    ("use a::inner as m;", "m::T", {"a/inner.pir": "pub struct T { flag: bool }"}, "pub mod inner;"),
):
    with case(f"type path and reexport retain identity: {path}"):
        run(app(f"{setup} fn Main(x: {path}) -> bool {{ return x.flag; }}"), body, files=files)

with case("qualified record construction uses the imported constructor"):
    run(app("fn Main(x: bool) -> bool { let value = a::T { flag: x }; return value.flag; }"),
        "pub struct T { flag: bool }")
with case("qualified constant is an expression path"):
    run(app("fn Main() -> index { return a::N; }"), "pub const N: index = 2;")
with case("imported constant alias is a lexical value"):
    run(app("use a::N as Imported; fn Main() -> index { return Imported; }"), "pub const N: index = 2;")
with case("private alias is not access authority"):
    run(app("mod child; fn Main(x: child::T) -> bool { return x.flag; }"),
        "pub struct T { flag: bool }", files={"child.pir": "use a::T;"}, refuses="source-name-private")
with case("private intermediate module is not access authority"):
    run(app("fn Main(x: a::inner::T) -> bool { return x.flag; }"), "mod inner;",
        files={"a/inner.pir": "pub struct T { flag: bool }"}, refuses="source-name-private")

for declaration, use in (
    ("pub const T: index = 1;", "fn Main(x: a::T) -> bool { return true; }"),
    ("pub struct N { flag: bool }", "fn Main() -> index { return a::N; }"),
    ("pub const Keep: index = 1;", "fn Main(x: bool) -> bool { return a::Keep(x); }"),
):
    with case(f"path lookup retains its requested category: {declaration}"):
        run(app(use), declaration, refuses="source-name-kind")

for setup, target in (("", "a::Identity::extra"), ("use a as m;", "m::Identity::extra"),
                      ("use a::Identity as I;", "I::extra")):
    with case(f"ordinary function is not a suffix namespace: {target}"):
        run(app(f"{setup} fn Main(x: bool) -> bool {{ return {target}(x); }}"),
            "pub fn Identity(x: bool) -> bool { return x; }", refuses="source-name-kind")

CELL = """pub interface Cell { type Value copy drop; nat N; local step(x: Value) -> Value; }
  pub component C: Cell { type Value = bool; nat N = 1;
    local step(x: bool) -> bool { return x; } }
  pub select Selected = C;
"""

def resolved_component_projection(report, target):
    # Concrete abstract members in generic signatures retain the existing
    # formation limit after successful resolution.
    assert report["phases"]["resolution"] == "complete", report
    assert report["phases"]["source_check"] == "incomplete", report
    assert [d["code"] for d in report["diagnostics"]] == ["library-abstract-type"], report
    declarations = {d["display_name"]: d for d in report["resolved_declarations"]}
    assert any(d["source"] == declarations["Main"]["identity_key"] and
               d["target"] == declarations[target]["identity_key"]
               for d in report["dependencies"]), report["dependencies"]

for prefix in ("a", "m"):
    with case(f"component type projection retains its resolved root: {prefix}"):
        report = run(app(f"""use a as m;
          fn Main<C: a::Cell>(x: {prefix}::Selected::Value) -> {prefix}::Selected::Value {{ return x; }}"""),
                     CELL, analyze=True)
        resolved_component_projection(report, "Selected")
with case("component selection aliases instantiate member calls and types"):
    run(app("""use a::Selected as Selected;
      fn Client<C: a::Cell>(x: C::Value) -> C::Value { return C::step(x); }
      link Linked = Client<Selected>;
      fn Main(x: bool) -> bool { return Linked(x); }
    """), CELL)
for owner in ("C", "Selected"):
    for member in ("Missing", "Value::extra"):
        with case(f"component type member must resolve completely: {owner}::{member}"):
            run(app(f"fn Main(x: a::{owner}::{member}) -> bool {{ return true; }}"),
                CELL, refuses="source-name-kind")
    with case(f"component call member must exist: {owner}"):
        run(app(f"fn Main(x: bool) -> bool {{ return a::{owner}::Missing(x); }}"),
            CELL, refuses="source-name-kind")

DOMAIN_CELL = """pub interface I { domain G: group; }
  pub component C: I { domain G: group = "bls12-381.g1"; }
"""
with case("component domain projection resolves its installed member path"):
    # Resolution completes; a concrete component domain in a signature keeps its
    # existing formation limit.
    report = run(app("fn Main(x: a::C::G::Scalar::Element) -> bool { return true; }"),
                 DOMAIN_CELL, analyze=True)
    assert report["phases"]["resolution"] == "complete", report
    assert [d["code"] for d in report["diagnostics"]] == ["source-type-domain"], report
for projection in ("G::Missing::Element", "G::Element::extra"):
    with case(f"component domain projections require complete installed members: {projection}"):
        run(app(f"fn Main(x: a::C::{projection}) -> bool {{ return true; }}"),
            DOMAIN_CELL, refuses="source-name-kind")

# Repeated module aliases are traversed segment by segment, never enumerated as
# alternative readings; the traversal depth is bounded.
for depth, refuses in ((64, None), (65, "source-resolution-limit")):
    with case(f"module alias traversal is bounded: {depth} segments"):
        alias_path = "::".join(["a"] * depth + ["Leaf"])
        run(f"use self as a; fn Leaf(x: bool) -> bool {{ return x; }} "
            f"fn Main(x: bool) -> bool {{ return {alias_path}(x); }}",
            libraries={}, refuses=refuses)

RELATION = json.dumps(["zkc.relation.r1cs/1", "bls12-381.fr", "4", "1", "1",
                       [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]]])
VIEW = 'relation Circuit = r1cs("data.json"); pub derive Core = rank_one(Circuit, public_matrices);'
FIELD = 'Vector<"bls12-381.fr"::Element>'
for setup, target in (("", "a::Core_Assemble"), ("use a as m;", "m::Core_Assemble"),
                      ("use a::Core_Assemble as Assemble;", "Assemble")):
    with case(f"view helper authorization survives qualification: {target}"):
        run(app(f"{setup} fn Main(x: {FIELD}, y: {FIELD}) -> {FIELD} {{ return {target}(x,y); }}"),
            VIEW, files={"a/data.json": RELATION})
for kind, member in (("rank_one", "Evaluate"), ("rank_one", "BindingPoint0"),
                     ("multilinear", "BindingPoint3"), ("multilinear", "BindingPoint01"),
                     ("multilinear", "CheckBinding3")):
    with case(f"view kind and coordinate restrict exported helpers: {kind}::{member}"):
        run(app(f"use a::Core_{member} as Unused;"), VIEW.replace("rank_one", kind),
            files={"a/data.json": RELATION}, refuses="source-name-unresolved")
with case("an unused import cannot name a nonexistent view helper"):
    run(app("use a::Core_BindingPoint99 as Unused;"), VIEW,
        files={"a/data.json": RELATION}, refuses="source-name-unresolved")
with case("a predicate alias names the dependency bundle"):
    run(app("""use a::B as Imported;
      fn Main<F: Field>(x: F::Element) -> F::Element requires(Imported(F)) { return x; }
    """), "pub bundle B(F) = (Field(F));")
for prefix in ("self", "crate"):
    with case(f"{prefix} retains private local visibility"):
        run(f"struct T {{ flag: bool }} fn Main(x: {prefix}::T) -> bool {{ return x.flag; }}", libraries={})
with case("super reaches a private declaration from a descendant"):
    run("struct T { flag: bool } mod child;", libraries={},
        files={"child.pir": "fn Main(x: super::T) -> bool { return x.flag; }"})

with case("unknown enum alternative retains its semantic leaf diagnostic"):
    run("""interface Cell { type Value drop; }
      enum Outcome<C: Cell> { Ready(C::Value) }
      fn Client<C: Cell>(x: C::Value) -> bool {
        let result: Outcome<C> = Outcome::Missing(x); return true;
      }""", libraries={}, refuses="library-source-enum-alternative")
with case("unknown protocol dependency retains its semantic leaf diagnostic"):
    run("protocol Main { roles(A); return; } instance I: Main::missing { roles(A=Alice); }",
        libraries={}, refuses="source-static-projection")

# Distinct one-segment and nested dependencies must not collapse to one symbol.
PROJECTED_PROTOCOLS = """
  protocol Good { roles(A); inputs(A x: bool); outputs(A bool); return x; }
  protocol Bad { roles(A); inputs(A x: bool); outputs(A bool);
    let y = local A { zkc::core::not(x) }; return y; }
  protocol Mid { roles(A); dependencies(part: Bad()); return; }
  protocol Root { roles(A); dependencies(child_part: Good(), child: Mid()); return; }
"""
for setup, root_name in (("", "Root"), ("use Root as R;", "R"), ("use self as ns;", "ns::Root")):
    for members, selected in (("child_part", "Good"), ("child::part", "Bad")):
        with case(f"protocol member boundaries preserve the selected body: {root_name}::{members}"):
            source = (PROJECTED_PROTOCOLS + setup +
                      f"instance I: {root_name}::{members} {{ roles(A=Alice); }} entry E=I;")
            emitted = run(source, libraries={}, emit=True)
            assert emitted == run(source.replace(f"I: {root_name}::{members}", f"I: {selected}"),
                                  libraries={}, emit=True)
            instance = next(i for i in emitted[4] if i[1] == "I")
            body = next(p[-1] for p in emitted[3] if p[1] == instance[2])
            assert instance[2] == selected, instance
            assert (body == [["return", ["x"]]]) == (selected == "Good"), body
            run(source, libraries={})
for root_name in ("a::Root", "R"):
    with case(f"imported dependency preserves its body: {root_name}"):
        body = PROJECTED_PROTOCOLS.replace("protocol ", "pub protocol ")
        source = app(f"use a::Root as R; use a::Good as G; instance I: {root_name}::child_part {{ roles(A=Alice); }} entry E=I;")
        assert run(source, body, emit=True) == run(source.replace(f"I: {root_name}::child_part", "I: G"), body, emit=True)
        run(source, body)
with case("dotted dependency labels are obsolete ordinary binders"):
    run("protocol Good { roles(A); return; } protocol Root { roles(A); dependencies(child.part: Good()); return; }",
        libraries={}, refuses="source-syntax")

print(f"{counted()} structured name resolution cases")
