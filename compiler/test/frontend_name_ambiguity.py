"""Complete category-specific name candidates, opaque names and real members."""

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
    return f"module {{ {identity(name)}; {body} }}"


def app(body):
    return f"module {{ dependency a = {identity('a')}; {body} }}"


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


# Each use enters a distinct resolver category. Both spellings of a type must
# refuse at resolution, before a misleading element-type or field error.
CATEGORIES = (
    ("type", "struct a.T { flag: bool }",
     "fn Main(x: a.T) -> bool { return x.flag; }", "pub struct T { other: index }"),
    ("explicit type", "struct a.T { flag: bool }",
     "fn Main(x: a::T) -> bool { return x.flag; }", "pub struct T { other: index }"),
    ("constructor", "struct a.T { flag: bool }",
     "fn Main(x: bool) -> bool { let t = a.T { flag: x }; return t.flag; }",
     "pub struct T { other: index }"),
    ("value", "const a.N: index = 1;",
     "fn Main() -> index { return a.N; }", "pub const N: index = 2;"),
    ("static", "const a.N: index = 1;",
     "fn Main() -> index { let n = index::constant() attributes(a.N); return n; }",
     "pub const N: index = 2;"),
    ("predicate", "interface a.I { type Value drop; }",
     "fn Main<C: a.I>(x: C::Value) -> C::Value { return x; }",
     "pub interface I { type Value drop; }"),
    ("call", "fn a.Keep(x: bool) -> bool { return x; }",
     "fn Main(x: bool) -> bool { return a.Keep(x); }",
     "pub fn Keep(x: bool) -> bool { return x; }"),
    ("declaration", "protocol a.P { roles(A); return; }",
     "instance I: a.P { roles(A=A); }", "pub protocol P { roles(A); return; }"),
)
for category, exact, use, exported in CATEGORIES:
    for visibility in ("public", "private"):
        with case(f"{category}: complete {visibility} dependency candidate is ambiguous"):
            body = exported if visibility == "public" else exported.replace("pub ", "")
            run(app(f"{exact} {use}"), body, refuses="source-name-ambiguous")

for spelling in ("a.T", "a::T"):
    with case(f"dependency record {spelling} has its own field when unshadowed"):
        run(app(f"fn Main(x: {spelling}) -> index {{ return x.other; }}"),
            "pub struct T { other: index }")
    with case(f"exact opaque record {spelling} remains one name without a competing path"):
        run(app(f"struct a.T {{ flag: bool }} fn Main(x: {spelling}) -> bool {{ return x.flag; }}"))

with case("unambiguous record alias bypasses the conflicting spelling"):
    run(app("""struct a.T { flag: bool } use a::T as Imported;
      fn Main(x: Imported) -> index { return x.other; }"""),
        "pub struct T { other: index }")

with case("unambiguous constant alias bypasses the conflicting spelling"):
    run(app("""const a.N: index = 1; use a::N as Imported;
      fn Main() -> index { return Imported; }"""), "pub const N: index = 2;")

for exact, use, body in (
    ("const a.T: index = 1;", "fn Main(x: a.T) -> bool { return x.flag; }",
     "pub struct T { flag: bool }"),
    ("struct a.N { flag: bool }", "fn Main() -> index { return a.N; }",
     "pub const N: index = 2;"),
    ("struct a.Keep { flag: bool }", "fn Main(x: bool) -> bool { return a.Keep(x); }",
     "pub fn Keep(x: bool) -> bool { return x; }"),
    ("fn a.N(x: bool) -> bool { return x; }",
     "fn Main() -> index { let n = index::constant() attributes(a.N); return n; }",
     "pub const N: index = 2;"),
    ("const a.I: index = 1;", "fn Main<C: a.I>(x: C::Value) -> C::Value { return x; }",
     "pub interface I { type Value drop; }"),
):
    with case(f"wrong-category exact declaration does not shadow path: {exact}"):
        run(app(f"{exact} {use}"), body)

for exact, use, body in (
    ("struct a.T { flag: bool }", "fn Main(x: a.T) -> bool { return x.flag; }",
     "pub fn T(x: bool) -> bool { return x; }"),
    ("const a.N: index = 1;", "fn Main() -> index { return a.N; }",
     "pub struct N { flag: bool }"),
    ("fn a.Keep(x: bool) -> bool { return x; }",
     "fn Main(x: bool) -> bool { return a.Keep(x); }", "pub const Keep: index = 1;"),
):
    with case(f"wrong-category path does not compete with exact declaration: {exact}"):
        run(app(f"{exact} {use}"), body)

for alias, setup, files in (
    ("m", "use a as m;", {}),
    ("m", "use a::inner as m;", {"a/inner.pir": "module { pub struct T { flag: bool } }"}),
    ("child", "mod child;", {"child.pir": "module { pub use a::T; }"}),
):
    with case(f"type ambiguity follows module alias or reexport: {setup}"):
        run(app(f"{setup} struct {alias}.T {{ flag: bool }} fn Main(x: {alias}.T) -> bool {{ return x.flag; }}"),
            "pub struct T { flag: bool } pub mod inner;" if "inner" in setup else
            "pub struct T { flag: bool }", files=files, refuses="source-name-ambiguous")

for prefix in ("a", "m"):
    with case(f"two aliases of the same declaration are one candidate: {prefix}"):
        run(app(f"use a as m; use a::T as {prefix}.T; fn Main(x: {prefix}.T) -> bool {{ return x.flag; }}"),
            "pub struct T { flag: bool }")

with case("private alias path is not access authority"):
    run(app("mod child; fn Main(x: child.T) -> bool { return x.flag; }"),
        "pub struct T { flag: bool }", files={"child.pir": "module { use a::T; }"},
        refuses="source-name-private")

with case("private intermediate module is not access authority"):
    run(app("fn Main(x: a.inner.T) -> bool { return x.flag; }"),
        "mod inner;", files={"a/inner.pir": "module { pub struct T { flag: bool } }"},
        refuses="source-name-private")

with case("private intermediate module still supplies a complete ambiguity candidate"):
    run(app("struct a.inner.T { flag: bool } fn Main(x: a.inner.T) -> bool { return x.flag; }"),
        "mod inner;", files={"a/inner.pir": "module { pub struct T { flag: bool } }"},
        refuses="source-name-ambiguous")

# An ordinary function is not a namespace for suffixes: Identity exists and
# Identity.extra does not, so the spelling has one reading and is not ambiguous.
for setup, target in (("", "a.Identity.extra"), ("use a as m;", "m.Identity.extra"),
                      ("use a::Identity as I;", "I.extra")):
    for quoted in (False, True):
        with case(f"ordinary function is not a suffix namespace: {target}, quoted={quoted}"):
            call = json.dumps(target) if quoted else target
            run(app(f"""{setup} fn {target}(x: bool) -> bool {{ return bool::not(x); }}
              fn Main(x: bool) -> bool {{ return {call}(x); }}"""),
                "pub fn Identity(x: bool) -> bool { return x; }")
    with case(f"ordinary function suffix alone refuses: {target}"):
        run(app(f"{setup} fn Main(x: bool) -> bool {{ return {target}(x); }}"),
            "pub fn Identity(x: bool) -> bool { return x; }", refuses="source-name-kind")

with case("opaque dotted declaration at a dependency endpoint resolves completely"):
    run(app("fn Main(x: bool) -> bool { return a.Identity.extra(x); }"),
        "pub fn Identity.extra(x: bool) -> bool { return x; }")

with case("opaque dotted declaration endpoint competes with a local exact name"):
    run(app("""fn a.Identity.extra(x: bool) -> bool { return x; }
      fn Main(x: bool) -> bool { return a.Identity.extra(x); }"""),
        "pub fn Identity.extra(x: bool) -> bool { return x; }", refuses="source-name-ambiguous")

for member in ("On", "Missing", "On.extra"):
    with case(f"enum ambiguity requires an actual whole alternative: {member}"):
        run(app(f"""fn a.Flag.{member}(x: bool) -> bool {{ return x; }}
          fn Main(x: bool) -> bool {{ return a.Flag.{member}(x); }}"""),
            "pub enum Flag { On(bool) }",
            refuses="source-name-ambiguous" if member == "On" else None)

CELL = """pub interface Cell { type Value copy drop; nat N; local step(x: Value) -> Value; }
  pub component C: Cell { type Value = bool; nat N = 1;
    local step(x: bool) -> bool { return x; } }
  pub select Selected = C;
"""
for owner in ("C", "Selected"):
    for member in ("Value", "Missing", "Value.extra"):
        with case(f"{owner} type candidate requires a whole declared member: {member}"):
            run(app(f"""struct a.{owner}.{member} {{ flag: bool }}
              fn Main(x: a.{owner}.{member}) -> bool {{ return x.flag; }}"""), CELL,
                refuses="source-name-ambiguous" if member == "Value" else None)
    for member in ("step", "Missing", "step.extra"):
        with case(f"{owner} call candidate requires a whole declared member: {member}"):
            run(app(f"""fn a.{owner}.{member}(x: bool) -> bool {{ return x; }}
              fn Main(x: bool) -> bool {{ return a.{owner}.{member}(x); }}"""), CELL,
                refuses="source-name-ambiguous" if member == "step" else None)
    with case(f"{owner} static candidate requires a real member"):
        run(app(f"""const a.{owner}.N: index = 2;
          fn Main(x: Array<bool, a.{owner}.N>) -> Array<bool, a.{owner}.N> {{ return x; }}"""),
            CELL, refuses="source-name-ambiguous")

# These are resolution-only probes: formation of a concrete abstract member
# in a generic signature is outside this fix. Require complete resolution and
# the intended retained dependency, while explicitly asserting formation fails.
def resolved_component_projection(report, target):
    assert report["phases"]["resolution"] == "complete", report
    assert report["phases"]["source_check"] == "incomplete", report
    assert [d["code"] for d in report["diagnostics"]] == ["library-abstract-type"], report
    declarations = {d["display_name"]: d for d in report["resolved_declarations"]}
    assert any(d["source"] == declarations["Main"]["identity_key"] and
               d["target"] == declarations[target]["identity_key"]
               for d in report["dependencies"]), report["dependencies"]


for prefix in ("a", "m"):
    with case(f"component type projections retain their resolved root through {prefix}"):
        report = run(app(f"""use a as m;
          fn Main<C: a.Cell>(x: {prefix}::Selected::Value) -> {prefix}::Selected::Value {{ return x; }}"""), CELL, analyze=True)
        resolved_component_projection(report, "Selected")

with case("opaque component roots retain real projection boundaries"):
    report = run("""module {
      interface I { type Value copy drop; }
      component Opaque.C: I { type Value = bool; }
      fn Main<C: I>(x: Opaque.C::Value) -> Opaque.C::Value { return x; }
    }""", libraries={}, analyze=True)
    resolved_component_projection(report, "Opaque.C")

with case("component selection aliases still instantiate real member calls and types"):
    run(app("""use a::Selected as Selected;
      fn Client<C: a.Cell>(x: C::Value) -> C::Value { return C::step(x); }
      link Linked = Client<Selected>;
      fn Main(x: bool) -> bool { return Linked(x); }
    """), CELL)

# View helpers are authorized by their view owner, including use aliases.
RELATION = json.dumps(["zkc.relation.r1cs/1", "bls12-381.fr", "4", "1", "1",
                       [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]]])
VIEW = 'relation Circuit = r1cs("data.json"); pub derive Core = rank_one(Circuit, public_matrices);'
FIELD = "Vector<bls12-381.fr::Element>"
for setup, prefix in (("", "a.Core"), ("use a as m;", "m.Core"),
                      ("use a::Core as V;", "V")):
    for member in ("Assemble", "Assemble.extra", "Missing"):
        target = f"{prefix}_{member}"
        with case(f"view helper candidate is complete: {target}"):
            run(app(f"""{setup} fn {target}(x: {FIELD}, y: {FIELD}) -> {FIELD} {{ return x; }}
              fn Main(x: {FIELD}, y: {FIELD}) -> {FIELD} {{ return {target}(x,y); }}"""),
                VIEW, files={"a/data.json": RELATION},
                refuses="source-name-ambiguous" if member == "Assemble" and prefix != "V" else None)



for kind, member, ambiguous in (
    ("rank_one", "Residuals", True),
    ("rank_one", "Evaluate", False),
    ("rank_one", "BindingPoint0", False),
    ("multilinear", "BindingPoint1", True),
    ("multilinear", "BindingPoint2", True),
    ("multilinear", "BindingPoint3", False),
    ("multilinear", "BindingPoint01", False),
    ("multilinear", "CheckBinding1", True),
    ("multilinear", "CheckBinding2", True),
    ("multilinear", "CheckBinding3", False),
):
    with case(f"view helper exists for its kind and coordinate: {kind}.{member}"):
        run(app(f"""fn a.Core_{member}(x: bool) -> bool {{ return x; }}
          fn Main(x: bool) -> bool {{ return a.Core_{member}(x); }}"""),
            VIEW.replace("rank_one", kind), files={"a/data.json": RELATION},
            refuses="source-name-ambiguous" if ambiguous else None)


with case("an unused import cannot name a nonexistent view helper"):
    run(app("use a::Core_BindingPoint99 as Unused;"), VIEW,
        files={"a/data.json": RELATION}, refuses="source-name-unresolved")

with case("a bundle predicate competes with a dependency predicate"):
    run(app("""bundle a.B(F) = (Field(F));
      fn Main<F: Field>(x: F::Element) -> F::Element requires(a.B(F)) { return x; }
    """), "pub bundle B(F) = (Field(F));", refuses="source-name-ambiguous")

with case("a predicate alias can disambiguate a bundle"):
    run(app("""bundle a.B(F) = (Field(F)); use a::B as Imported;
      fn Main<F: Field>(x: F::Element) -> F::Element requires(Imported(F)) { return x; }
    """), "pub bundle B(F) = (Field(F));")

for prefix in ("self", "crate"):
    with case(f"{prefix} paths preserve visibility of private local declarations"):
        run("module { struct T { flag: bool } fn Main(x: " + prefix +
            ".T) -> bool { return x.flag; } }", libraries={})

with case("super path reaches a private declaration from a descendant"):
    run("module { struct T { flag: bool } mod child; }", libraries={},
        files={"child.pir": "module { fn Main(x: super.T) -> bool { return x.flag; } }"})


for projection, ambiguous in (("G.Scalar.Element", True), ("G.Missing.Element", False),
                              ("G.Element.extra", False)):
    with case(f"component domain projections require complete installed members: {projection}"):
        run(app(f"""struct a.C.{projection} {{ flag: bool }}
          fn Main(x: a.C.{projection}) -> bool {{ return x.flag; }}"""),
            '''pub interface I { domain G: group; }
              pub component C: I { domain G: group = "bls12-381.g1"; }''',
            refuses="source-name-ambiguous" if ambiguous else None)

with case("imported real view helper remains callable"):
    run(app(f"""use a::Core_Assemble as Assemble;
      fn Main(x: {FIELD}, y: {FIELD}) -> {FIELD} {{ return Assemble(x,y); }}"""),
        VIEW, files={"a/data.json": RELATION})


with case("an unknown enum alternative retains its semantic leaf diagnostic"):
    run("""module {
      interface Cell { type Value drop; }
      enum Outcome<C: Cell> { Ready(C::Value) }
      fn Client<C: Cell>(x: C::Value) -> bool {
        let result: Outcome<C> = Outcome::Missing(x);
        return true;
      }
    }""", libraries={}, refuses="library-source-enum-alternative")

with case("an unknown protocol dependency retains its semantic leaf diagnostic"):
    run("""module { protocol Main { roles(A); return; }
      instance I: Main::missing { roles(A=Alice); }
    }""", libraries={}, refuses="source-static-projection")

with case("a missing protocol member does not compete with an exact protocol"):
    run("""module {
      protocol Main { roles(A); return; }
      protocol Main.missing { roles(A); return; }
      instance I: Main.missing { roles(A=Alice); } entry main=I;
    }""", libraries={})


with case("alternative module readings still consume a bounded resolution budget"):
    # Each a or a.a prefix is a module alias to this same scope. Enumerating
    # all complete readings is exponential although every leaf is identical.
    # Counting actual lookup atoms must still refuse before enumerating them.
    path = ".".join(["a"] * 34 + ["Leaf"])
    run("module { use self as a; use self as a.a; "
        "fn Leaf(x: bool) -> bool { return x; } "
        f"fn Main(x: bool) -> bool {{ return {path}(x); }} }}",
        libraries={}, refuses="source-resolution-limit")


# The dependency label child.part and the two-member path child::part denote
# different protocols, with observably different bodies. Compare the entire
# emitted carrier against an explicit selection, as well as admitting it.
PROJECTED_PROTOCOLS = """
  protocol Good { roles(A); inputs(A x: bool); outputs(A bool); return x; }
  protocol Bad { roles(A); inputs(A x: bool); outputs(A bool);
    let y = local A { bool::not(x) }; return y; }
  protocol Mid { roles(A); dependencies(part: Bad()); return; }
  protocol Root { roles(A); dependencies(child.part: Good(), child: Mid()); return; }
"""
for setup, root_name in (("", "Root"), ("use Root as R;", "R"),
                         ("use self as ns;", "ns::Root"),
                         ("use self as ns;", "ns.Root")):
    for members, selected in (("child.part", "Good"), ("child::part", "Bad")):
        with case(f"protocol dependency boundaries preserve the selected body: {root_name}::{members}"):
            source = ("module {" + PROJECTED_PROTOCOLS + setup +
                      f"instance I: {root_name}::{members} {{ roles(A=Alice); }} entry E=I; }}")
            direct = source.replace(f"I: {root_name}::{members}", f"I: {selected}")
            emitted = run(source, libraries={}, emit=True)
            assert emitted == run(direct, libraries={}, emit=True)
            instance = next(i for i in emitted[4] if i[1] == "I")
            body = next(p[-1] for p in emitted[3] if p[1] == instance[2])
            assert instance[2] == selected, instance
            assert (body == [["return", ["x"]]]) == (selected == "Good"), body
            run(source, libraries={})

for root_name in ("a::Root", "a.Root", "R"):
    with case(f"imported dotted dependency retains its body: {root_name}"):
        body = PROJECTED_PROTOCOLS.replace("protocol ", "pub protocol ")
        source = app(f"""use a::Root as R; use a::Good as G;
          instance I: {root_name}::child.part {{ roles(A=Alice); }} entry E=I;""")
        assert run(source, body, emit=True) == run(
            source.replace(f"I: {root_name}::child.part", "I: G"), body, emit=True)
        run(source, body)

for prefix in ("a.part", "a::part"):
    with case(f"dotted dependency alias preserves member boundaries: {prefix}"):
        body = PROJECTED_PROTOCOLS.replace("protocol ", "pub protocol ")
        source = app(f"""use a.part::Good as G;
          instance I: {prefix}::Root::child.part {{ roles(A=Alice); }} entry E=I;""")
        source = source.replace("dependency a =", "dependency a.part =")
        assert run(source, body, emit=True) == run(
            source.replace(f"I: {prefix}::Root::child.part", "I: G"), body, emit=True)
        run(source, body)

with case("a dotted dependency is not the two-member path with the same flattened spelling"):
    run("""module {
      protocol Good { roles(A); return; }
      protocol Root { roles(A); dependencies(child.part: Good()); return; }
      instance I: Root::child::part { roles(A=Alice); } entry E=I;
    }""", libraries={}, refuses="source-static-projection")

with case("a dotted dependency with no competing nested path is recognized in ambiguity checks"):
    run("""module {
      protocol Good { roles(A); return; }
      protocol Root { roles(A); dependencies(child.part: Good()); return; }
      protocol Root.child.part { roles(A); return; }
      instance I: Root::child.part { roles(A=Alice); } entry E=I;
    }""", libraries={}, refuses="source-name-ambiguous")

# Member lookup must resolve a selection's base in the same Static category as
# the selection itself, regardless of unrelated declarations at its spelling.
for unrelated in ("", "fn a.C(x: bool) -> bool { return x; }",
                  "struct a.C { flag: bool }", "protocol a.C { roles(A); return; }"):
    for spelling in ("a.C", "a::C"):
        for exact, use in (
            ("struct a.S.Value { flag: bool }",
             "fn Main(x: a.S.Value) -> bool { return x.flag; }"),
            ("const a.S.N: index = 2;",
             "fn Main(x: Array<bool, a.S.N>) -> Array<bool, a.S.N> { return x; }"),
            ("fn a.S.step(x: bool) -> bool { return x; }",
             "fn Main(x: bool) -> bool { return a.S.step(x); }"),
        ):
            with case(f"selection preserves Static target category: {spelling}, {unrelated}, {exact}"):
                run("module { use self as a; " + CELL.replace("pub ", "") +
                    unrelated + f" select S = {spelling}; " + exact + use + "}",
                    libraries={}, refuses="source-name-ambiguous")

# Dotted enum declaration roots are opaque in both type and call paths; the
# alternative remains a separate member after imported-symbol rewriting.
for spelling in ("a::Outcome.part", "a.Outcome.part"):
    with case(f"dotted enum root preserves nominal identity and constructor: {spelling}"):
        run(app(f"""fn Main<C: a.Cell>(x: C::Value) -> C::Value {{
          let result: a.Outcome.part<C> = {spelling}::Ready(x);
          match result -> (out) {{ Ready(v) => {{ yield (v); }} }}
          return out;
        }}"""), "pub interface Cell { type Value drop; } pub enum Outcome.part<C: Cell> { Ready(C::Value) }")
    with case(f"dotted enum root preserves the missing-alternative diagnostic: {spelling}"):
        run(app(f"""fn Main<C: a.Cell>(x: C::Value) -> C::Value {{
          let result: a.Outcome.part<C> = {spelling}::Missing(x); return x;
        }}"""), "pub interface Cell { type Value drop; } pub enum Outcome.part<C: Cell> { Ready(C::Value) }",
            refuses="library-source-enum-alternative")

for spelling in ("a::Root.part", "a.Root.part"):
    with case(f"dotted protocol root preserves the missing-member diagnostic: {spelling}"):
        run(app(f"instance I: {spelling}::missing {{ roles(A=Alice); }}"),
            "pub protocol Root.part { roles(A); return; }",
            refuses="source-static-projection")

for member in ("Value.part", "Missing.part"):
    for spelling in (f"a::C::{member}", f"a.C.{member}"):
        with case(f"dotted component member requires the whole member: {spelling}"):
            run(app(f"""struct a.C.{member} {{ flag: bool }}
              fn Main(x: {spelling}) -> bool {{ return x.flag; }}"""),
                """pub interface I { type Value.part copy drop; }
                  pub component C: I { type Value.part = bool; }""",
                refuses="source-name-ambiguous" if member == "Value.part" else None)

print(f"{counted()} complete name resolution cases")
