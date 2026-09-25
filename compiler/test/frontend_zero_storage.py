"""Empty representations retain ownership across checked-library composition.

Self-contained authored programs exercise helpers, aggregate paths, region
joins, nominal associated slots, and public representation boundaries.
"""
import json

from cases import case
from commands import Commands
from tools import records

commands = Commands(records())

REGRESSIONS = {
    "empty helper round trip": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local step(x: Value) -> Value; }
  component Impl: Cell { type Value = (); local step(x: Value) -> Value { return Id(x); } }
  fn Id(x: ()) -> () { return x; }
  fn Client<C: Cell>(x: C::Value) -> C::Value { return C::step(x); }
  link Closed = Client<Impl>;
}''',
    "empty helper result creation": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local make(b: bool) -> Value; }
  component Impl: Cell { type Value = (); local make(b: bool) -> Value { return Unit(b); } }
  fn Unit(b: bool) -> () { return (); }
  fn Client<C: Cell>(b: bool) -> C::Value { return C::make(b); }
  link Closed = Client<Impl>;
}''',
    "mixed aggregate helper input": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local f(x: (Value, bool)) -> bool; }
  component Impl: Cell { type Value = (); local f(x: (Value, bool)) -> bool { return Snd(x); } }
  fn Snd(p: ((), bool)) -> bool { return p.1; }
  fn Client<C: Cell>(x: (C::Value, bool)) -> bool { return C::f(x); }
  link Closed = Client<Impl>;
}''',
    "mixed aggregate projection": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local step(x: Value, b: bool) -> bool; }
  component Impl: Cell { type Value = (); local step(x: Value, b: bool) -> bool { let p = (x, b); return p[1]; } }
  fn Client<C: Cell>(x: C::Value, b: bool) -> bool { return C::step(x, b); }
  link Closed = Client<Impl>;
}''',
    "mixed aggregate conditional capture": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local f(x: (Value, bool), b: bool) -> bool; }
  component Impl: Cell { type Value = ();
    local f(x: (Value, bool), b: bool) -> bool {
      if b capture(x) -> (r) { yield (x.1); } else { yield (x.1); }
      return r;
    }
  }
  fn Client<C: Cell>(x: (C::Value, bool), b: bool) -> bool { return C::f(x, b); }
  link Closed = Client<Impl>;
}''',
    "mixed aggregate conditional result": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local f(x: ((), bool), b: bool) -> (Value, bool); }
  component Impl: Cell { type Value = ();
    local f(x: ((), bool), b: bool) -> (Value, bool) {
      if b capture(x) -> (r) { yield (x); } else { yield (x); }
      return r;
    }
  }
  fn Client<C: Cell>(x: ((), bool), b: bool) -> (C::Value, bool) { return C::f(x, b); }
  link Closed = Client<Impl>;
}''',
    "empty tuple projection": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local first(x: (Value, Value)) -> Value; }
  component Impl: Cell { type Value = (); local first(x: (Value, Value)) -> Value { return x.0; } }
  fn Client<C: Cell>(x: (C::Value, C::Value)) -> C::Value { return C::first(x); }
  link Closed = Client<Impl>;
}''',
    "distinct associated slot conversion": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Swap { type A drop; type B drop; local f(x: A) -> B; }
  component Impl: Swap { type A = (); type B = (); local f(x: A) -> B { return x; } }
  fn Client<C: Swap>(x: C::A) -> C::B { return C::f(x); }
  link Closed = Client<Impl>;
}''',
    "empty conditional result creation": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local make(x: (), b: bool) -> Value; }
  component Impl: Cell { type Value = ();
    local make(x: (), b: bool) -> Value {
      if b capture(x) -> (y) { yield (x); } else { yield (x); }
      return y;
    }
  }
  fn Client<C: Cell>(x: (), b: bool) -> C::Value { return C::make(x, b); }
  link Closed = Client<Impl>;
}''',
    "projected empty result disposal": '''module { library(namespace="example", name="cells", version="1", resolution="capture-1");
  interface Cell { type Value drop; local erase(x: (Value, bool)) -> (); }
  component Impl: Cell { type Value = (); local erase(x: (Value, bool)) -> () { return x.0; } }
  fn Client<C: Cell>(x: (C::Value, bool)) -> () { return C::erase(x); }
  link Closed = Client<Impl>;
}''',
}

# Logical unit counts at the authored Closed boundary, independent of storage.
PORTS = {
    "empty helper round trip": (1, 1), "empty helper result creation": (0, 1),
    "mixed aggregate helper input": (1, 0), "mixed aggregate projection": (1, 0),
    "mixed aggregate conditional capture": (1, 0), "mixed aggregate conditional result": (0, 1),
    "empty tuple projection": (2, 1), "distinct associated slot conversion": (1, 1),
    "empty conditional result creation": (0, 1), "projected empty result disposal": (1, 0),
}


def emit(text):
    encoded = commands.source("protocol-source", text)
    carrier = json.loads(encoded)
    assert json.loads(commands.source("protocol-source", encoded)) == carrier
    commands.source("protocol-admit", encoded)
    return carrier, encoded


for name, text in REGRESSIONS.items():
    with case(f"zero storage {name} links and independently admits"):
        carrier, encoded = emit(text)
        closed = next(f for f in carrier[2] if f[1] == "Closed")
        inputs = [port[1] for port in closed[2]]
        outputs = closed[3]
        assert tuple(sum(t.startswith("resource_unit:") for t in ports)
                     for ports in (inputs, outputs)) == PORTS[name]
        if name == "distinct associated slot conversion":
            assert inputs[0] != outputs[0], "associated slots must remain nominal"
            assert "resource_unit.consume" in encoded
            assert "resource_unit.create" in encoded
        if name in ("empty helper round trip", "empty helper result creation", "mixed aggregate conditional result", "empty conditional result creation"):
            assert "resource_unit.create" in encoded
        if name in ("empty helper round trip", "mixed aggregate helper input", "mixed aggregate projection", "mixed aggregate conditional capture", "projected empty result disposal"):
            assert "resource_unit.consume" in encoded


IDENTITY = REGRESSIONS["empty helper round trip"].replace("return Id(x);", "return x;")

with case("same-slot empty identity transfers without creation or disposal"):
    _, encoded = emit(IDENTITY)
    assert "resource_unit.create" not in encoded
    assert "resource_unit.consume" not in encoded

with case("private empty aggregate cannot duplicate its public input"):
    commands.source("protocol-source", IDENTITY.replace(
        "return x; } }", "let pair = (x, x); return pair.0; } }"),
        refuses="library-resource-use")

with case("private empty helper calls cannot reuse an input"):
    commands.source("protocol-source", REGRESSIONS["empty helper round trip"].replace(
        "return Id(x);", "let first = Id(x); return Id(x);"),
        refuses="library-resource-use")

with case("capture moves the resource even when the private tuple is empty"):
    commands.source("protocol-source", REGRESSIONS["empty conditional result creation"].replace(
        "make(x: (), b: bool)", "make(x: Value, b: bool)").replace(
        "x: (), b: bool) -> C::Value", "x: C::Value, b: bool) -> C::Value").replace(
        "return y;", "return x;"), refuses="library-resource-use")

with case("abstract clients cannot rebrand equal empty representations"):
    commands.source("protocol-source", REGRESSIONS["distinct associated slot conversion"].replace(
        "return C::f(x);", "return x;"), refuses="library-type-mismatch")

with case("a non-droppable abstract input still requires a use"):
    text = IDENTITY.replace("type Value drop;", "type Value;").replace(
        "fn Client<C: Cell>(x: C::Value) -> C::Value { return C::step(x); }",
        "fn Client<C: Cell>(x: C::Value, b: bool) -> bool { return b; }").replace(
        "link Closed = Client<Impl>;", "")
    commands.source("protocol-source", text, refuses="library-resource-leak")

with case("copyable empty data can still be reused by its private body"):
    emit(IDENTITY.replace("type Value drop;", "type Value copy drop;").replace(
        "return x; } }", "let pair = (x, x); return pair.0; } }"))

with case("a stopping helper never reaches boundary resource creation"):
    _, encoded = emit(REGRESSIONS["empty helper result creation"].replace(
        "fn Unit(b: bool) -> () { return (); }",
        "fn Unit(b: bool) -> () { stop refused; }"))
    assert "refused" in encoded
    assert "resource_unit.create" not in encoded

with case("nested mixed aggregate paths preserve zero-storage ownership"):
    text = REGRESSIONS["mixed aggregate helper input"].replace(
        "(Value, bool)", "((Value, bool), bool)").replace(
        "(C::Value, bool)", "((C::Value, bool), bool)").replace(
        "((), bool)", "(((), bool), bool)").replace("return p.1;", "return p.0.1;")
    emit(text)

with case("a helper adapter inside each arm retains nested call resolution"):
    text = REGRESSIONS["mixed aggregate conditional capture"].replace(
        "yield (x.1);", "let value = Snd(x); yield (value);").replace(
        "  link Closed", "  fn Snd(p: ((), bool)) -> bool { return p.1; }\n  link Closed")
    emit(text)

with case("mixed join creates only on the plain arm without widening its input"):
    emit('''module {
      library(namespace="example", name="mixed-join", version="1", resolution="r1");
      interface Cell { type Value drop; local choose(x: Value, y: (), b: bool) -> Value; }
      component Impl: Cell {
        type Value = ();
        local choose(x: Value, y: (), b: bool) -> Value {
          if b capture(x, y) -> (r) { yield (x); } else { yield (y); }
          return r;
        }
      }
      fn Client<C: Cell>(x: C::Value, y: (), b: bool) -> C::Value {
        return C::choose(x, y, b);
      }
      link Closed = Client<Impl>;
    }''')


# A known private variant carries an empty owned payload beside stored data.
MIXED_VARIANT = '''module { library(namespace="example", name="cells", version="1", resolution="capture-1"); enum Holder { Has(((), bool)), Nothing(bool) } interface Cell { type Value drop; local f(x: (Value, bool), b: bool) -> bool; } component Impl: Cell { type Value = ();
               local f(x: (Value, bool), b: bool) -> bool {
                 let h: Holder = Holder::Has(x);
                 match h capture(b) -> (r) { Has(p) => { yield (b); }, Nothing(q) => { yield (q); } }
                 return r;
               }
             } fn Client<C: Cell>(x: (C::Value, bool), b: bool) -> bool { return C::f(x, b); } link Closed = Client<Impl>; }'''

with case("private mixed variant transports and disposes its empty resource"):
    carrier, encoded = emit(MIXED_VARIANT)
    closed = next(f for f in carrier[2] if f[1] == "Closed")
    assert sum(p[1].startswith("resource_unit:") for p in closed[2]) == 1
    assert closed[3] == ["bool"]
    assert "variant:" in encoded
    assert "resource_unit.consume" in encoded
    assert "resource_unit.create" not in encoded

with case("packing a private variant consumes the affine input once"):
    commands.source("protocol-source", MIXED_VARIANT.replace(
        "return r;", "let twice: Holder = Holder::Has(x); return r;"),
        refuses="library-resource-use")

with case("private empty input without drop permission cannot acquire an adapter"):
    commands.source("protocol-source", REGRESSIONS["empty helper round trip"].replace(
        "type Value drop;", "type Value;"), refuses="library-resource-profile")


with case("private variant reuse is refused by linker ownership admission"):
    commands.source("protocol-source", MIXED_VARIANT.replace(
        "return r;",
        "match h capture(b) -> (again) { Has(p) => { yield (b); }, "
        "Nothing(q) => { yield (q); } } return again;"),
        refuses="library-resource-use")

with case("copyable nondroppable empty values cannot acquire an affine adapter"):
    commands.source("protocol-source", REGRESSIONS["empty helper round trip"].replace(
        "type Value drop;", "type Value copy;"), refuses="library-resource-profile")

with case("equal empty representations of distinct components do not authorize a cast"):
    text = IDENTITY.replace(
        "fn Client<C: Cell>(x: C::Value) -> C::Value { return C::step(x); }",
        "fn Client<C: Cell, D: Cell>(x: C::Value) -> D::Value { return x; }").replace(
        "link Closed = Client<Impl>;", "")
    commands.source("protocol-source", text, refuses="library-type-mismatch")


PLAIN_VARIANT_HELPER = MIXED_VARIANT.replace(
    "match h capture(b) -> (r) { Has(p) => { yield (b); }, Nothing(q) => { yield (q); } }",
    "let r = Check(h);").replace(
    " fn Client", " fn Check(h: Holder) -> bool { match h capture() -> (r) { "
    "Has(p) => { yield (p.1); }, Nothing(q) => { yield (q); } } return r; } fn Client")

with case("a private variant adapts its active payload into a plain helper"):
    _, encoded = emit(PLAIN_VARIANT_HELPER)
    assert "resource_unit.consume" in encoded
    assert "resource_unit.create" not in encoded

with case("plain variant adaptation cannot consume the source twice"):
    commands.source("protocol-source", PLAIN_VARIANT_HELPER.replace(
        "let r = Check(h);", "let first = Check(h); let r = Check(h);"),
        refuses="library-resource-use")

NESTED_VARIANT_HELPER = PLAIN_VARIANT_HELPER.replace(
    "interface Cell", "enum Outer { Wrap(Holder), Other(bool) } interface Cell").replace(
    "let r = Check(h);", "let outer: Outer = Outer::Wrap(h); let r = CheckOuter(outer);").replace(
    " fn Client", " fn CheckOuter(outer: Outer) -> bool { match outer capture() -> (r) { "
    "Wrap(h) => { let b = Check(h); yield (b); }, Other(b) => { yield (b); } } return r; } fn Client")

with case("nested private variants recursively adapt active payloads"):
    emit(NESTED_VARIANT_HELPER)

with case("nested variant permissions prevent repeated plain helper use"):
    commands.source("protocol-source", NESTED_VARIANT_HELPER.replace(
        "let r = CheckOuter(outer);", "let first = CheckOuter(outer); let r = CheckOuter(outer);"),
        refuses="library-resource-use")


def linked_variant_leaves(text, display_name=None):
    report = json.loads(commands.source("protocol-analyze", text))
    assert report["state"] == "source_checked", report["diagnostics"]
    def walk(leaves):
        for leaf in leaves:
            if leaf["kind"] == "variant":
                yield leaf
                for alternative in leaf["alternatives"]:
                    yield from walk(alternative)
    return [leaf for link in report["checked_libraries"]["links"]
            for function in link["functions"]
            if display_name is None or function["display_name"] == display_name
            for layout in function["layouts"]
            for leaf in walk(layout["leaves"])]


with case("nested variants meet ownership from every alternative"):
    leaves = linked_variant_leaves(NESTED_VARIANT_HELPER, "Impl::f")
    def carries_unit(leaf):
        return leaf["kind"] == "resource_unit" or any(
            carries_unit(child) for alt in leaf["alternatives"] for child in alt)
    rich = [leaf for leaf in leaves if carries_unit(leaf)]
    assert rich
    assert all(not leaf["copy"] and leaf["drop"] for leaf in rich)
    # The adapter's new plain variants regain copy only after consuming the
    # active token; the original enriched variants remain affine.
    # Only Impl::f is inspected: plain helper inputs cannot satisfy this check.
    # Its authored Holder and Outer both carry the original token, so its plain
    # layouts belong to the recursively rebuilt adapter results.
    plain = [leaf for leaf in leaves if not carries_unit(leaf)]
    assert plain
    assert all(leaf["copy"] and leaf["drop"] for leaf in plain)
    assert {tuple(leaf["type"]["fields"]) for leaf in plain} == {
        ("Has", "Nothing"), ("Wrap", "Other"),
    }

with case("a droppable token does not grant drop to another variant alternative"):
    text = '''module {
      library(namespace="example", name="variant-permissions", version="1", resolution="r1");
      interface Cell { type Value drop; type Required; }
      component Impl: Cell { type Value = (); type Required = bool; }
      enum Choice<C: Cell> { Has((C::Value, bool)), Other(C::Required) }
      enum Outer<C: Cell> { Wrap(Choice<C>), Spare(bool) }
      fn Client<C: Cell>(x: Outer<C>) -> Outer<C> { return x; }
      link Closed = Client<Impl>;
    }'''
    leaves = linked_variant_leaves(text)
    assert leaves
    assert all(not leaf["copy"] and not leaf["drop"] for leaf in leaves)
    commands.source("protocol-source", text.replace(
        "fn Client<C: Cell>(x: Outer<C>) -> Outer<C> { return x; }",
        "fn Client<C: Cell>(x: Outer<C>, b: bool) -> bool { return b; }"),
        refuses="library-resource-leak")


CAPTURE_ALIASES = '''module {
  library(namespace="example", name="capture-aliases", version="1", resolution="r1");
  interface Marker {}
  component Impl: Marker {}
  fn Client<C: Marker>(x: bool) -> bool {
    let pair = (x, x);
    if x capture(pair, x) -> (result) {
      yield (pair.0);
    } else {
      yield (x);
    }
    return result;
  }
  link Closed = Client<Impl>;
}'''

with case("copyable aggregate aliases share one conditional carrier capture"):
    emit(CAPTURE_ALIASES)

with case("copyable aggregate aliases share one match carrier capture"):
    emit(CAPTURE_ALIASES.replace(
        "  interface Marker", "  enum Choice { First(bool), Second(bool) }\n  interface Marker").replace(
        "    if x capture(pair, x) -> (result) {\n      yield (pair.0);\n    } else {\n      yield (x);\n    }",
        "    let choice: Choice = Choice::First(x);\n"
        "    match choice capture(pair, x) -> (result) {\n"
        "      First(value) => { yield (pair.0); },\n"
        "      Second(value) => { yield (x); }\n    }"))

with case("flattened capture deduplication never authorizes an affine alias"):
    commands.source("protocol-source", REGRESSIONS["mixed aggregate conditional capture"].replace(
        "if b capture(x)", "let alias = x; if b capture(x, alias)"),
        refuses="library-resource-use")

with case("flattened capture deduplication never authorizes a nested affine variant alias"):
    commands.source("protocol-source", NESTED_VARIANT_HELPER.replace(
        "let r = CheckOuter(outer);",
        "let alias = outer; if b capture(outer, alias) -> (r) { "
        "let value = CheckOuter(outer); yield (value); } else { "
        "let value = CheckOuter(alias); yield (value); }"),
        refuses="library-resource-use")


PUBLIC_VARIANT_RETURN = '''module {
  library(namespace="example", name="variant-return", version="1", resolution="r1");
  enum Holder { Has(((), bool)), Nothing(bool) }
  interface Cell { type Value drop; local get(x: (Value, bool), b: bool) -> Holder; }
  component Impl: Cell {
    type Value = ();
    local get(x: (Value, bool), b: bool) -> Holder {
      if b capture(x, b) -> (holder) {
        let h: Holder = Holder::Has(x); yield (h);
      } else {
        let h: Holder = Holder::Nothing(b); yield (h);
      }
      return holder;
    }
  }
  fn Client<C: Cell>(x: (C::Value, bool), b: bool) -> Holder {
    return C::get(x, b);
  }
  link Closed = Client<Impl>;
}'''

with case("a public variant return disposes the private active payload token"):
    carrier, encoded = emit(PUBLIC_VARIANT_RETURN)
    closed = next(f for f in carrier[2] if f[1] == "Closed")
    assert len(closed[3]) == 1 and closed[3][0].startswith("variant:")
    assert "resource_unit:" not in closed[3][0]
    assert "resource_unit.consume" in encoded
    assert "resource_unit.create" not in encoded


VARIANT_RESULT_JOIN = '''module {
  library(namespace="example", name="variant-result-join", version="1", resolution="r1");
  enum Holder { Has(((), bool)), Nothing(bool) }
  interface Cell { type Value drop; local get(x: (Value, bool), b: bool) -> bool; }
  component Impl: Cell {
    type Value = ();
    local get(x: (Value, bool), b: bool) -> bool {
      if b capture(x, b) -> (holder) {
        let h: Holder = Holder::Has(x); yield (h);
      } else {
        let h = Plain(b); yield (h);
      }
      return Check(holder);
    }
  }
  fn Plain(b: bool) -> Holder {
    PLAIN_CONSTRUCTOR
    return h;
  }
  fn Check(h: Holder) -> bool {
    match h capture() -> (result) {
      Has(pair) => { yield (pair.1); }, Nothing(b) => { yield (b); }
    }
    return result;
  }
  fn Client<C: Cell>(x: (C::Value, bool), b: bool) -> bool {
    return C::get(x, b);
  }
  link Closed = Client<Impl>;
}'''

for alternative, constructor in [
    ("Has", "let pair = ((), b); let h: Holder = Holder::Has(pair);"),
    ("Nothing", "let h: Holder = Holder::Nothing(b);"),
]:
    with case(f"a plain {alternative} helper result joins an owned variant"):
        _, encoded = emit(VARIANT_RESULT_JOIN.replace("PLAIN_CONSTRUCTOR", constructor))
        # The generated exhaustive conversion has a creation operation in Has,
        # even when the helper returns Nothing. Execution tests distinguish the
        # selected alternative's actual requests from this static declaration.
        assert "resource_unit.create" in encoded
        assert "resource_unit.consume" in encoded
