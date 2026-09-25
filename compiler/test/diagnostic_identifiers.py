"""Every compiler diagnostic that source or a carrier can reach, named by its identifier.

A diagnostic's identifier is the stable part of it; the prose after it may change.
Each case here gives the compiler the smallest input that reaches one identifier
and reads that identifier back from where the compiler renders it,
`<location>: error: <identifier>: <message>`. A project that cannot be captured
is not located in any source, and its refusal prints the identifier alone.

Finding the identifier as a substring of what was printed would not be a test.
Identifiers nest (`library-call` is a prefix of `library-call-arity`, and
`library-source-enum` of six others), a diagnostic can quote another identifier
inside its message, and a project's diagnostics print paths that here run
through a directory named after the case.
"""

import copy
import json
import re

from cases import case
from commands import Commands
from tools import compiler, records

root = records()
commands = Commands(root)

LOCATED = re.compile(r": error: ([a-z0-9]+(?:-[a-z0-9]+)*): ")
UNLOCATED = re.compile(r"^([a-z0-9]+(?:-[a-z0-9]+)*)$", re.M)


def identifiers(stderr):
    """The identifiers a refusal names, in the order it names them."""
    return LOCATED.findall(stderr) or UNLOCATED.findall(stderr)


def refused(code, *arguments, stdin=None, cwd=None):
    """Run the compiler and require that the first diagnostic it names is `code`."""
    result = commands.attempt([compiler, *arguments], stdin=stdin, cwd=cwd)
    assert result.returncode > 0, f"{arguments} was accepted"
    assert not result.stdout, f"{arguments} refused and still printed {result.stdout[:200]}"
    named = identifiers(result.stderr)
    assert named[:1] == [code], f"expected {code}, the compiler named {named}:\n{result.stderr}"


def source(code, text, command="protocol-source"):
    refused(code, command, "-", stdin=text)


def project(code, files, *libraries, application="app.pir"):
    """Write a project's files under a directory named for the case and compile it."""
    directory = root / code
    for name, text in files.items():
        path = directory / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    options = [f"--library={directory / name}" for name in libraries]
    refused(code, "protocol-source", directory / application, *options)


def compiled(text):
    """The carrier the compiler emits for an accepted source."""
    return commands.run([compiler, "protocol-source", "-"], stdin=text)


IDENTITY = 'library(namespace="example", name="cells", version="1", resolution="capture-1");'
CELL = "interface Cell { type Value drop; local step(x: Value) -> Value; }"
MARKER = "interface Marker { }"
CLIENT = "fn Client<C: Cell>(x: C::Value) -> C::Value { return C::step(x); }"
EMPTY = "component EmptyCell: Cell { type Value = (); local step(x: Value) -> Value { return x; } }"
BOOL = "component BoolCell: Cell { type Value = bool; local step(x: Value) -> Value { return x; } }"
SCALAR = ("component ScalarCell<F: domain field>: Cell { type Value = field<F>; "
          "local step(x: Value) -> Value { return x; } }")
ENUM = "enum Outcome<C: Cell> { Ready(C::Value), Invalid(bool) }"
BOX = "struct Box { value: bool }"
BOXES = "interface Boxes { type Value copy drop; local pack(x: bool) -> Value; }"
REGION = """fn Client<C: Cell>(value: C::Value, ok: bool) -> bool {
  let result: Outcome<C> = Outcome::Ready(value);
  match result capture(ok) -> (answer) {
    Ready(value) => { let next = C::step(value); yield (ok); },
    Invalid(error) => { yield (error); }
  }
  return answer;
}"""


def library(*declarations):
    """A checked-library module holding these declarations."""
    return " ".join(["module {", IDENTITY, *declarations, "}"])


def region(old, new):
    """The enum-matching client with one edit, beside the declarations it uses."""
    assert old in REGION, old
    return library(CELL, BOOL, ENUM, REGION.replace(old, new))


def dependency(name):
    return f'dependency {name} = library(namespace="test", name="{name}", version="1", resolution="r1");'


def owns(name):
    return f'library(namespace="test", name="{name}", version="1", resolution="r1");'


# Checked-library sources through `protocol-source`, one identifier each.
SOURCES = [
    # A static parameter bounded by two interfaces rather than one.
    ("library-source-parameter",
     library(CELL, "enum Outcome<C: Cell + Cell> { Ready(bool), Invalid(bool) }")),
    # A natural literal wider than 64 bits.
    ("library-source-natural",
     library(CELL, "fn Client<C: Cell>(x: Array<C::Value, 99999999999999999999>) -> bool { return true; }")),
    # A component's natural member without the equation that defines it.
    ("library-source-static",
     library("interface Views { type View drop; nat Width; }",
             "component ViewsImpl: Views { nat Width; type View = bool; }")),
    # A selection alias applied to static arguments.
    ("library-source-selection",
     library(CELL, CLIENT, EMPTY, "select A = EmptyCell;", "link L = Client<A<EmptyCell>>;")),
    # An interface name used where a type is expected.
    ("library-source-type",
     library(CELL, "fn Client<C: Cell>(x: Cell) -> bool { return true; }")),
    # An enum with no alternatives.
    ("library-source-enum", library(CELL, "enum Outcome<C: Cell> { }")),
    # An enum's component parameter given a domain.
    ("library-source-enum-actual",
     library(CELL, ENUM, 'fn Client<C: Cell>(x: Outcome<"koala-bear">) -> bool { return true; }')),
    # An enum type spelled without its static actuals.
    ("library-source-enum-arity",
     library(CELL, ENUM, "fn Client<C: Cell>(x: Outcome) -> bool { return true; }")),
    # A record type spelled with static arguments it does not declare.
    ("library-source-record-generic",
     library(BOX, BOXES, 'component Impl: Boxes { type Value = Box<"koala-bear">; '
                         "local pack(x: bool) -> Value { return x; } }")),
    # An interface function with static parameters of its own.
    ("library-source-member-generic",
     library("interface Cell { type Value drop; local step<N: nat>(x: Value) -> Value; }")),
    # The same effect listed twice.
    ("library-source-effect",
     library("interface Cell { type Value drop; local step(x: Value) -> Value effects (local, local); }")),
    # An installed operation called without the static actuals it requires.
    ("library-source-operation",
     library("interface Cell { type Value copy drop; local step(x: Value) -> Value; }",
             "component ScalarCell<F: domain field>: Cell { type Value = field<F>; "
             "local step(x: Value) -> Value { let y = field::add(x, x); return y; } }")),
    # A helper's static parameter that nothing in the call determines.
    ("library-source-inference",
     library(CELL, "fn Helper<D: Cell>(ok: bool) -> bool { return ok; }",
             "fn Client<C: Cell>(x: C::Value, ok: bool) -> C::Value { let y = Helper(ok); return C::step(x); }")),
    # An empty array literal with no expected type.
    ("library-source-array",
     library(CELL, "fn Client<C: Cell>(x: C::Value) -> C::Value { let v = []; return C::step(x); }")),
    # An enum constructor given attributes.
    ("library-source-enum-constructor",
     region("Outcome::Ready(value);", "Outcome::Ready(value) attributes(1);")),
    # A record literal with more fields than the record declares.
    ("library-source-record",
     library(BOX, BOXES, "component Impl: Boxes { type Value = Box; "
                         "local pack(x: bool) -> Value { return Box { value: x, other: x }; } }")),
    # A checked struct built directly rather than through its constructor.
    ("library-source-record-authority",
     library("checked struct Box(value: bool) constructors(Make);",
             "fn Make(value: bool) -> Box { return Box(value = value); }", BOXES,
             "component Impl: Boxes { type Value = Box; local pack(x: bool) -> Value { return Box { value: x }; } }")),
    # An array length, which checked bodies do not have.
    ("library-source-expression",
     library(CELL, "fn Client<C: Cell>(x: Array<C::Value, 2>) -> index { return x.len(); }")),
    # A tuple pattern over a value that is not a product.
    ("library-source-pattern",
     library(CELL, "fn Client<C: Cell>(x: C::Value) -> C::Value { let (a, b) = C::step(x); return a; }")),
    # A match over a bool rather than an enum value.
    ("library-source-match", region("match result", "match ok")),
    # One arm yields more values than the match binds.
    ("library-source-match-output", region("yield (error);", "yield (error, error);")),
    # Two names bound to a one-value payload.
    ("library-source-match-payload",
     region("Invalid(error) => { yield (error); }", "Invalid(a, b) => { yield (a); }")),
    # A yield in a function body, outside any region.
    ("library-source-yield",
     library(CELL, "fn Client<C: Cell>(x: C::Value) -> C::Value { yield (x); }")),
    # A component function declared without a body.
    ("library-source-body",
     library(CELL, "component EmptyCell: Cell { type Value = (); local step(x: Value) -> Value external; }")),
    # A component whose interface names a component.
    ("library-source-interface",
     library(CELL, "component EmptyCell: EmptyCell { type Value = (); local step(x: Value) -> Value { return x; } }")),
    # A module header naming a convenience profile the compiler does not have;
    # the carrier holds explicit bindings only, so nothing could stand for it.
    ("source-profile", "module standard { fn F(x: bool) -> bool { return x; } }"),
    # A profile module whose map traversal is checked by the library layer.
    ("library-source-profile",
     "module standard { fn F(items: Array<bool, 2>) -> Array<bool, 2> "
     "{ return map items |item| { bool::not(item) }; } }"),
    # An association whose subject is a name rather than a quoted string.
    ("library-source-association", library("association A = B;")),
    # A facet without `required` or `optional`.
    ("library-source-facet", library("interface Cell { type Value drop; facet Value Cell; }")),
    # An interface member introduced by `fn`, which interfaces do not declare.
    ("library-source-member", library("interface Cell { type Value drop; fn step(x: Value) -> Value; }")),
    # An array whose count is a domain rather than a natural.
    ("library-array",
     library(MARKER, 'fn Client<C: Marker>(x: Array<bool, "koala-bear">) -> bool { return true; }')),
    # A field constant other than 0 or 1 over a domain parameter.
    ("library-attribute-bound",
     library(MARKER, "fn Client<C: Marker, F: domain field>(x: bool) -> field<F> "
                     "{ return field::constant::<F>() attributes(2); }")),
    # A member call with more operands than the function declares.
    ("library-call-arity",
     library(CELL, "fn Client<C: Cell>(x: C::Value) -> C::Value { return C::step(x, x); }")),
    # An array literal shorter than its declared type.
    ("library-construct",
     library(MARKER, "fn Client<C: Marker>(a: bool) -> Array<bool, 2> { return [a]; }")),
    # The same facet declared twice.
    ("library-facet",
     library('interface Cell { type Value drop; facet optional "o" "n"; facet optional "o" "n"; }')),
    # A field member equated to a group.
    ("library-interface-equation", library('interface I { domain F: field = "ristretto255.group"; }')),
    # A type member declared twice.
    ("library-interface-member", library("interface Cell { type Value drop; type Value drop; }")),
    # A requirement with no arguments.
    ("library-requirement",
     library(MARKER, "fn Client<C: Marker>(x: bool) -> bool requires (Field()) { return x; }")),
    # A component applied to more static actuals than it declares.
    ("library-static-arity",
     library(CELL, CLIENT, SCALAR, 'link Scalar = Client<ScalarCell<"koala-bear", 2>>;')),
    # A field type over a group domain.
    ("library-type-sort", library("interface I { domain G: group; local f(x: field<G>) -> field<G>; }")),
    # A component that leaves an interface type undefined.
    ("library-representation",
     library("interface Marker { type Value copy drop; }", "component M: Marker { type Other = bool; }")),
    # Two component types defined as each other.
    ("library-representation-cycle",
     library("interface Two { type A copy drop; type B copy drop; }",
             "component M: Two { type A = Self::B; type B = Self::A; }")),
    # A zero-storage representation for an interface type that must not be dropped.
    ("library-resource-profile",
     library("interface Cell { type Value; }", "component Impl: Cell { type Value = (); }",
             "fn Client<C: Cell>(x: bool) -> bool { return x; }", "link Closed = Client<Impl>;")),
    # Two component naturals defined as each other.
    ("library-substitution-cycle",
     library("interface Two { nat A; nat B; }", "component M: Two { nat A = Self::B; nat B = Self::A; }")),
    # A requirement that projects a type member as though it were a static.
    ("library-static-member",
     library("interface Marker { type Value copy drop; }", "component M: Marker { type Value = bool; }",
             'fn Client<C: Marker>(x: C::Value) -> C::Value requires ("="(C::Value, C::Value)) { return x; }',
             "link Closed = Client<M>;")),
]

# A join of a plain public variant input with a variant built from a
# zero-storage value. The program is valid (docs/spec/profiles/source/
# checked-libraries.md, "Representation and execution"): the unit may be dropped
# and the plain arm should create one. Linking still carries the unit back into
# the public input and refuses; docs/status.md records the gap. When linking
# creates the unit on the plain arm, this case becomes an accepted program in
# frontend_zero_storage.py. The linker's other layout checks run after
# adaptation and stop the compiler as defects instead of refusing.
SOURCES += [
    ("library-resource-boundary", library(
        "enum Holder { Has(((), bool)), Nothing(bool) }",
        "interface Cell { type Value drop; "
        "local pick(h: Holder, x: (Value, bool), b: bool) -> Holder; }",
        "component Impl: Cell { type Value = (); "
        "local pick(h: Holder, x: (Value, bool), b: bool) -> Holder { "
        "if b capture(h, x) -> (r) { yield (h); } "
        "else { let g: Holder = Holder::Has(x); yield (g); } return r; } }",
        "fn Client<C: Cell>(h: Holder, x: (C::Value, bool), b: bool) -> Holder "
        "{ return C::pick(h, x, b); }",
        "link Closed = Client<Impl>;")),
]

# Ordinary sources through `protocol-source`, one identifier each.
SOURCES += [
    # A use path that continues past a function.
    ("source-import-path", "module { fn Main(x: bool) -> bool { return x; } use Main::x; }"),
    # A child module declared in a source read from standard input.
    ("source-module-missing", "module { mod child; }"),
    # `super` in a root module.
    ("source-module-parent", "module { use super::X; }"),
    # A private function re-exported as public.
    ("source-private-reexport", "module { fn F(x: bool) -> bool { return x; } pub use F as G; }"),
    # An entry protocol whose dependency names a function.
    ("source-entry-dependency",
     "module { fn F() -> () { return; } protocol P { roles(A); dependencies(c: F()); return; } entry E = P; }"),
    # An entry protocol that takes natural parameters.
    ("source-entry-parameters", "module { protocol P { roles(A); parameters(n); return; } entry E = P; }"),
    # Static arguments given to a protocol that has none.
    ("source-entry-target", "module { protocol P { roles(A); return; } entry E = P::<F=koala-bear>; }"),
    # A concrete domain in a generic protocol's requirement.
    ("source-static-domain", "module { protocol P<F:Field> requires (Field(koala-bear)) { roles(A); return; } }"),
    # An array type with no count.
    ("source-array-count", "module { fn Use(x: Array<bool>) -> () { return (); } }"),
    # An entry naming a function.
    ("source-declaration-kind", "module { fn Helper(x: bool) -> bool { return x; } entry main = Helper; }"),
    # A placement block with no final value.
    ("source-local-result",
     "module { protocol Q { roles (P); inputs (P x: bool); outputs (P bool); local P { let y = x; }; return x; } }"),
    # A tuple pattern over a bool.
    ("source-product-pattern", "module { fn F(x: bool) -> bool { let (a, b) = x; return a; } }"),
    # A protocol loop with an empty body.
    ("source-protocol-body", "module { protocol Q { roles(A); loop 1 carry () -> () { } return; } }"),
    # A protocol that ends without a terminator.
    ("source-protocol-terminator",
     "module { protocol Q { roles (P, V); inputs (P x: bool); outputs (V bool); message m: P(x) -> V(y); } }"),
    # A resource unit whose slot is a type rather than a quoted slot name.
    ("source-resource-unit", "module { fn Use(x: ResourceUnit<bool>) -> () { return (); } }"),
    # A dependency's static argument named for a parameter the callee does not have.
    ("source-static-parameter",
     "module { protocol Child<F:Field> { roles(A); return; } "
     "protocol P<F:Field> { roles(A); dependencies(c: Child::<G=F>()); return; } }"),
    # `pub` on an entry.
    ("source-visibility",
     "module { protocol Q { roles (P); inputs (P x: bool); outputs (P bool); return x; } pub entry main = Q; }"),
]

for code, text in SOURCES:
    with case(code):
        source(code, text)

# One identifier can stand for conditions that are unrelated but for their
# name, so where the cause is opposite or the layer differs, both are named.
with case("library-source-match: more arms than the parser admits"):
    alternatives = ", ".join(f"A{i}(bool)" for i in range(33))
    arms = ", ".join(f"A{i}(x) => {{ yield (x); }}" for i in range(33))
    source("library-source-match",
           library(f"enum Big {{ {alternatives} }}",
                   f"fn Client(v: Big) -> bool {{ match v -> (answer) {{ {arms} }} return answer; }}"),
           command="protocol-parse")

with case("library-source-yield: a return inside a region"):
    source("library-source-yield", region("yield (error);", "return error;"))

with case("source-product-limit"):
    # A product over 4096 leaves, written as a type and built as an expression.
    source("source-product-limit", "module { fn Use(x: (Array<bool, 4096>, bool)) -> () { return (); } }")
    source("source-product-limit",
           "module { fn Use(x: Array<bool, 4096>, y: bool) -> () { let p = (x, y); return (); } }")

with case("source-type-depth"):
    # Aggregate nesting beyond 64, reached only through a struct field: one
    # written type is refused by the parser's own depth bound first.
    nested = "bool"
    for _ in range(63):
        nested = f"({nested},)"
    source("source-type-depth",
           f"module {{ struct A(x: B); struct B(x: {nested}); fn Use(v: A) -> A {{ return v; }} }}")

with case("a check of the lowered library source keeps its identifier"):
    # A linked client whose lowered inputs exceed the ordinary source's bound
    # is refused by that bound, under its own name.
    wide = ", ".join(f"a{i}: Array<bool, 4000>" for i in range(9))
    source("source-limit",
           library(CELL, EMPTY, f"fn Client<C: Cell>({wide}, x: C::Value) -> C::Value {{ return C::step(x); }}",
                   "link Wide = Client<EmptyCell>;"))

# Projects, which are read from files.
with case("project-module-name"):
    # A child module name longer than 128 bytes.
    project("project-module-name", {"app.pir": f"module {{ mod {'a' * 129}; }}"})

with case("project-module-root"):
    # A child module file that holds a construction rather than a module.
    project("project-module-root", {"app.pir": "module { mod child; }", "child.pir": "construction E {}"})

with case("source-dependency-duplicate"):
    # Two dependencies under one alias.
    project("source-dependency-duplicate",
            {"app.pir": f"module {{ {dependency('a')} {dependency('a')} }}", "a.pir": f"module {{ {owns('a')} }}"},
            "a.pir")

with case("source-library-cycle"):
    # Two libraries that depend on each other.
    project("source-library-cycle",
            {"app.pir": f"module {{ {dependency('a')} }}",
             "a.pir": f"module {{ {owns('a')} {dependency('b')} }}",
             "b.pir": f"module {{ {owns('b')} {dependency('a')} }}"},
            "a.pir", "b.pir")

with case("source-library-identity"):
    # A library root that declares no identity.
    project("source-library-identity", {"app.pir": "module {}", "lib.pir": "module {}"}, "lib.pir")

with case("source-project-kind"):
    # A construction as the application of a project that has libraries.
    project("source-project-kind",
            {"app.pir": "construction E { producer p; validator v; random r at (); accept 1; suite s; }",
             "lib.pir": f"module {{ {owns('a')} }}"},
            "lib.pir")

with case("source-name-reserved"):
    # Declarations spelled with the prefixes of the symbols the compiler
    # generates for imported declarations, linked library functions, their
    # client entries and library operation bindings. None of these collides with
    # a generated symbol; the prefix alone refuses it.
    for declaration in ("fn src_f(x: bool) -> bool { return x; }",
                        "fn lib_f(x: bool) -> bool { return x; }",
                        "fn client_f(x: bool) -> bool { return x; }",
                        "bind __library_operation_0 = control::require();"):
        source("source-name-reserved", f"module {{ {declaration} }}")
    # Only the prefix is reserved.
    compiled("module { fn my_src_f(x: bool) -> bool { return x; } }")

with case("source-name-ambiguous"):
    # A root function spelled as the path to a child module's function, called
    # by that spelling unquoted.
    project("source-name-ambiguous",
            {"app.pir": "module { mod inner; fn inner.Keep(x: bool) -> bool origin Chosen() { return x; } "
                        "fn Main(x: bool) -> bool { return inner.Keep(x); } }",
             "inner.pir": "module { pub fn Keep(x: bool) -> bool { return x; } }"})

with case("a lowering refusal keeps its identifier and location"):
    # A generic in a child module whose origin a root function with an explicit
    # origin also claims. Lowering finds the collision; the refusal is its own,
    # located in the child module, not wrapped in another identifier.
    project("source-origin-collision",
            {"app.pir": "module { mod inner; fn inner.Keep(x: bool) -> bool origin Chosen() { return x; } }",
             "inner.pir": "module { fn Keep<F: Field>(x: bool) -> bool { return x; } }"})
    said = commands.attempt([compiler, "protocol-source", root / "source-origin-collision" / "app.pir"])
    assert said.stderr.startswith(f"{root / 'source-origin-collision' / 'inner.pir'}:1:10: error: "), said.stderr

# Carriers the compiler would not emit, made by damaging one it did.
CARRIER = library(
    CELL, BOOL, "enum Outcome<C: Cell> { Ready(C::Value, bool), Invalid(bool) }",
    """fn Client<C: Cell>(value: C::Value, ok: bool) -> bool {
      let result: Outcome<C> = Outcome::Ready(value, ok);
      match result capture() -> (answer) {
        Ready(value, flag) => { let next = C::step(value); yield (flag); },
        Invalid(error) => { yield (error); }
      }
      return answer;
    }""",
    "link Closed = Client<BoolCell>;")


def record(tree, tag):
    """The first carrier record of this kind, as a list that can be edited in place."""
    if isinstance(tree, list):
        if tree and tree[0] == tag:
            return tree
        for child in tree:
            found = record(child, tag)
            if found is not None:
                return found
    return None


def damaged(edit):
    carrier = copy.deepcopy(emitted_carrier)
    edit(carrier)
    return json.dumps(carrier)


emitted_carrier = json.loads(compiled(CARRIER))
# The edits below index a match record as [tag, name, input, captures, arms,
# outputs] and an arm as [alternative, payload, body]; the first arm binds the
# two payload values of `Ready`.
match_record = record(emitted_carrier, "match")
assert match_record is not None and len(match_record[4][0][1]) == 2, match_record

with case("variant-shape"):
    # A variant record with a field missing, read by the source decoder.
    source("variant-shape", damaged(lambda carrier: record(carrier, "variant").pop()))

with case("local-match-shape"):
    # A match record with a field missing, read by the source decoder.
    source("local-match-shape", damaged(lambda carrier: record(carrier, "match").pop()))

with case("local-match-payload"):
    # One arm binding the same name to both payload values, judged at admission.
    def repeat_payload(carrier):
        arm = record(carrier, "match")[4][0]
        arm[1] = [arm[1][0], arm[1][0]]
    source("local-match-payload", damaged(repeat_payload), command="protocol-admit")

with case("local-match-yield"):
    # One arm yielding more ports than the other, judged at admission.
    def widen_yield(carrier):
        arm = record(carrier, "match")[4][0]
        ports = record(arm[2], "yield")
        ports[1] = ports[1] * 2
    source("local-match-yield", damaged(widen_yield), command="protocol-admit")
