"""Library-owned operator coherence and checked-call elaboration."""

import json

from cases import case
from commands import Commands
from source_text import unlocated
from tools import compiler, records


root = records()
commands = Commands(root)


def common(text):
    return json.loads(commands.source("protocol-source", text))


def same(authored, named):
    # Anonymous checked-library identities intentionally hash captured bytes.
    # Fix the package identity when comparing two authored spellings.
    if "interface " in authored and "library(" not in authored:
        declaration = 'module { library(namespace="operators", name="comparison", version="1", resolution="fixed");'
        authored = authored.replace("module {", declaration, 1)
        named = named.replace("module {", declaration, 1)
    result = common(authored)
    assert result == common(named)
    assert result == common(commands.source("protocol-format", authored))
    return result


RECORD = """module {
  struct Number(value: index);
  #[operator(add)]
  fn Add(a: Number, b: Number) -> Number { return a; }
  fn Main(a: Number, b: Number) -> Number { return a + b; }
}"""

with case("attribute roundtrip and inspection"):
    parsed = json.loads(commands.source("protocol-parse", RECORD))["content"]
    assert parsed["functions"][0]["operator"] == "add"
    formatted = commands.source("protocol-format", RECORD)
    assert "#[operator(add)]\n" in formatted
    assert unlocated(parsed) == unlocated(
        json.loads(commands.source("protocol-parse", formatted))["content"]
    )

with case("record addition retains the ordinary function and call"):
    emitted = same(RECORD, RECORD.replace("return a + b", "return Add(a, b)"))
    assert '"Add"' in json.dumps(emitted)
    main = next(f for f in emitted[2] if f[1] == "Main")
    assert main[4][0][0] == "apply" and main[4][0][2] == "Add"

for hook, symbol, unary in [("sub", "-", False), ("mul", "*", False), ("neg", "-", True)]:
    with case(f"record {hook} selects its checked function"):
        text = RECORD.replace("operator(add)", f"operator({hook})")
        expression = "-a" if unary else f"a {symbol} b"
        if unary:
            text = text.replace("fn Add(a: Number, b: Number)", "fn Add(a: Number)")
        text = text.replace("a + b", expression)
        same(text, text.replace(f"return {expression}", "return Add(a)" if unary else "return Add(a, b)"))

with case("nested records are selected before flattening"):
    text = RECORD.replace("return a + b", "return (a + b) + (b + a)")
    same(text, text.replace("(a + b) + (b + a)", "Add(Add(a, b), Add(b, a))"))

with case("flat let operator path preserves nominal heads"):
    text = RECORD.replace("return a + b;", "let c = a + b; return c;")
    same(text, text.replace("a + b", "Add(a, b)"))

with case("generic record arguments use ordinary inference after head lookup"):
    text = """module {
      use zkc::algebra;
      use zkc::algebra::Field;
      struct Number<F: domain Field>(value: F::Element);
      #[operator(add)] fn Add<F: Field>(a: Number<F>, b: Number<F>)
          -> Number<F> { return a; }
      fn Main<F: Field>(a: Number<F>, b: Number<F>) -> Number<F> {
        return a + b;
      }
    }"""
    same(text, text.replace("a + b", "Add(a, b)"))

with case("mixed record and logical heads use checked generic arguments"):
    text = """module {
      use zkc::algebra;
      use zkc::algebra::Field;
      struct Number<F: domain Field>(value: F::Element);
      #[operator(mul)] fn Scale<F: Field>(a: Number<F>, b: F::Element)
          -> Number<F> { return a; }
      fn Main<F: Field>(a: Number<F>, b: F::Element) -> Number<F> {
        return a * b;
      }
    }"""
    same(text, text.replace("a * b", "Scale(a, b)"))

with case("selected source operator still checks exact static arguments"):
    text = """module {
      use zkc::algebra;
      use zkc::algebra::Field;
      struct Number<F: domain Field>(value: F::Element);
      #[operator(add)] fn Add<F: Field>(a: Number<F>, b: Number<F>)
          -> Number<F> { return a; }
      fn Main<A: Field, B: Field>(a: Number<A>, b: Number<B>)
          -> Number<A> { return a + b; }
    }"""
    commands.source("protocol-source", text, refuses="source-static-conflict")

with case("selected source operator keeps its public requirements"):
    text = """module {
      use zkc::algebra;
      use zkc::algebra::{Field, PrimeField};
      struct Number<F: domain Field>(value: F::Element);
      #[operator(add)] fn Add<F: PrimeField>(a: Number<F>, b: Number<F>)
          -> Number<F> { return a; }
      fn Main<F: Field>(a: Number<F>, b: Number<F>) -> Number<F> {
        return a + b;
      }
    }"""
    commands.source("protocol-source", text, refuses="generic-public-requirement")

with case("selected source operator keeps affine operand use"):
    text = """module {
      use zkc::algebra;
      use zkc::algebra::Field;
      use zkc::random;
      struct Number<F: domain Field>(value: random::Rng<F>);
      #[operator(neg)] fn Negate<F: Field>(a: Number<F>) -> Number<F> { return a; }
      fn Main<F: Field>(a: Number<F>) -> Number<F> {
        let b = -a; return -a;
      }
    }"""
    commands.source("protocol-source", text, refuses="generic-resource-reuse")

with case("zero-leaf records still have nominal operator heads"):
    text = RECORD.replace("struct Number(value: index);", "struct Number(value: ());")
    same(text, text.replace("a + b", "Add(a, b)"))

with case("a structurally equal record does not acquire another head's hook"):
    text = RECORD.replace("fn Main", "struct Other(value: index); fn Main")
    text = text.replace("fn Main(a: Number, b: Number) -> Number", "fn Main(a: Other, b: Other) -> Other")
    commands.source("protocol-source", text, refuses="source-operator-unresolved")

for change, code in [
    (("operator(add)", "operator(div)"), "source-operator-attribute"),
    (("#[operator(add)]", "#[operator(add)] #[operator(add)]"), "source-operator-attribute"),
    (("struct Number", "#[operator(add)] struct Number"), "source-operator-attribute"),
    (("fn Add(a: Number, b: Number)", "fn Add(a: Number)"), "source-operator-arity"),
    (("fn Add(a: Number, b: Number) -> Number { return a; }", "fn Add(a: Number, b: Number) -> () { return (); }"), "source-operator-result"),
    (("fn Add(a: Number, b: Number) -> Number { return a; }", "fn Add(a: Number, b: Number) -> (Number, Number) { return (a, b); }"), "source-operator-result"),
    (("fn Add(a: Number, b: Number) -> Number { return a; }", "fn Add(a: Number, b: Number) -> Number external;"), "source-operator-body"),
    (("fn Add(a: Number, b: Number)", "fn Add(a: index, b: index)"), "source-operator-ownership"),
    (("fn Main", "#[operator(add)] fn Other(a: Number, b: Number) -> Number { return b; } fn Main"), "source-operator-duplicate"),
    (("fn Add(a: Number, b: Number)", "fn Add(a: Number, b: (index, index))"), "source-operator-head"),
]:
    with case(f"reject {code}: {change[1]}"):
        commands.source("protocol-source", RECORD.replace(*change), refuses=code)

with case("different static instantiations do not create disjoint overloads"):
    text = """module {
      struct Number<F: domain Field>(value: F::Element);
      #[operator(add)] fn First(a: Number<"koala-bear">, b: Number<"koala-bear">)
          -> Number<"koala-bear"> { return a; }
      #[operator(add)] fn Second(a: Number<"bls12-381.fr">, b: Number<"bls12-381.fr">)
          -> Number<"bls12-381.fr"> { return a; }
    }"""
    commands.source("protocol-source", text, refuses="source-operator-duplicate")

with case("return types cannot disambiguate duplicate operand heads"):
    text = RECORD.replace("fn Main", "#[operator(add)] fn Other(a: Number, b: Number) -> index { return a.value; } fn Main")
    commands.source("protocol-source", text, refuses="source-operator-duplicate")

INTRINSIC = """module {
  use zkc::algebra;
  use zkc::algebra::Field;
  use zkc::curve;
  use zkc::curve::ScalarAction;
  fn Main<F: Field>(a: F::Element, b: F::Element) -> F::Element {
    return a + b * -a;
  }
}"""

with case("intrinsic sugar has the named operation identity"):
    same(INTRINSIC, INTRINSIC.replace("a + b * -a", "algebra::add(a, algebra::mul(b, algebra::neg(a)))"))

with case("installed operators require imported authority"):
    text = 'module { fn Main(a: "koala-bear"::Element, b: "koala-bear"::Element) -> "koala-bear"::Element { return a + b; } }'
    commands.source("protocol-source", text, refuses="source-operator-unresolved")

with case("vector multiplication remains unresolved"):
    text = INTRINSIC.replace("F::Element", "algebra::Vector<F::Element>").replace("a + b * -a", "a * b")
    commands.source("protocol-source", text, refuses="source-operator-unresolved")

with case("scalar group permutation keeps nested evaluation order"):
    text = """module {
      use zkc::algebra;
      use zkc::algebra::Field;
      use zkc::curve;
      use zkc::curve::ScalarAction;
      fn Main<G: ScalarAction>(p: G::Element, q: G::Element,
          a: G::Scalar::Element, b: G::Scalar::Element) -> G::Element
          requires (Field(G::Scalar)) {
        return (a * b) * (p + q);
      }
    }"""
    expanded = text.replace("(a * b) * (p + q)", "curve::scale(field: algebra::mul(a, b), group: curve::add(p, q))")
    emitted = same(text, expanded)
    operations = [i for i in emitted[1][0][-1] if i[0] == "op"]
    assert [op[2] for op in operations] == ["field.mul", "curve.add", "curve.scale"]
    assert operations[2][5] == [operations[1][6][0], operations[0][6][0]]

COMPONENT = """module {
  struct Number(value: index);
  #[operator(add)] fn Add(a: Number, b: Number) -> Number { return a; }
  interface Cell { type Value copy drop; local add(a: Value, b: Value) -> Value; }
  component Numbers: Cell {
    type Value = Number;
    local add(a: Number, b: Number) -> Number { return a + b; }
  }
  fn Client<C: Cell>(a: C::Value, b: C::Value) -> C::Value { return C::add(a, b); }
  link Closed = Client<Numbers>;
}"""

with case("component body shares record operator lookup"):
    same(COMPONENT, COMPONENT.replace("return a + b", "return Add(a, b)"))

with case("checked helpers retain bindings for ordinary callers"):
    text = COMPONENT[:-1] + "fn Ordinary(a: Number, b: Number) -> Number { return a + b; } }"
    same(text, text.replace("return a + b", "return Add(a, b)"))

# These hooks use the checked library's supported record schema. Generic
# records are independently refused there, so they cannot establish routing
# equality. The all-record hook infers F from the call's result only *after*
# selecting Add by its two record heads.
CHECKED_RECORD = """module {
  library(namespace="operators", name="checked", version="1", resolution="fixed");
  use zkc::algebra;
  use zkc::algebra::{Field, PrimeField};
  struct Number(value: index);
  #[operator(add)]
  fn Add<F: domain Field>(a: Number, b: Number) -> F::Element
      requires (Field(F)) effects (local) {
    let ignored = map [true] |item| { item };
    return algebra::from_index::<F>(a.value);
  }
  fn Main<F: domain Field>(a: Number, b: Number) -> F::Element
      requires (Field(F)) effects (local) { return a + b; }
  configure Closed = Main(F = "koala-bear");
}"""
CHECKED_MIXED = (CHECKED_RECORD.replace("operator(add)", "operator(mul)")
                 .replace("Add", "Scale").replace("b: Number", "b: F::Element")
                 .replace("a + b", "a * b")
                 .replace("algebra::from_index::<F>(a.value)", "b"))

for heads, base, expression, named in [
    ("record", CHECKED_RECORD, "a + b", "Add(a, b)"),
    ("mixed", CHECKED_MIXED, "a * b", "Scale(a, b)"),
]:
    for traversal in ["map [true] |item| { item }",
                      "fold [true] with false |state, item| { item }"]:
        with case(f"generic checked {heads} hook with {traversal.split()[0]}"):
            text = base.replace("map [true] |item| { item }", traversal)
            emitted = same(text, text.replace(expression, named))
            assert any(f[1] == "Closed" for f in emitted[2])

    with case(f"generic checked {heads} hook reaches transitive ordinary callers"):
        signature = ("(a: Number, b: " + ("Number" if heads == "record" else "F::Element")
                     + ") -> F::Element requires (Field(F)) effects (local)")
        # Reverse the dependency order to require closure, not source order.
        outer = (f"fn Outer<F: domain Field>{signature} {{ return Middle(a, b); }}\n"
                 f"fn Middle<F: domain Field>{signature} {{ return Main(a, b); }}\n")
        text = base.replace("  fn Main", outer + "  fn Main").replace("= Main(F", "= Outer(F")
        same(text, text.replace(expression, named))

    signature = ('(a: Number, b: ' + ('Number' if heads == 'record' else '"koala-bear"::Element')
                 + ') -> "koala-bear"::Element effects (local)')
    component = base[:base.index("  fn Main")] + f"""
          interface Cell {{ local run{signature}; }}
          component Numbers: Cell {{ local run{signature} {{ return {expression}; }} }}
          fn Client<C: Cell>{signature} {{ return C::run(a, b); }}
          link Closed = Client<Numbers>;
        }}"""
    with case(f"generic checked {heads} hook in component body"):
        same(component, component.replace(expression, named))

    with case(f"component-discovered generic {heads} hook reaches ordinary users"):
        text = component.replace("    let ignored = map [true] |item| { item };", "")
        ordinary = base[base.index("  fn Main"):].replace("Closed", "OrdinaryClosed")
        text = text.rstrip()[:-1] + ordinary
        same(text, text.replace(expression, named))

    with case(f"generic checked {heads} hook retains unused registration"):
        text = base[:base.index("  fn Main")] + "}"
        common(text)

    with case(f"generic checked {heads} hook keeps required predicates"):
        text = base.replace("requires (Field(F))", "requires (PrimeField(F))", 1)
        for spelling in [text, text.replace(expression, named)]:
            commands.source("protocol-source", spelling, refuses="library-bound")
        accepted = text.replace("requires (Field(F))", "requires (PrimeField(F))")
        same(accepted, accepted.replace(expression, named))

with case("operator discovery leaves unrelated ordinary functions on their checker"):
    text = CHECKED_RECORD[:-1] + """
      fn Ordinary<F: Field>(a: F::Element, b: F::Element) -> F::Element {
        return a + b;
      }
      struct Other(value: index);
      #[operator(add)] fn OtherAdd(a: Other, b: Other) -> Other { return b; }
      fn OtherUser(a: Other, b: Other) -> Other { return a + b; }
    }"""
    named = text.replace("return a + b;", "return Add(a, b);", 1)
    emitted = same(text, named)
    assert any(f[1] == "Ordinary" for f in emitted[1])
    assert any(f[1] == "OtherUser" for f in emitted[3][2])
    report = json.loads(commands.source("protocol-analyze", text))
    assert report["state"] == "source_checked"
    assert {c["name"] for c in report["checked_libraries"]["clients"]} == {"Add", "Main"}
    identities = {d["symbol"]: d["identity_key"] for d in report["resolved_declarations"]}
    assert not any(d["source"] == identities["Main"] and d["target"] == identities["Add"]
                   for d in report["dependencies"])

CHECKED_AFFINE = """module {
  library(namespace="operators", name="checked", version="1", resolution="fixed");
  use zkc::algebra::Field;
  use zkc::random;
  struct Token(value: random::Rng<"bls12-381.fr">);
  #[operator(mul)]
  fn Scale<F: domain Field>(a: Token, b: F::Element) -> Token effects (local) {
    let ignored = map [true] |item| { item };
    return a;
  }
  fn Main<F: domain Field>(a: Token, b: F::Element) -> Token effects (local) {
    return a * b;
  }
  configure Closed = Main(F = "koala-bear");
}"""

with case("generic checked operator consumes an affine operand exactly once"):
    same(CHECKED_AFFINE, CHECKED_AFFINE.replace("a * b", "Scale(a, b)"))

with case("generic checked operator refuses affine operand reuse like its named call"):
    text = CHECKED_AFFINE.replace("return a * b;", "let c = a * b; return a * b;")
    for spelling in [text, text.replace("a * b", "Scale(a, b)")]:
        commands.source("protocol-source", spelling, refuses="library-resource-use")

with case("generic checked operator does not infer a static argument from head lookup"):
    text = CHECKED_RECORD.replace("-> F::Element", "-> Number")
    text = text.replace("algebra::from_index::<F>(a.value)", "a")
    for spelling in [text, text.replace("a + b", "Add(a, b)")]:
        commands.source("protocol-source", spelling, refuses="library-source-inference")

with case("generic checked operator still checks conflicting static constraints"):
    text = CHECKED_MIXED.replace("fn Main<F: domain Field>",
                                "fn Main<F: domain Field, G: domain Field>")
    start = text.index("  fn Main")
    text = text[:start] + text[start:].replace("-> F::Element", "-> G::Element")
    text = text.replace('Main(F = "koala-bear")',
                        'Main(F = "koala-bear", G = "bls12-381.fr")')
    for spelling in [text, text.replace("a * b", "Scale(a, b)")]:
        commands.source("protocol-source", spelling, refuses="library-source-inference")

with case("checked generic hook discovered through another checked helper"):
    start = CHECKED_RECORD.index("  #[operator(add)]")
    end = CHECKED_RECORD.index("  fn Main")
    helper = CHECKED_RECORD[start:end].replace("  #[operator(add)]\n", "").replace("fn Add", "fn Traverse")
    hook = """#[operator(add)]
      fn Add<F: domain Field>(a: Number, b: Number) -> F::Element
          requires (Field(F)) effects (local) { return Traverse(a, b); }
    """
    text = CHECKED_RECORD[:start] + helper + hook + CHECKED_RECORD[end:]
    same(text, text.replace("a + b", "Add(a, b)"))

with case("checked hooks cannot use result types to disambiguate duplicate heads"):
    text = CHECKED_RECORD[:-1] + """
      #[operator(add)] fn OtherAdd(a: Number, b: Number) -> Number { return a; }
    }"""
    for spelling in [text, text.replace("a + b", "Add(a, b)")]:
        commands.source("protocol-source", spelling, refuses="source-operator-duplicate")

with case("generic checked record schemas keep the existing named-call refusal"):
    text = CHECKED_MIXED.replace("struct Number(value: index)",
                                "struct Number<F: domain Field>(value: F::Element)")
    text = text.replace("a: Number", "a: Number<F>")
    for spelling in [text, text.replace("a * b", "Scale(a, b)")]:
        commands.source("protocol-source", spelling, refuses="library-source-record-generic")


with case("opaque associated operands cannot select an operator"):
    text = COMPONENT.replace("return C::add(a, b)", "return a + b")
    commands.source("protocol-source", text, refuses="source-operator-unresolved")

with case("a registration cannot use an opaque associated operand head"):
    text = COMPONENT.replace("fn Add(a: Number, b: Number)", "fn Add<C: Cell>(a: Number, b: C::Value)")
    commands.source("protocol-source", text, refuses="source-operator-head")

with case("component intrinsic operators retain named identity"):
    text = """module {
      use zkc::algebra;
  use zkc::algebra::{Field, PrimeField};
      interface Cell { type Value copy drop;
        local add(a: Value, b: Value) -> Value effects (local); }
      component Numbers: Cell {
        type Value = index;
        local add(a: index, b: index) -> index effects (local) { let c = a + b; return c; }
      }
      fn Client<C: Cell>(a: C::Value, b: C::Value) -> C::Value effects (local) { return C::add(a, b); }
      link Closed = Client<Numbers>;
    }"""
    same(text, text.replace("a + b", "algebra::index_add(a, b)"))
    commands.source("protocol-source", text.replace(" effects (local)", ""), refuses="library-effect")

with case("component field operators infer static arguments from operands"):
    text = """module {
      use zkc::algebra;
  use zkc::algebra::{Field, PrimeField};
      interface Cell { type Value copy drop;
        local add(a: Value, b: Value) -> Value effects (local); }
      component Numbers: Cell {
        type Value = "koala-bear"::Element;
        local add(a: "koala-bear"::Element, b: "koala-bear"::Element)
            -> "koala-bear"::Element effects (local) { return a + b; }
      }
      fn Client<C: Cell>(a: C::Value, b: C::Value) -> C::Value effects (local) { return C::add(a, b); }
      link Closed = Client<Numbers>;
    }"""
    same(text, text.replace("a + b", 'algebra::add::<"koala-bear">(a, b)'))

with case("component scalar group permutation preserves identity and evaluation"):
    signature = '(a: "bls12-381.fr"::Element, p: "bls12-381.g1"::Element) -> "bls12-381.g1"::Element effects (local)'
    text = f'''module {{
      use zkc::algebra; use zkc::curve;
      interface Scale {{ local run{signature}; }}
      component Scaling: Scale {{ local run{signature} {{ return (a * a) * (p + p); }} }}
      fn Client<C: Scale>{signature} {{ return C::run(a, p); }}
      link Closed = Client<Scaling>;
    }}'''
    named = text.replace('(a * a) * (p + p)', 'curve::scale::<"bls12-381.g1">(field: algebra::mul::<"bls12-381.fr">(a, a), group: curve::add::<"bls12-381.g1">(p, p))')
    same(text, named)


def identity(name):
    return f'library(namespace="operators", name="{name}", version="1", resolution="r1")'


def project(source, libraries, refuses=None, command="protocol-source"):
    app = root / "app.pir"
    app.write_text(source)
    paths = []
    for name, text in libraries.items():
        path = root / name if name.endswith(".pir") else root / name / "lib.pir"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        if path.name == "lib.pir":
            paths.append(f"--library={path}")
    return commands.run([compiler, command, app, *paths], refuses=refuses)


LIBRARY = f'''module {{ {identity("numbers")};
  pub struct Number(value: index);
  #[operator(add)] pub fn Add(a: Number, b: Number) -> Number {{ return a; }}
}}'''
APP = f'''module {{ dependency n = {identity("numbers")};
  use n::{{Number as Alias, Add}};
  fn Main(a: Alias, b: Alias) -> Alias {{ return a + b; }}
}}'''

with case("imported record aliases preserve the defining operator identity"):
    assert project(APP, {"numbers": LIBRARY}) == project(APP.replace("a + b", "Add(a, b)"), {"numbers": LIBRARY})

with case("an imported alias grants no operator ownership"):
    text = APP.replace("fn Main", "#[operator(add)] fn Foreign(a: Alias, b: Alias) -> Alias { return b; } fn Main")
    project(text, {"numbers": LIBRARY}, "source-operator-ownership")

with case("a foreign private function does not export an operator"):
    text = APP.replace("Number as Alias, Add", "Number as Alias")
    private = LIBRARY.replace("#[operator(add)] pub fn", "#[operator(add)] fn")
    project(text, {"numbers": private}, "source-operator-unresolved")

with case("a public operator follows its dependency's exported scope"):
    text = APP.replace("Number as Alias, Add", "Number as Alias")
    assert project(text, {"numbers": LIBRARY}) == project(APP, {"numbers": LIBRARY})

with case("same spelling in another package is a distinct nominal head"):
    other = LIBRARY.replace(identity("numbers"), identity("other"))
    text = APP.replace("use n::", f'dependency other = {identity("other")}; use other::Number as Other; use n::')
    project(text, {"numbers": LIBRARY, "other": other})

with case("a private module's public function needs an exported path"):
    facade = f'module {{ {identity("numbers")}; mod inner; pub use inner::Number; }}'
    inner = LIBRARY.replace(identity("numbers") + ";", "")
    text = APP.replace("Number as Alias, Add", "Number as Alias")
    project(text, {"numbers": facade, "numbers/inner.pir": inner}, "source-operator-unresolved")
    reexport = facade.replace("inner::Number", "inner::{Number, Add}")
    assert project(text, {"numbers": reexport, "numbers/inner.pir": inner}) == project(APP, {"numbers": reexport, "numbers/inner.pir": inner})

with case("duplicate hooks in linked child modules reject even without uses"):
    text = "module { struct Number(value: index); mod left; mod right; }"
    child = """module { use super::Number;
      #[operator(add)] fn Add(a: Number, b: Number) -> Number { return a; }
    }"""
    project(text, {"left.pir": child, "right.pir": child}, "source-operator-duplicate")


# Installed authority is per file and per exporting module, even for intrinsic
# index types. Source hooks follow callable visibility in the owning package or
# a direct dependency's exports, without importing the hook's spelling.
INDEX = "fn Sum(a: index, b: index) -> index { return a + b; }"
with case("index arithmetic has no implicit installed import"):
    commands.source("protocol-source", f"module {{ {INDEX} }}",
                    refuses="source-operator-unresolved")
    common(f"module {{ use zkc::algebra::Indices; {INDEX} }}")
    common(f"module {{ use zkc::algebra::index_sub; {INDEX} }}")
    common(f"module {{ fn Ref(a: index) -> index {{ return zkc::algebra::index_add(a, a); }} {INDEX} }}")

with case("installed authority does not flow from parent or sibling files"):
    text = "module { use zkc::algebra; mod left; mod right; }"
    left = f"module {{ use zkc::algebra; {INDEX} }}"
    right = f"module {{ {INDEX} }}"
    project(text, {"left.pir": left, "right.pir": right}, "source-operator-unresolved")
    project(text, {"left.pir": left, "right.pir": right.replace("module {", "module { use zkc::algebra::Indices;")})

with case("public source hook discovery crosses sibling files without imports"):
    text = "module { mod numbers; mod consumer; }"
    numbers = LIBRARY.replace(identity("numbers") + ";", "")
    consumer = """module {
      fn Main(a: super::numbers::Number, b: super::numbers::Number)
          -> super::numbers::Number { return a + b; }
    }"""
    project(text, {"numbers.pir": numbers, "consumer.pir": consumer})
    project(text, {"numbers.pir": numbers.replace("pub fn Add", "fn Add"),
                   "consumer.pir": consumer}, "source-operator-unresolved")

with case("a private hook stays visible to descendants of its declaring module"):
    text = RECORD.replace("fn Main(a:", "mod child; fn Main(a:")
    child = "module { use super::Number; fn Child(a: Number, b: Number) -> Number { return a + b; } }"
    project(text, {"child.pir": child})

with case("same-package public reexport exposes a hook through a private module"):
    # Stable package identity permits a whole-output comparison after editing
    # the spelling in a child file; anonymous identities hash captured bytes.
    text = f"module {{ {identity('publicalias')}; mod outer; mod consumer; }}"
    outer = "module { mod hidden; pub use hidden::{Number, Add}; }"
    hidden = LIBRARY.replace(identity("numbers") + ";", "")
    consumer = "module { use super::outer::Number; fn Main(a: Number, b: Number) -> Number { return a + b; } }"
    exposed = {"outer.pir": outer, "outer/hidden.pir": hidden, "consumer.pir": consumer}
    named = dict(exposed, **{"consumer.pir": consumer.replace("a + b", "super::outer::Add(a, b)")})
    assert project(text, exposed) == project(text, named)
    project(text, {"outer.pir": outer.replace("{Number, Add}", "Number"),
                   "outer/hidden.pir": hidden, "consumer.pir": consumer}, "source-operator-unresolved")

with case("private module scope permits hooks only inside its subtree"):
    text = "module { mod outer; }"
    outer = "module { mod hidden; mod consumer; }"
    hidden = LIBRARY.replace(identity("numbers") + ";", "")
    consumer = "module { use super::hidden::Number; fn Main(a: Number, b: Number) -> Number { return a + b; } }"
    project(text, {"outer.pir": outer, "outer/hidden.pir": hidden, "outer/consumer.pir": consumer})

with case("source function calls confer no installed operator authority"):
    library = f"module {{ {identity('numbers')}; pub fn Id(a: index) -> index {{ return a; }} }}"
    text = f"module {{ dependency n = {identity('numbers')}; fn Main(a: index) -> index {{ return n::Id(a) + a; }} }}"
    project(text, {"numbers": library}, "source-operator-unresolved")
    project(text.replace("module {", "module { use zkc::algebra::Indices;", 1), {"numbers": library})

with case("indirect dependency hooks require an exposed reexport"):
    middle = f"module {{ {identity('middle')}; dependency n = {identity('numbers')}; pub use n::Number; }}"
    text = f"module {{ dependency middle = {identity('middle')}; use middle::Number; fn Main(a: Number, b: Number) -> Number {{ return a + b; }} }}"
    project(text, {"middle": middle, "numbers": LIBRARY}, "source-operator-unresolved")
    project(text, {"middle": middle.replace("n::Number", "n::{Number, Add}"), "numbers": LIBRARY})

with case("private operator visibility does not spend the authored name budget"):
    # This valid project used to exhaust name resolution during the internal
    # per-module, per-hook lookup. None of these modules uses an operator.
    text = "module { " + " ".join(f"mod child{i};" for i in range(64)) + " }"
    child = "module { " + " ".join(
        f"struct R{j}(value: index); "
        f"#[operator(add)] fn Add{j}(a: R{j}, b: R{j}) -> R{j} {{ return a; }}"
        for j in range(16)) + " }"
    project(text, {f"child{i}.pir": child for i in range(64)})


def recovered(text, unavailable, checked, libraries=None):
    report = json.loads(project(text, libraries or {}, command="protocol-analyze"))
    assert report["state"] == "incomplete", report
    assert [d["code"] for d in report["diagnostics"]] == ["source-name-unresolved"], report["diagnostics"]
    lost = {d["display_name"] for d in report["resolved_declarations"]
            if d["resolution"] == "unavailable"}
    assert lost == set(unavailable), lost
    functions = {d["display_name"]: d for d in report["declarations"] if d["kind"] == "function"}
    for name in checked:
        assert functions[name]["body_state"] == "source_checked", functions[name]
    for name in unavailable:
        if name in functions:
            assert functions[name]["body_state"] == "deferred", functions[name]
    return report


RECOVERY = """module {
  use zkc::algebra;
  struct R(value: index);
  struct S(value: index);
  #[operator(add)] fn Broken(a: R, b: R) -> Missing { return a; }
  #[operator(add)] fn Valid(a: S, b: S) -> S { return a; }
  fn User(a: R, b: R) -> R { return a + b; }
  fn Caller(a: R, b: R) -> R { return User(a, b); }
  fn Unrelated(unused: R, a: S, b: S) -> S { return a + b; }
  fn Indices(a: index, b: index) -> index { return a + b; }
  fn Independent(a: bool) -> bool { return a; }
}"""
SURVIVORS = {"Valid", "Unrelated", "Indices", "Independent"}
for label, expression in (
    ("direct expression", "return a + b;"),
    ("flat call", "let c = a + b; return c;"),
    ("local alias", "let c = a; return c + b;"),
    ("annotation", "let c: R = a; return c + b;"),
):
    with case(f"recovery records exact operator dependencies: {label}"):
        text = RECOVERY.replace("fn User(a: R, b: R) -> R { return a + b; }",
                                f"fn User(a: R, b: R) -> R {{ {expression} }}")
        recovered(text, {"Broken", "User", "Caller"}, SURVIVORS)

with case("recovery follows a hook whose body references an unavailable helper"):
    text = RECOVERY.replace("-> Missing { return a; }", "-> R { return Helper(a); }")
    text = text.replace("struct R(value: index);", "struct R(value: index); fn Helper(a: R) -> Missing { return a; }")
    recovered(text, {"Helper", "Broken", "User", "Caller"}, SURVIVORS)

with case("recovery follows operands returned by ordinary functions"):
    text = RECOVERY.replace("return a + b; }\n  fn Caller", "return Identity(a) + b; }\n  fn Caller")
    text = text.replace("struct R(value: index);", "struct R(value: index); fn Identity(a: R) -> R { return a; }")
    recovered(text, {"Broken", "User", "Caller"}, SURVIVORS | {"Identity"})

with case("recovery preserves nominal heads through record projection"):
    text = RECOVERY.replace("struct R(value: index);", "struct R(value: index); struct Wrapper(value: R);")
    text = text.replace("return a + b; }\n  fn Caller", "let c = Wrapper(value=a); return c.value + b; }\n  fn Caller")
    recovered(text, {"Broken", "User", "Caller"}, SURVIVORS)

with case("recovery selects mixed record and generic logical operand heads"):
    text = """module {
      use zkc::algebra::Field;
      struct R<F: domain Field>(value: F::Element);
      #[operator(mul)] fn Broken<F: Field>(a: R<F>, b: F::Element)
          -> Missing { return a; }
      fn User<F: Field>(a: R<F>, b: F::Element) -> R<F> { return a * b; }
      fn Independent(a: bool) -> bool { return a; }
    }"""
    recovered(text, {"Broken", "User"}, {"Independent"})

with case("unary and binary hooks have distinct recovery keys"):
    text = RECOVERY.replace("operator(add)", "operator(sub)").replace("a + b", "a - b")
    text = text.replace("fn Independent", "#[operator(neg)] fn Neg(a: R) -> R { return a; } fn Unary(a: R) -> R { return -a; } fn Independent")
    recovered(text, {"Broken", "User", "Caller"}, SURVIVORS | {"Neg", "Unary"})

with case("unknown hook operand heads never become recovery wildcards"):
    text = RECOVERY.replace("fn Broken(a: R, b: R) -> Missing", "fn Broken(a: R, b: Missing) -> R")
    text = text.replace("fn User(a: R, b: R) -> R { return a + b; }", "")
    text = text.replace("fn Caller(a: R, b: R) -> R { return User(a, b); }", "")
    recovered(text, {"Broken"}, SURVIVORS)

with case("component operator users participate in transitive recovery"):
    text = COMPONENT.replace("fn Add(a: Number, b: Number) -> Number", "fn Add(a: Number, b: Number) -> Missing")
    text = text.replace("link Closed = Client<Numbers>;", "link Closed = Client<Numbers>; fn Independent(a: bool) -> bool { return a; }")
    report = json.loads(project(text, {}, command="protocol-analyze"))
    assert [d["code"] for d in report["diagnostics"]] == ["source-name-unresolved"], report["diagnostics"]
    assert {d["display_name"] for d in report["resolved_declarations"]
            if d["resolution"] == "unavailable"} == {"Add", "Numbers", "Closed"}
    independent = next(d for d in report["declarations"] if d["display_name"] == "Independent")
    assert independent["body_state"] == "source_checked", independent

with case("unavailable invisible hook does not suppress a real missing operator"):
    text = "module { mod hidden; mod consumer; }"
    hidden = """module { pub struct R(value: index);
      #[operator(add)] fn Broken(a: R, b: R) -> Missing { return a; }
    }"""
    consumer = "module { use super::hidden::R; fn User(a: R, b: R) -> R { return a + b; } }"
    report = json.loads(project(text, {"hidden.pir": hidden, "consumer.pir": consumer}, command="protocol-analyze"))
    assert [d["code"] for d in report["diagnostics"]] == ["source-name-unresolved", "source-operator-unresolved"]
    assert {d["display_name"] for d in report["resolved_declarations"]
            if d["resolution"] == "unavailable"} == {"hidden::Broken"}

print(f"source operators: {commands.save()} checks")
