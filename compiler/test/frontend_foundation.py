"""Source products, lexical placement, and distributed protocol interfaces."""
import json

from cases import case
from commands import Commands
from tools import records

commands = Commands(records())


def run(mode, text, refuses=None):
    return commands.source(mode, text, refuses=refuses)


def source(text):
    return json.loads(run("protocol-source", text))


def stable(text):
    common = source(text)
    formatted = run("protocol-format", text)
    assert source(formatted) == common
    assert run("protocol-format", formatted) == formatted
    run("protocol-import", text)
    return common


PRODUCTS = '''module {
  struct Pair<F: domain Field> { left: F::Element, right: F::Element }
  fn PairUp<F: Field>(x: F::Element, y: F::Element) -> (F::Element, F::Element) {
    (x, y)
  }
  fn First<F: Field>(p: (F::Element, F::Element)) -> F::Element { p.0 }
  fn Test<F: Field>(x: F::Element, y: F::Element) -> F::Element {
    let p = PairUp(y: y, x: x);
    let (a, b) = PairUp(x, y);
    let record = Pair { right: b, left: a };
    let nested = (record, (), p);
    let answer = First(nested.2);
    answer
  }
}'''

with case("products are values; nested records retain nominal types"):
    common = stable(PRODUCTS)
    fn = next(f for f in common[1] if f[1] == "Test")
    assert fn[6][0][4] == ["x", "y"]  # Named arguments are bound in signature order.
    assert fn[6][0][5] == ["p.0", "p.1"]
    report = json.loads(run("protocol-analyze", PRODUCTS))
    assert any(t["kind"] == "product" for t in report["types"])

with case("named argument failures are checked before operand rearrangement"):
    for bad in ("PairUp(x: x, x: y)", "PairUp(z: x, y: y)", "PairUp(x: x, y)"):
        run("protocol-source", PRODUCTS.replace("PairUp(y: y, x: x)", bad),
            refuses="source-argument-name")

with case("nominal mismatch cannot hide inside a product"):
    bad = '''module {
      struct Left<F: domain Field> { value: F::Element }
      struct Right<F: domain Field> { value: F::Element }
      fn Get<F: Field>(p: (Left<F>, bool)) -> F::Element { p.0.value }
      fn Bad<F: Field>(p: Right<F>, flag: bool) -> F::Element {
        let tuple = (p, flag); let result = Get(tuple); result
      }
    }'''
    run("protocol-source", bad, refuses="source-struct-mismatch")

with case("named arguments evaluate in written order, once"):
    text = '''module {
      fn Pair(x: index, y: index) -> (index, index) { (x, y) }
      fn Use() -> (index, index) { Pair(y: 7, x: 11) }
    }'''
    module = stable(text)
    fn = next(f for f in module[2] if f[1] == "Use")
    body = fn[4]
    assert [op[3] for op in body if op[0] == "op"] == [["7"], ["11"]]
    call = next(op for op in body if op[0] == "apply")
    constants = [op for op in body if op[0] == "op"]
    assert call[4] == [constants[1][5][0], constants[0][5][0]]

with case("unit is one source value and no PIR leaves"):
    text = '''module {
      fn Guard<>(condition: bool) -> () { control::require(condition); () }
      fn Check<>(condition: bool) -> () { let done = Guard(condition); done }
    }'''
    module = stable(text)
    assert all(fn[5] == [] for fn in module[1])
    assert module[1][1][6][-1] == ["return", []]

PLACEMENT = '''module {
  fn Twice<F: Field>(x: F::Element) -> F::Element { x + x }
  protocol SendTwice<F: Field> {
    roles (Worker, Checker);
    inputs (Worker x: F::Element, Checker expected: F::Element);
    outputs (Checker accepted: bool, Worker result: F::Element);
    let result = local Worker {
      let doubled = Twice(x);
      doubled
    };
    message result_message: Worker(result) -> Checker(received);
    let accepted = local Checker {
      let valid = field::equal(received, expected);
      control::require(valid);
      valid
    };
    finish { result, accepted };
  }
  configure Selected = SendTwice(F = "bls12-381.fr");
  instance main: Selected { roles (Worker=Worker, Checker=Checker); }
  entry test = main;
}'''

with case("placement checks generic templates and lowers closed helpers"):
    common = stable(PLACEMENT)
    protocol = common[3][3][0]
    assert protocol[5] == [["Checker", "bool"], ["Worker", "field:bls12-381.fr"]]
    assert protocol[7][-1] == ["return", ["accepted", "result"]]
    assert [op[0] for op in protocol[7]] == ["local", "message", "local", "return"]
    assert len(common[3][2]) == 2  # Only selected closures are emitted.
    assert common[3][2][0][2] == [["x", "field:bls12-381.fr"]]

for label, old, new, code in (
    ("peer capture", "Twice(x)", "Twice(expected)", "source-value-reference"),
    ("scratch escape", "Worker(result)", "Worker(doubled)", "source-name-unresolved"),
    ("wrong output owner", "finish { result, accepted }", "finish { result: received, accepted }", "source-protocol-return"),
    ("missing output", "finish { result, accepted }", "finish { accepted }", "source-output-port"),
    ("duplicate output", "finish { result, accepted }", "finish { result, result }", "source-output-port"),
    ("hidden communication", "let doubled = Twice(x);", "message secret: Worker(x) -> Checker(leak);", "source-syntax"),
):
    with case(label):
        run("protocol-source", PLACEMENT.replace(old, new), refuses=code)

with case("a product cannot implicitly change message serialization"):
    text = PLACEMENT.replace("let doubled = Twice(x);", "let doubled = (x, x);").replace(
        "Worker result: F::Element", "Worker result: (F::Element, F::Element)")
    run("protocol-source", text, refuses="source-struct-message")

with case("explicit aggregate annotations preserve nominal/product identity"):
    stable(PRODUCTS.replace("let nested =", "let nested: (Pair<F>, (), (F::Element, F::Element)) ="))
    run("protocol-source", PRODUCTS.replace("let nested =", "let nested: (index, bool) ="),
        refuses="source-annotation-type")
    stable(PRODUCTS.replace("let answer =", "let copy: (F::Element, F::Element) = p; let answer ="))

with case("direct generic entry selects a closed root without configuration boilerplate"):
    direct = PLACEMENT[:PLACEMENT.index("  configure Selected")] + '''
      entry main = SendTwice::<F = "bls12-381.fr">;
    }'''
    stable(direct)
    run("protocol-source", direct.replace('F = "bls12-381.fr"', 'Wrong = "bls12-381.fr"'),
        refuses="source-static-argument")

with case("requirements admit predicates and explicit associated equality"):
    text = '''module {
      fn Identity<G: domain Group, F: domain Field>(x: F::Element) -> F::Element
        where ScalarAction(G), Field(F), G::Scalar == F { x }
    }'''
    stable(text)

with case("constructor restriction is authority rather than a proof annotation"):
    text = '''module {
      struct Prepared<F: domain Field> constructors(Make) { value: F::Element }
      fn Make<F: Field>(value: F::Element) -> Prepared<F> { Prepared { value } }
    }'''
    stable(text)
    run("protocol-source", text.replace("constructors(Make)", "constructors(Other)"),
        refuses="source-name-unresolved")

with case("retained bindings distinguish source products from their leaf layout"):
    report = json.loads(run("protocol-analyze", PRODUCTS))
    nested = next(b for b in report["local_bindings"] if b["name"] == "nested")
    assert report["types"][nested["type"]]["kind"] == "product"
    assert len(nested["leaves"]) == 4
    assert report["scopes"][nested["scope"]]["parent"] is not None
    assert all(0 <= u["binding"] < len(report["local_bindings"]) for u in report["value_uses"])

with case("closed composition maps named child outputs independently of written order"):
    text = PLACEMENT[:PLACEMENT.index("  configure Selected")] + '''
      protocol TwiceThenReturn<F: Field> {
        roles (Worker, Checker);
        inputs (Worker x: F::Element, Checker expected: F::Element);
        outputs (Worker result: F::Element, Checker accepted: bool);
        dependencies(child: SendTwice::<F=F>());
        invoke child(x, expected) -> {result: value, accepted: ok};
        finish { accepted: ok, result: value };
      }
      entry main = TwiceThenReturn::<F="bls12-381.fr">;
    }'''
    stable(text)
    run("protocol-source", text.replace("result: value, accepted: ok", "result: value, result: ok"),
        refuses="source-output-port")

with case("products preserve affine leaf usage"):
    text = '''module {
      fn Twice<F: Field>(coins: Rng<F>) -> F::Element {
        let tuple = (coins, ());
        let (first, rest) = random::draw(tuple.0);
        let (second, last) = random::draw(tuple.0);
        first
      }
    }'''
    run("protocol-source", text, refuses="generic-resource-reuse")

with case("placement captures used leaves and does not consume unrelated resources"):
    text = '''module {
      protocol Draw<F: Field> {
        roles(Worker);
        inputs(Worker coins: Rng<F>, Worker x: F::Element);
        outputs(Worker value: F::Element);
        let doubled = local Worker { x + x };
        let value = local Worker { let (random, remaining) = random::draw(coins); random };
        finish { value };
      }
      entry main = Draw::<F="bls12-381.fr">;
    }'''
    common = stable(text)
    helpers = common[2]
    assert helpers[0][2] == [["x", "field:bls12-381.fr"]]
    assert helpers[1][2] == [["coins", "rng:bls12-381.fr"]]

with case("record construction checks product structure before leaf layout"):
    text = '''module {
      struct Left { value: index }
      struct Right { value: index }
      struct Box { pair: (Left, ()) }
      fn Good(x: index) -> Box { Box { pair: (Left { value: x }, ()) } }
    }'''
    stable(text)
    for bad, code in (
        ("(Right { value: x }, ())", "source-annotation-type"),
        ("(Left { value: x }, x)", "source-struct-value"),
        ("(Left { value: x }, (), x)", "source-annotation-type"),
        ("(Left { value: x },)", "source-annotation-type"),
    ):
        run("protocol-source", text.replace("(Left { value: x }, ())", bad),
            refuses=code)

with case("call result annotations check structure before layout"):
    text = '''module {
      fn Pair(x: index) -> (index, index) { (x, x) }
      fn Bad(x: index) -> index { let p: (index, index, index) = Pair(x); x }
    }'''
    run("protocol-source", text, refuses="source-struct-mismatch")

with case("result annotations preserve phantom domain parameters"):
    text = '''module {
      struct Marker<F: domain Field> { flag: bool }
      fn Make<F: Field>(flag: bool) -> Marker<F> { Marker::<F> { flag } }
      fn Bad<A: Field, B: Field>(flag: bool) -> bool {
        let marker: Marker<B> = Make::<A>(flag);
        flag
      }
    }'''
    run("protocol-source", text, refuses="source-annotation-type")

with case("profile operation binding visits return and tail expressions"):
    for body in ("field.add(x, x)", "return field.add(x, x);",
                 "field.add(x, field.add(x, x))"):
        text = ('module "arkworks.bls12-381/1" { '
                'fn Twice(x: field) -> field { ' + body + ' } }')
        module = stable(text)
        assert any(b[1] == "field.add" for b in module[1])

with case("operators reject zero-leaf aggregates without inspecting a scalar"):
    for shape in ("()", "((),)", "((), ())"):
        for body in ("let z = x + y; z", "x + y"):
            text = f"module {{ fn Bad(x: {shape}, y: {shape}) -> {shape} {{ {body} }} }}"
            run("protocol-source", text, refuses="source-struct-value")
            report = json.loads(run("protocol-analyze", text))
            assert report["phase"] == "semantic_error"
            assert report["diagnostics"][0]["code"] == "source-struct-value"

with case("region captures and induction variables retain their lexical scopes"):
    text = '''module {
      fn Scoped(flag: bool, u: (), x: index) -> index {
        if flag capture(u, x) -> (a) { yield(x); } else { yield(x); }
        for i in 0..2 { let inner = i; }
        a
      }
    }'''
    stable(text)
    report = json.loads(run("protocol-analyze", text))
    bindings = report["local_bindings"]
    outer = next(b["scope"] for b in bindings if b["name"] == "a")
    captured = [b for b in bindings if b["name"] == "x" and b["span"]]
    assert len(captured) == 2
    assert len({b["scope"] for b in captured}) == 2
    for binding in captured:
        scope = binding["scope"]
        assert report["scopes"][scope]["parent"] == outer
        assert any(b["name"] == "u" and b["scope"] == scope for b in bindings)
        assert any(u["binding"] == binding["id"] and u["scope"] == scope
                   for u in report["value_uses"])
    index = next(b for b in bindings if b["name"] == "i")
    inner = next(b for b in bindings if b["name"] == "inner")
    assert index["scope"] == inner["scope"]
    assert report["scopes"][index["scope"]]["parent"] == outer

print(f"{commands.save()} frontend foundation controls passed")
