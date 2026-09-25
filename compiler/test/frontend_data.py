"""Authoring data forms: bundles, structs, operators and checked structs.

Every form is authoring syntax. A source written with it must produce the same
encoded common records as a separately authored source in the expanded
notation, and every refusal is identified by its stable code.
"""
import json
import pathlib
import shutil
from commands import Commands
from tools import ROOT, compiler, examples, records



commands = Commands(records())


def run(mode, text, refuses=None):
    """What the compiler printed, or what it said when it refused."""
    printed = commands.source(mode, text, refuses=refuses)
    return commands.last.stderr if refuses else printed


def common(text):
    return json.loads(run("protocol-source", text))


def same(authored, expanded):
    left, right = common(authored), common(expanded)
    assert left == right, (json.dumps(left), json.dumps(right))
    # Formatting is a syntax-only operation and must keep the meaning.
    assert common(run("protocol-format", authored)) == left
    return left


# --- Constraint bundles -----------------------------------------------------
BODY = '''{
    let q = curve::scale(p, k);
    return q;
  }'''
HEAD = ("fn Scale<F: PairingField>(p: F::PairingG1::Element, k: F::Element)"
        " -> F::PairingG1::Element")
bundled = f'''module {{
  bundle Scalars(G) = (ScalarAction(G), Field(G::Scalar));
  bundle PairingArithmetic(F) = (
    Scalars(F::PairingG1), Scalars(F::PairingG2), "="(F::PairingG1::Scalar, F)
  );
  {HEAD} requires (PairingArithmetic(F)) {BODY}
}}'''
expanded = f'''module {{
  {HEAD} requires (
    ScalarAction(F::PairingG1), Field(F::PairingG1::Scalar),
    ScalarAction(F::PairingG2), Field(F::PairingG2::Scalar),
    "="(F::PairingG1::Scalar, F)
  ) {BODY}
}}'''
record = same(bundled, expanded)
# The header bound comes first, then the expansion in declared order.
assert [r[0] for r in record[1][0][3]] == [
    "PairingField", "ScalarAction", "Field", "ScalarAction", "Field", "="]

# A use is a position, not a set member: order and duplicates are the author's.
IDENTITY = """module {
  bundle Scalars(G) = (ScalarAction(G), Field(G::Scalar));
  fn Id<F: PairingField>(x: F::Element) -> F::Element CLAUSE { return x; }
}"""
twice = IDENTITY.replace("CLAUSE", "requires (Field(F), Scalars(F::PairingG1), Field(F))")
assert [r[0] for r in common(twice)[1][0][3]] == [
    "PairingField", "Field", "ScalarAction", "Field", "Field"]

# `where T: Bundle` is the one-parameter use; a header bound is a capability.
where = IDENTITY.replace("CLAUSE", "where F::PairingG1: Scalars")
assert [r[0] for r in common(where)[1][0][3]] == [
    "PairingField", "ScalarAction", "Field"]
run("protocol-source",
    bundled.replace("<F: PairingField>", "<F: PairingArithmetic>"),
    "source-bound")

# Forward use and declaration order are independent.
forward = bundled.replace(
    "  bundle Scalars(G) = (ScalarAction(G), Field(G::Scalar));\n", "").replace(
    "  fn Scale", "  bundle Scalars(G) = (ScalarAction(G), Field(G::Scalar));\n  fn Scale")
assert common(forward) == record

run("protocol-source", bundled.replace("PairingArithmetic(F))", "PairingArithmetic(F, F))"),
    "source-bundle-arity")
run("protocol-source", bundled.replace("Scalars(F::PairingG2)", "Scalars()"),
    "source-bundle-arity")
run("protocol-source", bundled.replace("bundle Scalars(G)", "bundle Field(G)"),
    "source-name-unresolved")
run("protocol-source", bundled.replace("bundle Scalars(G)", "bundle Scalars(G, G)"),
    "source-bundle-name")
run("protocol-source", bundled.replace("bundle Scalars(G)", "bundle Scale(G)"),
    "source-duplicate-symbol")
run("protocol-source", bundled.replace("Field(G::Scalar)", "Field(H::Scalar)"),
    "source-name-unresolved")
cycle = bundled.replace("Field(G::Scalar));", "Field(G::Scalar), PairingArithmetic(G));")
run("protocol-source", cycle, "source-bundle-cycle")
# A refusal inside an expansion is reported at the use and names the bundle.
error = run("protocol-source", bundled.replace("ScalarAction(G)", "ScalarAction(G, G)"),
            "generic-predicate-arity")
assert "from bundle 'PairingArithmetic'" in error, error
wide = "bundle Wide(F) = (" + ", ".join(["Field(F)"] * 40) + ");"
huge = "bundle Huge(F) = (" + ", ".join(["Wide(F)"] * 40) + ");"
run("protocol-source",
    f"module {{ {wide} {huge} fn Id<F: domain Field>(x: F::Element) -> F::Element"
    " requires (Huge(F)) { return x; } }", "requirements-limit")
# Bundles are authoring syntax: syntax inspection shows them, common source does not.
assert json.loads(run("protocol-parse", bundled))["content"]["bundles"][0]["name"] == "Scalars"
assert "bundle" not in json.dumps(record)

# --- Structs ----------------------------------------------------------------
STRUCTS = """
  struct Pair<F: domain Field>(x: F::Element, y: F::Element);
  struct Sums<F: domain Field>(input: Pair<F>, sum: F::Element);
"""
TAIL = """
  configure Make = MakePair(F = "koala-bear");
  configure Add = Sum(F = "koala-bear");
  configure Final = Total(F = "koala-bear");
  protocol Demo {
    roles (P, V);
    inputs (P SEED);
    outputs (V "koala-bear"::Element);
    LOCALS
    message result: P(t) -> V(received);
    return received;
  }
  instance concrete: Demo { roles (P = P, V = V); }
  entry main = concrete;
"""
struct_source = "module {" + STRUCTS + """
  fn MakePair<F: Field>(a: F::Element, b: F::Element) -> Pair<F> {
    let doubled = field::add(b, b);
    let p = Pair(y = doubled, x = a);
    return p;
  }
  fn Sum<F: Field>(p: Pair<F>) -> Sums<F> {
    let total = field::add(p.x, p.y);
    let s = Sums(input = p, sum = total);
    return s;
  }
  fn First<F: Field>(p: Pair<F>) -> F::Element { return p.x; }
  fn Total<F: Field>(s: Sums<F>) -> F::Element {
    let first = First(s.input);
    let again = field::add(first, s.sum);
    return again;
  }
""" + TAIL.replace("SEED", 'seed: Pair<"koala-bear">').replace("LOCALS", """
    local P: let p = Make(seed.x, seed.y);
    local P: let s = Add(p);
    local P: let t = Final(s);""") + "}"
struct_expanded = """module {
  fn MakePair<F: Field>(a: F::Element, b: F::Element) -> (F::Element, F::Element) {
    let doubled = field::add(b, b);
    return (a, doubled);
  }
  fn Sum<F: Field>(p.x: F::Element, p.y: F::Element)
      -> (F::Element, F::Element, F::Element) {
    let total = field::add(p.x, p.y);
    return (p.x, p.y, total);
  }
  fn First<F: Field>(p.x: F::Element, p.y: F::Element) -> F::Element { return p.x; }
  fn Total<F: Field>(s.input.x: F::Element, s.input.y: F::Element, s.sum: F::Element)
      -> F::Element {
    let first = First(s.input.x, s.input.y);
    let again = field::add(first, s.sum);
    return again;
  }
""" + TAIL.replace("SEED", 'seed.x: "koala-bear"::Element, P seed.y: "koala-bear"::Element'
        ).replace("LOCALS", """
    local P: let (p.x, p.y) = Make(seed.x, seed.y);
    local P: let (s.input.x, s.input.y, s.sum) = Add(p.x, p.y);
    local P: let t = Final(s.input.x, s.input.y, s.sum);""") + "}"
struct_record = same(struct_source, struct_expanded)
assert '"Pair"' not in json.dumps(struct_record) and "Sums" not in json.dumps(struct_record)
# The whole pipeline accepts the flattened source.
run("protocol-compile", struct_source)


def struct_module(body, structs=STRUCTS):
    return "module {" + structs + body + "}"


# Written and inferred static arguments, and a struct result annotation, agree.
inferred = struct_module("""
  fn Make<F: Field>(a: F::Element) -> Pair<F> { let p = Pair(x = a, y = a); return p; }
  fn Use<F: Field>(a: F::Element) -> F::Element { let p = Make(a); return p.y; }
""")
for text in (inferred.replace("Pair(x = a", "Pair::<F>(x = a"),
             inferred.replace("let p = Make(a)", "let p: Pair<F> = Make(a)")):
    assert common(text) == common(inferred)
# A struct without parameters names closed domains.
closed = struct_module("""
  fn Id(p: Fixed) -> Fixed { return p; }
""", 'struct Fixed(x: "koala-bear"::Element);')
assert common(closed) == common(
    'module { fn Id(p.x: "koala-bear"::Element) -> "koala-bear"::Element { return p.x; } }')

# An affine leaf keeps its own rule: one read, or one whole-struct use.
draws = """
  struct Draws<F: domain Field>(coins: Rng<F>, scale: F::Element);
  fn Spend<F: Field>(d: Draws<F>) -> F::Element { let (r, rest) = random::draw(d.coins); return r; }
  fn Twice<F: Field>(d: Draws<F>) -> F::Element { BODY }
"""
run("protocol-source", struct_module(draws.replace(
    "BODY", "let (r, a) = random::draw(d.coins); let (s, b) = random::draw(d.coins); return r;"), ""),
    "generic-resource-reuse")
run("protocol-source", struct_module(draws.replace(
    "BODY", "let (r, a) = random::draw(d.coins); let s = Spend(d); return r;"), ""),
    "generic-resource-reuse")
common(struct_module(draws.replace("BODY", "let s = Spend(d); return s;"), ""))

# Loops carry and yield structs leaf by leaf, and an invoke passes them whole.
looped = struct_module("""
  fn Step<F: Field>(p: Pair<F>) -> Pair<F> {
    let q = Pair(x = p.y, y = field::add(p.x, p.y));
    return q;
  }
  configure Advance = Step(F = "koala-bear");
  protocol Walk {
    roles (P, V);
    parameters (n);
    inputs (P start: Pair<"koala-bear">);
    outputs (P Pair<"koala-bear">);
    loop n carry (state = start) -> (finish) {
      local P: let next = Advance(state);
      yield (next);
    }
    return finish;
  }
  protocol Outer {
    roles (P, V);
    parameters (n);
    inputs (P start: Pair<"koala-bear">);
    outputs (V "koala-bear"::Element);
    dependencies (walk: Walk(n = n));
    invoke walk(start) -> (finish);
    message result: P(finish.y) -> V(received);
    return received;
  }
  instance walk: Walk { parameters (n = 2); roles (P = P, V = V); }
  instance outer: Outer { parameters (n = 2); dependencies (walk = walk); roles (P = P, V = V); }
  entry main = outer;
""")
looped_record = common(looped)
text = json.dumps(looped_record)
for leaf in ("state.x", "state.y", "finish.x", "finish.y", "next.x", "start.y"):
    assert json.dumps(leaf) in text, leaf
run("protocol-compile", looped)

# Refusals.
def refuse(body, code, structs=STRUCTS):
    return run("protocol-source", struct_module(body, structs), code)


USE = "fn Use<F: Field>(p: Pair<F>, a: F::Element) -> F::Element { BODY }"
refuse(USE.replace("BODY", "let q = Missing(x = a, y = a); return a;"), "source-name-unresolved")
refuse("fn Bad<F: Field>(p: Pair<F, F>) -> F::Element { return p.x; }", "source-type-arity")
refuse("fn Bad<G: domain Group>(p: Pair<G>) -> G::Element { return p.x; }", "source-type-domain")
refuse("", "source-struct-field", "struct Twice<F: domain Field>(x: F::Element, x: F::Element);")
refuse("", "source-struct-field", "struct Dotted<F: domain Field>(a.b: F::Element);")
refuse("", "source-struct-field", "struct Empty();")
refuse(USE.replace("BODY", "let q = Pair(x = a); return a;"), "source-struct-field")
refuse(USE.replace("BODY", "let q = Pair(x = a, y = a, z = a); return a;"), "source-struct-field")
refuse(USE.replace("BODY", "let q = Pair(x = a, x = a); return a;"), "source-struct-field")
refuse("", "source-struct-cycle",
       "struct A<F: domain Field>(b: B<F>); struct B<F: domain Field>(a: A<F>);")
refuse("", "source-struct-bound", "struct Bounded<F: Field>(x: F::Element);")
# Resolved nominal identities no longer share the installed type's symbol.
# A local declaration is selected explicitly in its scope; it cannot capture
# installed types in separately resolved dependency code.
for name in ("Proof", "Vector", "Rng"):
    common(struct_module(
        f"fn Keep<F: Field>(x: {name}<F>) -> {name}<F> {{ return x; }}",
        f"struct {name}<F: domain Field>(x: F::Element);"))
wide = "struct Wide<F: domain Field>(" + ", ".join(f"f{i}: F::Element" for i in range(4097)) + ");"
refuse("", "source-struct-limit", wide)
# A struct is not a single value, and a single value is not a struct.
refuse(USE.replace("BODY", "let b = field::add(p, a); return b;"), "source-struct-value")
refuse(USE.replace("BODY", "let b = Use(a, a); return b;"), "source-struct-value")
refuse(USE.replace("BODY", "return p;"), "source-annotation-type")
refuse("fn Bad<F: Field>(a: F::Element) -> Pair<F> { return a; }", "source-struct-value")
refuse(USE.replace("BODY", "let q = Sums(input = a, sum = a); return a;"), "source-struct-value")
refuse(USE.replace("BODY", "let v = [p]; return a;"), "source-struct-value")
refuse(USE.replace("BODY", "let q: F::Element = p; return a;"), "source-annotation-type")
# Struct identity is nominal, including static arguments.
OTHER = STRUCTS + "struct Other<F: domain Field>(x: F::Element, y: F::Element);"
refuse(USE.replace("BODY", "let q = Other(x = a, y = a); let b = Use(q, a); return b;"),
       "source-struct-mismatch", OTHER)
refuse("fn Bad<F: Field>(q: Other<F>) -> Pair<F> { return q; }", "source-annotation-type", OTHER)
refuse(USE.replace("BODY", "let q = Other(x = a, y = a); let s = Sums(input = q, sum = a); return a;"),
       "source-struct-mismatch", OTHER)
refuse("""fn Two<F: Field, E: Field>(p: Pair<F>, a: E::Element) -> E::Element {
    let q = Pair(x = a, y = a); let s = Sums::<E>(input = p, sum = a); return a; }""",
       "source-annotation-type")
# Bindings are immutable, and a message carries one explicit value.
refuse(USE.replace("BODY", "let mut q = Pair(x = a, y = a); return a;"), "source-struct-mutable")
refuse(USE.replace("BODY", "let mut b = a; b = p; return a;"), "source-struct-mutable")
refuse(USE.replace("BODY", "let q = Pair(x = a, y = a); let a.z = a; let p = q; return a;"),
       "source-value-duplicate")
refuse(USE.replace("BODY", "let p.x = a; return a;"), "source-value-duplicate")
refuse("""
  protocol Send {
    roles (P, V);
    inputs (P seed: Pair<"koala-bear">);
    outputs (V "koala-bear"::Element);
    message pair: P(seed) -> V(received);
    return received;
  }""", "source-struct-message")
refuse("""
  protocol Walk {
    roles (P, V);
    inputs (P start: Pair<"koala-bear">, P lone: "koala-bear"::Element);
    outputs (P Pair<"koala-bear">);
    return lone;
  }""", "source-struct-value")
# Struct declarations are authoring syntax.
inspected = json.loads(run("protocol-parse", struct_source))["content"]
assert [d["name"] for d in inspected["structs"]] == ["Pair", "Sums"]

# --- Operators --------------------------------------------------------------
# An operator spells an installed operation. The frontend owns the spelling and
# the installed contract owns the meaning, so no source declares one.
COMBINE = """
  fn Combine<G: ScalarAction>(alpha: G::Element, base: G::Element, delta: G::Element,
      r: G::Scalar::Element, s: G::Scalar::Element) -> G::Element
    where G::Scalar: Field {
    BODY
    return d;
  }
"""


def operators(body):
    return "module {" + COMBINE.replace("BODY", body) + "}"


with_operators = operators("""
    let a = alpha + base + delta * r;
    let c = a + -(delta * (r * s - r));
    let d = s * c;""")
with_calls = operators("""
    let a = curve::add(curve::add(alpha, base), curve::scale(delta, r));
    let c = curve::add(a, curve::neg(curve::scale(delta, field::sub(field::mul(r, s), r))));
    let d = curve::scale(c, s);""")
same(with_operators, with_calls)

# Every spelling is the named call over the same operands.
SPELLINGS = [
    ("+", "field::add(x, y)", "x", "y"), ("-", "field::sub(x, y)", "x", "y"),
    ("*", "field::mul(x, y)", "x", "y"), ("+", "curve::add(p, q)", "p", "q"),
    ("*", "curve::scale(p, x)", "p", "x"), ("*", "curve::scale(p, x)", "x", "p"),
    ("+", "vector::add(v, w)", "v", "w"), ("-", "vector::sub(v, w)", "v", "w"),
    ("*", "vector::scale(v, x)", "v", "x"), ("*", "vector::scale(v, x)", "x", "v"),
    ("+", "index::add(i, j)", "i", "j"), ("-", "index::sub(i, j)", "i", "j"),
    ("*", "index::mul(i, j)", "i", "j"),
]
UNARY = [("field::neg(x)", "x"), ("curve::neg(p)", "p")]
EVERY = """module {
  fn Every<G: ScalarAction>(x: G::Scalar::Element, y: G::Scalar::Element, p: G::Element,
      q: G::Element, v: Vector<G::Scalar::Element>, w: Vector<G::Scalar::Element>,
      i: index, j: index) -> index where G::Scalar: Field {
    BODY
    return i;
  }
}"""
infix = "\n".join(f"    let r{n} = {a} {symbol} {b};"
                  for n, (symbol, _, a, b) in enumerate(SPELLINGS))
infix += "\n" + "\n".join(f"    let n{n} = -{a};" for n, (_, a) in enumerate(UNARY))
named = "\n".join(f"    let r{n} = {call};" for n, (_, call, _, _) in enumerate(SPELLINGS))
named += "\n" + "\n".join(f"    let n{n} = {call};" for n, (call, _) in enumerate(UNARY))
same(EVERY.replace("BODY", infix), EVERY.replace("BODY", named))

# Precedence is fixed and binary operators associate to the left.
assert common(operators("let d = alpha + base * r + delta;")) == common(
    operators("let d = curve::add(curve::add(alpha, curve::scale(base, r)), delta);"))
assert common(operators("let d = (alpha + base) * r;")) == common(
    operators("let d = curve::scale(curve::add(alpha, base), r);"))
assert common(operators("let d = alpha * (r - s - r);")) == common(
    operators("let d = curve::scale(alpha, field::sub(field::sub(r, s), r));"))
assert common(operators("let d = -alpha * r;")) == common(
    operators("let d = curve::scale(curve::neg(alpha), r);"))
# Operands run in written order, whatever order the operation takes them in.
written = common(operators("let d = (r * s) * (alpha + base);"))
calls = [i for i in written[1][-1][-1] if i[0] == "op"]
assert [c[2] for c in calls] == ["field.mul", "curve.add", "curve.scale"], calls
# A use has a spelling or it does not; the selected call is checked as written.
run("protocol-source", operators("let d = alpha * base;"), "source-operator-unresolved")
run("protocol-source", operators("let d = alpha - base;"), "source-operator-unresolved")
hadamard = EVERY.replace("BODY", "let r = v * w;")
run("protocol-source", hadamard, "source-operator-unresolved")
mixed = """module {
  fn Mixed<G: ScalarAction, H: ScalarAction>(p: G::Element, k: H::Scalar::Element)
      -> G::Element { let d = p * k; return d; }
}"""
run("protocol-source", mixed, "source-type-mismatch")
error = run("protocol-source", operators("let d = alpha-base;"), "source-name-unresolved")
assert "alpha - base" in error, error
# No source declares an operator, and none reaches portable source.
run("protocol-source", "module { operator + (a, b) = field::add(a, b); }", "source-syntax")
assert "operator" not in json.dumps(common(with_operators))
run("protocol-source", "module {" + STRUCTS + """
  fn Bad<F: Field>(p: Pair<F>, a: F::Element) -> F::Element { let d = a + p; return d; }
}""", "source-struct-value")

# In a closed module an operator is the qualified call, with its default binding.
CLOSED = """module {
  fn Check(base: "bls12-381.g1"::Element, image: "bls12-381.g1"::Element,
      c: "bls12-381.fr"::Element, z: "bls12-381.fr"::Element) -> "bls12-381.g1"::Element {
    [left] let left = LEFT;
    [sum] let sum = SUM;
    return sum;
  }
}"""
same(CLOSED.replace("LEFT", "base * z").replace("SUM", "left + image * c"),
     CLOSED.replace("LEFT", "curve::scale(base, z)").replace(
         "SUM", "curve::add(left, curve::scale(image, c))"))

# --- Checked structs --------------------------------------------------------
CHECKED = """
  checked struct Bound<F: domain Field>(
    assignment: Vector<F::Element>, statement: Vector<F::Element>
  ) constructors (Bind);
  fn Bind<F: Field>(assignment: Vector<F::Element>, statement: Vector<F::Element>)
      -> Bound<F> {
    control::require(index::equal(assignment.len(), statement.len()));
    let bound = Bound(assignment = assignment, statement = statement);
    return bound;
  }
  fn Prove<F: Field>(bound: Bound<F>) -> Vector<F::Element> {
    let sum = vector::add(bound.assignment, bound.statement);
    return sum;
  }
"""
PROTOCOL = """
  configure Binding = Bind(F = "koala-bear");
  configure Proving = Prove(F = "koala-bear");
  protocol Run {
    roles (P, V);
    inputs (P assignment: Vector<"koala-bear"::Element>,
            P statement: Vector<"koala-bear"::Element>);
    outputs (P Vector<"koala-bear"::Element>);
    local P: let bound = Binding(assignment, statement);
    local P: let sum = Proving(bound);
    return sum;
  }
  instance run: Run { roles (P = P, V = V); }
  entry main = run;
"""
checked_source = "module {" + CHECKED + PROTOCOL + "}"
checked_expanded = """module {
  fn Bind<F: Field>(assignment: Vector<F::Element>, statement: Vector<F::Element>)
      -> (Vector<F::Element>, Vector<F::Element>) {
    control::require(index::equal(assignment.len(), statement.len()));
    return (assignment, statement);
  }
  fn Prove<F: Field>(bound.assignment: Vector<F::Element>, bound.statement: Vector<F::Element>)
      -> Vector<F::Element> {
    let sum = vector::add(bound.assignment, bound.statement);
    return sum;
  }
""" + PROTOCOL.replace("let bound = Binding", "let (bound.assignment, bound.statement) = Binding"
        ).replace("Proving(bound)", "Proving(bound.assignment, bound.statement)") + "}"
same(checked_source, checked_expanded)
run("protocol-compile", checked_source)


def checked(extra, base=CHECKED):
    return "module {" + base + extra + "}"


# The value is built only where its checks are written.
forge = """
  fn Forge<F: Field>(a: Vector<F::Element>) -> Vector<F::Element> {
    let forged = Bound(assignment = a, statement = a);
    let sum = Prove(forged);
    return sum;
  }"""
run("protocol-source", checked(forge), "source-checked-construction")
# Skipping the constructor leaves nothing to pass: a vector is not a Bound.
run("protocol-source", checked("""
  fn Skip<F: Field>(a: Vector<F::Element>) -> Vector<F::Element> {
    let sum = Prove(a, a);
    return sum;
  }"""), "source-call-arity")
run("protocol-source", checked("""
  fn Skip<F: Field>(a: Vector<F::Element>) -> Vector<F::Element> {
    let sum = Prove(a);
    return sum;
  }"""), "source-struct-value")
# A struct of the same fields is a different type.
run("protocol-source", checked("""
  struct Loose<F: domain Field>(assignment: Vector<F::Element>, statement: Vector<F::Element>);
  fn Skip<F: Field>(a: Vector<F::Element>) -> Vector<F::Element> {
    let loose = Loose(assignment = a, statement = a);
    let sum = Prove(loose);
    return sum;
  }"""), "source-struct-mismatch")
# Fields stay readable, and a plain struct may carry a checked value.
common(checked("""
  struct Job<F: domain Field>(bound: Bound<F>, scale: F::Element);
  fn Pack<F: Field>(bound: Bound<F>, scale: F::Element) -> Job<F> {
    let job = Job(bound = bound, scale = scale);
    return job;
  }
  fn Size<F: Field>(job: Job<F>) -> index { let n = job.bound.statement.len(); return n; }
"""))
# Constructors are functions of this module that return the type.
for constructors in ("Missing", "Prove", "Opaque"):
    run("protocol-source", checked("""
  fn Opaque<F: Field>(a: Vector<F::Element>) -> Bound<F> external;
""" if constructors == "Opaque" else "", CHECKED.replace(
        "constructors (Bind)", f"constructors (Bind, {constructors})")),
        "source-name-unresolved" if constructors == "Missing" else "source-checked-constructor")
run("protocol-source", "module { checked struct Bare(x: bool); }", "source-syntax")
# A value would arrive without its constructor from a bodiless function or the host.
run("protocol-source", checked("""
  fn Opaque<F: Field>(a: Vector<F::Element>) -> Bound<F> external;
"""), "source-checked-external")
hosted = """
  protocol Hosted {
    roles (P, V);
    inputs (P bound: INPUT);
    outputs (P Vector<"koala-bear"::Element>);
    local P: let sum = Proving(bound);
    return sum;
  }
  configure Proving = Prove(F = "koala-bear");
"""
entry = """
  instance hosted: Hosted { roles (P = P, V = V); }
  entry main = hosted;
"""
run("protocol-source", checked(hosted.replace("INPUT", 'Bound<"koala-bear">') + entry),
    "source-checked-input")
run("protocol-source", checked("""
  struct Job<F: domain Field>(bound: Bound<F>, scale: F::Element);
  fn Unpack<F: Field>(job: Job<F>) -> Vector<F::Element> { let s = Prove(job.bound); return s; }
  configure Proving = Unpack(F = "koala-bear");
""" + hosted.replace("INPUT", 'Job<"koala-bear">').replace(
    '  configure Proving = Prove(F = "koala-bear");\n', "") + entry), "source-checked-input")
# A protocol that is only invoked may receive a checked value from its parent.
common(checked(hosted.replace("INPUT", 'Bound<"koala-bear">') + """
  configure Binding = Bind(F = "koala-bear");
  protocol Parent {
    roles (P, V);
    inputs (P a: Vector<"koala-bear"::Element>);
    outputs (P Vector<"koala-bear"::Element>);
    dependencies (child: Hosted());
    local P: let bound = Binding(a, a);
    invoke child(bound) -> (sum);
    return sum;
  }
  instance hosted: Hosted { roles (P = P, V = V); }
  instance parent: Parent { dependencies (child = hosted); roles (P = P, V = V); }
  entry main = parent;
"""))

# --- Maintained example -----------------------------------------------------
# The readable Groth16 source and its hand-expanded twin are one common source.


def materialized(source):
    directory = records()
    root = pathlib.Path(directory)
    shutil.copy(source, root / "groth16.pir")
    shutil.copy(ROOT / "examples/relations/multiply.r1cs.json", root / "circuit.r1cs")
    outputs = []
    for mode, path in (("protocol-resolve", "groth16.pir"),
                       ("protocol-materialize", "resolved.json")):
        printed = commands.run([compiler, mode, root / path])
        (root / "resolved.json").write_text(printed)
        outputs.append(printed)
    return outputs[1]


readable = examples / "groth16.pir"
assert materialized(readable) == materialized(
    ROOT / "tests/fixtures/groth16-expanded.pir")
text = readable.read_text()
for form in ("bundle ", " + ", "struct ", "constructors (BindAssignment)"):
    assert form in text, form
assert run("protocol-format", text) == text

print(f"frontend data forms: {commands.save()} compiler checks passed")
