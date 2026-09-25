"""Tool-level source notation, identity, formatting, and diagnostic checks."""

import copy
import json
from pathlib import Path
import random
from cases import case
from commands import Commands
from source_text import COLLISION
from tools import compiler, examples, records


root = Path(__file__).resolve().parents[2]


commands = Commands(records())


def run(command, *files, text=None, refuses=None):
    """The whole result, for a caller that reads more than one stream."""
    commands.run([compiler, command, *(files or ("-",))], stdin=text,
                 refuses=refuses)
    return commands.last


def encode(value):
    return json.dumps(value, ensure_ascii=False)


temporary = records()
directory = Path(temporary)
sources = {}
for file in sorted(examples.glob("*.json")):
    original = json.loads(file.read_text())
    if not isinstance(original, list) or original[0] not in (
        "zkc.protocol/1", "zkc.construction/1",
    ):
        continue
    pretty = run("protocol-format", file).stdout
    assert not pretty.startswith("[")
    assert json.loads(run("protocol-source", text=pretty).stdout) == original
    assert run("protocol-format", text=pretty).stdout == pretty
    run("protocol-format-check", text=pretty)
    run("protocol-format-check", text="\n" + pretty, refuses="source-not-formatted")
    target = directory / file.with_suffix(".pir").name
    target.write_text(pretty)
    sources[file.name] = target
    checked_in = file.with_suffix(".pir")
    assert checked_in.is_file(), f"missing maintained text fixture: {checked_in}"
    assert json.loads(run("protocol-source", checked_in).stdout) == original
    run("protocol-format-check", checked_in)

# Exact construction equality is stronger than matching terminal outcomes:
# source, message, public-binding and draw identities are all retained.
for stem in ("two-factor", "committed-two-factor", "dleq"):
    json_source = examples / f"{stem}.json"
    text_source = sources[f"{stem}.json"]
    json_descriptor = examples / f"{stem}.construction.json"
    text_descriptor = sources[f"{stem}.construction.json"]
    for mode in ("protocol-import", "protocol-project", "protocol-compile"):
        assert run(mode, json_source).stdout == run(mode, text_source).stdout
    expected = run("protocol-construct", json_source, json_descriptor).stdout
    actual = run("protocol-construct", text_source, text_descriptor).stdout
    assert json.loads(actual) == json.loads(expected)
    candidate = directory / f"{stem}.constructed.json"
    candidate.write_text(actual)
    run("protocol-check-construction", text_source, text_descriptor, candidate)
    # Constructed common programs also use the same developer notation.
    constructed = json.loads(actual)[2]
    pretty = run("protocol-format", text=encode(constructed)).stdout
    assert json.loads(run("protocol-source", text=pretty).stdout) == constructed
    assert run("protocol-compile", text=pretty).stdout == run(
        "protocol-compile", text=encode(constructed)
    ).stdout

# Roles are explicit declarations, including more than two roles. Names
# containing '-' and zero-result calls exercise token boundaries.
relay = '''module "arkworks.multilinear.bls12-381/1" {
      fn Identity(a: field) -> (field) { return (a); }
      protocol Relay {
        roles (Alice, Bob, Checker);
        inputs (Alice input-value: field);
        outputs (Checker field);
        local [copy] Alice: let owned = Identity(input-value);
        message [first] scalar: Alice(owned)->Bob(received);
        message [second] scalar: Bob(received)->Checker(result);
        return (result);
      }
      instance relay: Relay { roles (Alice=Alice, Bob=Bob, Checker=Checker); }
      entry main = relay;
    }'''
parsed = json.loads(run("protocol-source", text=relay).stdout)
projected = json.loads(run("protocol-project", text=relay).stdout)
assert [p[3] for p in projected[4]] == ["Alice", "Bob", "Checker"]
pretty = run("protocol-format", text=relay).stdout
assert json.loads(run("protocol-source", text=pretty).stdout) == parsed

# Comments are retained even inside lists and at EOF. A second formatting
# pass must be byte-identical, while comments remain outside source identity.
commented = relay.replace("roles (Alice, Bob, Checker);", '''
      // declared roles
      roles (Alice, /* first /* nested */ note */ Bob, // next role
             Checker);''', 1) + "\n// final comment without newline"
formatted = run("protocol-format", text=commented).stdout
for comment in ("// declared roles", "/* first /* nested */ note */",
                "// next role", "// final comment without newline"):
    assert comment in formatted
assert run("protocol-format", text=formatted).stdout == formatted
assert json.loads(run("protocol-source", text=formatted).stdout) == parsed

# Empty modules and external bodies remain declarations, not executable
# protocol implementations. Unknown role ownership uses existing admission.
run("protocol-source", text='module {}')
external = relay.replace(
    "fn Identity(a: field) -> (field) { return (a); }",
    "fn Identity(a: field) -> (field) external;",
)
run("protocol-source", text=external)
run("protocol-compile", text=external, refuses="interactive-external-body")
invalid_role = relay.replace("local [copy] Alice", "local [copy] Bob")
bad_file = directory / "bad-owner.pir"
bad_file.write_text(invalid_role)
error = run("protocol-source", bad_file, refuses="source-protocol-role")
bad_line = next(i for i, line in enumerate(invalid_role.splitlines(), 1)
                if "local [copy] Bob" in line)
assert f"{bad_file}:{bad_line}:" in error.stderr, error.stderr
assert "local [copy] Bob" in error.stderr
run("protocol-source", text=relay.replace("[second]", "[first]"),
    refuses="interactive-site")
run("protocol-source", text=relay.replace("Identity(input-value)", "Identity(absent)"),
    refuses="source-name-unresolved")
run("protocol-source", text=relay.replace("roles (Alice, Bob, Checker);", "roles ();"),
    refuses="source-protocol-role")
empty_roles = copy.deepcopy(parsed)
empty_roles[3][0][2] = []
run("protocol-admit",
    text=encode(empty_roles), refuses="interactive-admission")

# Source locations must survive JSON vector growth, nested body construction,
# and interleaved kinds of declarations. Changing unrelated text cannot move
# an error to the start of the module or to an unrelated instance.
for nesting in (0, 3):
    for padding in (0, 1, 17):
        body = 'return (absent);' if not nesting else 'yield (absent);'
        for level in range(nesting):
            body = (f'loop [l{level}] 1 carry () -> () {{\n{body}\n}}\n'
                    + ('return ();' if level == nesting - 1 else 'yield ();'))
        broken = ('module {\nprotocol Broken {\nroles (P);\n'
                  + body + '\n}\n'
                  + ''.join(f'fn F{i}() -> () external;\n'
                                f'protocol Z{i} {{ roles (P); external; }}\n'
                            for i in range(padding)) + '}')
        expected_line = next(i for i, line in enumerate(broken.splitlines(), 1)
                             if '(absent)' in line)
        diagnostic = run("protocol-source", text=broken, refuses="source-name-unresolved")
        assert f'-:{expected_line}:1:' in diagnostic.stderr, diagnostic.stderr
cycle = '''module {
protocol A { roles (P); dependencies (b: B()); invoke [ab] b() -> (); return (); }
protocol B { roles (P); dependencies (a: A()); invoke [ba] a() -> (); return (); }
protocol Z { roles (P); return (); }
instance z: Z { roles (P = P); }
entry main = z;
}'''
diagnostic = run("protocol-source", text=cycle, refuses="interactive-call-cycle")
assert '-:2:1:' in diagnostic.stderr, diagnostic.stderr

# New authoring boundary: missing references/types/requirements are editing
# states. Formatting must retain their tokens/comments and still reject them
# at the admission wrapper. JSON-to-text retains its admitted-only contract.
edits = [
    (relay.replace("Identity(input-value)", "Missing(input-value)"),
     "source-name-unresolved"),
    (relay.replace("Identity(input-value)", "Identity(absent)"),
     "source-name-unresolved"),
    (relay.replace("outputs (Checker field);", "outputs (Checker unknown);"),
     "source-name-unresolved"),
    ('''module {
          fn Fold<F: domain Field>(a: Table<F>, r: F::Element) -> (Table<F>) {
            let b = poly::fold::<F>(a, r); // missing public requirement
            return (b);
          }
        }''', "generic-public-requirement"),
    ('''module { fn Bad<>() -> () {
          uninstalled::<>(); /* preserve the unknown operation */
          return ();
        } }''', "source-name-unresolved"),
]
for editing, code in edits:
    pretty = run("protocol-format", text=editing).stdout
    assert run("protocol-format", text=pretty).stdout == pretty
    run("protocol-source", text=editing, refuses=code)
    run("protocol-source", text=pretty, refuses=code)
assert "// missing public requirement" in run("protocol-format", text=edits[3][0]).stdout
assert "/* preserve the unknown operation */" in run("protocol-format", text=edits[4][0]).stdout
bad_json = copy.deepcopy(parsed)
bad_json[3][0][7][0][3] = "Missing"
run("protocol-format", text=encode(bad_json), refuses="interactive-local-symbol")

# Independently written expected records cover every site-bearing grammar
# production, zero/multiple outputs and declared roles beyond P/V. Reserve
# labels even in future nested blocks, decoded from quoted spellings.
anonymous = r'''module {
      bind guard = control.require();
      bind commit = curve.commit(bls12-381.g1);
      fn Guard(x: bool) -> () { guard(x); return (); }
      fn Commit(b: Vector<"bls12-381.g1"::Element>, n: Nonce<"bls12-381.fr">)
          -> (Vector<"bls12-381.g1"::Element>, Nonce<"bls12-381.fr">) {
        let (p, ready) = commit(b, n); return (p, ready);
      }
      fn Pair(x: bool, y: bool) -> (bool, bool) { return (x, y); }
      protocol Leaf {
        roles (Alice); inputs (Alice x: bool, Alice y: bool);
        outputs (Alice bool, Alice bool);
        local Alice: let (a, b) = Pair(x, y); return (a, b);
      }
      protocol Root {
        roles (Alice, Bob, Checker);
        inputs (Alice x: bool, Alice y: bool,
                Alice bases: Vector<"bls12-381.g1"::Element>, Alice nonce: Nonce<"bls12-381.fr">);
        outputs (Alice Vector<"bls12-381.g1"::Element>, Alice Nonce<"bls12-381.fr">);
        dependencies (child: Leaf());
        local Alice: Guard(x);
        local Alice: let (p, ready) = Commit(bases, nonce);
        invoke child(x, y) -> (a, b);
        message flag: Alice(a) -> Bob(v);
        message flag: Bob(v) -> Checker(w);
        loop 1 carry () capture (x) -> () {
          local [__site_0] Alice: Guard(x);
          loop 0 carry () capture (x) -> () {
            local ["__site_\u0031"] Alice: Guard(x);
            local Alice: Guard(x);
            yield ();
          }
          yield ();
        }
        return (p, ready);
      }
      protocol Halt { roles (Checker); stop Checker reject; }
      instance leaf: Leaf { roles (Alice = Alice); }
      instance root: Root {
        dependencies (child = leaf);
        roles (Alice = Alice, Bob = Bob, Checker = Checker);
      }
      entry main = root;
    }'''
resolved = json.loads(run("protocol-source", text=anonymous).stdout)
assert resolved[0] == "zkc.protocol/1"
assert resolved[2][0][4][0] == ["op", "__site_0", "guard", [], ["x"], []]
assert resolved[2][1][4][0] == ["op", "__site_0", "commit", [], ["b", "n"], ["p", "ready"]]
assert resolved[3][0][7][0] == ["local", "__site_0", "Alice", "Pair", ["x", "y"], ["a", "b"]]
assert resolved[3][1][7] == [
    ["local", "__site_2", "Alice", "Guard", ["x"], []],
    ["local", "__site_3", "Alice", "Commit", ["bases", "nonce"], ["p", "ready"]],
    ["call", "__site_4", "child", ["x", "y"], ["a", "b"]],
    ["message", "__site_5", "flag", "Alice", "Bob", "a", "v"],
    ["message", "__site_6", "flag", "Bob", "Checker", "v", "w"],
    ["loop", "__site_7", ["constant", "1"], [], ["x"], [
        ["local", "__site_0", "Alice", "Guard", ["x"], []],
        ["loop", "__site_8", ["constant", "0"], [], ["x"], [
            ["local", "__site_1", "Alice", "Guard", ["x"], []],
            ["local", "__site_9", "Alice", "Guard", ["x"], []],
            ["yield", []]], []],
        ["yield", []]], []],
    ["return", ["p", "ready"]],
]
assert resolved[3][2][7] == [["stop", "__site_0", "Checker", "reject"]]
pretty = run("protocol-format", text=anonymous).stdout
assert '["__site_\\u0031"]' in pretty  # retain the original token spelling
assert "[__site_2]" not in pretty  # text formatting leaves anonymous sites implicit
assert json.loads(run("protocol-source", text=pretty).stdout) == resolved
inspectable = run("protocol-format", text=encode(resolved)).stdout
assert "[__site_9]" in inspectable  # carrier inspection exposes generated names
assert json.loads(run("protocol-source", text=inspectable).stdout) == resolved
perturbations = [
    anonymous.replace("module {", "module { fn __site_2() -> () { return (); }", 1),
    anonymous.replace("protocol Leaf", "protocol Unrelated { roles (Z); stop [__site_2] Z reject; } protocol Leaf"),
    anonymous.replace("entry main", "// unrelated comment __site_2\nentry main"),
]
for changed in perturbations:
    carrier = json.loads(run("protocol-source", text=changed).stdout)
    actual_root = next(p for p in carrier[3] if p[1] == "Root")
    assert actual_root == resolved[3][1]
duplicate = anonymous.replace('["__site_\\u0031"]', '[__site_0]')
run("protocol-source", text=duplicate, refuses="interactive-site")
run("protocol-format", text=duplicate)
# Names outside the site namespace (including a later selector) cannot cause
# the site they refer to to be renamed during parsing.
generic_effects = '''module {
      fn Guard<>(x: bool) -> () { control::require::<>(x); return (); }
      fn Commit<G: domain Group>(bases: Vector<G::Element>, nonce: Nonce<G::Scalar>)
          -> (Vector<G::Element>, Nonce<G::Scalar>) requires (ScalarAction(G)) {
        let (points, ready) = curve::commit::<G>(bases, nonce);
        return (points, ready);
      }
    }'''
effects = json.loads(run("protocol-source", text=generic_effects).stdout)
assert effects[1][0][6][0] == ["op", "__site_0", "control.require", [], [], ["x"], []]
assert effects[1][1][6][0] == ["op", "__site_0", "curve.commit", ["G"], [],
                             ["bases", "nonce"], ["points", "ready"]]
assert json.loads(run("protocol-source", text=run("protocol-format", text=encode(effects)).stdout).stdout) == effects
generic_anonymous = '''module {
      fn Fold<F: domain Field>(a: Table<F>, r: F::Element) -> (Table<F>)
          requires (CommRing(F)) {
        let b = poly::fold::<F>(a, r); return (b);
      }
      configure Partial = Fold();
      configure Fast = Partial(F = bls12-381.fr) using (__site_0 = "arkworks-msb/poly.fold");
      configure Alias = Fast();
      protocol Calls {
        roles (Researcher);
        inputs (Researcher a: Table<"bls12-381.fr">, Researcher r: "bls12-381.fr"::Element);
        outputs (Researcher Table<"bls12-381.fr">, Researcher Table<"bls12-381.fr">);
        local Researcher: let x = Fast(a, r);
        local Researcher: let y = Alias(a, r);
        return (x, y);
      }
      instance calls: Calls { roles (Researcher = Researcher); }
      entry main = calls;
    }'''
library = json.loads(run("protocol-source", text=generic_anonymous).stdout)
assert library[1][0][6][0] == ["op", "__site_0", "poly.fold", ["F"], [], ["a", "r"], ["b"]]
assert library[3][3][0][7][0][1] == "__site_0"
assert library[3][3][0][7][1][1] == "__site_1"
run("protocol-source", text=generic_anonymous.replace("using (__site_0", "using (__site_1"),
    refuses="generic-implementation-site")
shared = json.loads(run("protocol-export", text=run("protocol-import", text=generic_anonymous).stdout).stdout)
assert len(shared[2]) == 1
assert shared[3][0][7][0][3] == shared[3][0][7][1][3]
assert shared[3][0][7][0][1] != shared[3][0][7][1][1]
# An unrelated explicit label must leave specialization bodies/bindings
# unchanged: the old file-global reservation perturbed their code keys.
unrelated = generic_anonymous.replace("protocol Calls", "protocol Unused { roles (Z); stop [__site_0] Z reject; } protocol Calls")
again = json.loads(run("protocol-export", text=run("protocol-import", text=unrelated).stdout).stdout)
assert again[1:3] == shared[1:3]

negatives = [
    ("", "source-syntax"),
    ("module", "source-syntax"),
    ('module {', "source-syntax"),
    ('module {} trailing', "source-syntax"),
    ("@", "source-character"),
    ('module "bad', "source-string"),
    ('module "bad\\q" {}', "source-string"),
    ("/* unterminated", "source-comment"),
    ("/*" * 65 + "*/" * 65, "source-depth"),
    (" " * (1024 * 1024 + 1), "byte-limit"),
    (relay.replace("roles (Alice, Bob, Checker);", "roles (Alice); roles (Bob);"),
     "source-duplicate"),
    (relay.replace("roles (Alice, Bob, Checker);", ""), "source-syntax"),
    (relay.replace("roles (Alice=Alice, Bob=Bob, Checker=Checker);", ""),
     "source-syntax"),
    (relay.replace("outputs (Checker field);", "outputs (Checker unknown);"),
     "source-name-unresolved"),
    ('construction main { producer P; producer V; }', "source-duplicate"),
    ('construction main {}', "source-syntax"),
    ('construction main { accept 00; }', "source-number"),
]
for text, code in negatives:
    with case(f"malformed source refused as {code}"):
        run("protocol-source", text=text, refuses=code)
        if (code.startswith("source-") and code not in ("source-type", "source-name-unresolved")) or code == "byte-limit":
            run("protocol-format", text=text, refuses=code)

# Printer shape guards: malformed public descriptors must not reach indexed
# array access. Profile/context validation still belongs to construction.
descriptor = json.loads((examples / "dleq.construction.json").read_text())
malformed = [None, {}, [], ["unknown"], ["zkc.construction/1"]]
for index in range(1, 9):
    mutation = copy.deepcopy(descriptor)
    mutation[index] = None
    malformed.append(mutation)
for value in malformed:
    with case(f"printer refuses malformed descriptor {value!r:.40}"):
        result = commands.attempt([compiler, "protocol-format", "-"],
                                  stdin=encode(value), timeout=20)
        assert result.returncode == 1, (value, result.stderr)
        assert not result.stdout

# JSON descriptors obey the same list bound as the text parser. A printer
# must not report success for a descriptor its own reader cannot consume.
for target in ("draws", "public", "ports"):
    oversized = copy.deepcopy(descriptor)
    pairs = [["A", "s"]] * 32769
    if target == "draws":
        oversized[5][1] = pairs
    elif target == "public":
        oversized[4] = [["label", []]] * 32769
    else:
        oversized[4][0][1] = pairs
    # Typed decoding now rejects this malformed list before printing.
    run("protocol-format", text=encode(oversized), refuses="interactive-shape")
    if target == "draws":
        oversized[5][1].pop()
    elif target == "public":
        oversized[4].pop()
    else:
        oversized[4][0][1].pop()
    boundary = run("protocol-format", text=encode(oversized)).stdout
    assert json.loads(run("protocol-source", text=boundary).stdout) == oversized

# Escapes in public labels round-trip as values; they do not become source
# names or code. Attribute strings remain exact, including decimal spelling.
unusual = copy.deepcopy(descriptor)
unusual[4][0][0] = '한글 "label" \\ path\nnext'
readable = run("protocol-format", text=encode(unusual)).stdout
assert json.loads(run("protocol-source", text=readable).stdout) == unusual
for label in (r'\ud800', r'\udfff', r'\ud800\u0061', r'\ud800\ud800'):
    with case(f"lone surrogate {label} is refused"):
        invalid = readable.replace(json.dumps(unusual[4][0][0], ensure_ascii=False),
                                   '"' + label + '"')
        run("protocol-source", text=invalid, refuses="source-string")
for spelling, expected in ((r'\ud83d\ude00', '😀'), (r'\\ud800', r'\ud800')):
    valid = readable.replace(json.dumps(unusual[4][0][0], ensure_ascii=False),
                             '"' + spelling + '"')
    assert json.loads(run("protocol-source", text=valid).stdout)[4][0][0] == expected
raw_invalid = readable.encode().replace('한글'.encode(), b'\xff')
invalid = commands.attempt([compiler, 'protocol-source', '-'], stdin=raw_invalid,
                           text=False, timeout=20)
assert invalid.returncode == 1 and b'source-string' in invalid.stderr

# Fixed-seed formatting mutations independently exercise legal whitespace,
# trailing commas and comment placement without changing source records.
rng = random.Random(42)
for iteration in range(40):
    changed = relay
    for delimiter in (";", "{", "}", ","):
        if rng.choice((True, False)):
            changed = changed.replace(delimiter, delimiter + f" /* edit {iteration} */\n")
    formatted = run("protocol-format", text=changed).stdout
    assert json.loads(run("protocol-source", text=formatted).stdout) == parsed
    assert run("protocol-format", text=formatted).stdout == formatted

# Whitespace expansion must not produce an unreadable file. Both the input
# and its normalized JSON fit the limits, but canonical indentation does not.
comments = "/*" + "x" * 66 + "*/"
large = 'module {' + comments * 14500 + '}'
run("protocol-source", text=large)
run("protocol-format", text=large, refuses="source-limit")

# Sampled suffix truncations must terminate; any surviving complete document
# must retain the original source. This also covers lexer EOF error paths.
for end in range(0, len(relay), 7):
    result = commands.attempt([compiler, "protocol-source", "-"],
                              stdin=relay[:end], timeout=20)
    assert result.returncode in (0, 1), result.stderr
    if result.returncode == 0:
        assert json.loads(result.stdout) == parsed
    else:
        assert not result.stdout

# Bounded elaboration compares independently authored explicit substitutions,
# including sites, callable categories and ordered public assumptions.
def common(text):
    return json.loads(run("protocol-source", text=text).stdout)


def equivalent(inferred, explicit):
    actual = common(inferred)
    assert actual == common(explicit)
    assert common(run("protocol-format", text=encode(actual)).stdout) == actual
    return actual


inferred = '''module {
  fn Four<F: Field>(x: F::Element) -> F::Element {
    [first] let y = Twice(x);
    [second] let z = Twice(y);
    return z;
  }
  fn Twice<F: Field>(x: F::Element) -> F::Element {
    [sum] let y = field::add(x, x); return y;
  }
}'''
explicit = '''module {
  fn Four<F: domain Field>(x: F::Element) -> F::Element requires (Field(F)) {
    [first] let y = Twice::<F>(x);
    [second] let z = Twice::<F>(y);
    return z;
  }
  fn Twice<F: domain Field>(x: F::Element) -> F::Element requires (Field(F)) {
    [sum] let y = field::add::<F>(x, x); return y;
  }
}'''
record = equivalent(inferred, explicit)
assert record[1][0][6][0] == ["apply", "first", "Twice", ["F"], ["x"], ["y"]]
assert record[1][1][6][0] == ["op", "sum", "field.add", ["F"], [], ["x", "x"], ["y"]]

# Syntax inspection never fabricates common records or inferred arguments.
syntax = json.loads(run("protocol-parse", text=inferred).stdout)
assert syntax["kind"] == "syntax-inspection" and syntax["format"] == "pir-text"
call = syntax["content"]["functions"][0]["body"][0]
assert call["kind"] == "unresolved-call" and call["callee"] == "Twice"
assert call["staticArguments"] is None and call["outputs"] == ["y"]
unknown = inferred.replace("Twice(x)", "NotInstalled(x)")
assert json.loads(run("protocol-parse", text=unknown).stdout)["content"]["functions"][0]["body"][0]["callee"] == "NotInstalled"
run("protocol-format", text=unknown)
run("protocol-source", text=unknown, refuses="source-name-unresolved")
explicit_syntax = json.loads(run("protocol-parse", text=explicit).stdout)
assert explicit_syntax["content"]["functions"][0]["body"][0]["staticArguments"] == ["F"]

constant = '''module {
  fn One<F: Field>() -> F::Element {
    let one: F::Element = field::constant() attributes (1); return one;
  }
}'''
equivalent(constant, '''module {
  fn One<F: Field>() -> F::Element {
    let one = field::constant::<F>() attributes (1); return one;
  }
}''')
run("protocol-source", text=constant.replace(": F::Element =", " ="),
    refuses="source-static-unresolved")
run("protocol-source", text=constant.replace("let one: F::Element =", "let one: bool ="),
    refuses="source-type-mismatch")

# Complete tuple annotations preserve arity; unused parameters still need statics.
pair = '''module {
  fn Pair<F: domain Field>(x: bool) -> (bool, bool) { return (x, x); }
  fn Use<F: domain Field>(x: bool) -> (bool, bool) {
    let (a, b): (bool, bool) = Pair::<F>(x); return (a, b);
  }
}'''
common(pair)
run("protocol-source", text=pair.replace("Pair::<F>(x)", "Pair(x)"),
    refuses="source-static-unresolved")
run("protocol-source", text=pair.replace("(a, b): (bool, bool)", "(a, b): bool"),
    refuses="source-annotation-arity")

# Kind-only declarations cannot acquire body-derived assumptions. Bounds are
# stored in header / where / requires order, including intentional duplicates.
weak = '''module { fn Id<F: domain Field>(x: F::Element) -> F::Element { return x; } }'''
assert common(weak)[1][0][3] == []
strong = common(weak.replace("domain Field", "TwoAdicField"))
assert strong[1][0][3] == [["TwoAdicField", ["F"]]]
ordered = '''module {
  fn Id<F: TwoAdicField, G: ScalarAction>(x: F::Element) -> F::Element
      where G::Scalar: Field, F: PrimeField
      requires (Field(F), Field(F)) { return x; }
}'''
assert common(ordered)[1][0][3] == [
    ["TwoAdicField", ["F"]], ["ScalarAction", ["G"]],
    ["Field", ["G.Scalar"]], ["PrimeField", ["F"]],
    ["Field", ["F"]], ["Field", ["F"]],
]
run("protocol-source", text=inferred.replace("F: Field", "F: domain Field"),
    refuses="generic-public-requirement")

associated = '''module {
  fn Scalar<G: ScalarAction>(x: G::Scalar::Element) -> G::Scalar::Element { return x; }
  fn Use<G: ScalarAction>(x: G::Scalar::Element) -> G::Scalar::Element {
    let y = Scalar::<G>(x); return y;
  }
}'''
common(associated)
run("protocol-source", text=associated.replace("Scalar::<G>(x)", "Scalar(x)"),
    refuses="source-static-unresolved")
associated_add = '''module {
  fn Add<G: ScalarAction>(x: G::Scalar::Element) -> G::Scalar::Element
      where G::Scalar: Field {
    let y = field::add(x, x); return y;
  }
}'''
equivalent(associated_add, associated_add.replace("field::add(x", "field::add::<G::Scalar>(x"))

partial = '''module {
  fn Id<F: domain Field, G: domain Group>(x: F::Element) -> F::Element { return x; }
  configure Partial = Id(G = "bls12-381.g1");
  fn Use<F: domain Field>(x: F::Element) -> F::Element {
    let y = Partial(x); return y;
  }
}'''
equivalent(partial, partial.replace("Partial(x)", "Partial::<F>(x)"))
run("protocol-source", text=partial.replace("Partial(x)", 'Partial::<F, "bls12-381.g1">(x)'),
    refuses="generic-static-arity")

# Ordinary functions, bound operations, generic operations, helpers and empty
# generic definitions retain their categories, including zero-result guards.
closed = '''module {
  bind both = bool::and();
  fn Use(x: bool) -> bool { let y = Identity(x); let z = both(x, y); return z; }
  fn Identity(x: bool) -> bool { return x; }
  fn Guard<>(x: bool) -> () { control::require(x); return; }
}'''
categories = common(closed)
assert categories[3][2][0][4][0][0] == "apply"
assert categories[3][2][0][4][1][0] == "op"
assert categories[1][0][6][0] == ["op", "__site_0", "control.require", [], [], ["x"], []]
run("protocol-source", text=closed.replace("let y = Identity(x);", "Identity(x);").replace("both(x, y)", "both(x, x)"),
    refuses="source-call-arity")
# Unit is a source value, even when its PIR layout has no leaves.
assert common(closed.replace("control::require(x);", "let y = control::require(x);")) == categories
run("protocol-source", text=closed.replace("let y = Identity(x);", "let x = Identity(x);").replace("both(x, y)", "both(x, x)"),
    refuses="source-value-duplicate")
run("protocol-source", text=inferred.replace("let z = Twice(y)", "let y = Twice(y)").replace("return z", "return y"),
    refuses="source-value-duplicate")
run("protocol-source", text=closed.replace("fn Identity(x", "fn Use(x"),
    refuses="source-duplicate-symbol")
# The encoded record's view of the choice; frontend_elaboration.py checks the
# same choice as the elaboration report's `kind`, and owns the format roundtrip
# over the quoted spellings.
primitive = common(COLLISION)
assert primitive[1][1][6][0][0] == "op"
helper = common(COLLISION.replace("bool::and(x, x)", '\"bool.and\"(x, x)'))
assert helper[1][1][6][0][0] == "apply"

conflict = '''module {
  fn Bad<F: Field, E: Field>(x: F::Element, y: E::Element) -> F::Element {
    let z = field::add(x, y); return z;
  }
}'''
run("protocol-source", text=conflict, refuses="source-static-conflict")
run("protocol-source", text=conflict.replace("field::add(x, y)", "field::add::<F>(x, y)"),
    refuses="source-static-conflict")

# Inference cannot copy consumed resources or insert implicit cleanup.
affine = '''module {
  fn Draw<F: Field>(rng: Rng<F>) -> (F::Element, Rng<F>) {
    let (n, next) = random::draw(rng); return (n, next);
  }
}'''
equivalent(affine, affine.replace("random::draw(rng)", "random::draw::<F>(rng)"))
run("protocol-source", text=affine.replace("return (n, next);",
    "let (again, last) = random::draw(rng); return (again, last);"),
    refuses="generic-resource-reuse")
run("protocol-source", text=affine.replace("let (n, next) = random::draw(rng);", "random::draw(rng);").replace("return (n, next);", "return;"),
    refuses="source-call-arity")

# Obsolete syntax is refused, while nested types and unsupported tuple forms
# have independent controls rather than being silently interpreted differently.
for old in [
    'module { fn F<>() -> () { () = control.require<>(x); return (); } }',
    'module { fn F<F: domain Field>(x: field:F) -> () { return; } }',
    'module { fn F<>() -> () { let x = apply Helper<>(); return; } }',
]:
    run("protocol-format", text=old, refuses="source-syntax")
run("protocol-source", text='module { fn F<F: Field>(x: Vector<Vector<F::Element>>) -> () { return; } }',
    refuses="source-type")

# An annotation supplies the extension itself; the base projection alone must
# never be inverted, nor may an extension conversion appear implicitly.
embedding = '''module {
  fn Embed<E: ExtensionField>(x: Vector<E::BaseField::Element>) -> Vector<E::Element> {
    let y: Vector<E::Element> = vector::embed(x); return y;
  }
}'''
equivalent(embedding, embedding.replace("let y: Vector<E::Element> = vector::embed(x)",
                                      "let y = vector::embed::<E>(x)"))
run("protocol-source", text=embedding.replace("let y: Vector<E::Element>", "let y"),
    refuses="source-static-unresolved")
no_conversion = '''module {
  fn Id<E: ExtensionField>(x: Vector<E::Element>) -> Vector<E::Element> { return x; }
  fn Use<E: ExtensionField>(x: Vector<E::BaseField::Element>) -> Vector<E::Element> {
    let y = Id::<E>(x); return y;
  }
}'''
run("protocol-source", text=no_conversion, refuses="source-static-conflict")

# Tuple expected types solve two independent holes in a forward helper call.
tuple_expected = '''module {
  fn Use<F: Field, G: Field>() -> (F::Element, G::Element) {
    let (a, b): (F::Element, G::Element) = Pair(); return (a, b);
  }
  fn Pair<F: Field, G: Field>() -> (F::Element, G::Element) {
    let a = field::constant::<F>() attributes (1);
    let b = field::constant::<G>() attributes (2); return (a, b);
  }
}'''
equivalent(tuple_expected, tuple_expected.replace(
    "let (a, b): (F::Element, G::Element) = Pair()", "let (a, b) = Pair::<F, G>()"))
run("protocol-source", text=tuple_expected.replace(
    "let (a, b): (F::Element, G::Element)", "let (a, b)"), refuses="source-static-unresolved")
run("protocol-source", text=tuple_expected.replace(
    "Pair()", "Pair::<F>()"), refuses="generic-static-arity")

strong_helper = '''module {
  fn Strong<F: PrimeField>(x: F::Element) -> F::Element { return x; }
  fn Weak<F: Field>(x: F::Element) -> F::Element { let y = Strong(x); return y; }
}'''
run("protocol-source", text=strong_helper, refuses="generic-public-requirement")
equivalent(strong_helper.replace("Weak<F: Field>", "Weak<F: PrimeField>"),
           strong_helper.replace("Weak<F: Field>", "Weak<F: PrimeField>").replace("Strong(x)", "Strong::<F>(x)"))

# A result cannot be used to infer a previous unannotated nullary call.
run("protocol-source", text=constant.replace("let one: F::Element", "let one").replace(
    "return one;", "let two: F::Element = field::add(one, one); return two;"),
    refuses="source-static-unresolved")

nonce = '''module {
  fn Respond<F: Field>(x: F::Element, c: F::Element, n: Nonce<F>) -> F::Element {
    let y = curve::response(x, c, n); return y;
  }
}'''
equivalent(nonce, nonce.replace("curve::response(x", "curve::response::<F>(x"))
run("protocol-source", text=nonce.replace("return y;",
    "let z = curve::response(x, c, n); return z;"), refuses="generic-resource-reuse")
# Affine permits an unused value; retaining a binding is different from silently
# discarding a call's results or synthesizing a cleanup operation.
unused = common(affine.replace("-> (F::Element, Rng<F>)", "-> ()").replace("return (n, next);", "return;"))
assert len(unused[1][0][6]) == 2
assert unused[1][0][6][0][2] == "random.draw"

# A protocol-local generic call must have a named closed configuration.
local_generic = '''module {
  fn Id<F: domain Field>(x: F::Element) -> F::Element { return x; }
  configure Closed = Id(F = "koala-bear");
  protocol P { roles (A); inputs (A x: "koala-bear"::Element);
    outputs (A "koala-bear"::Element); local A: let y = Closed(x); return y; }
}'''
common(local_generic)
run("protocol-source", text=local_generic.replace("Closed(x)", "Id(x)"),
    refuses="source-local-configuration")
run("protocol-source", text=local_generic.replace('Id(F = "koala-bear")', "Id()"),
    refuses="source-local-configuration")
# Category errors do not fall back to an installed primitive.
run("protocol-source", text='''module {
  fn Plain(x: bool) -> bool { return x; }
  fn Generic<>(x: bool) -> bool { let y = Plain(x); return y; }
}''', refuses="generic-call-target")
run("protocol-source", text=closed.replace("Identity(x);", "Identity::<>(x);", 1))
run("protocol-source", text=closed.replace("Identity(x);", 'Identity::<"koala-bear">(x);', 1),
    refuses="generic-static-arity")

# Source locations point to the failing call, not the enclosing declaration.
conflicting = inferred.replace("[first] let y = Twice(x);", "[first] let y: bool = Twice(x);")
error = run("protocol-source", text=conflicting, refuses="source-type-mismatch")
assert "-:3:" in error.stderr and "let y: bool" in error.stderr

# Common JSON inspection is tagged too; it is never confused with admission.
json_inspection = json.loads(run("protocol-parse", text=encode(record)).stdout)
assert json_inspection["kind"] == "syntax-inspection"
assert json_inspection["format"] == "common-source-json"

# Inspection explains the same resolved calls without converting their kinds.
report = json.loads(run("protocol-inspect", text=inferred).stdout)
assert [(c["kind"], c["static_arguments"], c["static_origin"]) for c in report["elaborated_calls"]] == [
    ("algorithm", ["F"], "inferred"), ("algorithm", ["F"], "inferred"),
    ("operation", ["F"], "inferred"),
]
assert report["elaborated_calls"][0]["results"] == [{"name": "y", "type": "field:F"}]
assert report["definitions"][0]["declared"] == [["Field", ["F"]]]
written_report = json.loads(run("protocol-inspect", text=explicit).stdout)
assert all(c["static_origin"] == "written" for c in written_report["elaborated_calls"])
run("protocol-source", text=inferred.replace("Twice(x)", "Twice(x) attributes (1)"),
    refuses="algorithm-call-syntax")
run("protocol-source", text=pair.replace("Pair::<F>(x)", 'Pair::<"bls12-381.g1">(x)'),
    refuses="source-generic-term")

# Closed bound operation attributes are distinct from statics and runtime args;
# opaque function/domain names retain their periods exactly.
attribute = '''module {
  bind constant = field::constant("koala-bear");
  fn "custom.name"() -> "koala-bear"::Element {
    let one = constant() attributes ("1"); return one;
  }
}'''
attribute_record = common(attribute)
assert attribute_record[2][0][1] == "custom.name"
assert attribute_record[2][0][4][0][3] == ["1"]
assert common(run("protocol-format", text=encode(attribute_record)).stdout) == attribute_record
noncanonical_attribute = attribute.replace('attributes ("1")', 'attributes ("01")')
assert '"01"' in run("protocol-format", text=noncanonical_attribute).stdout
run("protocol-source", text=noncanonical_attribute, refuses="noncanonical-natural")

# Formatting uses the syntax budget even for semantically unsupported nesting.
for depth in (64, 65):
    nested_type = "Vector<" * depth + "F::Element" + ">" * depth
    nested_source = f"module {{ fn Deep<F: Field>(x: {nested_type}) -> () {{ return; }} }}"
    if depth == 64:
        formatted = run("protocol-format", text=nested_source).stdout
        assert run("protocol-format", text=formatted).stdout == formatted
        run("protocol-source", text=nested_source, refuses="source-type")
    else:
        run("protocol-format", text=nested_source, refuses="source-depth")
        run("protocol-source", text=nested_source, refuses="source-depth")

# Public contracts and origins cannot be accepted and then dropped at the
# ordinary/generic common-model category boundary.
run("protocol-source", text='''module {
  fn Plain() -> () requires (Field("koala-bear")) { return; }
}''', refuses="source-function-contract")
run("protocol-source", text='''module {
  fn Generic<>() -> () origin Original() { return; }
}''', refuses="source-function-origin")

help_result = commands.attempt([compiler, "--help"])
assert "protocol-format" in help_result.stdout
print(f"frontend: {commands.save()} command checks, including the malformed-shape and truncation controls")
