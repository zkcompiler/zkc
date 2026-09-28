"""Standalone parser/formatter regressions."""

import json

from commands import Commands
from source_text import unlocated
from tools import records

commands = Commands(records())


def run(command, text, refuses=None):
    """What the compiler printed, which a refusal leaves empty."""
    return commands.source(command, text, refuses=refuses)


def parse(text):
    return unlocated(json.loads(run("protocol-parse", text))["content"])


def roundtrip(text):
    original = parse(text)
    formatted = run("protocol-format", text)
    assert parse(formatted) == original
    assert run("protocol-format", formatted) == formatted
    return original


# EOF ends only the implicit file scope. Empty text and comments are modules.
for empty in ("", "// only a comment\n", "/* empty */"):
    roundtrip(empty)
for unfinished in ("}", "fn X() -> () {", "struct X { value: bool"):
    run("protocol-parse", unfinished, "source-syntax")

# Quoted spellings remain names, never declaration/instruction/clause keywords.
for tag, rest in (
    ("fn", "X() -> () { return; }"),
    ("bind", "b = bool::and();"),
    ("configure", "C = X();"),
    ("protocol", "P { roles (A); }"),
    ("instance", "I: P { roles (A = Alice); }"),
    ("entry", "E = I;"),
):
    run("protocol-parse", f' "{tag}" {rest} ', "source-syntax")
for instruction in (
    '"local" A: f();', '"message" S: A(x) -> B(y);',
    '"invoke" P() -> ();', '"stop" A reason;',
    '"loop" 1 carry () -> () { yield; }', '"return";', '"yield";',
):
    run("protocol-parse", f' protocol P {{ roles (A, B); {instruction} }} ',
        "source-syntax")
for header in ('"roles" (A);', 'roles (A); "inputs" (A x: bool);',
               'roles (A); "outputs" (A bool);',
               'roles (A); "parameters" (n);', 'roles (A); "dependencies" ();'):
    run("protocol-parse", f' protocol P {{ {header} }} ', "source-syntax")
for key, value in (("roles", "(A = Alice)"), ("parameters", "(n = 1)"),
                   ("dependencies", "(D = I)")):
    run("protocol-parse", f' instance I: P {{ "{key}" {value}; }} ',
        "source-syntax")
construction = ('construction E { producer A; validator B; suite S; '
                'accept 0; random R at (); public x = (); }')
for key in ("producer", "validator", "suite", "accept", "random", "public"):
    run("protocol-parse", construction.replace(key, f'"{key}"', 1), "source-syntax")
for text in ('"module" {}', '"construction" E {}',
             ' fn X() -> () "external"; ',
             ' fn X() -> () "origin" X() external; ',
             ' fn X() -> () "requires" () external; '):
    run("protocol-parse", text, "source-syntax")
# A quoted statement keyword is an exact string, not a statement or name.
run("protocol-parse", ' fn X() -> () { "let" x = X(); } ', "source-identifier")
quoted = roundtrip('''
  fn r#fn(r#return: bool) -> bool {
    let r#let = r#return(r#return); return r#let;
  }
  protocol r#protocol { roles (r#roles); local r#roles: r#local(); }
  instance r#instance: r#protocol { roles (r#roles = r#external); }
  entry r#entry = r#instance;
''')
assert quoted["functions"][0]["body"][0]["callee"] == "return"
assert quoted["protocols"][0]["body"][0]["callee"] == "local"

# Path separators and turbofish are token grammar, independent of whitespace
# and comments. A turbofish alone does not make an unqualified call qualified.
for callee, qualified in (("Twice", False), ("field::add", True)):
    baseline = None
    for separator in ("::<", ":: <", " ::<", "::/*c*/<",
                      "/*before*/ :: // after\n <"):
        text = ('fn X<F: Field>(x: F::Element) -> F::Element { '
                f'let y = {callee}{separator}F /*arg*/ :: /*member*/ Scalar>(x); '
                'return y; }')
        content = roundtrip(text)
        call = content["functions"][0]["body"][0]
        assert call["qualified"] == qualified
        assert call["staticArguments"] == ["F::Scalar"]
        if baseline is None:
            baseline = content
        assert content == baseline
run("protocol-parse", ' fn X() -> () { X<F>(); } ', "source-syntax")

# A header keyword followed by a colon is a where subject, including after
# comments; a following header or body still permits an optional trailing comma.
for subject in ("requires", "origin", "external"):
    for spelling in (subject, "r#" + subject):
        for suffix in ("external;", "requires () external;",
                       "origin X() external;", "{ return; }"):
            text = (f' fn X<F: Field, {spelling}: Field>() -> () '
                    f'where F: Field, {spelling} /*colon*/ : PrimeField, {suffix} ')
            content = roundtrip(text)
            assert content["functions"][0]["requirements"][-1]["arguments"] == [subject]
    projected = (f' fn X<F: Field, {subject}: Group>() -> () '
                 f'where F: Field, {subject} /*path*/ :: Scalar: Field external; ')
    assert parse(projected)["functions"][0]["requirements"][-1]["arguments"] == [
        subject + "::Scalar"]
    declared = (f' fn X<F: Field, {subject}: Field>() -> () '
                f'where F: Field, {subject} /*colon*/ : PrimeField, {{ return; }} ')
    common = json.loads(run("protocol-source", declared))
    assert common[1][0][3][-1] == ["PrimeField", [subject]]

# Parentheses group a type/value; a trailing comma forms a product.
baseline = parse(' fn X(x: bool) -> bool { let y: bool = Y(x); return y; } ')
grouped = roundtrip(' fn X(x: bool) -> (bool) { let y: (bool) = Y(x); return (y); } ')
assert grouped == baseline
product = roundtrip(' fn X(x: bool) -> (bool,) { let (y,): (bool,) = Y(x); return (y,); } ')
assert product != baseline
assert product["functions"][0]["results"][0]["kind"] == "product-type"
singleton = (' fn X<F: Field>(x: F::Element) -> F::Element { let y: F::Element = zkc::algebra::add(x, x); return y; } ')
assert run("protocol-source", singleton) == run(
    "protocol-source", singleton.replace("-> F::Element", "-> (F::Element,)")
    .replace("let y: F::Element", "let (y,): (F::Element,)")
    .replace("return y;", "return (y,);"))

# Obsolete arbitrary names refuse; raw identifiers keep the decoded identity.
for text, code in (
    ('fn X<F-: Field>(x: F::Element) -> F::Element { return x; }', "source-syntax"),
    ('fn X<F: Field>(x-: F::Element) -> F::Element { return x-; }', "source-syntax"),
    ('fn "X"(x: bool) -> bool { return x; }', "source-identifier"),
    ('struct Flags(ready: bool);', "source-syntax"),
    ('struct Flags { ready: bool } fn X(x: bool) -> Flags { Flags(ready=x) }', "source-syntax"),
    ('module { fn X(x: bool) -> bool { return x; } }', "source-module-wrapper"),
):
    run("protocol-parse", text, code)
assert roundtrip('fn X<r#F: Field>(r#x: r#F::Element) -> r#F::Element '
                 '{ let r#y = Twice::<r#F>(r#x); return r#y; }') == parse(
    'fn X<F: Field>(x: F::Element) -> F::Element '
    '{ let y = Twice::<F>(x); return y; }')

# Long paths are iterative and share the existing 32768-member type-path cap.
for members in (1024, 32768):
    path = "F" + "::M" * members
    content = parse(f' fn X() -> () {{ {path}(); }} ')
    assert content["functions"][0]["body"][0]["callee"] == "F" + "::M" * members
for text in (
    'fn X() -> () { ' + 'F' + '::M' * 32769 + '(); }',
    'fn X() -> ' + 'F' + '::M' * 32769 + ' external;',
    'fn X() -> () { X(' + ','.join(['x'] * 32769) + '); }',
):
    run("protocol-parse", text, "source-limit")
run("protocol-parse", 'fn X() -> ' + 'Vec<' * 66 + 'bool' + '>' * 66
    + ' external;', "source-depth")

print(f"{commands.save()} parser/formatter checks passed")
