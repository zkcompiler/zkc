"""Authored names require lexical, declaration, or installed authority."""

import json
import re
from contextlib import contextmanager
from itertools import count

from cases import case, counted
from commands import Commands
from tools import compiler, records

root = records()
commands = Commands(root, timeout=30)
ids = count()


def identity(name):
    return f'library(namespace="authority", name="{name}", version="1", resolution="r1")'


@contextmanager
def project():
    folder = root / f"project-{next(ids)}"
    folder.mkdir()
    yield folder


def run(folder, source, libraries=None, files=None, refuses=None, mode="protocol-source", construction=None):
    def write(name, text):
        path = folder / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    app = write("app.pir", source)
    options = [f"--library={write(name, text)}" for name, text in (libraries or {}).items()]
    for name, text in (files or {}).items():
        write(name, text)
    descriptor = [write("construction.pir", construction)] if construction is not None else []
    result = commands.run([compiler, mode, app, *descriptor, *options], refuses=refuses)
    return json.loads(result) if result and mode in ("protocol-source", "protocol-analyze", "protocol-construct") else result


BITS = f'''module {{ {identity("bits")};
  fn Raw(x: bool) -> bool {{ return x; }}
  pub fn Keep(x: bool) -> bool {{ return Raw(x); }}
}}'''
def depending(source):
    """The same application, declaring the library it is captured with.

    Every captured library must be in the application's dependency closure,
    so a probe that a library's names stay out of reach declares it.
    """
    return source.replace("module {", f"module {{ dependency bits = {identity('bits')};", 1)


APP = f'''module {{ dependency bits = {identity("bits")};
  fn Main(x: bool) -> bool {{ return bits::Keep(x: x); }}
}}'''

with case("qualified ordinary calls preserve named ports"), project() as folder:
    run(folder, APP, {"bits/lib.pir": BITS}, mode="protocol-admit")

with case("crate self and super ordinary paths resolve callable targets"), project() as folder:
    run(folder, '''module { mod child;
      fn Keep(x: bool) -> bool { return x; }
      fn Main(x: bool) -> bool { return crate::child::Call(x: x); }
    }''', files={"child.pir": '''module {
      fn Local(x: bool) -> bool { return super::Keep(x: x); }
      pub fn Call(x: bool) -> bool { return self::Local(x: x); }
    }'''}, mode="protocol-admit")

with case("quoted foreign private symbols cannot be called"), project() as folder:
    report = run(folder, APP, {"bits/lib.pir": BITS}, mode="protocol-analyze")
    raw = next(d["symbol"] for d in report["resolved_declarations"] if d["display_name"] == "Raw")
    for spelling in (raw, json.dumps(raw)):
        run(folder, APP.replace("bits::Keep", spelling), {"bits/lib.pir": BITS},
            refuses="source-name-unresolved")

with case("a quoted private unchecked constructor cannot bypass its wrapper"), project() as folder:
    library = f'''module {{ {identity("bits")};
      pub checked struct Token(ok: bool) constructors(MintRaw);
      fn MintRaw(ok: bool) -> Token {{ return Token(ok = ok); }}
      pub fn Mint(ok: bool) -> Token {{ control::require(ok); return MintRaw(ok); }}
    }}'''
    app = f'''module {{ dependency bits = {identity("bits")}; use bits::{{Token, Mint}};
      fn Main(ok: bool) -> Token {{ return Mint(ok); }}
    }}'''
    report = run(folder, app, {"bits/lib.pir": library}, mode="protocol-analyze")
    assert report["state"] == "source_checked", report["diagnostics"]
    raw = next(d["symbol"] for d in report["resolved_declarations"] if d["display_name"] == "MintRaw")
    run(folder, app.replace("return Mint(ok)", f'return "{raw}"(ok)'),
        {"bits/lib.pir": library}, refuses="source-name-unresolved")

with case("closed checked functions never become authored flat call targets"), project() as folder:
    library = f'''module {{ {identity("bits")};
      pub interface I {{ local step(x: bool) -> bool; }}
      component C: I {{ local step(x: bool) -> bool {{ return x; }} }}
      fn Use<X: I>(x: bool) -> bool {{ return X::step(x); }}
      pub link Closed = Use<C>;
    }}'''
    app = APP.replace("bits::Keep", "bits::Closed")
    output = run(folder, app, {"bits/lib.pir": library})
    symbols = set(re.findall(r'(?:lib|client)_[0-9a-f]{64}', json.dumps(output)))
    assert symbols, output
    for symbol in sorted(symbols):
        for callee in (symbol, json.dumps(symbol)):
            run(folder, app.replace("bits::Closed", callee), {"bits/lib.pir": library},
                refuses="source-name-unresolved")

for category, body in (
    ("raw ordinary helper", "return AppOnly(x);"),
    ("raw prepared helper", "return Core_Products(x);"),
    ("foreign enum", "return Flag::On(x);"),
):
    with case(f"a library cannot bind the application's {category}"), project() as folder:
        library = BITS.replace("return Raw(x);", body)
        app = APP.replace("fn Main", "fn AppOnly(x: bool) -> bool { return x; }\n"
                          "enum Flag { On(bool) }\nfn Main")
        run(folder, app, {"bits/lib.pir": library}, refuses="source-name-unresolved")

with case("foreign raw protocol names cannot bind application protocols"), project() as folder:
    library = f'''module {{ {identity("bits")};
      pub protocol Caller {{ roles(A); inputs(A x: bool); outputs(A bool);
        dependencies(other: AppOnly()); invoke other(x) -> (y); return y;
      }}
    }}'''
    run(folder, depending("module { protocol AppOnly { roles(A); inputs(A x: bool); outputs(A bool); return x; } }"),
        {"bits/lib.pir": library}, refuses="source-name-unresolved")

with case("quoted nominal types do not import private declarations"), project() as folder:
    library = BITS.replace("fn Raw", "struct Hidden { bit: bool }\nfn Raw")
    report = run(folder, APP, {"bits/lib.pir": library}, mode="protocol-analyze")
    symbol = next(d["symbol"] for d in report["resolved_declarations"] if d["display_name"] == "Hidden")
    run(folder, APP.replace("fn Main(x: bool) -> bool", f'fn Main(x: "{symbol}") -> bool'),
        {"bits/lib.pir": library}, refuses="source-name-unresolved")

with case("installed operation modules refuse ambiguity before renaming"), project() as folder:
    run(folder, "module { mod field; fn F(x: koala-bear::Element) -> koala-bear::Element { return field::add(x, x); } }",
        files={"field.pir": "module { pub fn add(x: koala-bear::Element, y: koala-bear::Element) -> koala-bear::Element { return x; } }"},
        refuses="library-source-call-ambiguity")

with case("installed operation dependency aliases refuse ambiguity"), project() as folder:
    run(folder, APP.replace("bits =", "bool =").replace("bits::Keep(x: x)", "bool::not(x)"),
        {"bits/lib.pir": BITS}, refuses="library-source-call-ambiguity")

with case("explicit installed paths and exact dotted helper names retain their target kinds"), project() as folder:
    library = BITS.replace("fn Raw", 'fn "bool.not"(x: bool) -> bool { return x; }\nfn Raw').replace("return Raw(x)", "return bool::not(x)")
    primitive = run(folder, APP, {"bits/lib.pir": library})
    assert any(binding[1] == "bool.not" for binding in primitive[1]), primitive
    exact = run(folder, APP, {"bits/lib.pir": library.replace("bool::not(x)", '\"bool.not\"(x)')})
    assert not any(binding[1] == "bool.not" for binding in exact[1]), exact

with case("opaque installed dotted roots survive similarly named modules"), project() as folder:
    run(folder, '''module { mod bn254;
      fn Identity(x: bn254.fr::Element) -> bn254.fr::Element { return x; }
    }''', files={"bn254.pir": "module { pub fn Dummy(x: bool) -> bool { return x; } }"},
        mode="protocol-admit")

with case("application type names do not capture installed vocabulary in libraries"), project() as folder:
    library = f'''module {{ {identity("bits")};
      pub fn Keep(x: Vector<koala-bear::Element>) -> Vector<koala-bear::Element> {{ return x; }}
    }}'''
    app = f'''module {{ dependency bits = {identity("bits")}; struct Vector {{ bit: bool }}
      fn Main(x: bool) -> bool {{ return x; }}
    }}'''
    run(folder, app, {"bits/lib.pir": library}, mode="protocol-admit")

for prefix, files in (
    ("imported", {"bits/lib.pir": 'module "arkworks.bls12-381/1" {}'}),
    ("child", {"child.pir": 'module "arkworks.bls12-381/1" {}'}),
):
    with case(f"{prefix} profiles refuse explicitly"), project() as folder:
        run(folder, "module { mod child; }" if prefix == "child" else "module {}",
            libraries=files if prefix == "imported" else {},
            files=files if prefix == "child" else {}, refuses="source-profile-owner")

with case("application root profile remains allowed"), project() as folder:
    run(folder, 'module "arkworks.bls12-381/1" { fn Id(x: field) -> field { return x; } }',
        mode="protocol-admit")

with case("explicit anonymous owner claims refuse but synthetic applications work"), project() as folder:
    run(folder, "module { fn Id(x: bool) -> bool { return x; } }", mode="protocol-admit")
    for name, version, resolution in (("application", "anonymous", "project"),
                                      ("installed-contracts", "1", "builtin")):
        run(folder, f'module {{ library(namespace="zkc",name="{name}",version="{version}",resolution="{resolution}"); }}',
            refuses="source-library-reserved")

with case("anonymous declaration identity is scoped to captured project bytes"), project() as folder:
    source = "module { fn Id(x: bool) -> bool { return x; } }"
    first = run(folder, source, mode="protocol-analyze")["resolved_declarations"][0]["identity"]
    second = run(folder, source.replace("return x", "return true"), mode="protocol-analyze")["resolved_declarations"][0]["identity"]
    assert first != second

for selected in ("pub select Export = C;", "pub seal Export = C;", "pub link Export = Use<C>;"):
    with case(f"public selection checks private nominal closure: {selected}"), project() as folder:
        source = f'''module {{ {identity("bits")};
          struct Hidden {{ bit: bool }}
          interface I {{ type Value copy drop; local step(x: Value) -> Value; }}
          component C: I {{ type Value = Hidden; local step(x: Hidden) -> Hidden {{ return x; }} }}
          fn Use<X: I>(x: X::Value) -> X::Value {{ return X::step(x); }}
          {selected}
        }}'''
        run(folder, source, refuses="source-private-signature")

with case("public configure cannot expose a private record signature"), project() as folder:
    run(folder, '''module {
      struct Hidden { bit: bool }
      fn Private<F: Field>(x: Hidden) -> Hidden { return x; }
      pub configure Public = Private(F = "koala-bear");
    }''', refuses="source-private-signature")

with case("public wrappers may hide private implementation with a public signature"), project() as folder:
    run(folder, '''module {
      struct Hidden { bit: bool }
      fn Private<F: Field>(x: bool) -> bool { let h = Hidden { bit: x }; return h.bit; }
      pub configure Public = Private(F = "koala-bear");
      fn Main(x: bool) -> bool { return Public(x: x); }
    }''', mode="protocol-admit")

with case("explicit origins cannot copy another declaration's origin"), project() as folder:
    run(folder, '''module {
      fn First(x: bool) -> bool { return x; }
      fn Second(x: bool) -> bool origin First() { return x; }
    }''', refuses="source-origin-collision")

with case("unique explicit root origins remain supported"), project() as folder:
    output = run(folder, 'module { fn Identity(x: bool) -> bool origin Chosen() { return x; } }')
    assert "Chosen" in json.dumps(output)

with case("imported functions cannot claim explicit origins"), project() as folder:
    run(folder, APP, {"bits/lib.pir": BITS.replace("fn Raw(x: bool) -> bool", "fn Raw(x: bool) -> bool origin Chosen()")},
        refuses="source-origin-owner")

with case("component member and ordinary module origins qualify both owners"), project() as folder:
    left = f'''module {{ {identity("left")};
      pub interface I {{ local step(x: bool) -> bool; }}
      pub component Comp: I {{ local step(x: bool) -> bool {{ return x; }} }}
    }}'''
    right = f'module {{ {identity("right")}; pub mod Comp; }}'
    app = f'''module {{ dependency left = {identity("left")}; dependency right = {identity("right")};
      use left::{{I, Comp}};
      fn Use<X: I>(x: bool) -> bool {{ return X::step(x); }} link Closed = Use<Comp>;
      fn Main(x: bool) -> bool {{ let y = Closed(x); return right::Comp::step(y); }}
    }}'''
    output = run(folder, app, {"left/lib.pir": left, "right/lib.pir": right},
                 {"right/Comp.pir": "module { pub fn step(x: bool) -> bool { return x; } }"})
    origins = set(re.findall(r'l[0-9a-f]{16}\.Comp\.step', json.dumps(output)))
    assert len(origins) == 2, output


RELATION = ["zkc.relation.r1cs/1", "bls12-381.fr", "4", "1", "1",
            [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]]]

with case("relation helpers require an accessible view target"), project() as folder:
    library = f'''module {{ {identity("bits")};
      relation Circuit = r1cs("data.json");
      pub derive Core = rank_one(Circuit, public_matrices);
    }}'''
    files = {"bits/data.json": json.dumps(RELATION)}
    report = run(folder, depending("module {}"), {"bits/lib.pir": library}, files, mode="protocol-analyze")
    assert report["state"] == "source_checked", report["diagnostics"]
    view = next(d["symbol"] for d in report["resolved_declarations"] if d["display_name"] == "Core")
    for helper in (view + "_Products", json.dumps(view + "_Products"), view + "_op_0"):
        run(folder, depending(f"module {{ fn Main(x: bool) -> bool {{ return {helper}(x); }} }}"),
            {"bits/lib.pir": library}, files, refuses="source-name-unresolved")
    app = f'''module {{ dependency bits = {identity("bits")}; use bits::Core as Named;
      fn Main(statement: Vector<bls12-381.fr::Element>, witness: Vector<bls12-381.fr::Element>)
          -> Vector<bls12-381.fr::Element> {{ return Named_Assemble(statement, witness); }}
    }}'''
    run(folder, app, {"bits/lib.pir": library}, files, mode="protocol-admit")
    run(folder, app.replace("Named_Assemble", "bits::Core_Assemble"),
        {"bits/lib.pir": library}, files, mode="protocol-admit")

with case("explicit capture names cannot resolve through application globals"), project() as folder:
    library = BITS.replace("return Raw(x);", "if x capture(AppOnly) -> (y) { yield x; } else { yield x; } return y;")
    app = APP.replace("fn Main", "const AppOnly: index = 1; fn Main")
    run(folder, app, {"bits/lib.pir": library}, refuses="source-name-unresolved")

with case("operation attribute strings remain literal data"), project() as folder:
    run(folder, '''module {
      fn Main() -> koala-bear::Element {
        let value: koala-bear::Element = field::constant() attributes ("7");
        return value;
      }
    }''', mode="protocol-admit")

with case("a public component cannot publish a private interface"), project() as folder:
    run(folder, '''module {
      interface Hidden { local step(x: bool) -> bool; }
      pub component C: Hidden { local step(x: bool) -> bool { return x; } }
    }''', refuses="source-private-signature")

with case("exact quoted authored helpers and protocol names remain resolvable"), project() as folder:
    run(folder, '''module {
      fn "custom.name"(x: bool) -> bool { return x; }
      fn Main(x: bool) -> bool { return "custom.name"(x: x); }
      protocol "Main.child" { roles(A); return; }
      instance I: "Main.child" { roles(A=Alice); } entry E=I;
    }''', mode="protocol-admit")

with case("opaque bare operation attributes are not identifier references"), project() as folder:
    source = '''module {
      fn Observe<T: domain Transcript, E: domain Codec>(s: Transcript<T>, x: bool)
          -> Transcript<T> requires (Transcript(T), Encodes.bool(E)) {
        return transcript::observe::bool::<T,E>(s,x) attributes(N,message,schema,P,V);
      }
    }'''
    before = run(folder, source)
    assert before == run(folder, source.replace("module {", "module { const N: index=8;", 1))

with case("installed contract binding names preserve owner-specific binding selection"), project() as folder:
    library = f'''module {{ {identity("bits")};
      bind "field.add" = field.add("koala-bear");
      pub fn Add(x: koala-bear::Element) -> koala-bear::Element {{ return "field.add"(x, x); }}
    }}'''
    app = f'''module {{ dependency bits = {identity("bits")};
      bind "field.add" = field.add("bn254.fr");
      fn Main(x: koala-bear::Element) -> koala-bear::Element {{ return bits::Add(x); }}
    }}'''
    run(folder, app, {"bits/lib.pir": library}, mode="protocol-admit")

with case("explicit root origins reserve only their actual emitted origins"), project() as folder:
    run(folder, '''module {
      fn First(x: bool) -> bool origin Different() { return x; }
      fn Second(x: bool) -> bool origin First() { return x; }
    }''', mode="protocol-admit")

for form in ("runtime type", "runtime constructor", "static type", "static constructor", "static actual"):
    with case(f"local binders cannot authorize a foreign private nominal: {form}"), project() as folder:
        library = BITS.replace("fn Raw", "struct Hidden { bit: bool }\nfn Raw")
        report = run(folder, APP, {"bits/lib.pir": library}, mode="protocol-analyze")
        symbol = next(d["symbol"] for d in report["resolved_declarations"] if d["display_name"] == "Hidden")
        probes = {
            "runtime type": f"fn Main({symbol}: bool, h: {symbol}) -> bool {{ return {symbol}; }}",
            "runtime constructor": f"fn Main({symbol}: bool) -> bool {{ let h = {symbol} {{ bit: {symbol} }}; return {symbol}; }}",
            "static type": f"fn Main<{symbol}: domain Field>(h: {symbol}, x: bool) -> bool {{ return x; }}",
            "static constructor": f"fn Main<{symbol}: domain Field>(x: bool) -> bool {{ let h = {symbol} {{ bit: x }}; return x; }}",
            "static actual": f"fn Main({symbol}: bool) -> bool {{ return Helper::<{symbol}>({symbol}); }} fn Helper<F: Field>(x: bool) -> bool {{ return x; }}",
        }
        run(folder, depending("module { " + probes[form] + " }"), {"bits/lib.pir": library},
            refuses="source-name-unresolved")

with case("runtime argument names do not hide qualified dependency calls"), project() as folder:
    run(folder, APP.replace("Main(x: bool)", "Main(bits: bool)").replace("bits::Keep(x: x)", "bits::Keep(x: bits)"),
        {"bits/lib.pir": BITS}, mode="protocol-admit")

with case("runtime argument names do not hide qualified dependency types"), project() as folder:
    library = BITS.replace("fn Raw", "pub struct Box { bit: bool }\nfn Raw")
    app = f'''module {{ dependency bits = {identity("bits")};
      fn Main(bits: bits::Box, other: bits::Box) -> bits::Box {{ return other; }}
    }}'''
    run(folder, app, {"bits/lib.pir": library}, mode="protocol-admit")

with case("ordinary binders may have generated-looking spelling without gaining type authority"), project() as folder:
    symbol = "src_" + "1" * 40
    run(folder, f"module {{ fn Main({symbol}: bool) -> bool {{ return {symbol}; }} }}", mode="protocol-admit")

with case("anonymous origin qualifiers stay stable after captured comment edits"), project() as folder:
    library = BITS.replace("Keep", "Verify")
    app = f'''module {{ dependency bits = {identity("bits")};
      fn Verify(x: bool) -> bool {{ return bits::Verify(x); }}
    }}'''
    before = run(folder, app, {"bits/lib.pir": library}, mode="protocol-analyze")
    after = run(folder, app + "\n// app comment\n", {"bits/lib.pir": library + "\n// library comment\n"}, mode="protocol-analyze")
    def origin(report):
        return next(d for d in report["resolved_declarations"]
                    if d["display_name"] == "Verify" and d["identity"]["library"] == "application")
    assert origin(before)["origin"] == origin(after)["origin"] == "application.Verify"
    assert origin(before)["identity"] != origin(after)["identity"]

with case("closed checked-record leaf functions cannot be called to forge a token"), project() as folder:
    library = f'''module {{ {identity("bits")};
      pub checked struct Token(ok: bool) constructors(MintRaw);
      fn MintRaw(ok: bool) -> Token {{ return Token(ok = ok); }}
      pub fn Mint(ok: bool) -> Token {{ control::require(ok); return MintRaw(ok); }}
      pub interface I {{ local accept(token: Token) -> bool; }}
      component C: I {{ local accept(token: Token) -> bool {{ return token.ok; }} }}
      fn Use<X: I>(token: Token) -> bool {{ return X::accept(token); }}
      pub link Closed = Use<C>;
    }}'''
    app = f'''module {{ dependency bits = {identity("bits")};
      fn Main(token: bits::Token) -> bool {{ return bits::Closed(token); }}
    }}'''
    output = run(folder, app, {"bits/lib.pir": library})
    symbols = sorted(set(re.findall(r'(?:lib|client)_[0-9a-f]{64}', json.dumps(output))))
    assert symbols, output
    for symbol in symbols:
        for callee in (symbol, json.dumps(symbol)):
            run(folder, depending(f"module {{ fn Main(raw: bool) -> bool {{ return {callee}(raw); }} }}"),
                {"bits/lib.pir": library}, refuses="source-name-unresolved")

with case("explicit root functions may share an authored logical origin group"), project() as folder:
    run(folder, '''module {
      fn First(x: bool) -> bool origin Group() { return x; }
      fn Second(x: bool) -> bool origin Group() { return x; }
    }''', mode="protocol-admit")

with case("a root explicit group cannot spoof an imported automatic origin"), project() as folder:
    run(folder, depending('module { fn Main(x: bool) -> bool origin Keep() { return x; } }'),
        {"bits/lib.pir": BITS}, refuses="source-origin-collision")

with case("an opaque dotted type is not a local static projection"), project() as folder:
    library = f'''module {{ {identity("bits")};
      pub fn Keep<F: Field>(x: F.Hidden) -> bool {{ return true; }}
    }}'''
    run(folder, depending('module { struct "F.Hidden" { bit: bool } }'),
        {"bits/lib.pir": library}, refuses="source-name-unresolved")

for kind, private, member in (
    ("representation", "struct Hidden { bit: bool }", "type"),
    ("static equation", 'association Hidden = "private subject";', "association"),
):
    with case(f"a component {kind} cannot self-bind a private sibling symbol"), project() as folder:
        header = f'module {{ {identity("bits")}; mod inner; '
        libraries = {"bits/lib.pir": header + "}"}
        files = {"bits/inner.pir": "module { " + private + " }"}
        report = run(folder, depending("module {}"), libraries, files, mode="protocol-analyze")
        symbol = next(d["symbol"] for d in report["resolved_declarations"] if d["display_name"] == "inner::Hidden")
        permission = " copy drop" if member == "type" else ""
        library = header + f'''
          pub interface I {{ {member} {symbol}{permission}; }}
          pub component C: I {{ {member} {symbol} = {symbol}; }}
        }}'''
        run(folder, depending("module {}"), {"bits/lib.pir": library}, files,
            refuses="source-name-unresolved")

with case("component representation aliases see earlier concrete members"), project() as folder:
    run(folder, '''module {
      interface I { type First copy drop; type Second copy drop; local step(x: Second) -> Second; }
      component C: I {
        type First = bool; type Second = First;
        local step(x: Second) -> Second { return x; }
      }
      fn Use<X: I>(x: X::Second) -> X::Second { return X::step(x); }
      link Closed = Use<C>;
      fn Main(x: bool) -> bool { return Closed(x); }
    }''', mode="protocol-admit")

with case("flat authored value binders retain exact dotted spellings"), project() as folder:
    run(folder, '''module {
      fn Main(p.x: bool, p.y: bool) -> (bool, bool) {
        return (p.x, p.y);
      }
    }''', mode="protocol-admit")

for category in ("callee", "value"):
    with case(f"a resolved declaration prefix cannot authorize a foreign {category} suffix"), project() as folder:
        report = run(folder, APP, {"bits/lib.pir": BITS}, mode="protocol-analyze")
        symbol = next(d["symbol"] for d in report["resolved_declarations"] if d["display_name"] == "Keep")
        if category == "callee":
            library = BITS.replace("fn Raw", "pub fn Bounce(x: bool) -> bool { return Keep::extra(x); }\nfn Raw")
            forged = f'fn "{symbol}.extra"(x: bool) -> bool {{ return bool::not(x); }}'
        else:
            library = BITS.replace("fn Raw", "pub fn Count() -> index { return Keep.extra; }\nfn Raw")
            forged = f"const {symbol}.extra: index = 7;"
        # The member is refused where the library spells it, and a declaration
        # spelled as the symbol it would reach is refused where it is declared.
        run(folder, depending("module { }"), {"bits/lib.pir": library}, refuses="source-name-kind")
        run(folder, depending("module { " + forged + " }"), {"bits/lib.pir": library},
            refuses="source-name-reserved")

with case("a generated view operation binding is not a public view helper"), project() as folder:
    library = f'''module {{ {identity("bits")}; relation Circuit = r1cs("data.json");
      pub derive Core = rank_one(Circuit, public_matrices);
    }}'''
    app = f'''module {{ dependency bits = {identity("bits")}; use bits::Core;
      fn Main(x: bool) -> bool {{ return Core::op_0(x); }}
    }}'''
    run(folder, app, {"bits/lib.pir": library}, {"bits/data.json": json.dumps(RELATION)},
        refuses="source-name-kind")

with case("unresolved hyphenated values retain the subtraction spacing hint"), project() as folder:
    run(folder, "module { fn F(alpha: index, base: index) -> index { return alpha-base; } }",
        refuses="source-name-unresolved")
    assert "write 'alpha - base'" in commands.last.stderr

with case("native entry declarations do not consume the draw selector cap"), project() as folder:
    entries = " ".join(f"entry e{i} = run;" for i in range(32768))
    run(folder, "module { protocol P { roles(A); return (); } "
        "instance run: P { roles(A=A); } " + entries + " }", mode="protocol-admit")

DRAW_LIBRARY = f'''module {{ {identity("draws")};
  pub fn Keep(coins: Rng<"bls12-381.fr">)
      -> (bls12-381.fr::Element, Rng<"bls12-381.fr">) {{
    [draw] let (x, after) = random::draw(coins); return (x, after);
  }}
}}'''
DRAW_APP = f'''module {{ dependency a = {identity("draws")};
  fn Accept(x: bls12-381.fr::Element) -> bool {{ return field::equal(x, x); }}
  protocol Round {{ roles(P,V); inputs(V coins: Rng<"bls12-381.fr">); outputs(V bool);
    local [sample] V: let (x, after) = a::Keep(coins);
    local [accept] V: let ok = Accept(x); return ok;
  }}
  instance round: Round {{ roles(P=P,V=V); }} entry main=round;
}}'''
DRAW_DESCRIPTOR = '''construction main {
  producer P; validator V; random coins at (a::Keep draw);
  accept 0; suite "merlin3.bls12-381.fr64be/1";
}'''

with case("an explicit root origin cannot free its emitted name for an imported origin"), project() as folder:
    source = DRAW_APP.replace("fn Accept", "fn Keep(x: bool) -> bool origin Z() { return x; } fn Accept")
    report = run(folder, source, {"draws/lib.pir": DRAW_LIBRARY}, mode="protocol-analyze")
    imported = next(d for d in report["resolved_declarations"]
                    if d["display_name"] == "Keep" and d["origin"] != "Z")
    assert imported["origin"] != "Keep", imported
    result = run(folder, source, {"draws/lib.pir": DRAW_LIBRARY}, mode="protocol-construct",
                 construction=DRAW_DESCRIPTOR)
    assert result[0] == "zkc.construction-result/1", result
    assert {row[4] for row in result[4] if row[7] == "construction"} == {imported["symbol"]}, result[4]

with case("conflicting construction selector paths refuse a construction, not the program"), project() as folder:
    # The application's own "a.Keep" and the dependency's Keep reached as a.Keep
    # are one selector path for two declarations. A construction cannot choose;
    # compiling the program asks nothing of selectors.
    alone = f'''module {{ dependency bits = {identity("bits")};
      fn "bits.Keep"(x: bool) -> bool {{ return x; }}
    }}'''
    run(folder, alone, {"bits/lib.pir": BITS})
    # An exact authored name wins over a path, so the body reaches the
    # library's Keep through an alias; the descriptor's selector stays a.Keep.
    source = DRAW_APP.replace("fn Accept", 'use a::Keep as Sample; fn "a.Keep"(x: bool) -> bool { return x; } fn Accept')
    source = source.replace("a::Keep(coins)", "Sample(coins)")
    run(folder, source, {"draws/lib.pir": DRAW_LIBRARY})
    run(folder, source, {"draws/lib.pir": DRAW_LIBRARY}, mode="protocol-construct",
        construction=DRAW_DESCRIPTOR, refuses="source-selector-ambiguity")

with case("exponential module reexports exhaust a construction's deterministic shared budget"), project() as folder:
    # 2^27 selector paths reach one function. The program resolves; indexing
    # its selectors for a construction exhausts the same budget every time.
    files = {}
    for i in range(28):
        files[f"m{i}.pir"] = (f"module {{ pub use crate::m{i+1} as a; pub use crate::m{i+1} as b; }}"
                               if i < 27 else "module { pub fn Leaf(x: bool) -> bool { return x; } }")
    source = DRAW_APP.replace("fn Accept", " ".join(f"pub mod m{i};" for i in range(28)) + " fn Accept")
    run(folder, source, {"draws/lib.pir": DRAW_LIBRARY}, files)
    for _ in range(2):
        run(folder, source, {"draws/lib.pir": DRAW_LIBRARY}, files, mode="protocol-construct",
            construction=DRAW_DESCRIPTOR, refuses="source-resolution-limit")

with case("a library with more selector paths than a construction admits still compiles"), project() as folder:
    # Every alias of a module is another path to each of its declarations:
    # 201 paths to 200 functions exceed the 32768 selectors a construction may
    # index, which is a limit on constructions, not on programs.
    functions = " ".join(f"pub fn F{i}(x: bool) -> bool {{ return x; }}" for i in range(200))
    aliases = " ".join(f"pub use m as A{i};" for i in range(200))
    wide = f'module {{ {identity("wide")}; pub mod m; {aliases} }}'
    source = DRAW_APP.replace("fn Accept", f'dependency wide = {identity("wide")}; fn Accept')
    libraries = {"draws/lib.pir": DRAW_LIBRARY, "wide/lib.pir": wide}
    run(folder, source, libraries, {"wide/m.pir": f"module {{ {functions} }}"})
    run(folder, source, libraries, {"wide/m.pir": f"module {{ {functions} }}"}, mode="protocol-construct",
        construction=DRAW_DESCRIPTOR, refuses="source-resolution-limit")

for kind in ("ordinary definition", "component member"):
    with case(f"source selector paths cannot capture a foreign closed {kind}"), project() as folder:
        if kind == "ordinary definition":
            other = f'module {{ {identity("other")}; pub mod a; }}'
            files = {"other/a.pir": "module { pub fn Keep(x: bool) -> bool { return x; } }"}
        else:
            other = f'''module {{ {identity("other")};
              pub interface I {{ local Keep(x: bool) -> bool; }}
              pub component a: I {{ local Keep(x: bool) -> bool {{ return x; }} }}
            }}'''
            files = {}
        source = DRAW_APP.replace("fn Accept", f'dependency other = {identity("other")}; fn Accept')
        run(folder, source, {"draws/lib.pir": DRAW_LIBRARY, "other/lib.pir": other}, files,
            mode="protocol-construct", construction=DRAW_DESCRIPTOR,
            refuses="construction-source-selector-ambiguous")

print(f"resolver authority: {counted()} cases, {commands.save()} commands")
