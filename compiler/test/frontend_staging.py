"""Bounded static construction, compared with independent concrete source."""
import json

from cases import case
from commands import Commands
from source_text import unlocated
from tools import records, examples

commands = Commands(records())


def run(command, text, refuses=None):
    return commands.source(command, text, refuses=refuses)


def common(text):
    return json.loads(run("protocol-source", text))


def parse(text):
    return unlocated(json.loads(run("protocol-parse", text))["content"])


def generated(owner, kind, site):
    return f"__stage_{owner.encode().hex()}_{kind}_{site.encode().hex()}"


helper = """fn Id<F: Field>(x: F::Element) -> F::Element { return x; }"""
family = """protocol Family<F: Field> requires (CommRing(F)) {
  roles (P); inputs (P x: F::Element); outputs (P F::Element);
  local [id] P: let y = Id::<F>(x); return y;
}"""
configs = """configure Small = Family(F = koala-bear);
configure Large = Family(F = bls12-381.fr);"""
instances = """instance I: Small { roles (P = Prover); }
instance J: Large { roles (P = Prover); }
entry E = I; entry Q = J;"""
source = f"module {{ {helper} {family} {configs} {instances} }}"

with case("two fields match independently expanded protocols and function configurations"):
    concrete = []
    functions = []
    for name, domain in (("Small", "koala-bear"), ("Large", "bls12-381.fr")):
        fn = generated(name, "fn", "id")
        concrete.append(f"""protocol {name} {{
          roles (P); inputs (P x: {domain}::Element); outputs (P {domain}::Element);
          local [id] P: let y = "{fn}"(x); return y;
        }}""")
        functions.append(f'configure "{fn}" = Id(F = {domain});')
    expanded = f"module {{ {helper} {' '.join(concrete)} {' '.join(functions)} {instances} }}"
    assert common(source) == common(expanded)
    run("protocol-admit", source)
    assert common(source) == common(source)
    assert common(source) == common(run("protocol-format", source))

with case("generic definitions remain in source inspection"):
    syntax = parse(source)
    assert syntax["protocols"][0]["generic"]
    assert syntax["protocols"][0]["staticParameters"][0]["bounds"] == ["Field"]
    assert syntax["protocols"][0]["requirements"][0]["predicate"] == "CommRing"

with case("group family uses installed scalar association and requirements"):
    group = """module {
      fn Identity<G: domain Group>(x: G::Element) -> G::Element { return x; }
      protocol Family<G: domain Group> requires (ScalarAction(G), Field(G::Scalar)) {
        roles (P); inputs (P x: G::Element); outputs (P G::Element);
        local [id] P: let y = Identity::<G>(x); return y;
      }
      configure Concrete = Family(G = bls12-381.g1);
      instance I: Concrete { roles (P = Prover); } entry E = I;
    }"""
    run("protocol-admit", group)
    run("protocol-source", group.replace("G = bls12-381.g1", "G = koala-bear"), "source-static-sort")

with case("nested dependency specialization uses enclosing actuals"):
    child = generated("Main", "dep", "child")
    composed = """module {
      protocol Child<F: Field> { roles (P); inputs (P x: F::Element);
        outputs (P F::Element); return x; }
      protocol Parent<F: Field> { roles (P); inputs (P x: F::Element);
        outputs (P F::Element); dependencies (child: Child::<F=F>());
        invoke [invoke] child(x) -> (y); return y; }
      configure Main = Parent(F=koala-bear);
      instance C: Main::child { roles (P=Prover); }
      instance I: Main { dependencies (child=C); roles (P=Prover); } entry E=I;
    }"""
    expanded = f"""module {{
      protocol "{child}" {{ roles (P); inputs (P x: koala-bear::Element);
        outputs (P koala-bear::Element); return x; }}
      protocol Main {{ roles (P); inputs (P x: koala-bear::Element);
        outputs (P koala-bear::Element); dependencies (child: "{child}"());
        invoke [invoke] child(x) -> (y); return y; }}
      instance C: "{child}" {{ roles (P=Prover); }}
      instance I: Main {{ dependencies (child=C); roles (P=Prover); }} entry E=I;
    }}"""
    assert common(composed) == common(expanded)
    run("protocol-admit", composed)

for replacement, diagnostic in (
    ("bls12-381.g1", "source-static-sort"),
    ("missing", "source-name-unresolved"),
):
    with case("wrong configured field: " + replacement):
        run("protocol-source", source.replace("F = koala-bear", "F = " + replacement), diagnostic)

with case("mixed operands still fail concrete checking"):
    mixed = source.replace("inputs (P x: F::Element)", "inputs (P x: bls12-381.fr::Element)")
    run("protocol-source", mixed, "source-call-type")

with case("explicit function instantiation is required"):
    run("protocol-source", source.replace("Id::<F>(x)", "Id(x)"), "source-local-generic")

with case("constant arithmetic and index expression match explicit naturals"):
    consts = "const N: index = (BASE * 3 + 1) / 2 % 7; const BASE: index = 4;"
    body = "fn Count() -> index { let n = N; return n; }"
    assert common(f"module {{ {consts} {body} }}") == common("module { " + body.replace("= N", "= 6") + " }")
    parsed = parse(f"module {{ {consts} {body} }}")
    assert len(parsed["constants"]) == 2

with case("runtime lexical variables shadow constants"):
    f = "fn Count(N: index) -> index { let y = N; return y; }"
    assert common("module { const N: index=8; " + f + " }") == common("module { " + f + " }")

with case("quoted names are never natural constant references"):
    run("protocol-source", 'module { const N: index=8; fn Count() -> index { let x = "N"; return x; } }', "source-value-reference")

with case("constant operation attribute uses atom kind"):
    bare = "module { const N: index=8; fn Count() -> index { let x=index::constant() attributes(N); return x; } }"
    assert common(bare) == common(bare.replace("attributes(N)", "attributes(8)"))
    quoted = bare.replace("attributes(N)", 'attributes("N")')
    # Quoting preserves the attribute bytes; common admission owns whether that
    # preserved value is valid for the selected operation.
    run("protocol-source", quoted, "expected-natural")
    run("protocol-admit", quoted, "expected-natural")

with case("natural parameters and loops use constants without changing identities"):
    text = """module {
      const N: index=2*3;
      protocol P { roles (A); parameters (rounds);
        loop [l] N carry () -> () { yield; } return; }
      instance I: P { parameters (rounds=N); roles (A=Alice); } entry E=I;
    }"""
    expanded = text.replace("const N: index=2*3;", "").replace("[l] N", "[l] 6").replace("rounds=N", "rounds=6")
    assert common(text) == common(expanded)
    run("protocol-source", text.replace("rounds=N", 'rounds="N"'), "source-constant-reference")

for expression, diagnostic in (
    ("MISSING", "source-name-unresolved"), ("N", "source-constant-cycle"),
    ("4294967296", "source-constant-overflow"), ("4294967295 + 1", "source-constant-overflow"),
    ("65536 * 65536", "source-constant-overflow"), ("0 - 1", "source-constant-underflow"),
    ("1 / 0", "source-constant-zero-divisor"), ("1 % 0", "source-constant-zero-divisor"),
    ("-1", "source-constant-expression"), ('"N"', "source-constant-expression"),
    ("f()", "source-name-unresolved"),
):
    with case("constant refusal: " + expression):
        run("protocol-source", f"module {{ const N: index={expression}; }}", diagnostic)

for header, diagnostic in (
    ("F: domain Unknown", "generic-declared-sort"), ("F: Missing", "source-name-unresolved"),
    ("F: Field, F: Field", "generic-duplicate-parameter"),
):
    with case("unused family declaration checked: " + header):
        run("protocol-source", f"module {{ protocol P<{header}> {{ roles(A); return; }} }}", diagnostic)

with case("cyclic generators fail before unbounded expansion"):
    text = """module { protocol P<F: Field> { roles(A);
      dependencies (child: P::<F=F>()); return; } configure C=P(F=koala-bear); }"""
    run("protocol-source", text, "source-specialization-cycle")

with case("generic instances require a configured protocol"):
    run("protocol-source", source.replace("instance I: Small", "instance I: Family"), "source-static-required")

with case("strict parser refuses incomplete and invalid declarations"):
    for text in ("module {", "module { const N:index=; fn Good()->(){return;} }",
                 "module { protocol P<F:Field>{roles(A);", "module { const N:index=1 }"):
        run("protocol-parse", text, "source-syntax")

with case("example admission and format stability"):
    text = (examples / "domain-family.pir").read_text()
    run("protocol-admit", text)
    formatted = run("protocol-format", text)
    assert parse(text) == parse(formatted)
    assert common(text) == common(formatted)


with case("unselected opaque attributes are not constant references"):
    opaque = """module {
      const N:index=8;
      fn Observe<T:domain Transcript, E:domain Codec>(s:Transcript<T>, x:bool)
          -> Transcript<T> requires (Transcript(T), Encodes.bool(E)) {
        let y=transcript::observe::bool::<T,E>(s,x) attributes(N,message,schema,P,V);
        return y;
      }
    }"""
    assert common(opaque) == common(opaque.replace("const N:index=8;", ""))
    assert common(opaque) == common(opaque.replace("attributes(N,", 'attributes("N",'))

with case("domain binders never replace role or value names"):
    renamed_roles = source.replace("roles (P)", "roles (F)").replace("P x:", "F x:").replace("outputs (P ", "outputs (F ").replace("] P:", "] F:").replace("roles (P =", "roles (F =")
    concrete = common(renamed_roles)
    assert concrete == common(renamed_roles)
    run("protocol-admit", renamed_roles)

with case("quoted type roots remain opaque"):
    run("protocol-source", source.replace("x: F::Element", 'x: "F"::Element'), "source-name-unresolved")

with case("constant forward dependency cycle and depth are bounded"):
    run("protocol-source", "module { const A:index=B; const B:index=A; }", "source-constant-cycle")
    chain = " ".join(f"const C{i}:index=C{i+1};" for i in range(66)) + "const C66:index=1;"
    run("protocol-source", "module {" + chain + "}", "source-constant-depth")
    reversed_chain = "const C66:index=1;" + " ".join(f"const C{i}:index=C{i+1};" for i in reversed(range(66)))
    run("protocol-source", "module {" + reversed_chain + "}", "source-constant-depth")

with case("specialization count is bounded"):
    configs = " ".join(f"configure C{i}=P(F=koala-bear);" for i in range(1025))
    run("protocol-source", "module {protocol P<F:Field>{roles(A);return;}" + configs + "}", "source-staging-limit")


with case("numeric operation attributes respect runtime binders"):
    text = "module { const N:index=8; fn Count(N:index)->index {let x=index::constant() attributes(N);return x;} }"
    run("protocol-source", text, "expected-natural")

with case("protocol loop count respects runtime binders"):
    text = "module { const N:index=8; protocol P { roles(A);inputs(A N:index);loop N carry()->(){yield;}return;} }"
    run("protocol-source", text, "source-protocol-count")


with case("named domain order is canonical and equality requirements fail closed"):
    text = '''module {
      protocol P<F:Field, H:Field> requires ("="(F,H)) {
        roles(A); inputs(A x:F::Element,A y:H::Element);
        outputs(A F::Element,A H::Element); return(x,y);
      }
      configure C=P(F=koala-bear,H=koala-bear);
    }'''
    assert common(text) == common(text.replace("F=koala-bear,H=koala-bear", "H=koala-bear,F=koala-bear"))
    run("protocol-source", text.replace("H=koala-bear", "H=bls12-381.fr"), "source-static-requirement")

with case("generated configuration collisions are refused"):
    collision = generated("Small", "fn", "id")
    run("protocol-source", source.replace("module {", f'module {{ fn "{collision}"()->(){{return;}}', 1), "source-static-duplicate")

with case("constant declaration order does not change emitted content"):
    prefix = "module { const A:index=B*2; const B:index=3;"
    suffix = "fn Count()->index{let n=A;return n;} }"
    assert common(prefix+suffix) == common("module { const B:index=3; const A:index=B*2;"+suffix)


for actuals, code in (("", "source-static-arity"), ("G=koala-bear", "source-static-argument"),
                      ("F=koala-bear,F=koala-bear", "source-static-arity")):
    with case("named specialization rejects malformed actuals: " + actuals):
        run("protocol-source", "module {protocol P<F:Field>{roles(A);return;} configure C=P("+actuals+");}", code)

with case("quoted requirement roots are not substituted"):
    run("protocol-source", 'module {protocol P<F:Field>requires(Field("F")){roles(A);return;}}', "source-name-unresolved")

with case("protocol configuration has an explicit declaration category"):
    run("protocol-source", "module {protocol P{roles(A);return;} configure C=P();}", "source-static-target")
    run("protocol-source", "module {protocol P<F:Field>{roles(A);return;} configure C=P(F=koala-bear) using(x=y);}", "source-static-target")

with case("generic dependency requires explicit actuals"):
    run("protocol-source", "module {protocol P<F:Field>{roles(A);return;} protocol Q{roles(A);dependencies(c:P());return;}}", "source-static-required")

with case("protocol requirements require a static parameter list"):
    run("protocol-source", "module {protocol P requires(Field(koala-bear)){roles(A);return;}}", "source-static-contract")

with case("acyclic specialization depth is bounded"):
    children = " ".join(f"protocol P{i}<F:Field>{{roles(A);dependencies(c:P{i+1}::<F=F>());return;}}" for i in range(65))
    text = "module {"+children+"protocol P65<F:Field>{roles(A);return;} configure C=P0(F=koala-bear); }"
    run("protocol-source", text, "source-specialization-depth")


for path in ("Missing::child", "Main::missing", "Id::child"):
    with case("instance projection refuses unknown/nonprotocol path: " + path):
        text = '''module { fn Id()->(){return;} protocol Main{roles(A);return;}
          instance I: PATH{roles(A=Alice);} }'''.replace("PATH", path)
        code = {"Missing::child": "source-name-unresolved",
                "Main::missing": "source-static-projection",
                "Id::child": "source-name-kind"}[path]
        run("protocol-source", text, code)

with case("nested instance projections follow declared dependency identities"):
    text = '''module {
      protocol Leaf<F:Field>{roles(A);return;}
      protocol Mid<F:Field>{roles(A);dependencies(leaf:Leaf::<F=F>());return;}
      protocol Root<F:Field>{roles(A);dependencies(mid:Mid::<F=F>());return;}
      configure Main=Root(F=koala-bear);
      instance L:Main::mid::leaf{roles(A=Alice);}
      instance M:Main::mid{dependencies(leaf=L);roles(A=Alice);}
      instance I:Main{dependencies(mid=M);roles(A=Alice);} entry E=I;
    }'''
    run("protocol-admit", text)
    assert common(text) == common(run("protocol-format", text))

with case("quoted instance protocol roots stay opaque"):
    text = '''module {protocol "Main.child"{roles(A);return;}
      instance I:"Main.child"{roles(A=Alice);} entry E=I;}'''
    run("protocol-admit", text)
    assert "protocolPath" not in parse(text)["instances"][0]
    colon = text.replace("Main.child", "Main::child")
    assert parse(colon)["instances"][0]["protocol"] == "Main::child"
    assert "protocolPath" not in parse(colon)["instances"][0]
    run("protocol-admit", colon, "interactive-name")

print(f"{commands.save()} staging controls passed")
