"""Retained frontend subjects, source-only refusals and partial query states."""

import json

from cases import case
from commands import Commands
from tools import records

commands = Commands(records())


def analyze(text):
    return json.loads(commands.source("protocol-analyze", text))


def common(text):
    return json.loads(commands.source("protocol-source", text))


with case("nominal identities survive identical common layouts"):
    source = '''module {
      struct A<F: domain Field>(x: F::Element);
      fn Id<F: domain Field>(value: A<F>) -> A<F> { return value; }
    }'''
    other = source.replace("struct A<", "struct B<").replace("A<F>", "B<F>")
    assert common(source) == common(other)
    first, second = analyze(source), analyze(other)
    assert first["state"] == second["state"] == "source_checked"
    assert first["admission"] == second["admission"] == "not_requested"
    assert {x["name"] for x in first["declarations"] if x["kind"] == "record"} == {"A"}
    assert {x["name"] for x in second["declarations"] if x["kind"] == "record"} == {"B"}
    identity = next(d for d in first["declarations"] if d["name"] == "Id")
    value_type = first["types"][identity["inputs"][0]["type"]]
    assert value_type["kind"] == "record"


CHECKED = '''module {
  checked struct Checked<F: domain Field>(value: F::Element) constructors(Make);
  struct Wrapper<F: domain Field>(checked: Checked<F>);
  fn Make<F: Field>(value: F::Element) -> Checked<F> {
    let result = Checked(value=value); return result;
  }
  protocol Foreign { roles (P); outputs (P RESULT); external; }
}'''
for result in ['Checked<"koala-bear">', 'Wrapper<"koala-bear">']:
    with case(f"external protocol cannot issue {result}"):
        text = CHECKED.replace("RESULT", result)
        commands.source("protocol-source", text, refuses="source-checked-external")
        report = analyze(text)
        assert report["state"] == "incomplete"
        assert any(d["code"] == "source-checked-external" for d in report["diagnostics"])

with case("plain external results remain a separate admission concern"):
    report = analyze(CHECKED.replace("RESULT", '"koala-bear"::Element'))
    assert report["state"] == "source_checked", report
    assert report["admission"] == "not_requested"

with case("syntax recovery retains surrounding declarations but never emits"):
    text = '''module {
      fn Before(x: bool) -> bool { return x; }
      fn Broken(x: bool) -> bool { let x = ; }
      fn After(x: bool) -> bool { return x; }
    }'''
    report = analyze(text)
    assert report["state"] == "incomplete", report
    assert {"Before", "After"} <= {d["name"] for d in report["declarations"]}
    assert report["diagnostics"]
    commands.source("protocol-source", text, refuses="source-syntax")

with case("static error keeps its structured diagnostic identity"):
    text = "module { const A: index = B; const B: index = A; }"
    report = analyze(text)
    assert report["state"] == "incomplete"
    assert any(d["code"] == "source-constant-cycle" for d in report["diagnostics"]), report
    commands.source("protocol-source", text, refuses="source-constant-cycle")

with case("new query is not a portable PIR producer"):
    report = analyze("module { fn Id(x: bool) -> bool { return x; } }")
    assert report["format"] == "zkc.frontend-analysis/1"
    commands.source("protocol-source", json.dumps(report), refuses="source-syntax")


# An unused family is still checked under its abstract requirements. Selection
# is not needed to expose these source errors, and common admission remains a
# distinct later judgment.
FAMILY = '''module {
  fn Id<F:Field>(x:F::Element)->F::Element {return x;}
  protocol Family<F:Field, H:Field> {
    roles(A,B); inputs(A x:F::Element,B z:H::Element); outputs(B F::Element);
    local A:let y=Id::<F>(x);
    message row:A(y)->B(received);
    return received;
  }
}'''
with case("unused protocol family has a checked abstract source body"):
    report = analyze(FAMILY)
    assert report["phase"] == "source_checked", report
    declaration = next(d for d in report["declarations"] if d["name"] == "Family")
    assert declaration["body_state"] == "source_checked"
    assert declaration["signature_checked"]
    assert not report["instantiations"]
    call = next(u for u in report["uses"] if u["owner"] == declaration["id"])
    assert call["bindings"] and call["requirements"]

for label, before, after, code in (
    ("mixed parameters", "Id::<F>(x)", "Id::<H>(x)", "source-call-type"),
    ("local ownership", "local A:", "local B:", "source-protocol-role"),
    ("message ownership", "A(y)->B(received)", "B(y)->A(received)", "source-protocol-role"),
    ("return ownership", "return received", "return x", "source-protocol-return"),
    ("missing capability", "<F:Field, H:Field>", "<F:domain Field, H:Field>", "source-protocol-requirement"),
    ("missing callee", "Id::<F>", "Missing::<F>", "source-name-unresolved"),
    ("wrong result annotation", "let y=", "let y:H::Element=", "source-call-type"),
):
    with case(f"abstract family refuses {label}"):
        text = FAMILY.replace(before, after)
        report = analyze(text)
        assert report["phase"] == "semantic_error", report
        assert any(d["code"] == code for d in report["diagnostics"]), report
        commands.source("protocol-source", text, refuses=code)

with case("failed source body is deferred, not external"):
    report = analyze("module { fn Bad(x:bool)->bool { let y=Missing(x); return y; } }")
    assert report["phase"] == "semantic_error", report
    declaration = next(d for d in report["declarations"] if d["name"] == "Bad")
    assert declaration["has_body"] and declaration["body_state"] == "deferred"


with case("quoted static actual never captures a protocol parameter"):
    text = FAMILY.replace("Id::<F>", 'Id::<"F">')
    commands.source("protocol-source", text, refuses="source-name-unresolved")
    assert any(d["code"] == "source-name-unresolved" for d in analyze(text)["diagnostics"])

with case("generic loop count resolves before selection"):
    template = "module { CONSTANT protocol P<F:Field>{roles(A); PARAMETERS loop N carry()->(){yield;} return;} }"
    invalid = template.replace("CONSTANT", "").replace("PARAMETERS", "")
    commands.source("protocol-source", invalid, refuses="source-name-unresolved")
    for constant, parameter in (("const N:index=2;", ""), ("", "parameters(N);")):
        text = template.replace("CONSTANT", constant).replace("PARAMETERS", parameter)
        assert analyze(text)["phase"] == "source_checked", analyze(text)
    shadow = template.replace("CONSTANT", "const N:index=2;").replace("PARAMETERS", "inputs(A N:index);")
    commands.source("protocol-source", shadow, refuses="source-protocol-count")

with case("quoted dependency actual never captures its enclosing parameter"):
    text = '''module {
      protocol Child<F:Field>{roles(A);return;}
      protocol P<F:Field>{roles(A);dependencies(c:Child::<F="F">());invoke c()->();return;}
    }'''
    commands.source("protocol-source", text, refuses="source-name-unresolved")

with case("abstract dependency natural agreement resolves both declarations"):
    text = '''module {
      protocol Child<F:Field>{roles(A);parameters(N);return;}
      protocol P<F:Field>{roles(A);parameters(M);dependencies(c:Child::<F=F>(N=M));invoke c()->();return;}
    }'''
    assert analyze(text)["phase"] == "source_checked", analyze(text)
    commands.source("protocol-source", text.replace("N=M", "N=Absent"), refuses="source-protocol-parameter")
    commands.source("protocol-source", text.replace("N=M", "Absent=M"), refuses="source-protocol-parameter")


with case("bound domain names cannot capture installed identities on emission"):
    text = '''module {
      fn Id<koala-bear:Field>(x:"koala-bear"::Element)->"koala-bear"::Element{return x;}
      configure C=Id(koala-bear=bls12-381.fr);
    }'''
    commands.source("protocol-source", text, refuses="source-static-name")
    assert analyze(text)["phase"] == "semantic_error"


for label, fragment, code in (
    ("generic signature", 'fn Bad<F:Field>(x:"F"::Element)->F::Element{return x;}', "source-name-unresolved"),
    ("family signature", 'protocol Bad<F:Field>{roles(A);inputs(A x:"F"::Element);return;}', "source-name-unresolved"),
    ("generic expression call", 'fn Bad<F:Field>(x:F::Element)->F::Element{let y=Id::<"F">(x);return y;}', "source-name-unresolved"),
    ("generic requirement", 'fn Bad<F:domain Field>(x:F::Element)->F::Element requires(Field("F")){return x;}', "source-name-unresolved"),
    ("bundle requirement", 'bundle Bad(F)=(Field("F"));', "source-name-unresolved"),
    ("where requirement", 'fn Bad<F:domain Field>(x:F::Element)->F::Element where "F":Field {return x;}', "source-name-unresolved"),
):
    with case(f"quoted roots remain identities in {label}"):
        text = 'module {fn Id<F:Field>(x:F::Element)->F::Element{return x;}' + fragment + '}'
        commands.source("protocol-source", text, refuses=code)
        assert analyze(text)["phase"] == "semantic_error"

with case("specialization preserves a record named like a domain parameter"):
    text = '''module {
      struct F(v:bool); struct "koala-bear"(v:bool);
      protocol P<F:Field>{roles(A);inputs(A s:F);outputs(A F);return s;}
      configure C=P(F=koala-bear);
      instance I:C{roles(A=Alice);} entry E=I;
    }'''
    for program in (text, text.replace('struct "koala-bear"(v:bool);', '')):
        report = analyze(program)
        assert report["phase"] == "source_checked", report
        template, concrete = (next(d for d in report["declarations"] if d["name"] == name) for name in ("P", "C"))
        assert template["inputs"][0]["type"] == concrete["inputs"][0]["type"]
        assert template["outputs"][0]["type"] == concrete["outputs"][0]["type"]
        assert concrete["inputs"][0]["display"] == "F"
        assert report["instantiations"]
        common(program)

with case("concrete protocols get the same source type check as families"):
    text = '''module {
      fn Id(x:"koala-bear"::Element)->"koala-bear"::Element{return x;}
      protocol P {roles(A);inputs(A x:"koala-bear"::Element);outputs(A "koala-bear"::Element);
        local A:let y=Id(x);return y;}
      instance I:P{roles(A=Alice);}entry E=I;
    }'''
    malformed = text.replace('inputs(A x:"koala-bear"', 'inputs(A x:"bls12-381.fr"')
    commands.source("protocol-source", malformed, refuses="source-call-type")
    report = analyze(malformed)
    protocol = next(d for d in report["declarations"] if d["name"] == "P")
    assert report["phase"] == "semantic_error" and protocol["body_state"] == "deferred"
    # Mutate the portable input independently, so source refusal cannot stand
    # in for the common checker. Its own owner still rejects the same mismatch.
    portable = common(text)
    assert portable[0] == "zkc.protocol/1"
    portable[3][0][4][0][2] = "field:bls12-381.fr"
    commands.source("protocol-admit", json.dumps(portable), refuses="interactive-local-signature")

with case("profile defaults are resolved before source type retention"):
    text = '''module "arkworks.bls12-381/1" {
      fn Id(x:field)->field {return x;}
      fn VectorId(x:Vector<field>)->Vector<field> {return x;}
    }'''
    report = analyze(text)
    assert report["phase"] == "source_checked", report
    for name, expected in (("Id", "field:bls12-381.fr"), ("VectorId", "vector:bls12-381.fr")):
        d = next(d for d in report["declarations"] if d["name"] == name)
        assert d["inputs"][0]["display"] == d["outputs"][0]["display"] == expected
    common(text)


with case("quoted loop count never captures a natural parameter"):
    for parameters in ("", "<F:Field>"):
        text = 'module {protocol P' + parameters + '{roles(A);parameters(N);loop "N" carry()->(){yield;}return;}}'
        commands.source("protocol-source", text, refuses="source-protocol-count")


with case("unused dependency declarations bind their complete contracts"):
    text = '''module {
      protocol Child<F:Field>{roles(A);return;}
      protocol P<F:Field>{roles(A);dependencies(c:Child::<F=F>());return;}
    }'''
    assert analyze(text)["phase"] == "source_checked"
    commands.source("protocol-source", text.replace("F=F", 'F="F"'), refuses="source-name-unresolved")
    commands.source("protocol-source", text.replace("Child::<F=F>()", "Child()"), refuses="source-static-required")
    commands.source("protocol-source", text.replace("protocol P<F:Field>", "protocol P<F:domain Field>"), refuses="source-protocol-requirement")


with case("static values remain queryable without emitting constant declarations"):
    report = analyze("module {const N:index=M*2;const M:index=4;}")
    constants = {d["name"]: d for d in report["declarations"] if d["kind"] == "constant"}
    assert report["phase"] == "source_checked"
    assert constants["N"]["constant_value"] == 8 and constants["M"]["constant_value"] == 4
    assert all(d["sort"] == "index" and d["signature_checked"] for d in constants.values())
    assert common("module {const N:index=8;}") == common("module {}")

for label, fragment, code in (
    ("function type", "fn Bad<G:ScalarAction>(x:G.Scalar::Element)->G::Scalar::Element{return x;}", "source-name-unresolved"),
    ("family type", "protocol Bad<G:ScalarAction>{roles(A);inputs(A x:G.Scalar::Element);return;}", "source-name-unresolved"),
    ("function static argument", "fn Bad<G:ScalarAction>(x:G::Scalar::Element)->G::Scalar::Element{let y=Id::<G.Scalar>(x);return y;}", "source-name-unresolved"),
    ("family static argument", "protocol Bad<G:ScalarAction>{roles(A);inputs(A x:G::Scalar::Element);local A:let y=Id::<G.Scalar>(x);return;}", "source-name-unresolved"),
    ("function requirement", "fn Bad<G:domain Group>() -> () requires(Field(G.Scalar)){return;}", "source-name-unresolved"),
    ("function where", "fn Bad<G:domain Group>() -> () where G.Scalar:Field {return;}", "source-name-unresolved"),
    ("bundle requirement", "bundle Bad(G)=(Field(G.Scalar));", "source-name-unresolved"),
    ("family requirement", "protocol Bad<G:domain Group> requires(Field(G.Scalar)){roles(A);return;}", "source-name-unresolved"),
):
    with case(f"dotted roots are opaque in {label}"):
        text = "module {fn Id<F:Field>(x:F::Element)->F::Element{return x;}" + fragment + "}"
        commands.source("protocol-source", text, refuses=code)
        assert analyze(text)["phase"] == "semantic_error"

with case("explicit projections check before and after family selection"):
    text = '''module {
      protocol P<G:ScalarAction>{roles(A);inputs(A x:G::Scalar::Element);
        outputs(A G::Scalar::Element);return x;}
      SELECTION
    }'''
    for selection in ("", "configure C=P(G=bls12-381.g1);"):
        valid = text.replace("SELECTION", selection)
        assert analyze(valid)["phase"] == "source_checked"
        common(valid)
        commands.source("protocol-source", valid.replace("G::Scalar", "G.Scalar"), refuses="source-name-unresolved")

with case("function configurations preserve root quotation and projection syntax"):
    text = '''module {fn Id<F:Field>(x:F::Element)->F::Element{return x;}
      configure C=Id(F=ACTUAL);}'''
    expected = common(text.replace("ACTUAL", '"bls12-381.fr"'))
    for actual in ("bls12-381.fr", "bls12-381.g1::Scalar", '"bls12-381.g1"::Scalar'):
        assert common(text.replace("ACTUAL", actual)) == expected
    for actual in ("bls12-381.g1.Scalar", '"bls12-381.g1.Scalar"'):
        commands.source("protocol-source", text.replace("ACTUAL", actual), refuses="source-name-unresolved")

with case("generic binder names cannot impersonate common domain projections"):
    commands.source("protocol-source", 'module {fn Bad<"G.Scalar":Field>() -> () {return;}}', refuses="source-static-name")
    commands.source("protocol-source", 'module {bundle Bad("G.Scalar")=(Field(G::Scalar));}', refuses="source-name-unresolved")

with case("family locals must have a supported specialization route"):
    text = '''module {
      fn H<>() -> () {return;}
      fn Id<F:Field>(x:F::Element)->F::Element{return x;}
      configure Open=Id();
      configure Closed=H();
      protocol P<F:Field>{roles(A);inputs(A x:F::Element);BODY return;}
      SELECTION
    }'''
    for body in ("local A:H();", "local A:let y=Open::<F>(x);", "local A:let y=Open(x);"):
        invalid = text.replace("BODY", body).replace("SELECTION", "")
        commands.source("protocol-source", invalid, refuses="source-local-configuration")
    for body in ("local A:H::<>();", "local A:Closed();", "local A:let y=Id::<F>(x);"):
        for selection in ("", "configure C=P(F=koala-bear);"):
            valid = text.replace("BODY", body).replace("SELECTION", selection)
            assert analyze(valid)["phase"] == "source_checked"
            common(valid)

print(f"frontend model and family bodies: {commands.save()} commands checked")
