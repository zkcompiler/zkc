"""Written AST controls at the public compiler boundary."""

import hashlib
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records
from project import project_arguments, project_inputs

commands = Commands(records())
fixtures = Path(__file__).parent / "fixtures" / "source-claims"


def inspect(source, name="written", modules=None):
    path = records() / (name + ".zkc")
    path.write_text(source)
    extra = []
    for module, text in (modules or {}).items():
        imported = records() / (name + "-" + module.replace("::", "-") + ".zkc")
        imported.write_text(text)
        extra.append(f"--module={module}={imported}")
    return json.loads(commands.run([
        compiler, "language-check", "--source-format=zkc",
        f"--module=written={path}", "--source-ast", *extra,
    ]))["source_ast"]


def declaration(document, owner):
    return next(row for row in document["declarations"] if row["owner"] == owner)


def node(record, path=()):
    return next(n for n in record["nodes"] if n["path"] == list(path))


def addresses(record):
    return [n["path"] for n in record["nodes"]]


with case("syntax precedes inference, notation lowering and generated entries"):
    source = """module written;
    pub math fn conjunction(x:bool,y:bool)->bool{return x&&y;}
    operator infixl(70) ⊙ = conjunction;
    math fn inferred(x:bool){let y=x;return y;}
    math fn generic<T:Type+Copy>(x:T)->T{return x;}
    math fn annotated(x:bool)->bool effects() where () {return x;}
    pub protocol P roles(A,B)(x:bool@A)->(ok:bool@B,copy:bool@B)
      spec {target t=relation(statement p=in.x@A){return p;} accept out.ok;}
      {let y=send A->B(x);let ok@B=y ⊙ y;return(ok,copy=ok);}
    """
    ast = inspect(source)
    assert ast["format"] == "zkc.source-ast/0"
    owners = {d["owner"] for d in ast["declarations"]}
    assert not any("::Inputs" in o or "::run" in o or "clause_" in o for o in owners)
    inferred = declaration(ast, "written::inferred")
    assert node(inferred)["result_type"] is None
    assert node(inferred)["effects"] is None
    assert not node(inferred)["requirements_written"]
    annotated = node(declaration(ast, "written::annotated"))
    assert annotated["effects"] == {"stop": False, "opaque": False}
    assert annotated["requirements_written"]
    generic = declaration(ast, "written::generic")
    assert node(generic, [["parameter", 0]])["permissions"] == ["Copy"]
    protocol = declaration(ast, "written::P")
    relation = node(protocol, [["clause", 0], ["subject", 0]])
    assert relation["name"] is None and relation["outputs"] == []
    notation = node(protocol, [["body", 0], ["stmt", 1], ["expr", 0]])
    assert notation["kind"] == "expr.notation_call" and notation["symbol"] == "⊙"
    assert node(protocol, [["body", 0], ["result", 0]])["shorthand"]
    for record in ast["declarations"]:
        paths = [json.dumps(p) for p in addresses(record)]
        assert len(paths) == len(set(paths)), record["owner"]
        assert all("binding" not in n or isinstance(n["binding"], (list, type(None)))
                   for n in record["nodes"])
    module = next(m for m in ast["sources"] if m["module"] == "written")
    assert module["bytes"] == len(source.encode())
    assert module["origin"] == "captured"
    for record in ast["declarations"]:
        for n in record["nodes"]:
            span = n["span"]
            if span["module"] == "written":
                assert 0 <= span["begin"] <= span["end"] <= len(source.encode())

with case("alpha renaming preserves paths while statement insertion renews them"):
    original = "module written; math fn f(x:bool){let y=x;return y;}"
    renamed = original.replace(" y", " z").replace("y=", "z=")
    a = declaration(inspect(original, "alpha-original"), "written::f")
    b = declaration(inspect(renamed, "alpha-renamed"), "written::f")
    assert addresses(a) == addresses(b)
    extra = original.replace("let y=x;", "let unused=x;let y=x;")
    c = declaration(inspect(extra, "alpha-inserted"), "written::f")
    assert node(c, [["body", 0], ["stmt", 1], ["pattern", 0]])["name"] == "y"
    assert node(a, [["body", 0], ["stmt", 0], ["pattern", 0]])["name"] == "y"

with case("claim addresses and domain spelling stay written"):
    source = (fixtures / "cardinality.zkc").read_text().replace("module claims;", "module written;")
    ast = inspect(source, "claims")
    module = declaration(ast, "written")
    claim = node(module, [["spec_block", 0], ["claim", 0]])
    assert claim["label"] == "sound"
    cardinality = next(n for n in module["nodes"]
                       if n["kind"] == "claim_expr.application" and n["text"] == "cardinality")
    assert node(module, cardinality["arguments"][0])["text"] == "Fr"
    assert "cardinalityDomain" not in json.dumps(ast)

with case("finite binders retain their written domains without synthetic lambdas"):
    source = """module written;
    type Vector<F:Field>=builtin("vector",F);
    domain Fr=field("koala-bear");
    fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,
        step:fn(S,item:I)->S effects(stop) where item_from(item,rows))->S
        effects(stop)=finite("local.fold");
    fn sum<I:Type+Copy+Drop,F:Field>(rows:domain<I>,
        term:fn(item:I)->F effects(stop) where item_from(item,rows))->F
        effects(stop){return fold(rows,0,fn(state,item)=>state+term(item));}
    reduction ∑=sum;
    fn f(xs:Vector<Fr>,ys:Vector<Fr>)->Fr{return ∑ (x in xs)(y in ys),x*y;}
    """
    record = declaration(inspect(source, "binders"), "written::f")
    reductions = [n for n in record["nodes"] if n["kind"] == "expr.reduction"]
    assert len(reductions) == 1 and reductions[0]["symbol"] == "∑"
    assert len(reductions[0]["binders"]) == 2
    assert not any(n["kind"] in ("expr.lambda", "expr.domain_product") for n in record["nodes"])
    for i, domain in enumerate(("xs", "ys")):
        binder = node(record, reductions[0]["binders"][i])
        assert node(record, binder["domain"])["text"] == domain
    assert reductions[0]["predicate"] is None

with case("module links and import alias omissions are retained"):
    source = """module written; pub module child;
    use library as lib; use library;
    math fn f(x:bool)->bool{return lib::same(x);}
    """
    ast = inspect(source, "modules", {
        "written::child": "module written::child; math fn g(x:bool)->bool{return x;}",
        "library": "module library;pub math fn same(x:bool)->bool{return x;}",
    })
    root = declaration(ast, "written")
    links = [n for n in root["nodes"] if n["kind"] == "module_link"]
    assert len(links) == 1 and links[0]["name"] == "child" and links[0]["public"]
    assert sum(d["owner"] == "written::child" for d in ast["declarations"]) == 1
    assert node(root, [["import", 0]])["alias"] == "lib"
    assert node(root, [["import", 1]])["alias"] is None

with case("one written construction handler keeps ordered selectors and one body"):
    source = """module written;
    interface TestTranscript<T:Field>{
      type State:Copy;
      fn initialize()->State effects(stop,opaque);
      fn observe(t:State,v:T)->State effects(stop,opaque);
      fn draw(t:State)->(State,T) effects(stop,opaque);
    }
    protocol Round<T:Field> roles(P,V)
      (secret:T@P,challenges:Random<T>@V)->(ok:bool@V){
      #[site(first)] let a=send P->V(secret);
      #[site(challenge)] let c=challenges.draw();
      #[site(delivery)] let r=send V->P(c);
      #[site(last)] let b=send P->V(secret+r);
      return b==a+c;
    }
    construction Derived<T:Field,H:TestTranscript<T>> for Round<T>{
      transcript H; replace challenges;
      on start(t){return t;}
      on message {first,last}(t,value){return H::observe(t,value);}
      on message delivery(t,value){return t;}
      on query challenge(t){return H::draw(t);}
    }
    """
    ast = inspect(source, "handlers")
    record = declaration(ast, "written::Derived")
    rules = node(record)["construction"]["rules"]
    assert len(rules) == 4
    first = node(record, rules[1])
    assert [[node(record, part)["name"] for part in path]
            for path in first["selectors"]] == [["first"], ["last"]]
    handler = node(record, first["handler"])
    assert handler["name"] is None and handler["body"] is not None
    paths = [json.dumps(p) for p in addresses(record)]
    assert len(paths) == len(set(paths))
    assert not any(d["owner"].startswith("written::Derived::") for d in ast["declarations"])
    state = declaration(ast, "written::TestTranscript::State")
    assert node(state)["permissions"] == ["Copy"]

for family in ("schnorr", "fri"):
    with case(f"complete {family} capture retains bounded sources and linked syntax"):
        manifest = Path(__file__).resolve().parents[2] / "examples/projects" / family / "zkc.toml"
        report = json.loads(commands.run([
            compiler, "language-check", "--source-format=zkc", "--source-ast",
            *project_arguments(manifest),
        ]))
        ast = report["source_ast"]
        modules, _ = project_inputs(manifest)
        source_rows = {row["module"]: row for row in ast["sources"]}
        for module, path in modules.items():
            encoded = path.read_bytes()
            assert source_rows[module]["bytes"] == len(encoded)
            assert source_rows[module]["sha256"] == hashlib.sha256(encoded).hexdigest()
        owners = {record["owner"] for record in ast["declarations"]}
        assert len(owners) == len(ast["declarations"])
        for record in ast["declarations"]:
            keys = {json.dumps(n["path"]) for n in record["nodes"]}
            assert len(keys) == len(record["nodes"]) and "[]" in keys
            for n in record["nodes"]:
                span = n["span"]
                assert 0 <= span["begin"] <= span["end"] <= source_rows[span["module"]]["bytes"]
            for member in node(record)["members"]:
                if "owner" in member:
                    assert member["owner"] in owners

            def check_edges(value):
                if isinstance(value, dict):
                    for child in value.values():
                        check_edges(child)
                elif isinstance(value, list):
                    if value and all(isinstance(part, list) and len(part) == 2
                                     and isinstance(part[0], str) and type(part[1]) is int
                                     for part in value):
                        assert json.dumps(value) in keys, (record["owner"], value)
                    else:
                        for child in value:
                            check_edges(child)

            check_edges(record["nodes"])

with case("source AST option is unique and check-only"):
    path = records() / "options.zkc"
    path.write_text("module written;")
    arguments = ["--source-format=zkc", f"--module=written={path}"]
    commands.run([compiler, "language-check", *arguments, "--source-ast", "--source-ast"],
                 refuses="source.options")
    commands.run([compiler, "language-emit", *arguments, "--source-ast"],
                 refuses="source.options")

print(f"Written source controls: {counted()} cases; {commands.save()}")
