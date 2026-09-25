"""Generic source authoring, admission, specialization and physical planning."""

import copy
import json
from pathlib import Path
from commands import Commands
from tools import corpus, records


root = Path(__file__).resolve().parents[2]
source = (corpus / "generic-operations.pir").read_text()


commands = Commands(records())
run = commands.source


def compile_library(library):
    return json.loads(run("protocol-compile", json.dumps(library)))


library = json.loads(run("protocol-source", source))
assert library[0] == "zkc.library/1" and len(library[1]) == 3
assert library[3][2] == []  # Original source has no generated executable body.
printed = run("protocol-format", json.dumps(library))
assert json.loads(run("protocol-source", printed)) == library
assert run("protocol-format", printed) == printed
logical = json.loads(run("protocol-export", run("protocol-import", source)))
assert logical[0] == "zkc.protocol/1" and len(logical[2]) == 4
assert sorted(f[5][0] for f in logical[2]) == ["Both", "Fold", "Fold", "Scale"]
folds = [f for f in logical[2] if f[5][0] == "Fold"]
assert folds[0][5] == folds[1][5] == ["Fold", [["F", "bls12-381.fr"]]]
calls = {r[1]: r[3] for r in logical[3][0][7] if r[0] == "local"}
assert calls["right"] == calls["shared"] != calls["left"]
assert len({f[1] for f in logical[2]}) == 4
prepared = json.loads(run("protocol-prepare", source))
assert prepared[0] == "zkc.protocol/1" and len(prepared[2]) == 5
original_calls = {r[1]: r[3] for r in library[3][3][0][7] if r[0] == "local"}
prepared_calls = {r[1]: r[3] for r in prepared[3][0][7] if r[0] == "local"}
assert prepared_calls == original_calls
assert {f[1] for f in prepared[2]} == set(original_calls.values())
assert {f[5][0] for f in prepared[2]} == {"Fold", "Scale", "Both"}
assert json.loads(run("protocol-prepare", json.dumps(prepared))) == prepared
# Preparing source names does not change the ordinary shared compilation path.
assert json.loads(run("protocol-export", run("protocol-import", source))) == logical
physical = compile_library(library)
bindings = {b[0]: b for b in physical[1]}
contracts = [b[1] for b in bindings.values()]
assert contracts.count("table.relayout") == 2
assert contracts.count("poly.fold") == 2
assert "curve.scale" in contracts and "bool.and" in contracts
assert {b[3] for b in bindings.values() if b[1] == "poly.fold"} == {
    "arkworks/poly.fold", "arkworks-msb/poly.fold"}
assert sorted(f[5] for f in physical[3]) == sorted(f[5] for f in logical[2])
assert json.loads(run("protocol-export", run("protocol-physical-ir", source))) == physical

# Unused partial configurations emit no code. Aliases share physical code only
# when all semantic bindings and fixed implementation choices agree.
unused = copy.deepcopy(library)
unused[2].append(["configure", "AnotherPartial", "Partial", [], []])
assert compile_library(unused) == physical
changed = copy.deepcopy(library)
changed[2][1][4] = []
shared = compile_library(changed)
assert len(shared[3]) == 3 and all(b[1] != "table.relayout" for b in shared[1])

# Source body participates in the specialization key, even for unreachable
# producers. Caller spelling never silently substitutes for definition identity.
modified = copy.deepcopy(library)
modified[1][0][6][0][1] = "another_fold"
modified[2][1][4][0][0] = "another_fold"
new = compile_library(modified)
assert {f[1] for f in new[3] if f[5][0] == "Fold"}.isdisjoint(
    f[1] for f in physical[3] if f[5][0] == "Fold")

for mutate, code in [
    (lambda x: x[1][0].__setitem__(3, []), "generic-public-requirement"),
    (lambda x: x[1][1][4][1].__setitem__(1, "field:G"), "generic-type"),
    (lambda x: x[2][1][3][0].__setitem__(1, "bls12-381.g1"), "generic-configuration-sort"),
    (lambda x: x[2][3].__setitem__(3, [["F", "bls12-381.fr"]]), "generic-configuration-rebinding"),
    (lambda x: x[2][0].__setitem__(2, "Shared"), "generic-configuration-reference"),
    (lambda x: x[2][1][4][0].__setitem__(0, "missing"), "generic-implementation-site"),
    (lambda x: x[2][1][4][0].__setitem__(1, "arkworks/curve.scale"), "binding-implementation"),
    (lambda x: x[3][3][0][7][1].__setitem__(3, "Unused"), "generic-open-instance"),
    (lambda x: x[1][0][6][0].__setitem__(3, []), "generic-static-arity"),
    (lambda x: x[1][0][6][0].__setitem__(5, ["missing", "r"]), "generic-value-reference"),
    (lambda x: x[1].append(copy.deepcopy(x[1][0])), "generic-duplicate-symbol"),
    (lambda x: x[1][0].__setitem__(5, ["group:F"]), "generic-type"),
    (lambda x: x[1][0][6][0].__setitem__(2, "undeclared"), "generic-operation"),
    (lambda x: x[1][0][6][0].__setitem__(4, ["extra"]), "interactive-kernel-parameters"),
]:
    broken = copy.deepcopy(library)
    mutate(broken)
    run("protocol-import", json.dumps(broken), refuses=code)

# Field literals mean natural casts at the generic source level. Independent
# Python integer arithmetic checks the compiled canonical constant.
modulus = 52435875175126190479447740508185965837690552500527637822603658699938581184513
literal = copy.deepcopy(library)
literal[1].append(["generic_function", "Literal", [["F", "Field"]],
    [["Field", ["F"]]], [], ["field:F"], [
        ["op", "constant", "field.constant", ["F"], [str(modulus * 3 + 17)], [], ["n"]],
        ["return", ["n"]]]])
literal[2].append(["configure", "Number", "Literal", [["F", "bls12-381.fr"]], []])
literal[3][3][0][7].insert(-1, ["local", "constant", "P", "Number", [], ["n"]])
assert json.loads(run("protocol-source", run("protocol-format", json.dumps(literal)))) == literal
result = compile_library(literal)
function = next(f for f in result[3] if f[5][0] == "Literal")
assert function[4][0][3] == ["17"]


for source, code in [
    ('module { fn Dup<T: domain Transcript>(t: Transcript<T>)->(Transcript<T>, Transcript<T>){return(t,t);} }', 'generic-resource-reuse'),
    ('module { fn Bad<F: domain Bogus>()->(){return();} }', 'generic-declared-sort'),
    ('module { fn Bad<G: domain Group>()->() requires (CommRing(G)){return();} }', 'generic-predicate-sort'),
    ('module { fn Bad<F: domain Field>()->() requires (CommRing(F,F)){return();} }', 'generic-predicate-arity'),
    ('module { fn Bad<F: domain Field>()->() requires (Unknown(F)){return();} }', 'source-name-unresolved'),
    ('module { fn Equal<E: domain Codec,D: domain Codec,X: domain Codec>()->() requires ("="(E,X),"="(X,D)){return();} configure C=Equal(E="zkcv.bool/1",D="zkcv.field.bls12-381.fr/1"); }', 'binding-requirement'),
    ('module { fn Bad<E: domain Codec,D: domain Codec,F: domain Field>()->() requires ("="(E,D),Encodes.field(E,F)){return();} configure C=Bad(D="zkcv.bool/1",F=bls12-381.fr); }', 'binding-requirement'),
    ('module { fn Fold<F: domain Field>(a:Table<F>,r:F::Element)->(Table<F>) requires (CommRing(F)){[f]let b = poly::fold::<F>(a,r);return(b);} configure Bad=Fold() using(f="arkworks/curve.scale"); }', 'binding-implementation'),
]:
    run("protocol-admit", source, refuses=code)
run("protocol-admit", 'module { fn Open<C: domain Commitment>(s:OpeningState<C>,p:Point<C::PointField>)->(C::EvaluationField::Element,Proof<C>) requires(MultilinearOpening(C)){[open]let (v,q) = pcs::open::<C>(s,p);return(v,q);} }')
run("protocol-admit", 'module { fn Good<E: domain Codec,D: domain Codec,F: domain Field>()->() requires ("="(E,D),Encodes.field(E,F)){return();} configure C=Good(D="zkcv.field.bls12-381.fr/1",F=bls12-381.fr); }')
print(f"generic libraries: {commands.save()} checks; source roundtrip, requirements, partial bindings, sharing, mixed plans, refusals")
