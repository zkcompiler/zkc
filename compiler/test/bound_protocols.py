"""Explicit operation bindings through text, MLIR, projection and planning."""

import copy
import json
from pathlib import Path
from commands import Commands
from tools import corpus, optimizer, records


root = Path(__file__).resolve().parents[2]
source = (corpus / "bound-operations.pir").read_text()


commands = Commands(records())
run = commands.source


def reject(value, code):
    run("protocol-import", json.dumps(value), refuses=code)


common = json.loads(run("protocol-source", source))
assert common[0] == "zkc.protocol/1" and isinstance(common[1], list)
printed = run("protocol-format", json.dumps(common))
assert json.loads(run("protocol-source", printed)) == common
mlir = run("protocol-import", source)
assert "pir.operation_binding" in mlir and "binding = @empty" in mlir
assert "profile =" not in mlir
restored = json.loads(run("protocol-export", mlir))
assert restored[0:2] == common[0:2]  # Local SSA spellings may canonicalize.
projected = json.loads(run("protocol-project", source))
assert projected[0] == "zkc.participants/1" and projected[1] == common[1]
physical = json.loads(run("protocol-compile", source))
assert physical[0] == "zkc.participants/1" and physical[2] == "physical"
assert all(b[3].startswith("arkworks/") for b in physical[1])
assert all("@" in port[1] for f in physical[3] for port in f[2])

directory = records()
selections = Path(directory) / "implementations.json"
selections.write_text(json.dumps([["fold_left", "arkworks-msb/poly.fold"]]))
option = "--implementations=" + str(selections)
mixed = json.loads(run("protocol-compile", source, option))
binding = {r[0]: r for r in mixed[1]}
assert binding["fold_left"][3] == "arkworks-msb/poly.fold"
assert binding["fold_right"][3] == "arkworks/poly.fold"
conversions = [b for b in mixed[1] if b[1] == "table.relayout"]
assert len(conversions) == 2
functions = {r[1]: r for r in mixed[3]}
left = functions["FoldLeft"][4]
assert [binding[op[2]][1] for op in left[:-1]] == [
    "table.relayout", "poly.fold", "table.relayout"]
assert left[1][1] == "fold"  # Original logical site is retained.
assert len(functions["FoldRight"][4]) == 2
physical_ir = run("protocol-physical-ir", source, option)
assert '"arkworks.mle-msb/1"' in physical_ir
assert '"arkworks.mle-lsb/1"' in physical_ir
assert json.loads(run("protocol-export", physical_ir)) == mixed
commands.run([optimizer, "--verify-each"], stdin=physical_ir)
# The same four refusals reach the claim commands in execution_bound_claims.py,
# which is a separate fact about those entry points; what this judges is the
# selection contract of protocol-compile itself.
for choices, error in [
    ([["missing", "arkworks/poly.fold"]], "binding-unknown-selection"),
    ([["fold_left", "arkworks/poly.fold"]] * 2, "binding-duplicate-selection"),
    ([["fold_left", "arkworks/curve.scale"]], "binding-implementation"),
    ([["fold_left", ""]], "binding-stage"),
]:
    selections.write_text(json.dumps(choices))
    run("protocol-compile", source, option, refuses=error)

for mutate, code in [
    (lambda x: x[1][0].__setitem__(2, ["bls12-381.g1"]), "binding-static-identity"),
    (lambda x: x[1][3].__setitem__(2, []), "binding-static-arity"),
    (lambda x: x[1][0].__setitem__(3, "arkworks/curve.scale"), "binding-implementation"),
    (lambda x: x[1].append(copy.deepcopy(x[1][0])), "binding-name"),
    (lambda x: x[2][0][2][0].__setitem__(1, "table"), "binding-type"),
    (lambda x: x[2][0][4][0].__setitem__(2, "scale"), "binding-operation-signature"),
    (lambda x: x[2][0][4][0].__setitem__(2, "uninstalled"), "binding-reference"),
    (lambda x: x[2][0].__setitem__(1, "fold_left"), "interactive-duplicate-symbol"),
]:
    damaged = copy.deepcopy(common)
    mutate(damaged)
    reject(damaged, code)

# Actual physical type/domain/representation corruption, independently supplied.
damaged = copy.deepcopy(physical)
damaged[3][0][2][0][1] = "table:bls12-381.fr@arkworks.mle-msb/1"
reject(damaged, "binding-operation-signature")
damaged = copy.deepcopy(physical)
damaged[1][0][3] = "arkworks-msb/poly.fold"
reject(damaged, "binding-operation-signature")

# Pairing binds two different associated groups even though their scalar field
# is identical. Exercise generic authoring, source codecs and actual MLIR SSA.
pairing_source = (corpus / "bn254-pairing.pir").read_text()
pairing_common = json.loads(run("protocol-source", pairing_source))
assert json.loads(run("protocol-source", run("protocol-format", json.dumps(pairing_common)))) == pairing_common
pairing_ir = run("protocol-import", pairing_source)
assert '"algebra.pairing_check"' in pairing_ir
pairing_plan = json.loads(run("protocol-compile", pairing_source))
selected = next(b for b in pairing_plan[1] if b[1] == "pairing.check")
assert selected[2:] == [["bn254.fr"], "arkworks/pairing.check"]
pairing_physical = run("protocol-physical-ir", pairing_source)
assert json.loads(run("protocol-export", pairing_physical)) == pairing_plan


verify_pairing = commands.verified


verify_pairing(pairing_ir)
verify_pairing(pairing_physical)
for before, after in [("bn254.g1", "bn254.g2"), ("bn254.g2", "bn254.g1")]:
    # Change actual group-vector SSA types without changing binding identities.
    verify_pairing(pairing_ir.replace('tensor<?x!algebra.group<"'+before+'">>',
                                      'tensor<?x!algebra.group<"'+after+'">>'),
                   "binding-operation-signature")
verify_pairing(pairing_ir.replace('"algebra.pairing_check"', '"algebra.curve_equal"'),
               "binding-operation")
verify_pairing(pairing_physical.replace('"arkworks.bn254-g1-vector/1"',
                                        '"arkworks.bn254-g2-vector/1"'),
               "binding-operation-signature")
run("protocol-source", pairing_source.replace("BNPair(left, right)", "BNPair(right, left)"),
    refuses="source-call-type")
run("protocol-source", pairing_source.replace("requires (PairingField(F))", "requires (Field(F))"),
    refuses="generic-public-requirement")

# Invalid static family, provider, attributes and operand ordering also refuse
# when the input is an independently authored physical JSON candidate.
for mutate, code in [
    (lambda b: b.__setitem__(2, ["bls12-381.fr"]), "binding-static-identity"),
    (lambda b: b.__setitem__(2, ["bn254.g1"]), "binding-static-identity"),
    (lambda b: b.__setitem__(2, []), "binding-static-arity"),
    (lambda b: b.__setitem__(3, "dalek/pairing.check"), "binding-implementation"),
]:
    bad = copy.deepcopy(pairing_plan)
    mutate(next(b for b in bad[1] if b[1] == "pairing.check"))
    reject(bad, code)
for corrupt_attributes in (False, True):
    bad = copy.deepcopy(pairing_plan)
    call = next(op for fn in bad[3] for op in fn[4]
                if op[0] == "op" and op[2] == selected[0])
    if corrupt_attributes:
        call[3] = ["0"]
        reject(bad, "interactive-kernel-parameters")
    else:
        call[4].reverse()
        reject(bad, "binding-operation-signature")

# The potential length failure prevents removal of unused pairing checks.
duplicate = pairing_source.replace(
    "[pair] let accepted = pairing::check::<F>(left, right);",
    "[unused] let unused = pairing::check::<F>(left, right);\n"
    "    [pair] let accepted = pairing::check::<F>(left, right);")
optimized = verify_pairing(run("protocol-import", duplicate), None, "--canonicalize", "--cse")
assert optimized.count('"algebra.pairing_check"(') == 2

# Reuse the independent authored coset pipeline with the BN254 convention.
coset_source = (corpus / "coset-kernels.pir").read_text().replace(
    "koala-bear", "bn254.fr")
verify_pairing(run("protocol-import", coset_source))
coset_physical = run("protocol-physical-ir", coset_source)
verify_pairing(coset_physical)
coset_plan = json.loads(run("protocol-compile", coset_source))
assert json.loads(run("protocol-export", coset_physical)) == coset_plan
for binding in coset_plan[1]:
    assert binding[3] == ("native/" if binding[1].startswith("indices.") else "arkworks/") + binding[1]
print(f"bound protocols: {commands.save()} checks; explicit bindings through text, "
      "MLIR, role projection and mixed-layout planning; BN254 pairing groups, "
      "codecs, binding selection and SSA refusals; the coset pipeline")
