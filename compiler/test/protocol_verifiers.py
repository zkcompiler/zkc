#!/usr/bin/env python3
"""Native SSA/symbol diagnostics; no JSON admission is used for negative inputs."""
import json
from bls_fixture import declaration, REPRESENTATIONS, PCS, module
from pathlib import Path
from commands import Commands
from tools import compiler, examples, optimizer, records

ARK = "arkworks.multilinear.bls12-381/1"
GROUP = "reference.group/1"
# Independently stated portable contracts, including the explicit opening state.
KERNELS = [
    ("field.constant", "algebra.exec.field_constant", [], ["field"]),
    ("field.add", "algebra.exec.field_add", ["field", "field"], ["field"]),
    ("field.mul", "algebra.exec.field_multiply", ["field", "field"], ["field"]),
    ("field.equal", "algebra.exec.field_equal", ["field", "field"], ["bool"]),
    ("bool.and", "algebra.exec.bool_and", ["bool", "bool"], ["bool"]),
    ("control.require", "local.exec.require", ["bool"], []),
    ("poly.product_sum", "poly.exec.product_sum", ["table", "table"], ["field"]),
    ("poly.product_round", "poly.exec.product_round", ["table", "table"], ["round"]),
    ("poly.boundary", "poly.exec.boundary", ["round"], ["field"]),
    ("poly.round_evaluate", "poly.exec.round_evaluate", ["round", "field"], ["field"]),
    ("poly.fold", "poly.exec.fold", ["table", "field"], ["table"]),
    ("poly.evaluate", "poly.exec.mle_evaluate", ["table", "point"], ["field"]),
    ("poly.empty_point", "poly.exec.empty_point", [], ["point"]),
    ("poly.append_point", "poly.exec.append_point", ["point", "field"], ["point"]),
    ("pcs.commit", "pcs.exec.commit", ["prover_key", "table"], ["commitment", "opening_state"]),
    ("pcs.open", "pcs.exec.open", ["opening_state", "point"], ["field", "proof"]),
    ("pcs.check", "pcs.exec.check", ["verifier_key", "commitment", "point", "field", "proof"], ["bool"]),
    ("random.draw", "crypto.exec.random_draw", ["rng"], ["field", "rng"]),
    ("curve.scale", "algebra.exec.group_scale", ["group", "field"], ["group"]),
    ("curve.commit", "crypto.exec.curve_commit", ["groups", "nonce"], ["groups", "nonce"]),
    ("curve.response", "crypto.exec.curve_response", ["field", "field", "nonce"], ["field"]),
    ("curve.equal", "algebra.exec.group_equal", ["group", "group"], ["bool"]),
]
TYPES = {
    "bool": "i1", "field": '!algebra.field<"bls12-381.fr">',
    "scalar": '!algebra.field<"reference.scalar">',
    "table": '!poly.multilinear<"bls12-381.fr">',
    "round": '!poly.quadratic<"bls12-381.fr">',
    "point": '!poly.point<"bls12-381.fr">',
    "group": '!algebra.group<"bls12-381.g1">',
    "groups": 'tensor<?x!algebra.group<"bls12-381.g1">>',
    **{k: f'!local.capability<"{k}:bls12-381.fr">' for k in ["rng", "nonce"]},
    **{k: f'!pcs.object<"{PCS}", "{k}">' for k in
       ["prover_key", "verifier_key", "commitment", "proof", "opening_state"]},
}


commands = Commands(records())


def run(tool, *args, text=None, op=None, code=None):
    """`op` is the operation the diagnostic must name: the offending one, not
    the exporter that reached it."""
    printed = commands.run([tool, *args], stdin=text, refuses=code if op else None)
    if op:
        assert f"error: '{op}' op" in commands.last.stderr, commands.last.stderr
    return printed


def wrapped(body, profile=ARK, stage="common"):
    profile = {"common": "protocol_exec", "logical": "exec", "physical": "physical"}[stage]
    contract = "" if stage == "common" else ", execution_contract = #protocol.execution_contract<legacy_participants_v1>"
    return (f'module {{ "protocol.module"() <{{profile = #protocol.profile<{profile}>{contract}}}> '
            f'({{\n{body}\n}}) : () -> () }}')


def kernel_ir(op, ins, outs, profile=ARK, physical=False, key=None, parameters="[]"):
    args = ", ".join(f"%a{i}: {t}" for i, t in enumerate(ins))
    operands = ", ".join(f"%a{i}" for i in range(len(ins)))
    result = (f"%r:{len(outs)} = " if outs else "")
    contract = next((k for k, spelling, _, _ in KERNELS if spelling == op),
                    key.removeprefix("arkworks/") if key else "curve.scale")
    if contract not in {k for k, _, _, _ in KERNELS}: contract = "bool.and"
    extra = ', binding = @binding' + (f', kernel = "{key}"' if key is not None else "")
    code = (f'local.func @f({args}) {{\n'
            f'  {result}"{op}"({operands}) <{{site = "s", parameters = {parameters}{extra}}}> '
            f': ({", ".join(ins)}) -> ({", ".join(outs)})\n'
            '  return\n}')
    code += '\n' + declaration(contract, physical=physical)
    text = wrapped(code, profile, "physical" if physical else "common")
    return text


def bad(text, op, code):
    run(optimizer, text=text, op=op, code=code)


def proto(name, deps="[]", body=None, roles='["P"]', ft="(i1) -> i1"):
    external = body is None
    if body is not None: body = body.replace("protocol.finish", "protocol.return")
    region = "" if external else f"^bb0(%a: i1):\n{body}"
    return (f'"protocol.exec_func"() <{{sym_name = "{name}", dependencies = {deps}, '
            f'function_type = {ft}, roles = {roles}, input_roles = ["P"], '
            f'output_roles = ["P"], parameters = [], external = {str(external).lower()}}}> '
            f'({{{region}}}) : () -> ()\n')


def participant(name, body, role="P", instance="i", ft="(i1) -> i1"):
    argument_type = ft.split(")")[0][1:]
    return (f'"protocol.participant"() <{{sym_name = "{name}", function_type = {ft}, '
            f'role = "{role}", instance = "{instance}", parameters = []}}> '
            f'({{^bb0(%a: {argument_type}):\n{body}}}) : () -> ()\n')


def instance(name, protocol, deps="[]", roles='[["P", "P"]]'):
    return (f'"protocol.instance"() <{{sym_name = "{name}", protocol = @{protocol}, '
            f'dependencies = {deps}, parameters = [], roles = {roles}}}> : () -> ()\n')


def entry(targets):
    return f'"protocol.entry"() <{{sym_name = "main", targets = {targets}}}> : () -> ()\n'


FINISH = '"protocol.finish"(%a) : (i1) -> ()\n'
CALL = '%r = "protocol.local_call"(%a) <{callee = @f, site = "s", role = "P"}> : (i1) -> i1\n' + FINISH
DEPEND = '%r = "protocol.call"(%a) <{dependency = "alias", site = "s"}> : (i1) -> i1\n' + FINISH
PARTCALL = '%r = "protocol.participant_call"(%a) <{callee = @child, site = "s"}> : (i1) -> i1\n' + FINISH

directory = records()
directory = Path(directory)
for key, op, inputs, outputs in KERNELS:
    profile = GROUP if key.startswith("curve.") else ARK
    params = '["0"]' if key == "field.constant" else "[]"
    ins, outs = [TYPES[t] for t in inputs], [TYPES[t] for t in outputs]
    bad(kernel_ir(op, ins + ["i1"], outs, profile, parameters=params), op, "binding-operation-signature")
    bad(kernel_ir(op, ins, outs + ["i1"], profile, parameters=params), op, "binding-operation-signature")
    wrong = [TYPES["field"] if t == "bool" else "i1" for t in outputs] or ["i1"]
    bad(kernel_ir(op, ins, wrong, profile, parameters=params), op, "binding-operation-signature")
    if ins:
        wrong = ["i1" if inputs[0] != "bool" else TYPES["field"], *ins[1:]]
        bad(kernel_ir(op, wrong, outs, profile, parameters=params), op, "binding-operation-signature")
    physical_inputs = [f'!plan.data<{TYPES[t]}, "{REPRESENTATIONS[t]}">' for t in inputs]
    physical_outputs = [f'!plan.data<{TYPES[t]}, "{REPRESENTATIONS[t]}">' for t in outputs]
    prefix = "arkworks/"
    bad(kernel_ir("plan.kernel", physical_inputs, physical_outputs + ['!plan.data<i1, "native.bool/1">'],
                  profile, True, prefix + key, params), "plan.kernel", "binding-operation-signature")

# Actual type parameters, including PCS scheme, cannot be substituted.
for t in ['!algebra.field<"f7">', '!algebra.field<"reference.scalar">']:
    bad(kernel_ir("algebra.exec.field_add", [t, t], [t]), "algebra.exec.field_add", "binding-operation-signature")
bad(kernel_ir("pcs.exec.open", ['!pcs.object<"other", "opening_state">', TYPES["point"]],
              [TYPES["field"], TYPES["proof"]]), "pcs.exec.open", "binding-operation-signature")
bad(kernel_ir("algebra.exec.group_scale", [TYPES["group"], TYPES["scalar"]], [TYPES["group"]]),
    "algebra.exec.group_scale", "binding-operation-signature")
bad(kernel_ir("algebra.exec.bool_and", ["i1"]*2, ["i1"], ARK, True), "algebra.exec.bool_and", "interactive-kernel-stage")
bad(kernel_ir("algebra.exec.bool_and", ["i1"]*2, ["i1"], parameters='["extra"]'), "algebra.exec.bool_and", "interactive-kernel-parameters")
bad(kernel_ir("algebra.exec.field_constant", [], [TYPES["field"]]), "algebra.exec.field_constant", "interactive-kernel-parameters")
for p, code in [('[true]', 'binding-parameters'), ('["01"]', 'noncanonical-natural'),
                ('["-1"]', 'expected-natural'), ('["not_a_number"]', 'expected-natural'),
                ('["52435875175126190479447740508185965837690552500527637822603658699938581184513"]', 'interactive-constant')]:
    bad(kernel_ir("algebra.exec.field_constant", [], [TYPES["field"]], parameters=p), "algebra.exec.field_constant", code)
data = '!plan.data<i1, "native.bool/1">'
for key in ["bool.and", "reference/bool.and", "arkworks/arkworks/bool.and", "arkworks/missing"]:
    code = "binding-implementation"
    bad(kernel_ir("plan.kernel", [data]*2, [data], ARK, True, key), "plan.kernel", code)
for t in [f'!plan.data<i1, "{GROUP}">', f'!plan.data<{TYPES["field"]}, "{ARK}">']:
    bad(kernel_ir("plan.kernel", [t, data], [data], ARK, True, "arkworks/bool.and"),
        "plan.kernel", "binding-operation-signature")
bad(kernel_ir("plan.kernel", ["i1"]*2, ["i1"], ARK, True, "arkworks/bool.and"),
    "plan.kernel", "must be")
bad('module { local.func @f(%a: i1) { %r = "algebra.exec.bool_and"(%a, %a) <{parameters = [], site = "s"}> : (i1, i1) -> i1\n return } }',
    "algebra.exec.bool_and", "interactive-kernel-context")

# These native call fixtures have no protocol.module, and cannot reach JSON export.
# Exact callee kinds and real SSA signatures must be checked by MLIR itself.
def bare(text):
    return "module {\n" + text + "\n}"
f = "local.func private @f(i1) -> i1\n"
run(optimizer, text=bare(f + proto("parent", body=CALL)))
bad(bare(proto("f") + proto("parent", body=CALL)), "protocol.local_call", "interactive-symbol-kind")
bad(bare(proto("parent", body=CALL)), "protocol.local_call", "interactive-symbol-kind")
bad(bare(f + proto("parent", body=CALL.replace('callee = @f, ', ''))),
    "protocol.local_call", "callee")
for ft in ["(i32) -> i1", "(i1) -> i32", "() -> i1"]:
    bad(bare(f"local.func private @f{ft}\n" + proto("parent", body=CALL)),
        "protocol.local_call", "interactive-call-signature")
bad(bare(f + proto("parent", body=CALL.replace('role = "P"', 'role = "Q"'))), "protocol.local_call", "interactive-local-role")
bad(bare(f + participant("parent", CALL)), "protocol.local_call", "parent")
run(optimizer, text=bare(f + participant("parent", CALL.replace(', role = "P"', '').replace("protocol.local_call", "local.call"))))

child = proto("child")
parent = proto("parent", '[["alias", @child, []]]', DEPEND)
# A global @alias is deliberately a different kind; only the declared alias matters.
run(optimizer, text=bare(child + "local.func private @alias()\n" + parent))
bad(bare(child + parent.replace('dependency = "alias"', 'dependency = "child"')),
    "protocol.call", "interactive-dependency")
bad(bare(proto("child", ft="(i32) -> i1") + parent), "protocol.call", "interactive-call-signature")
bad(bare(proto("child", ft="(i1) -> i32") + parent), "protocol.call", "interactive-call-signature")
bad(bare("local.func private @child(i1) -> i1\n" + proto("parent", '[["alias", @child, []]]')),
    "protocol.exec_func", "interactive-symbol-kind")
bad(bare(proto("parent", '[["alias", @missing, []]]')), "protocol.exec_func", "interactive-symbol-kind")
bad(bare(proto("child", roles='["Q"]') + proto("parent", '[["alias", @child, []]]')),
    "protocol.exec_func", "interactive-dependency-role")
for deps in ['[42 : i64]', '[["a", "child", []]]', '[["a", @child, []], ["a", @child, []]]', '[["a", @child, [true]]]', '[["a", @child]]']:
    bad(bare(child + proto("parent", deps)), "protocol.exec_func", "interactive-binding-attribute")
bad(bare(proto("parent", body=DEPEND)), "protocol.call", "interactive-dependency")

run(optimizer, text=bare(participant("child", FINISH, instance="different") + participant("parent", PARTCALL)))
bad(bare(f.replace("@f", "@child") + participant("parent", PARTCALL)), "protocol.participant_call", "interactive-symbol-kind")
bad(bare(participant("parent", PARTCALL)), "protocol.participant_call", "interactive-symbol-kind")
bad(bare(participant("child", FINISH, role="Q") + participant("parent", PARTCALL)), "protocol.participant_call", "interactive-call-role")
bad(bare(participant("child", '"local.stop"() <{site="stop", reason="incomplete"}> : () -> ()', ft="(i1) -> i32") + participant("parent", PARTCALL)), "protocol.participant_call", "interactive-call-signature")
bad(bare(participant("child", '"local.stop"() <{site="stop", reason="incomplete"}> : () -> ()', ft="(i32) -> i1") + participant("parent", PARTCALL)), "protocol.participant_call", "interactive-call-signature")

# Instance identity and the selected role map are checked, not only signatures.
defs = child + proto("other") + proto("parent", '[["alias", @child, []]]')
inst = instance("parent_i", "parent", '[["alias", @child_i]]')
run(optimizer, text=bare(defs + instance("child_i", "child") + inst))
bad(bare(f + instance("i", "f")), "protocol.instance", "interactive-symbol-kind")
bad(bare(instance("i", "missing")), "protocol.instance", "interactive-symbol-kind")
bad(bare(defs + instance("child_i", "other") + inst), "protocol.instance", "interactive-dependency-protocol")
bad(bare(defs + inst), "protocol.instance", "interactive-symbol-kind")
bad(bare(defs + inst.replace("@child_i", "@child")), "protocol.instance", "interactive-symbol-kind")
bad(bare(defs + instance("child_i", "child", roles='[["P", "Q"]]') + inst),
    "protocol.instance", "interactive-dependency-role")
bad(bare(defs + instance("parent_i", "parent")), "protocol.instance", "interactive-dependency-binding")
bad(bare(child + instance("i", "child", roles="[]")), "protocol.instance", "interactive-role-binding")
bad(wrapped(child + entry("[@child]")), "protocol.entry", "interactive-symbol-kind")
bad(wrapped(entry("[@missing]")), "protocol.entry", "interactive-symbol-kind")
bad(wrapped(entry('[["P", @missing]]')), "protocol.entry", "interactive-entry-targets")
bad(wrapped(f + entry('[["P", @f]]'), stage="logical"), "protocol.entry", "interactive-symbol-kind")
bad(wrapped(participant("p", FINISH) + entry('[["Q", @p]]'), stage="logical"), "protocol.entry", "interactive-entry-role")
bad(wrapped(participant("p", FINISH) + participant("q", FINISH, "Q", "j") +
            entry('[["P", @p], ["Q", @q]]'), stage="logical"), "protocol.entry", "interactive-entry-instance")

# Each portable contract stated above has a valid import and a complete pass
# route. The registry holds many more than these; that every registered kernel
# has well-formed contract facts is judged where the registry itself is
# visible, by compiler/test/operation_contracts.cpp.
for profile in [ARK, GROUP]:
    functions = []
    for key, _, inputs, outputs in KERNELS:
        if profile == ARK and key.startswith("curve."):
            continue
        if profile == GROUP and not (key.startswith("curve.") or key in ["bool.and", "control.require"]):
            continue
        args = [f"a{i}" for i in range(len(inputs))]
        results = [f"r{i}" for i in range(len(outputs))]
        functions.append(["function", key.replace(".", "_"), list(map(list, zip(args, inputs))), outputs,
                          [["op", "s", key, ["0"] if key == "field.constant" else [], args, results],
                           ["return", results]]])
    source = module(functions,
              [["protocol", "Empty", ["P"], [], [], [], [], [["return", []]]]],
              [["instance", "i", "Empty", [], [], [["P", "P"]]]], [["entry", "main", "i"]])
    path = directory / "kernels.json"
    path.write_text(json.dumps(source))
    common = run(compiler, "protocol-import", path)
    physical = run(optimizer, "--canonicalize", "--cse", "--zkc-project-participants",
                   "--zkc-select-physical", "--canonicalize", "--cse", text=common)
    run(optimizer, text=physical)

# The same two examples as interactive_protocols.py, which checks the stages
# themselves; what this adds is that canonicalization and common subexpression
# elimination around them leave the final plan equal to compiling in one step.
for name in ["group-exchange.json", "two-factor.json"]:
    common = run(compiler, "protocol-import", examples / name)
    physical = run(optimizer, "--canonicalize", "--cse", "--zkc-project-participants",
                   "--zkc-select-physical", "--canonicalize", "--cse", text=common)
    path = directory / "physical.mlir"
    path.write_text(physical)
    result = json.loads(run(compiler, "protocol-export", path))
    direct = json.loads(run(compiler, "protocol-compile", examples / name))
    assert result == direct
    if name == "two-factor.json":
        assert '"opening_state"' in common and '"opening_state"' in physical
# A foreign source stop remains the distinct participant incomplete terminator.
source = ["zkc.protocol/1", [], [],
          [["protocol", "Stop", ["P", "V"], [], [], [], [], [["stop", "s", "P", "incomplete"]]]],
          [["instance", "i", "Stop", [], [], [["P", "P"], ["V", "V"]]]], [["entry", "main", "i"]]]
path = directory / "stop.json"
path.write_text(json.dumps(source))
common = run(compiler, "protocol-import", path)
result = run(optimizer, "--zkc-project-participants", "--zkc-select-physical", text=common)
assert '"protocol.incomplete"' in result and '"local.stop"' in result

# Standalone declarations retain meaningful local checks even without a
# protocol.module owner. Caller tests above use independently well-formed callees.
bad(bare(participant("bad", FINISH, ft="(i1) -> i32")),
    "protocol.finish", "interactive-return-signature")
bad(bare(proto("bad", body=FINISH, ft="(i1) -> i32")),
    "protocol.return", "interactive-return-signature")
message = '%m = "protocol.message"(%a) <{site="send", schema="message", sender="P", receiver="Q"}> : (i1) -> i32'
bad(bare(proto("bad", body=message + "\n" + FINISH)), "protocol.message", "same type")
for carried, count, code in [(-1, "1", "interactive-loop-carried"),
                              (0, "nonsense", "interactive-loop-count"),
                              (0, "1048577", "interactive-loop-count")]:
    loop = f'"protocol.loop"() <{{site="loop", carried={carried} : i64, count="{count}", parameter=false}}> ({{"protocol.yield"() : () -> ()}}) : () -> ()'
    bad(bare(proto("bad", body=loop + "\n" + FINISH)), "protocol.loop", code)

# Operations whose contracts rely on an enclosing protocol/program may not
# appear as standalone builtin.module children and escape region admission.
for operation, text in [
    ("protocol.loop", '"protocol.loop"() <{site="x", carried=-1 : i64, count="nonsense", parameter=false}> ({}) : () -> ()'),
    ("protocol.finish", '"protocol.finish"() : () -> ()'),
    ("protocol.yield", '"protocol.yield"() : () -> ()'),
    ("protocol.incomplete", '"protocol.incomplete"() <{site="x"}> : () -> ()'),
]:
    run(optimizer, text=f" {text} ", op=operation, code="parent")

print(f"native verifier checks: {commands.save()} passed; {len(KERNELS)} "
      "portable kernel contracts and full example passes")
