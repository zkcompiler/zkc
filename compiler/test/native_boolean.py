"""Closed Boolean arithmetic, canonical literals and exact carrier boundaries."""
import copy
import itertools
import json
import re
from pathlib import Path
from commands import Commands
from tools import records, canonical_program

out = records()
commands = Commands(out)
source = (Path(__file__).parent / "fixtures/mathematical/booleans.mlir").read_text()

def evaluate(carrier, arguments):
    bindings = {b[0]: b[1] for b in carrier[1]}
    functions = {f[1]: f for f in carrier[2]}
    def body(instructions, env):
        for op in instructions:
            if op[0] in ("return", "yield"):
                return [env[n] for n in op[1]]
            if op[0] == "release":
                for n in op[1]: del env[n]
            elif op[0] == "bool_constant": env[op[2]] = op[3]
            elif op[0] == "op":
                args = [env[n] for n in op[4]]
                contract = bindings[op[2]]
                if contract == "bool.and": value = args[0] and args[1]
                elif contract == "bool.or": value = args[0] or args[1]
                elif contract == "bool.not": value = not args[0]
                else: raise AssertionError(contract)
                env[op[5][0]] = value
            elif op[0] == "if":
                env.update(zip(op[6], body(op[4] if env[op[2]] else op[5], {n: env[n] for n in op[3]})))
            elif op[0] == "local":
                f = functions[op[2]]
                env.update(zip(op[4], body(f[4], dict(zip((p[0] for p in f[2]), (env[n] for n in op[3]))))))
            else: raise AssertionError(op)
        raise AssertionError("no return")
    p = carrier[3][0]
    return body(p[6], dict(zip((p[0] for p in p[4]), arguments)))

for optimize in (False, True):
    passes = ["--zkc-project-protocol"]
    if optimize: passes += ["--zkc-simplify-participant"]
    logical = commands.verified(source, None, *passes, "--zkc-lower-math")
    assert "kernel.module" in logical and "kernel.call" in logical
    assert "algebra.exec.bool_and" not in logical
    bound = commands.verified(logical, None, "--zkc-lower-kernels")
    assert "arith." not in bound and "local.bool_constant" in bound
    commands.source("protocol-export", bound, refuses="native-physical-required")
    physical = commands.verified(bound, None, "--zkc-select-physical=release-storage=true")
    assert "local.bool_constant" in physical and "plan.bool_constant" not in physical
    # Physical selection changes only the representation of an ordered literal.
    def literals(text):
        return re.findall(r'"local.bool_constant"\(\) <\{([^}]+)\}>', text)
    logical_literals = literals(bound)
    assert logical_literals and logical_literals == literals(physical)
    # Even unused literals are reached work, so generic simplification must
    # preserve their values, sites and order in both executable profiles.
    for subject, literal_type in ((bound, "i1"),
                                  (physical, '!plan.data<i1, "native.bool/0">')):
        with_unused, changed = re.subn(
            r'(local\.func[^\n]+\{\n)',
            r'\1      %unused_literal = "local.bool_constant"() '
            '{site="unused_literal", value=true} : () -> ' + literal_type + '\n',
            subject, count=1)
        assert changed == 1
        admitted = commands.verified(with_unused)
        before = literals(admitted)
        assert len(before) == len(logical_literals) + 1
        simplified = commands.verified(admitted, None, "--canonicalize", "--cse")
        assert literals(simplified) == before
    # Each representation is valid alone, but not in the opposite profile.
    # An unused literal isolates admission from operand/signature mismatches.
    for subject, wrong_type in ((bound, '!plan.data<i1, "native.bool/0">'),
                                (physical, "i1")):
        mutant, changed = re.subn(
            r'(local\.func[^\n]+\{\n)',
            r'\1      %wrong_profile = "local.bool_constant"() '
            '{site="wrong_profile", value=true} : () -> ' + wrong_type + '\n',
            subject, count=1)
        assert changed == 1
        commands.verified(mutant, "native-local-policy")
    encoded = commands.source("protocol-export", physical)
    carrier = json.loads(encoded)
    assert carrier[0] == "zkc.program/0"
    for a, b, c in itertools.product((False, True), repeat=3):
        assert evaluate(carrier, [a, b, c, 11, 23, 31, 47]) == [
            True, False, a and b, a or b, a != b, a == b, a != b, not a,
            a if c else b, 11 if c else 23, 31 if c else 47]
    (out / f"booleans-{int(optimize)}.json").write_text(encoded)
    assert json.loads(canonical_program(commands, encoded)) == carrier

mutant = copy.deepcopy(carrier)
mutant[0] = "invalid.program"
canonical_program(commands, json.dumps(mutant), refuses="interactive-format")
for value in ("true", 1, None, []):
    mutant = copy.deepcopy(carrier)
    literal = next(op for f in mutant[2] for op in f[4] if op[0] == "bool_constant")
    literal[3] = value
    canonical_program(commands, json.dumps(mutant), refuses="native-boolean-value")
mutant = copy.deepcopy(carrier)
mutant[3][0][6].insert(0, ["bool_constant", "root_literal", "new_value", True])
canonical_program(commands, json.dumps(mutant), refuses="native-boolean-context")

for predicate in ("ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"):
    commands.verified(source.replace("cmpi eq", "cmpi " + predicate), "mathematical-dependencies", "--canonicalize", "--cse")
commands.verified(source.replace("%true = arith.constant true", "%unused = arith.constant 0 : i32\n    %true = arith.constant true"), "mathematical-dependencies", "--canonicalize", "--cse")
commands.verified(source.replace("arith.andi %a, %b : i1", "arith.andi %a, %b {trusted=true} : i1"), "mathematical-formation")

# Exercise recipes on already projected participant programs, bypassing common folding.
endpoint = commands.verified(source, None, "--zkc-project-protocol")
for operation in ("andi", "select"):
    if operation == "andi":
        mutant, changed = re.subn(r"arith.andi (%[a-zA-Z0-9_]+), %[a-zA-Z0-9_]+ : i1", r"arith.andi \1, \1 : i1", endpoint, count=1)
    else:
        mutant, changed = re.subn(r"arith.select (%[a-zA-Z0-9_]+), (%[a-zA-Z0-9_]+), %[a-zA-Z0-9_]+ : i1", r"arith.select \1, \2, \2 : i1", endpoint, count=1)
    assert changed == 1
    direct = commands.verified(mutant, None, "--zkc-lower-math", "--zkc-lower-kernels")
    simplified = commands.verified(mutant, None, "--zkc-simplify-participant", "--zkc-lower-math", "--zkc-lower-kernels")
    if operation == "andi":
        assert direct.count('algebra.exec.bool_and') > simplified.count('algebra.exec.bool_and')
    else:
        assert direct.count('local.if') > simplified.count('local.if')
    c = json.loads(commands.source("protocol-export", commands.verified(direct, None, "--zkc-select-physical")))
    for a, b, condition in itertools.product((False, True), repeat=3):
        values = evaluate(c, [a, b, condition, 11, 23, 31, 47])
        assert values[2 if operation == "andi" else 8] == a
    (out / ("same-" + operation + ".json")).write_text(json.dumps(c))

for label, parameters, signature, roles, expression, expected in [
    ("literal-only", "", "", "", "%out = arith.constant false", False),
    ("folded", "%a: i1", "i1", '["P"]', "%out = arith.cmpi eq, %a, %a : i1", True),
]:
    tiny = f'''module {{ "protocol.module"() ({{
      "protocol.func"() ({{ ^entry({parameters}):
        {expression}
        "protocol.return"(%out) : (i1) -> ()
      }}) {{sym_name="main", function_type=({signature}) -> i1, roles=["P"], input_roles=[{roles}], output_roles=[["P"]]}} : () -> ()
    }}) {{profile=#protocol.profile<protocol>}} : () -> () }}'''
    bound = commands.verified(tiny, None, "--zkc-project-protocol", "--zkc-lower-math", "--zkc-lower-kernels")
    assert "local.bool_constant" in bound
    c = json.loads(commands.source("protocol-export", commands.verified(bound, None, "--zkc-select-physical")))
    assert evaluate(c, [] if not parameters else [False]) == [expected]
    (out / (label + ".json")).write_text(json.dumps(c))

# Reusing the Boolean condition as a selected arm is legal even without folding.
mutant, changed = re.subn(r"arith.select (%[a-zA-Z0-9_]+), %[a-zA-Z0-9_]+, (%[a-zA-Z0-9_]+) : i1", r"arith.select \1, \1, \2 : i1", endpoint, count=1)
assert changed == 1
bound = commands.verified(mutant, None, '--zkc-lower-math', '--zkc-select-physical')
condition_arm = json.loads(commands.source('protocol-export', bound))
for a, b, c in itertools.product((False, True), repeat=3):
    assert evaluate(condition_arm, [a, b, c, 11, 23, 31, 47])[8] == (c or b)

# The profile owns the phase boundary and refuses unknown properties.
commands.verified(physical.replace('#protocol.profile<physical>', '#protocol.profile<physical>, unexpected="value"'), 'mlir-unknown-property')
for length in (128, 129):
    named = copy.deepcopy(carrier)
    literal = next(op for f in named[2] for op in f[4] if op[0] == 'bool_constant')
    literal[1] = 's' * length
    canonical_program(commands, json.dumps(named), refuses=None if length == 128 else 'interactive-name')

# Operation verification admits only logical Boolean or its exact native port.
for wrong_type in ("i8", "i64", "f32", "si1", "ui1",
                   '!plan.data<i1, "native.index/0">',
                   '!plan.data<i64, "native.bool/0">'):
    commands.verified(
        'module { %v = "local.bool_constant"() {value=true, site="literal"}'
        f' : () -> {wrong_type} }}', "native-boolean-type")
# A removed operation spelling is not a compatibility input.
commands.verified(physical.replace("local.bool_constant", "plan.bool_constant"),
                  "unregistered operation")
print(f"Boolean execution and representation checks: {commands.save()}")
