"""Formation, optimization and carrier boundaries for native service queries."""
import copy
import json
import re
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records, canonical_program

OUT = records()
commands = Commands(OUT)
source = (Path(__file__).parent / "fixtures/mathematical/services.mlir").read_text()


def project(text, name):
    logical = commands.verified(text, None, "--zkc-project-protocol", "--zkc-simplify-participant", "--zkc-lower-math")
    physical = commands.verified(logical, None, "--zkc-select-physical=linear-contractions=true release-storage=true")
    encoded = commands.source("protocol-export", physical)
    for suffix, content in [("source.mlir", text), ("logical.mlir", logical), ("physical.mlir", physical), ("json", encoded)]:
        (OUT / f"{name}.{suffix}").write_text(content)
    return json.loads(encoded), logical


with case("queries survive optimization and split calculation segments"):
    carrier, logical = project(source, "services")
    assert carrier[0] == "zkc.program/0"
    alice = next(p for p in carrier[3] if p[3] == "Alice")
    assert alice[7] == [["service_0", "random.bls12-381.fr/0", "0"], ["service_3", "random.bls12-381.fr/0", "3"]]
    assert len(alice[4]) == 2
    assert [op[1] for op in alice[6] if op[0] == "query"] == ["first_draw", "second_draw", "unused_draw"]
    assert [op[0] for op in alice[6]] == ["local", "query", "query", "query", "local", "send", "return"]
    assert "service_inputs = [0, 3]" in logical
    assert "selectors = [\"Alice\", \"Bob\"]" in logical
    assert "inputs = [1, 4]" in logical  # Statement common input indices.

with case("deferred boolean retains every query"):
    deferred = "\n".join(line for line in source.splitlines() if "protocol.guard" not in line)
    project(deferred, "services_deferred")

with case("native carrier imports and exports without changing its profile"):
    imported = canonical_program(commands, json.dumps(carrier))
    again = json.loads(imported)
    def alpha(value):
        names = {}
        def visit(item):
            if isinstance(item, list):
                return [visit(child) for child in item]
            if isinstance(item, str) and re.fullmatch(r"v[0-9]+", item):
                return names.setdefault(item, f"value_{len(names)}")
            return item
        return visit(value)
    assert alpha(again) == alpha(carrier)

with case("common service indices map to role-local ingress indices"):
    shifted = '''module { "protocol.module"() ({
      "protocol.func"() ({
      ^entry(%a: !algebra.field<"bls12-381.fr">, %service: !protocol.service_ref<"random.bls12-381.fr/0">):
        %draw = "protocol.query"(%service) {owner="Bob", method="draw", site="draw"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        "protocol.return"(%draw) : (!algebra.field<"bls12-381.fr">) -> ()
      }) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">, !protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">, roles=["Alice", "Bob"], input_roles=[["Alice"], ["Bob"]], output_roles=[["Bob"]]} : () -> ()
    }) {profile=#protocol.profile<protocol>} : () -> () }'''
    shifted_carrier, shifted_ir = project(shifted, "shifted_service_index")
    bob = next(p for p in shifted_carrier[3] if p[3] == "Bob")
    assert bob[7] == [["service_0", "random.bls12-381.fr/0", "0"]]
    assert 'service_inputs = [1]' in shifted_ir
    imported = canonical_program(commands, json.dumps(shifted_carrier))
    roundtrip = json.loads(imported)
    assert next(p for p in roundtrip[3] if p[3] == "Bob")[7] == bob[7]

for name, old, new in [
    ("shared reference owner", 'input_roles=[["Alice"]', 'input_roles=[["Alice", "Bob"]'),
    ("wrong query owner", 'method="draw", owner="Alice", site="first_draw"', 'method="draw", owner="Bob", site="first_draw"'),
    ("unknown service", "random.bls12-381.fr/0", "random.uninstalled/0"),
    ("unknown method", 'method="draw"', 'method="reset"'),
    ("duplicate occurrence", 'site="second_draw"', 'site="first_draw"'),
    ("query data argument", '"protocol.query"(%first)', '"protocol.query"(%first, %x)'),
]:
    with case(name):
        mutated = source.replace(old, new)
        # The argument mutation also updates its function type to reach formation.
        if name == "query data argument":
            mutated = "\n".join(line.replace(': (!protocol.service_ref<"random.bls12-381.fr/0">) ->', ': (!protocol.service_ref<"random.bls12-381.fr/0">, !algebra.field<"bls12-381.fr">) ->')
                                if '"protocol.query"(%first, %x)' in line else line for line in mutated.splitlines())
        commands.verified(mutated, "mathematical-formation", "--canonicalize", "--cse")

for name, mutate, reason in [
    ("unknown port", lambda c: next(p for p in c[3] if p[3] == "Alice")[6][2].__setitem__(2, "missing"), "service-query-context"),
    ("service input index", lambda c: next(p for p in c[3] if p[3] == "Alice")[7][0].__setitem__(2, "100"), "service-port-interface"),
    ("data service collision", lambda c: next(p for p in c[3] if p[3] == "Alice")[7][0].__setitem__(0, alice[4][0][0]), "service-port-interface"),
]:
    with case(name):
        mutated = copy.deepcopy(carrier)
        mutate(mutated)
        canonical_program(commands, json.dumps(mutated), refuses=reason)



with case("a query can be the first participant action"):
    project('''module {
    "protocol.module"() ({
      "protocol.func"() ({
      ^entry(%r: !protocol.service_ref<"random.bls12-381.fr/0">):
        %x = "protocol.query"(%r) {method="draw", owner="Alice", site="draw"} : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
        "protocol.return"(%x) : (!algebra.field<"bls12-381.fr">) -> ()
      }) {sym_name="main", function_type=(!protocol.service_ref<"random.bls12-381.fr/0">) -> (!algebra.field<"bls12-381.fr">), roles=["Alice"], input_roles=[["Alice"]], output_roles=[["Alice"]]} : () -> ()
    }) {profile=#protocol.profile<protocol>} : () -> ()
    }''', "service_single")


# Reference values must never become ordinary data or peer-available results.
field = '!algebra.field<"bls12-381.fr">'
reference = '!protocol.service_ref<"random.bls12-381.fr/0">'
for name, operation in [
    ("reference exchange", f'%bad = protocol.exchange %first {{sender="Alice", receiver="Bob", site="bad"}} : {reference}'),
    ("reference selection", f'%bad = "arith.select"(%go, %first, %second) : (i1, {reference}, {reference}) -> {reference}'),
    ("reference restriction", f'%bad = "protocol.restrict_roles"(%first) {{roles=["Alice"]}} : ({reference}) -> {reference}'),
    ("unavailable reply", f'%bad = protocol.exchange %a {{sender="Bob", receiver="Alice", site="bad"}} : {field}'),
]:
    with case(name):
        mutated = source.replace('    %middle =', f'    {operation}\n    %middle =')
        refusal = "mathematical-dependencies" if name == "reference selection" else "mathematical-formation"
        commands.verified(mutated, refusal, "--zkc-project-protocol", "--zkc-lower-math")

with case("references cannot be returned"):
    mutated = source.replace('"protocol.return"(%message, %accept)', '"protocol.return"(%first, %accept)')
    mutated = mutated.replace(f': ({field}, i1) -> ()', f': ({reference}, i1) -> ()')
    mutated = mutated.replace(f') -> ({field}, i1),', f') -> ({reference}, i1),')
    commands.verified(mutated, "mathematical-formation", "--zkc-project-protocol", "--zkc-lower-math")

with case("references cannot be statement operands"):
    mutated = source.replace(f'signature=({field}, i1)', f'signature=({reference}, i1)')
    mutated = mutated.replace('@relation(%x, %accept)', '@relation(%first, %accept)')
    mutated = mutated.replace(f': {field}, i1\n', f': {reference}, i1\n')
    commands.verified(mutated, "relation-declaration-signature", "--zkc-project-protocol", "--zkc-lower-math")

with case("references cannot be forwarded through helpers"):
    helper = f'''func.func private @ref_helper(%r: {reference}) -> {reference} {{
      return %r : {reference}
    }}'''
    mutated = source.replace('"protocol.module"() ({', '"protocol.module"() ({\n' + helper)
    mutated = mutated.replace('    %twice =', f'    %forwarded = func.call @ref_helper(%first) : ({reference}) -> {reference}\n    %twice =')
    commands.verified(mutated, "mathematical-formation", "--zkc-project-protocol", "--zkc-lower-math")

with case("unknown program tag refuses service queries"):
    mutated = copy.deepcopy(carrier)
    mutated[0] = "invalid.program"
    canonical_program(commands, json.dumps(mutated), refuses="interactive-format")

with case("participant records refuse an extra empty field"):
    mutated = copy.deepcopy(carrier)
    next(p for p in mutated[3] if p[3] == "Alice").insert(4, [])
    canonical_program(commands, json.dumps(mutated), refuses="interactive-record")

with case("service index MLIR attribute must have the admitted integer type"):
    bad = logical.replace('fr/0", 0]', 'fr/0", 18446744073709551616 : i128]')
    assert bad != logical
    commands.source("protocol-export", bad, refuses="mathematical-projection")

with case("service ports require their module profile even when unused"):
    # Construct the port-only shape from a freshly projected query-free program
    # so no data use remains dangling after removing queries.
    port_only = source[source.index('module {'):]
    port_only = port_only[:port_only.index('    protocol.statement')] + '\n    "protocol.return"(%x, %accept) : (!algebra.field<"bls12-381.fr">, i1) -> ()\n  }) {sym_name="main", function_type=(!protocol.service_ref<"random.bls12-381.fr/0">, !algebra.field<"bls12-381.fr">, i1, !protocol.service_ref<"random.bls12-381.fr/0">, i1, i1) -> (!algebra.field<"bls12-381.fr">, i1), roles=["Alice", "Bob", "Observer"], input_roles=[["Alice"], ["Alice"], ["Alice"], ["Alice"], ["Bob"], ["Observer"]], output_roles=[["Alice"], ["Bob"]]} : () -> ()\n}) {profile=#protocol.profile<protocol>} : () -> ()\n}'
    _, port_ir = project(port_only, "services_unused")
    assert '#protocol.profile<exec>' in port_ir
    malformed = port_ir.replace('#protocol.profile<exec>', '#protocol.profile<protocol>')
    commands.source("protocol-export", malformed, refuses="mathematical-module")

for name, instruction, reason in [
    ("participant conditional cannot hide a call", ["if", "branch", "condition", [], [["call", "hidden", "callee", [], []], ["yield", []]], [["yield", []]], []], "interactive-instruction"),
    ("program loops require value counts", ["loop", "loop", "1", [], [], [["query", "hidden", "service_0", "draw", [], ["out"]], ["yield", []]], []], "interactive-shape"),
    ("native participant calls are refused", ["call", "call", "callee", [], []], "interactive-instruction"),
]:
    with case(name):
        mutated = copy.deepcopy(carrier)
        next(p for p in mutated[3] if p[3] == "Alice")[6].insert(0, instruction)
        canonical_program(commands, json.dumps(mutated), refuses=reason)

with case("local functions cannot contain queries"):
    mutated = copy.deepcopy(carrier)
    mutated[2][0][4].insert(0, ["query", "hidden", "service_0", "draw", [], ["out"]])
    canonical_program(commands, json.dumps(mutated), refuses="service-query-context")

print(f"Native services: {counted()} cases; evidence: {OUT}")
