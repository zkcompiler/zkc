"""External R1CS semantics and actual native protocol application boundaries."""

import copy
import hashlib
import itertools
import json
from pathlib import Path
import re
import struct

from commands import Commands
from tools import compiler, records
from sumcheck_client import composed_sumcheck

OUT = records()
commands = Commands(OUT)
F = '!algebra.field<"bls12-381.fr">'
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513


def module(body):
    return f'module {{ "protocol.module"() ({{{body}}}) {{profile=#protocol.profile<protocol>}} : () -> () }}'


def empty_function(name, body="", roles='["Solo"]'):
    return f'"protocol.func"() ({{{body}\n"protocol.return"() : () -> ()}}) {{sym_name="{name}", function_type=() -> (), roles={roles}, input_roles=[], output_roles=[]}} : () -> ()'


def apply(name, site):
    return f'protocol.apply @{name}() {{roles=["Solo"],site="{site}"}} : () -> ()'


# Admission rejects recursion and expansion blowups before cloning.
commands.verified(
    module(empty_function("self", apply("self", "again"))), "protocol-application"
)
commands.verified(
    module(empty_function("a", apply("b", "b")) + empty_function("b", apply("a", "a"))),
    "protocol-application",
)
diamond = empty_function("f0")
for i in range(1, 19):
    diamond += empty_function(
        f"f{i}", apply(f"f{i - 1}", "left") + apply(f"f{i - 1}", "right")
    )
commands.verified(module(diamond), "protocol-application")
chain = empty_function("f0")
for i in range(1, 65):
    chain += empty_function(f"f{i}", apply(f"f{i - 1}", "next"))
commands.verified(module(chain), "protocol-application")
# Count expanded operand storage before cloning wide, otherwise cheap bodies.
wide = empty_function(
    "wide",
    f'%zero = "algebra.constant"() {{value="0"}} : () -> {F}\n%a = tensor.from_elements '
    + ",".join(["%zero"] * 4096)
    + f" : tensor<4096x{F}>",
)
commands.verified(
    module(
        wide
        + empty_function("main", "".join(apply("wide", f"use{i}") for i in range(250)))
    ),
    "protocol-application",
)
# Pure helper cost is charged at each protocol application, before inlining.
helper = (
    "func.func private @heavy() {\n"
    + "".join(f"%c{i} = arith.constant true\n" for i in range(2000))
    + "func.return\n}"
)
heavy = empty_function("component", "func.call @heavy() : () -> ()")
commands.verified(
    module(
        helper
        + heavy
        + empty_function(
            "main", "".join(apply("component", f"use{i}") for i in range(60))
        )
    ),
    "protocol-application",
)
# A shared symbol table keeps many independent applications inexpensive.
commands.verified(
    module(
        empty_function("leaf")
        + "".join(empty_function(f"f{i}", apply("leaf", "use")) for i in range(512))
    )
)
# Nested applications preserve order and prefix distinct occurrences.
small = module(
    empty_function(
        "leaf",
        '%yes = arith.constant true\nprotocol.guard %yes {owner="Solo",site="check"}',
    )
    + empty_function("middle", apply("leaf", "inner"))
    + empty_function("main", apply("middle", "outer"))
)
projected = commands.verified(small, None, "--zkc-project-protocol=simplify=false")
assert "apply_19_apply_5_outer_inner_check" in projected
assert "protocol.apply" not in projected
# Nested length prefixes can add decimal digits before the inner expansion.
long_sites = module(
    empty_function(
        "leaf",
        '%yes = arith.constant true\nprotocol.guard %yes {owner="Solo",site="c"}',
    )
    + empty_function("middle", apply("leaf", "s"))
    + empty_function("main", apply("middle", "s" * 4072))
)
commands.verified(long_sites, "protocol-application")

boundary = module("""
"protocol.func"() ({^bb0(%a:i1): "protocol.return"(%a) : (i1) -> ()})
 {sym_name="component",function_type=(i1)->i1,roles=["A","B"],input_roles=[["A","B"]],output_roles=[["B"]]} : () -> ()
"protocol.func"() ({^bb0(%a:i1):
 %r = protocol.apply @component(%a) {roles=["X","Y"],site="use"} : (i1)->i1
 "protocol.return"(%r) : (i1)->()})
 {sym_name="main",function_type=(i1)->i1,roles=["X","Y"],input_roles=[["X","Y"]],output_roles=[["Y"]]} : () -> ()""")
commands.verified(boundary, None, "--zkc-project-protocol")
commands.verified(
    boundary.replace('output_roles=[["Y"]]', 'output_roles=[["X"]]'),
    "mathematical-formation",
)
commands.verified(
    boundary.replace('roles=["X","Y"],site', 'roles=["X","X"],site'),
    "protocol-application",
)
commands.verified(
    boundary.replace('roles=["X","Y"],site', 'roles=["X"],site'), "protocol-application"
)
commands.verified(
    boundary.replace('input_roles=[["X","Y"]]', 'input_roles=[["Y"]]'),
    "mathematical-formation",
)
commands.verified(
    boundary.replace("@component(%a)", "@absent(%a)"), "protocol-application"
)

# Owner-local affine ports retain single-use custody through an application.
capability = '!local.capability<"resource_unit:Slot.A">'
affine = module(f""""protocol.func"() ({{^bb0(%a:{capability}): "protocol.return"(%a) : ({capability})->()}})
{{sym_name="component",function_type=({capability})->{capability},roles=["A"],input_roles=[["A"]],output_roles=[["A"]]}} : ()->()
"protocol.func"() ({{^bb0(%a:{capability}):
%r=protocol.apply @component(%a) {{roles=["X"],site="use"}} : ({capability})->{capability}
"protocol.return"(%r) : ({capability})->()}})
{{sym_name="main",function_type=({capability})->{capability},roles=["X"],input_roles=[["X"]],output_roles=[["X"]]}} : ()->()""")
commands.verified(affine, None, "--zkc-project-protocol")
commands.verified(
    affine.replace('"protocol.return"(%r)', '"protocol.return"(%a)'),
    "mathematical-formation",
)
# A third caller role never acquires a callee's declared result or actions.
asymmetric = module(""""protocol.func"() ({^bb0(%a:i1):
%r=protocol.exchange %a {sender="A",receiver="B",site="message"} : i1
protocol.guard %r {owner="B",site="check"}
"protocol.return"(%r) : (i1)->()})
{sym_name="component",function_type=(i1)->i1,roles=["A","B"],input_roles=[["A"]],output_roles=[["B"]]} : ()->()
"protocol.func"() ({^bb0(%a:i1):
%r=protocol.apply @component(%a) {roles=["Z","X"],site="use"} : (i1)->i1
"protocol.return"(%r) : (i1)->()})
{sym_name="main",function_type=(i1)->i1,roles=["X","Y","Z"],input_roles=[["Z"]],output_roles=[["X"]]} : ()->()""")
mapped = commands.verified(asymmetric, None, "--zkc-project-protocol=simplify=false")
assert 'peer = "Z"' in mapped and 'peer = "X"' in mapped
for block in mapped.split('"protocol.participant"')[1:]:
    if 'instance = "main",' in block and 'role = "Y"' in block.split("({", 1)[0]:
        assert (
            "protocol.send" not in block
            and "protocol.receive" not in block
            and "local.guard" not in block
        )
commands.verified(
    asymmetric.replace('output_roles=[["X"]]', 'output_roles=[["Y"]]'),
    "mathematical-formation",
)
# Dead invalid callee work cannot disappear when the application result is unused.
dead = asymmetric.replace(
    "%r=protocol.exchange",
    'protocol.guard %a {owner="B",site="invalid_dead"}\n%r=protocol.exchange',
    1,
)
commands.verified(dead, "mathematical-formation")

# Action occurrence encoding and collision refusal are independent checks.
leaf1 = empty_function(
    "first", '%yes=arith.constant true\nprotocol.guard %yes {owner="Solo",site="b_c"}'
)
leaf2 = empty_function(
    "second", '%yes=arith.constant true\nprotocol.guard %yes {owner="Solo",site="c"}'
)
encoded = commands.verified(
    module(
        leaf1
        + leaf2
        + empty_function("main", apply("first", "a") + apply("second", "a_b"))
    ),
    None,
    "--zkc-project-protocol",
)
assert "apply_1_a_b_c" in encoded and "apply_3_a_b_c" in encoded
collision = module(
    leaf2
    + empty_function(
        "main",
        '%yes=arith.constant true\nprotocol.guard %yes {owner="Solo",site="apply_3_use_c"}'
        + apply("second", "use"),
    )
)
commands.verified(collision)
commands.verified(collision, "mathematical-formation", "--zkc-project-protocol")
# Overlapping role names catch a missed substitution that could still verify.
service = '!protocol.service_ref<"random.bls12-381.fr/0">'
swap_leaf = f""""protocol.func"() ({{^bb0(%s:{service}):
%yes=arith.constant true
%r="protocol.query"(%s) {{method="draw",owner="B",site="draw"}} : ({service})->{F}
%m=protocol.exchange %r {{sender="B",receiver="A",site="message"}} : {F}
protocol.guard %yes {{owner="A",site="check"}}
"protocol.return"() : ()->()}})
{{sym_name="leaf",function_type=({service})->(),roles=["A","B"],input_roles=[["B"]],output_roles=[]}} : ()->()"""


def swap_caller(name, callee, roles):
    return f'''"protocol.func"() ({{^bb0(%s:{service}):
protocol.apply @{callee}(%s) {{roles={roles},site="use"}} : ({service})->()
"protocol.return"() : ()->()}})
{{sym_name="{name}",function_type=({service})->(),roles=["A","B"],input_roles=[["A"]],output_roles=[]}} : ()->()'''


swapped = commands.verified(
    module(
        swap_leaf
        + swap_caller("middle", "leaf", '["B","A"]')
        + swap_caller("main", "middle", '["A","B"]')
    ),
    None,
    "--zkc-project-protocol=simplify=false",
)
participants = []
for fragment in swapped.split('"protocol.participant"')[1:]:
    attributes, body = fragment.split("({", 1)
    body = body.split('"protocol.finish"', 1)[0]
    if 'instance = "main"' in attributes:
        participants.append((body, re.search(r'role = "([AB])"', attributes)[1]))
for body, role_name in participants:
    if role_name == "A":
        assert '"protocol.service_query"' in body and '"protocol.send"' in body
        assert 'peer = "B"' in body and "local.guard" not in body
    else:
        assert '"protocol.receive"' in body and "local.guard" in body
        assert 'peer = "A"' in body and '"protocol.service_query"' not in body
assert {role_name for _, role_name in participants} == {"A", "B"}
# Same entry service reference through two applications means one evolving root.
service = '!protocol.service_ref<"random.bls12-381.fr/0">'
service_source = module(f""""protocol.func"() ({{^bb0(%s:{service}):
%v="protocol.query"(%s) {{method="draw",owner="A",site="draw"}} : ({service})->{F}
"protocol.return"(%v) : ({F})->()}})
{{sym_name="draw",function_type=({service})->{F},roles=["A"],input_roles=[["A"]],output_roles=[["A"]]}} : ()->()
"protocol.func"() ({{^bb0(%s:{service}):
%a=protocol.apply @draw(%s) {{roles=["Checker"],site="first"}} : ({service})->{F}
%b=protocol.apply @draw(%s) {{roles=["Checker"],site="second"}} : ({service})->{F}
"protocol.return"(%a,%b) : ({F},{F})->()}})
{{sym_name="main",function_type=({service})->({F},{F}),roles=["Checker"],input_roles=[["Checker"]],output_roles=[["Checker"],["Checker"]]}} : ()->()""")
(OUT / "service_alias.bundle").write_text(
    commands.source("protocol-bundle", service_source, "--entry=main")
)
# A callee's statement acceptance index cannot silently become a caller index.
statement = 'relation.declare @predicate {kind="external",key="test",revision="0",signature=(i1)->i1,purposes=["statement"]}\n'
with_statement = boundary.replace(
    '"protocol.func"()', statement + '"protocol.func"()', 1
).replace(
    '^bb0(%a:i1): "protocol.return"(%a)',
    '^bb0(%a:i1): protocol.statement @predicate(%a) {selectors=["A"],acceptance=0:i64} : i1\n"protocol.return"(%a)',
    1,
)
commands.verified(with_statement, "protocol-application")

# Reusable public-table client with role substitution and explicit SSA connector.
fixtures = Path(__file__).parent / "fixtures/mathematical"
source = composed_sumcheck()
req = json.loads((fixtures / "sumcheck.requirements.json").read_text())
req["requirements"][0]["composition"] = {
    "entry": "main",
    "reduction_site": "reduce",
    "terminal_site": "decide",
}
requirement_path = OUT / "requirements.json"


def checked(text, requirement, entry="main", refuses=None, flags=()):
    requirement_path.write_text(json.dumps(requirement))
    return commands.source(
        "protocol-checked-bundle",
        text,
        f"--entry={entry}",
        f"--requirements={requirement_path}",
        *flags,
        refuses=refuses,
    )


def artifact(name, text):
    result = json.loads(text)
    (OUT / f"{name}.checked.json").write_text(text)
    (OUT / f"{name}.bundle").write_text(result["bundle"])
    return result["correspondence"]


artifact("tables", checked(source, req))
component_report = artifact("tables_reduction", checked(source, req, entry="reduction"))
assert set(component_report["bundles_sha256"]) == {"main", "reduction", "terminal"}
assert (
    component_report["bundles_sha256"]["main"]
    == hashlib.sha256((OUT / "tables.bundle").read_bytes()).hexdigest()
)
for before, after in [
    ("%r#0,%r#1", "%r#1,%r#0"),
    ("%r#2,%r#3", "%r#3,%r#2"),
    ("%r#3,%r#4", "%r#4,%r#3"),
]:
    bad = source.replace(before, after)
    commands.verified(bad)
    checked(bad, req, refuses="polynomial-composition")
wrong_req = copy.deepcopy(req)
wrong_req["requirements"][0]["composition"]["terminal_site"] = "missing"
checked(source, wrong_req, refuses="polynomial-composition")
source_path, candidate_path = OUT / "source.mlir", OUT / "candidate.mlir"
source_path.write_text(source)
candidate = commands.verified(source, None, "--zkc-project-protocol=simplify=false")
# Change only the wrapper decision; standalone components still pass their check.
pos = candidate.index('instance = "main"')
start, suffix = candidate[:pos], candidate[pos:]
suffix, count = re.subn(
    r"algebra.field_equal (%\w+), %\w+", r"algebra.field_equal \1, \1", suffix
)
assert count >= 1
bad_candidate = start + suffix
commands.verified(bad_candidate)
candidate_path.write_text(bad_candidate)
requirement_path.write_text(json.dumps(req))
commands.run(
    [
        compiler,
        "protocol-check-reductions",
        source_path,
        requirement_path,
        candidate_path,
    ],
    refuses="polynomial-composition",
)

# A changed supporting local definition must fail correspondence even when
# every composed participant body is unchanged.
local = f""""local.binding"() {{sym_name="constant",contract="field.constant",arguments=["bls12-381.fr"],implementation=""}} : ()->()
local.func @unused() -> {F} attributes {{logical_origin=["unused",[]]}} {{
 %c="algebra.exec.field_constant"() {{binding=@constant,parameters=["0"],site="constant"}} : ()->{F}
 local.return %c : {F}
}}"""
local_source = source.replace("func.func private", local + "\nfunc.func private", 1)
# This dependency is retained and verified even when the author does not use it.
commands.verified(local_source)
local_candidate = commands.verified(
    local_source, None, "--zkc-project-protocol=simplify=false"
)
local_changed = local_candidate.replace('parameters = ["0"]', 'parameters = ["1"]')
assert local_changed != local_candidate
commands.verified(local_changed)
source_path.write_text(local_source)
candidate_path.write_text(local_changed)
commands.run(
    [
        compiler,
        "protocol-check-reductions",
        source_path,
        requirement_path,
        candidate_path,
    ],
    refuses="polynomial-correspondence-declaration",
)


# Candidate-only declarations are outside the retained source contract too.
extra = candidate.replace(
    '"protocol.projection"',
    'relation.declare @extra {kind="external",key="test",revision="0",signature=()->i1,purposes=[]}\n"protocol.projection"',
    1,
)
commands.verified(extra)
source_path.write_text(source)
candidate_path.write_text(extra)
commands.run(
    [
        compiler,
        "protocol-check-reductions",
        source_path,
        requirement_path,
        candidate_path,
    ],
    refuses="polynomial-correspondence-declaration",
)


def relation(columns, outputs, inputs, rows):
    return [
        "zkc.relation.r1cs/0",
        "bls12-381.fr",
        str(columns),
        str(outputs),
        str(inputs),
        [
            [[[str(col), str(coef % P)] for col, coef in form] for form in row]
            for row in rows
        ],
    ]


multiply = [[(2, 1)], [(3, 1)], [(1, 1)]]
assets = {
    "multiply": relation(4, 1, 1, [multiply]),
    "three": relation(
        5, 1, 1, [multiply, [[(3, 1)], [(3, 1)], [(4, 1)]], [[], [], []]]
    ),
    "eight": relation(4, 1, 1, [multiply] * 8),
    "empty": relation(1, 0, 0, []),
    "cancel": relation(3, 0, 0, [[[(1, 1)], [(0, 1)], []], [[(2, 1)], [(0, 1)], []]]),
}


def products(asset, z):
    return [
        [sum(int(k) * z[int(i)] for i, k in row[m]) % P for row in asset[5]]
        for m in range(3)
    ]


def mle(values, point):
    result = 0
    for i, val in enumerate(values):
        for axis, x in enumerate(point):
            val = val * (x if i >> (len(point) - axis - 1) & 1 else 1 - x) % P
        result = (result + val) % P
    return result


def polynomial(asset, z, tau, point):
    a, b, c = (mle(v, point) for v in products(asset, z))
    eq = 1
    for t, x in zip(tau, point, strict=True):
        eq = eq * ((1 - t) * (1 - x) + t * x) % P
    return eq * (a * b - c) % P


runs, exact = [], []
for name, asset in assets.items():
    path = OUT / f"{name}.relation.json"
    path.write_text(json.dumps(asset))
    text = commands.source("relation-protocol", json.dumps(asset))
    requirements = json.loads(
        commands.source("relation-requirements", json.dumps(asset))
    )
    (OUT / f"{name}.mlir").write_text(text)
    report = artifact(name, checked(text, requirements))
    arity = report["requirements"][0]["arity"]
    assert [r["degree"] for r in report["requirements"][0]["rounds"]] == [3] * arity
    assert report["requirements"][0]["family"] == "r1cs-sum-to-point/0"
    assert report["requirements"][0]["composition"]["verifier_role"] == "Checker"
    (OUT / f"{name}_evaluate.bundle").write_text(
        commands.source("protocol-bundle", text, "--entry=evaluate")
    )
    if name == "multiply":
        for suffix, flags in [
            ("plain", ("--no-simplify",)),
            ("release", ("--release-storage",)),
            ("factored", ("--fix-polynomial-factors",)),
        ]:
            artifact(f"{name}_{suffix}", checked(text, requirements, flags=flags))
        # Family contract pins all generated source, including weight origin,
        # zero claim, public layout and recipe coefficients to the external R1CS.
        for before, after in [
            ('site = "weight_draw0"', 'site = "different_draw"'),
            ("index = 2 : i64", "index = 1 : i64"),
            ('value = "0"', 'value = "1"'),
        ]:
            bad = text.replace(before, after, 1)
            commands.verified(bad)
            checked(bad, requirements, refuses="r1cs-source-correspondence")
        changed = copy.deepcopy(requirements)
        changed["requirements"][0]["relation"][3:5] = ["0", "2"]
        checked(text, changed, refuses="r1cs-source-correspondence")
        commands.source(
            "protocol-checked-bundle",
            text,
            "--entry=main",
            refuses="checked-bundle-requirement-missing",
        )
        checked(
            text,
            requirements,
            entry="evaluate",
            refuses="polynomial-correspondence-entry",
        )
        original_projected = commands.verified(
            text, None, "--zkc-project-protocol=simplify=false"
        )
        identity = report["requirements"][0]["relation_identity"]
        changed_identity = original_projected.replace(identity, "f" * 64)
        assert changed_identity != original_projected
        commands.verified(changed_identity)
        source_path.write_text(text)
        candidate_path.write_text(changed_identity)
        requirement_path.write_text(json.dumps(requirements))
        commands.run(
            [
                compiler,
                "protocol-check-reductions",
                source_path,
                requirement_path,
                candidate_path,
            ],
            refuses="polynomial-correspondence-declaration",
        )
        # Statement port changes are structurally legal and cannot be inferred
        # from an unchanged participant body.
        changed_statement = original_projected.replace(
            "inputs = [0, 1]", "inputs = [1, 0]", 1
        )
        assert changed_statement != original_projected
        commands.verified(changed_statement)
        candidate_path.write_text(changed_statement)
        commands.run(
            [
                compiler,
                "protocol-check-reductions",
                source_path,
                requirement_path,
                candidate_path,
            ],
            refuses="polynomial-correspondence-interface",
        )

    assignments = (
        [[1, 6, 2, 3], [1, 7, 2, 3], [0, 0, 0, 0]]
        if name in ("multiply", "eight")
        else (
            [[1, 6, 2, 3, 9], [1, 6, 2, 3, 8]]
            if name == "three"
            else ([[1], [0]] if name == "empty" else [[1, 1, P - 1], [1, 0, 1]])
        )
    )
    for z in assignments:
        public = z[1 : 1 + int(asset[3]) + int(asset[4])]
        for statement in [public, [(x + 1) % P for x in public]][: 2 if public else 1]:
            expected_products = products(asset, z)
            bound = z[0] == 1 and z[1 : 1 + len(statement)] == statement
            satisfied = bound and all(
                (a * b - c) % P == 0 for a, b, c in zip(*expected_products)
            )
            sp, zp = OUT / "statement.json", OUT / "assignment.json"
            sp.write_text(json.dumps(list(map(str, statement))))
            zp.write_text(json.dumps(list(map(str, z))))
            independent = json.loads(
                commands.run([compiler, "relation-evaluate", path, sp, zp])
            )
            assert independent["products"] == [
                list(map(str, row)) for row in expected_products
            ]
            assert (independent["bound"], independent["satisfied"]) == (
                bound,
                satisfied,
            )
            exact.append(
                {
                    "bundle": f"{name}_evaluate",
                    "z": list(map(str, z)),
                    "statement": list(map(str, statement)),
                    "products": [
                        list(map(str, row + [0] * ((1 << arity) - len(row))))
                        for row in expected_products
                    ],
                    "bound": bound,
                    "satisfied": satisfied,
                }
            )
        if z[0] != 1:
            continue
        tapes = [
            [P - 1] * (2 * arity),
            list(range(2, 2 + arity)) + list(range(5, 5 + arity)),
            [0] * arity + [1] * arity,
            [1] * arity + [0] * arity,
        ]
        if name == "cancel" and z[1] == 1:
            tapes += [[pow(2, -1, P), 7]]
        for tape in tapes:
            tau, challenges = tape[:arity], tape[arity:]
            total = (
                sum(
                    polynomial(asset, z, tau, point)
                    for point in itertools.product((0, 1), repeat=arity)
                )
                % P
            )
            expected_rounds = []
            for i in range(arity):
                expected_rounds.append(
                    [
                        str(
                            sum(
                                polynomial(
                                    asset, z, tau, challenges[:i] + [x] + list(tail)
                                )
                                for tail in itertools.product(
                                    (0, 1), repeat=arity - i - 1
                                )
                            )
                            % P
                        )
                        for x in (0, 1, 2, 11)
                    ]
                )
            runs.append(
                {
                    "bundle": name,
                    "values": list(map(str, z[1:])),
                    "tape": list(map(str, tape)),
                    "arity": arity,
                    "accepted": total == 0,
                    "rounds": expected_rounds,
                }
            )
# The invalid cancel vector has zero unweighted sum; 1/2 is its bad-event weight.
assert any(
    r["bundle"] == "cancel" and r["values"] == ["1", str(P - 1)] and r["accepted"]
    for r in runs
)
assert any(
    r["bundle"] == "cancel" and r["values"] == ["1", str(P - 1)] and not r["accepted"]
    for r in runs
)

duplicate = relation(4, 1, 1, [[[(2, 3), (2, -2)], [(3, 1)], [(1, 1)]]])
commands.source(
    "relation-protocol", json.dumps(duplicate), refuses="relation-noncanonical"
)

# Binary ingestion uses the exact modulus and the same public layout.
asset = assets["multiply"]
header = (
    struct.pack("<I", 32)
    + P.to_bytes(32, "little")
    + struct.pack("<IIIIQI", 4, 1, 1, 1, 4, 1)
)
constraints = b"".join(
    struct.pack("<I", len(form))
    + b"".join(
        struct.pack("<I", int(i)) + int(k).to_bytes(32, "little") for i, k in form
    )
    for form in asset[5][0]
)
binary = (
    b"r1cs"
    + struct.pack("<II", 1, 3)
    + struct.pack("<IQ", 1, len(header))
    + header
    + struct.pack("<IQ", 2, len(constraints))
    + constraints
)
binary += struct.pack("<IQ", 3, 32) + struct.pack("<QQQQ", 0, 1, 2, 3)
binary_path = OUT / "multiply.r1cs"
binary_path.write_bytes(binary)
assert (
    commands.run([compiler, "relation-protocol", binary_path])
    == (OUT / "multiply.mlir").read_text()
)
for asset, refusal in [
    (relation(4, 1, 1, [multiply] * 9), "native-r1cs-limit"),
    (relation(129, 1, 1, [multiply]), "native-r1cs-limit"),
]:
    commands.source("relation-protocol", json.dumps(asset), refuses=refusal)
inside = relation(128, 0, 0, [[[(i, 1) for i in range(128)], [], []] for _ in range(8)])
commands.source("relation-protocol", json.dumps(inside))
outside = copy.deepcopy(inside)
outside[5][0][1] = [["0", "1"]]
commands.source("relation-protocol", json.dumps(outside), refuses="native-r1cs-limit")
other = copy.deepcopy(assets["multiply"])
other[1] = "bn254.fr"
commands.source("relation-protocol", json.dumps(other), refuses="native-r1cs-field")
(OUT / "execution.json").write_text(
    json.dumps({"runs": runs, "exact": exact}, indent=2)
)
print(
    f"composition admission, checked SSA wiring, {len(exact)} exact cases and {len(runs)} Sumcheck runs generated"
)
