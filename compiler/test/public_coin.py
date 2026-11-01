"""Verifier components, challenge deliveries and independently pinned views."""

import copy
import hashlib
import json
from pathlib import Path

from scoped_sources import scoped_function
from commands import Commands
from sumcheck_client import composed_sumcheck
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
F = '!algebra.field<"bls12-381.fr">'
S = '!protocol.service_ref<"random.bls12-381.fr/0">'
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513
source_path, requirement_path = OUT / "source.mlir", OUT / "requirement.json"
report_path = OUT / "view.json"


def requirement(bound, service, sites, prover="Prover", verifier="Checker"):
    return {
        "format": "zkc.public-coin-requirement/0",
        "subject": "authored",
        "deployment_entries": ["main"],
        "entry": "main",
        "prover": prover,
        "verifier": verifier,
        "service": service,
        "decision": 0,
        "bound_inputs": bound,
        "draws": [{"query_site": q, "delivery_site": d} for q, d in sites],
    }


def analyze(text, req, refuses=None, *, policy=()):
    source_path.write_text(text)
    requirement_path.write_text(json.dumps(req))
    output = commands.run(
        [compiler, "protocol-public-coin", source_path, requirement_path, *policy],
        refuses=refuses,
    )
    return json.loads(output) if refuses is None else None


def checked(name, text, req, *flags):
    requirement_path.write_text(json.dumps(req))
    result = json.loads(
        commands.source(
            "protocol-checked-bundle", text, f"--public-coin={requirement_path}", *flags
        )
    )
    assert result["format"] == "zkc.checked-run/0"
    record = result["public_coin"]
    assert record["source_sha256"] == hashlib.sha256(text.encode()).hexdigest()
    assert (
        record["bundle_sha256"] == hashlib.sha256(result["bundle"].encode()).hexdigest()
    )
    policy = tuple(
        flag for flag in flags if flag in {"--fuse-vector-reductions", "--no-finite-bulk", "--fuse-collect-fold", "--no-calculation-batching"} or flag.startswith("--oracle-realization=")
    )
    view = analyze(text, req, policy=policy)
    assert view == record["view"]
    route = record["subject_to_bundle_stages"]
    if req["subject"] == "realized":
        assert route[0] == "zkc-project-protocol"
        assert "checked-preparation" not in route and "checked-oracle-realization" not in route
    else:
        assert route[:2] == ["checked-preparation", "checked-oracle-realization"]
    (OUT / f"{name}.bundle").write_text(result["bundle"])
    (OUT / f"{name}.view.json").write_text(json.dumps(view))
    (OUT / f"{name}.mlir").write_text(text)
    (OUT / f"{name}.requirement.json").write_text(json.dumps(req))
    return view


def root(view):
    return view["graph"]["definitions"][view["graph"]["root"]]


def observation_actions(view, definition=None, prefix=""):
    """Small fixture traversal; production retains shared definitions."""
    definition = root(view) if definition is None else definition
    for action in definition["actions"]:
        label = action.get("site", "")
        label = f"apply_{len(prefix)}_{prefix}_{label}" if prefix else label
        if "callee" in action:
            assert action["kind"] != "protocol.repeat", "use DAG assertions for loops"
            yield from observation_actions(
                view, view["graph"]["definitions"][action["callee"]], label)
        else:
            yield definition, action, label


def event_sites(view, before=None):
    result = []
    for definition, action, label in observation_actions(view):
        if label == before:
            break
        if action["kind"] == "protocol.query" and "service" in action:
            result.append(("draw", label))
        elif action["observation"] == "receive":
            result.append(("receive", label))
    return result


def decision_dependencies(view):
    return root(view)["results"][view["decision"]]


def dependencies(view, refs, definition=None, arguments=None):
    definition = root(view) if definition is None else definition
    arguments = ([[{"kind": "input", "port": i}] for i in range(definition["formals"])]
                 if arguments is None else arguments)
    actions = {a["operation"]: a for a in definition["actions"]}
    result = []
    for ref in refs:
        atom = definition["atoms"][ref]
        if atom["kind"] == "formal":
            result.extend(arguments[atom["port"]])
        elif atom["kind"] in {"query", "receive"}:
            result.append({"kind": "draw" if atom["kind"] == "query" else "receive",
                           "operation": atom["operation"]})
        else:
            assert atom["kind"] in {"call_result", "call_stop"}
            action = actions[atom["operation"]]
            child = view["graph"]["definitions"][action["callee"]]
            actuals = [dependencies(view, bits, definition, arguments) if bits is not None else []
                       for bits in action["inputs"]]
            bits = child["stops"] if atom["kind"] == "call_stop" else child["results"][atom["port"]]
            result.extend(dependencies(view, bits, child, actuals))
    return result


def guard_actions(view):
    return [action for _, action, _ in observation_actions(view)
            if action["kind"] == "protocol.guard"]


tables = composed_sumcheck()
round_sites = [
    (f"apply_6_reduce_query{i}", f"apply_6_reduce_challenge{i}") for i in range(2)
]
table_req = requirement([0, 1, 2], 3, round_sites)
view = checked("tables", tables, table_req)
assert event_sites(view, view["graph"]["draws"][0]["site"]) == [
    ("receive", "apply_6_reduce_round0")
]
assert view["graph"]["draws"][0]["path"] == ["reduce", "query0"]
assert view["graph"]["draws"][0]["delivery"]["path"] == ["reduce", "challenge0"]
assert event_sites(view, view["graph"]["draws"][1]["site"]) == [
    ("receive", "apply_6_reduce_round0"),
    ("draw", "apply_6_reduce_query0"),
    ("receive", "apply_6_reduce_round1"),
]
assert {
    a["port"]
    for a in dependencies(view, decision_dependencies(view))
    if a["kind"] == "input"
} == {0, 1, 2}  # The reached guards also constrain the returning decision.
analyze(tables, {**table_req, "bound_inputs": [0, 1]}, "public-coin-unbound-input")
analyze(tables, {**table_req, "bound_inputs": [2]}, "public-coin-unbound-input")
# Both independent judgments can be requested in the same native invocation.
fixtures = Path(__file__).parent / "fixtures/mathematical"
polynomial = json.loads((fixtures / "sumcheck.requirements.json").read_text())
polynomial["requirements"][0]["composition"] = {
    "entry": "main",
    "reduction_site": "reduce",
    "terminal_site": "decide",
}
polynomial_path = OUT / "polynomial.json"
polynomial_path.write_text(json.dumps(polynomial))
checked("tables_both", tables, {**table_req, "deployment_entries": ["main", "reduction", "terminal"]}, f"--requirements={polynomial_path}")
assert checked("tables_plain", tables, table_req, "--no-simplify") == view
assert (
    checked(
        "tables_factored",
        tables,
        table_req,
        "--fix-polynomial-factors",
        "--release-storage",
    )
    == view
)

# The selected relation is unsatisfiable for every w. A statement-only future
# hash leaves w adaptive: residual sum = (1-tau)(w-1)+tau(w-2) = w-1-tau.
asset = [
    "zkc.relation.r1cs/0",
    "bls12-381.fr",
    "2",
    "0",
    "0",
    [
        [[["1", "1"]], [["0", "1"]], [["0", "1"]]],
        [[["1", "1"]], [["0", "1"]], [["0", "2"]]],
    ],
]
r1cs = commands.source("relation-protocol", json.dumps(asset))
r1cs_req = requirement([0], 1, [("weight_draw0", "weight0"), round_sites[0]])
r1cs_view = checked("r1cs", r1cs, r1cs_req)
assert r1cs_view["interface"]["statement_inputs"] == []
assert r1cs_view["interface"]["bound_non_statement_inputs"] == [0]
assert event_sites(r1cs_view, r1cs_view["graph"]["draws"][0]["site"]) == []
assert event_sites(r1cs_view, r1cs_view["graph"]["draws"][1]["site"]) == [
    ("draw", "weight_draw0"),
    ("receive", "apply_6_reduce_round0"),
]
analyze(r1cs, {**r1cs_req, "bound_inputs": []}, "public-coin-unbound-input")
for tau in (0, 1, 2, 7, P - 1):
    w = (1 + tau) % P
    residual = ((w - 1) % P, (w - 2) % P)
    assert any(residual)
    assert ((1 - tau) * residual[0] + tau * residual[1]) % P == 0
# A public-coordinate declaration is checked even if the selected decision
# happens to be independent of that port.
public_asset = copy.deepcopy(asset)
public_asset[4] = "1"
public_r1cs = commands.source("relation-protocol", json.dumps(public_asset))
analyze(public_r1cs, {**r1cs_req, "bound_inputs": []}, "public-coin-statement")
assert analyze(public_r1cs, r1cs_req)["interface"]["statement_inputs"] == [0]


def small(
    body,
    args=f"%x:{F},%s:{S}",
    types=f"{F},{S}",
    roles='[["Prover","Checker"],["Checker"]]',
    declarations="",
):
    return f"""module {{ "protocol.module"() ({{{declarations}
"protocol.func"() ({{^bb0({args}):
{body}
"protocol.return"(%ok) : (i1)->()}})
{{sym_name="main",function_type=({types})->i1,roles=["Prover","Checker"],input_roles={roles},output_roles=[["Checker"]]}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}"""


def query(site="draw", port="s"):
    return f'%{site}="protocol.query"(%{port}) {{method="draw",owner="Checker",site="{site}"}} : ({S})->{F}\n'


def delivery(value="draw", site="coin"):
    return f'%{site}=protocol.exchange %{value} {{sender="Checker",receiver="Prover",site="{site}"}} : {F}\n'


receive = f'%received=protocol.exchange %x {{sender="Prover",receiver="Checker",site="reply"}} : {F}\n'
compare = f"%ok=algebra.field_equal %received,%draw : ({F},{F})->i1\n"
shadow = small(query() + delivery() + receive + compare)
shadow_req = requirement([0], 1, [("draw", "coin")])
shadow_view = checked("shadow", shadow, shadow_req)
assert {
    a["kind"] for a in dependencies(shadow_view, decision_dependencies(shadow_view))
} == {"receive", "draw"}
assert event_sites(shadow_view, "draw") == []
assert event_sites(shadow_view) == [("draw", "draw"), ("receive", "reply")]
# A V-only bound port is valid for a V view; it is explicitly unsuitable for a
# shared hash computation until a later construction supplies its P component.
private = small(
    query() + delivery() + f"%ok=algebra.field_equal %x,%draw : ({F},{F})->i1",
    roles='[["Checker"],["Checker"]]',
)
assert analyze(private, {**shadow_req, "bound_inputs": [0]})["interface"]["prover_unavailable_bound_inputs"] == [0]
# A syntactic dependence survives an equality folder that knows x == x.
cancelled = small(
    query() + delivery() + f"%ok=algebra.field_equal %x,%x : ({F},{F})->i1"
)
analyze(cancelled, {**shadow_req, "bound_inputs": []}, "public-coin-unbound-input")
assert decision_dependencies(analyze(cancelled, shadow_req)) == [0]
# Keep the actual scalar request and its full static domain. An index draw is
# neither a field draw nor an atomic block of several samples.
index_service = '!protocol.service_ref<"random.koala-bear.ext8-binomial3/0">'
index_body = f'''%bound = "data.index"() {{value=8 : ui64}} : () -> ui64
%position = "protocol.query"(%s, %bound) {{method = "index", owner = "Checker", site = "draw"}} : ({index_service}, ui64) -> ui64
%delivered = "protocol.exchange"(%position) {{sender = "Checker", receiver = "Prover", site = "coin"}} : (ui64) -> ui64
%ok = algebra.field_equal %x, %x : ({F}, {F}) -> i1
'''
indexed = small(index_body).replace(S, index_service)
commands.verified(indexed, None)
index_req = {**shadow_req, "bound_inputs": [0]}
for upper in (1, 8, 17, (1 << 64) - 1):
    current = indexed.replace('value=8 : ui64', f'value={upper} : ui64')
    view = checked(f"index_{upper}", current, index_req)
    request = view["graph"]["draws"][0]["request"]
    assert request["contract"] == "random.koala-bear.ext8-binomial3/0"
    assert request["method"] == "index" and request["law"] == "uniform-index"
    assert request["static_arguments"] == [upper]
    constants = [a for a in root(view)["actions"] if a["kind"] == "data.index"]
    assert len(constants) == 1 and f"value = {upper} : ui64" in constants[0]["attributes"]
    query_action = next(a for a in root(view)["actions"] if a["kind"] == "protocol.query")
    assert query_action["operands"][1] == {"kind": "result", "operation": constants[0]["operation"], "port": 0}
    assert query_action["outputs"] == ["ui64"]
    for changed_request in ({**request, "method": "draw"},
                            {**request, "static_arguments": [upper ^ 1]},
                            {**request, "static_arguments": []},
                            {**request, "contract": "random.bls12-381.fr/0"}):
        changed_view = copy.deepcopy(view)
        changed_view["graph"]["draws"][0]["request"] = changed_request
        report_path.write_text(json.dumps(changed_view))
        commands.run([compiler, "protocol-check-public-coin", source_path,
                      requirement_path, report_path], refuses="public-coin-report")
    missing = copy.deepcopy(view)
    del missing["graph"]["draws"][0]["request"]
    report_path.write_text(json.dumps(missing))
    commands.run([compiler, "protocol-check-public-coin", source_path,
                  requirement_path, report_path], refuses="public-coin-report")

# The index actually contributes to the decision and must be delivered exactly.
index_dependent = indexed.replace(
    f'%ok = algebra.field_equal %x, %x : ({F}, {F}) -> i1',
    '%ok = "data.index_less"(%position, %bound) : (ui64, ui64) -> i1')
view = analyze(index_dependent, shadow_req)
assert decision_dependencies(view) == [2]
analyze(index_dependent.replace('"protocol.exchange"(%position)',
                                '"protocol.exchange"(%bound)'),
        shadow_req, "public-coin-dependence")

# Mixed field/index requests retain two distinct prefix boundaries.
field = '!algebra.field<"koala-bear.ext8-binomial3">'
mixed_body = index_body.replace('%ok = algebra.field_equal', f"""%field = "protocol.query"(%s) {{method="draw",owner="Checker",site="field"}} : ({index_service})->{field}
%field_delivery = "protocol.exchange"(%field) {{sender="Checker",receiver="Prover",site="field_coin"}} : ({field})->{field}
%ok = algebra.field_equal""")
mixed = small(mixed_body).replace(S, index_service)
mixed_req = requirement([0], 1, [("draw", "coin"), ("field", "field_coin")])
view = analyze(mixed, mixed_req)
assert [d["site"] for d in view["graph"]["draws"]] == ["draw", "field"]
assert [d["request"]["method"] for d in view["graph"]["draws"]] == ["index", "draw"]
assert view["graph"]["draws"][1]["request"]["law"] == "uniform-field"


# Exact edge, order, and service failures on otherwise admitted programs.
changed = (
    query()
    + f'%one="algebra.constant"() {{value=#algebra.literal<{F}, 1 : ui255>}} : ()->{F}\n%changed=algebra.field_add %draw,%one : ({F},{F})->{F}\n'
)
analyze(
    small(changed + delivery("changed") + receive + compare),
    shadow_req,
    "public-coin-dependence",
)
analyze(
    small(query() + receive + delivery() + compare), shadow_req, "public-coin-dependence"
)
analyze(small(query() + receive + compare), shadow_req, "public-coin-dependence")
analyze(
    small(query() + delivery() + delivery(site="twice") + receive + compare),
    shadow_req,
    "public-coin-dependence",
)
analyze(
    small(query() + query("other") + delivery() + receive + compare),
    shadow_req,
    "public-coin-dependence",
)
analyze(
    shadow,
    {**shadow_req, "draws": [{"query_site": "wrong", "delivery_site": "coin"}]},
    "public-coin-delivery",
)
analyze(
    shadow,
    {**shadow_req, "draws": [{"query_site": "draw", "delivery_site": "reply"}]},
    "public-coin-delivery",
)
analyze(
    shadow,
    {**shadow_req, "draws": [{"query_site": "draw", "delivery_site": "absent"}]},
    "public-coin-delivery",
)
second = small(
    query(port="s2") + delivery() + receive + compare,
    args=f"%x:{F},%s:{S},%s2:{S}",
    types=f"{F},{S},{S}",
    roles='[["Prover","Checker"],["Checker"],["Checker"]]',
)
analyze(second, shadow_req, "public-coin-service")
local_declaration = scoped_function("empty", [], [], "", [])
local = '"protocol.local_call"() {callee=@empty,site="local",role="Checker"} : ()->()\n'
analyze(
    small(
        local + query() + delivery() + receive + compare, declarations=local_declaration
    ),
    shadow_req,
)
# Role-restricted copies retain exact delivery, without granting another role.
restricted = (
    query() + f'%restricted=protocol.restrict_roles %draw {{roles=["Checker"]}} : {F}\n'
)
analyze(small(restricted + delivery("restricted") + receive + compare), shadow_req)
# Structural report checking always rederives facts from source and independent
# requirements, including source differences outside the selected expression.
view = analyze(shadow, shadow_req)
report_path.write_text(json.dumps(view))
assert (
    commands.json(
        [
            compiler,
            "protocol-check-public-coin",
            source_path,
            requirement_path,
            report_path,
        ]
    )["format"]
    == "zkc.public-coin-checked/0"
)
for change in [
    lambda v: v["graph"]["draws"][0].update(context=[0]),
    lambda v: root(v)["atoms"][-1].update(kind="formal", port=0),
    lambda v: root(v)["results"].__setitem__(0, []),
    lambda v: v.update(verifier="Prover"),
    lambda v: v.update(source_ir_sha256="0" * 64),
    lambda v: v.update(prepared_ir_sha256="0" * 64),
    lambda v: v.update(finite_bulk=False),
    lambda v: v.update(fuse_vector_reductions=True),
    lambda v: v.update(fuse_collect_fold=True),
    lambda v: v.pop("fuse_collect_fold"),
    lambda v: v.update(fuse_collect_fold="false"),
    lambda v: v.pop("finite_bulk"),
    lambda v: v.update(finite_bulk="true"),
    lambda v: v["graph"]["draws"][0].update(path=["unrelated"]),
]:
    bad = copy.deepcopy(view)
    change(bad)
    report_path.write_text(json.dumps(bad))
    commands.run(
        [
            compiler,
            "protocol-check-public-coin",
            source_path,
            requirement_path,
            report_path,
        ],
        refuses="public-coin-report",
    )
# The independently supplied policy must match even when this source has no
# eligible finite or fusion payload and its prepared IR remains identical.
for policy_index, policy in enumerate(
    [
        ("--fuse-collect-fold",),
        ("--no-finite-bulk", "--fuse-collect-fold"),
        ("--fuse-vector-reductions", "--fuse-collect-fold"),
        ("--no-finite-bulk", "--fuse-vector-reductions", "--fuse-collect-fold"),
        ("--no-finite-bulk",),
        ("--fuse-vector-reductions",),
        ("--no-finite-bulk", "--fuse-vector-reductions"),
    ]
):
    selected = checked(f"shadow_policy_{policy_index}", shadow, shadow_req, *policy)
    assert selected["finite_bulk"] == ("--no-finite-bulk" not in policy)
    assert selected["fuse_vector_reductions"] == ("--fuse-vector-reductions" in policy)
    assert selected["fuse_collect_fold"] == ("--fuse-collect-fold" in policy)
    assert selected["prepared_ir_sha256"] == view["prepared_ir_sha256"]
    report_path.write_text(json.dumps(selected))
    command = [
        compiler,
        "protocol-check-public-coin",
        source_path,
        requirement_path,
        report_path,
    ]
    commands.json([*command, *policy])
    commands.run(command, refuses="public-coin-report")
    # Relabeling a report cannot grant its own checking policy.
    report_path.write_text(json.dumps(view))
    commands.run([*command, *policy], refuses="public-coin-report")
for mode, extra in [
    ("protocol-public-coin", []),
    ("protocol-check-public-coin", [report_path]),
]:
    for flags in [
        ["--no-finite-bulk", "--no-finite-bulk"],
        ["--fuse-vector-reductions", "--fuse-vector-reductions"],
        ["--unknown-policy"],
    ]:
        commands.run(
            [compiler, mode, source_path, requirement_path, *extra, *flags],
            refuses="public-coin-options",
        )
report_path.write_text("[")
commands.run(
    [
        compiler,
        "protocol-check-public-coin",
        source_path,
        requirement_path,
        report_path,
    ],
    refuses="public-coin-report",
)
report_path.write_text("[" * 65)
commands.run(
    [
        compiler,
        "protocol-check-public-coin",
        source_path,
        requirement_path,
        report_path,
    ],
    refuses="public-coin-limit",
)
for bad in [
    {**shadow_req, "extra": True},
    {**shadow_req, "prover": "Checker"},
    {**shadow_req, "service": -1},
    {**shadow_req, "decision": 0.5},
    {**shadow_req, "bound_inputs": [0, 0]},
    {**shadow_req, "bound_inputs": [1024]},
    {**shadow_req, "draws": []},
    {**shadow_req, "draws": shadow_req["draws"] * 65},
]:
    analyze(shadow, bad, "public-coin-requirement")
for bad in [{**shadow_req, "service": 0}, {**shadow_req, "bound_inputs": [1]}]:
    analyze(
        shadow,
        bad,
        "public-coin-service" if bad["service"] == 0 else "public-coin-interface",
    )
analyze(shadow, {**shadow_req, "entry": "absent", "deployment_entries": ["absent"]}, "public-coin-interface")
analyze(shadow, {**shadow_req, "decision": 1}, "public-coin-interface")
requirement_path.write_text("[" * 65)
commands.run(
    [compiler, "protocol-public-coin", source_path, requirement_path],
    refuses="public-coin-limit",
)
commands.run(
    [compiler, "protocol-public-coin", source_path], refuses="public-coin-options"
)
# Existing group arithmetic is covered without binding the P-only witness.
# Prover-private randomness does not enter the verifier observation. Both a
# private nonce service and an entry nonce retain the same public challenge.
schnorr = (fixtures / "schnorr-services.mlir").read_text()
schnorr_req = requirement([0, 2], 4, [("draw_challenge", "challenge")], "Alice", "Bob")
analyze(schnorr, schnorr_req)
nonce_line = next(
    line for line in schnorr.splitlines() if '%k = "protocol.query"' in line
)
input_nonce = schnorr.replace(nonce_line, "").replace(f"%nonce: {S}", f"%k: {F}")
# Replace just the nonce port in the function signature; query service remains.
signature = input_nonce.index("function_type=")
input_nonce = input_nonce[:signature] + input_nonce[signature:].replace(S, F, 1)
schnorr_view = analyze(input_nonce, schnorr_req)
assert schnorr_view["interface"]["statement_inputs"] == [0, 2]
assert schnorr_view["interface"]["bound_non_statement_inputs"] == []
assert {
    a["port"]
    for a in dependencies(schnorr_view, decision_dependencies(schnorr_view))
    if a["kind"] == "input"
} == {0, 2}
# Nested application paths remain structured; expanded names follow the same
# left-fold convention as actual preparation, even under role substitution.
nested = shadow.replace('sym_name="main"', 'sym_name="leaf"')
caller = f""""protocol.func"() ({{^bb0(%x:{F},%s:{S}):
%ok=protocol.apply @leaf(%x,%s) {{roles=["Prover","Checker"],site="inner"}} : ({F},{S})->i1
"protocol.return"(%ok) : (i1)->()}}) {{sym_name="middle",function_type=({F},{S})->i1,roles=["Prover","Checker"],input_roles=[["Prover","Checker"],["Checker"]],output_roles=[["Checker"]]}} : ()->()"""
outer = (
    caller.replace("@leaf", "@middle")
    .replace('site="inner"', 'site="outer"')
    .replace('sym_name="middle"', 'sym_name="main"')
)
nested = nested.replace("}) {profile=", caller + outer + "}) {profile=")
nested_req = requirement(
    [0], 1, [("apply_19_apply_5_outer_inner_draw", "apply_19_apply_5_outer_inner_coin")]
)
nested_view = analyze(nested, nested_req)
assert nested_view["graph"]["draws"][0]["path"] == ["outer", "inner", "draw"]
assert nested_view["graph"]["draws"][0]["delivery"]["path"] == ["outer", "inner", "coin"]
# An unused statement operand is still mandatory, independent of SSA liveness.
statement = f'relation.declare @predicate {{kind="external",key="view",revision="0",signature=({F})->i1,purposes=["statement"]}}'
bind = f'protocol.statement @predicate(%x) {{selectors=["Checker"],acceptance=0:i64}} : {F}\n'
dead_statement = small(
    bind + query() + delivery() + "%ok=arith.constant true", declarations=statement
)
analyze(dead_statement, {**shadow_req, "bound_inputs": []}, "public-coin-statement")
assert (
    decision_dependencies(analyze(dead_statement, shadow_req))
    == []
)
# The dependent guard can exceed the reporting budget while SSA work remains
# small: wide dependencies must be charged per emitted guard, not only once.
wide_sum = "%v0"
adds = ""
for i in range(1, 100):
    adds += f"%sum{i}=algebra.field_add {wide_sum},%v{i} : ({F},{F})->{F}\n"
    wide_sum = f"%sum{i}"
guard_work = (
    query()
    + delivery()
    + adds
    + f"%ok=algebra.field_equal {wide_sum},{wide_sum} : ({F},{F})->i1\n"
    + "".join(
        f'protocol.guard %ok {{owner="Checker",site="guard{i}"}}\n' for i in range(660)
    )
)
analyze(
    small(
        guard_work,
        args=",".join(f"%v{i}:{F}" for i in range(100)) + f",%s:{S}",
        types=",".join([F] * 100 + [S]),
        roles="[" + '["Checker"],' * 100 + '["Checker"]]',
    ),
    requirement(list(range(100)), 100, [("draw", "coin")]),
    "public-coin-limit",
)

# Review regressions: the JSON reader must agree with typed integer consumers.
view = analyze(shadow, shadow_req)
for token in ("0.0", "0e0", "-0", "00", "+0"):
    report_path.write_text(
        json.dumps(view).replace('"decision": 0', f'"decision": {token}', 1)
    )
    commands.run(
        [
            compiler,
            "protocol-check-public-coin",
            source_path,
            requirement_path,
            report_path,
        ],
        refuses="public-coin-report",
    )
for before, after in [
    ('"service": 1', '"service": 1.0'),
    ('"decision": 0', '"decision": 0e0'),
    ('"decision": 0', '"decision": -0'),
    ('"service": 1', '"service": 01'),
    ('"service": 1', '"service": +1'),
]:
    requirement_path.write_text(json.dumps(shadow_req).replace(before, after))
    commands.run(
        [compiler, "protocol-public-coin", source_path, requirement_path],
        refuses="public-coin-requirement",
    )
# Repeated keys must not become last-wins premises, even with escaped names or
# replaced nested objects. Whitespace and key order remain ordinary JSON.
requirement_path.write_text(json.dumps(shadow_req))
for data in [
    '{"verifier":"Prover",' + json.dumps(view)[1:],
    '{"\\u0076erifier":"Prover",' + json.dumps(view)[1:],
    '{"graph":{"nested":1},' + json.dumps(view)[1:],
    json.dumps(view).replace(
        '"decision": 0', '"decision": 1,"decision": 0', 1
    ),
]:
    report_path.write_text(data)
    commands.run(
        [
            compiler,
            "protocol-check-public-coin",
            source_path,
            requirement_path,
            report_path,
        ],
        refuses="public-coin-report",
    )
for data in [
    '{"bound_inputs":[0],' + json.dumps(shadow_req)[1:],
    '{"\\u0062ound_inputs":[0],' + json.dumps(shadow_req)[1:],
    json.dumps(shadow_req).replace(
        '"query_site": "draw"', '"query_site": "wrong","query_site": "draw"'
    ),
]:
    requirement_path.write_text(data)
    commands.run(
        [compiler, "protocol-public-coin", source_path, requirement_path],
        refuses="public-coin-requirement",
    )
requirement_path.write_text(json.dumps(shadow_req, indent=2, sort_keys=True))
view = analyze(shadow, shadow_req)
report_path.write_text(json.dumps(view, indent=2, sort_keys=True))
commands.run(
    [compiler, "protocol-check-public-coin", source_path, requirement_path, report_path]
)
# A string with escaped quotes, backslashes and numeric punctuation still uses
# ordinary JSON string parsing; only numeric tokens are constrained.
escaped_name = 'missing "quote" \\ -1.0'
escaped = {**shadow_req, "entry": escaped_name, "deployment_entries": [escaped_name]}
analyze(shadow, escaped, "public-coin-interface")
# Unicode escapes denote scalars; LLVM's replacement of lone surrogates must
# not change the name that a different JSON reader observes. Native names are
# ASCII, but the JSON boundary rejects malformed escapes before interface lookup.
for escape in (r"\uD800", r"\uDC00", r"\uD800\u0041", r"\uD800\uD800"):
    requirement_path.write_text(
        json.dumps(shadow_req).replace('"main"', '"' + escape + '"')
    )
    commands.run(
        [compiler, "protocol-public-coin", source_path, requirement_path],
        refuses="public-coin-requirement",
    )
    requirement_path.write_text(json.dumps(shadow_req))
    report_path.write_text(json.dumps(view).replace('"main"', '"' + escape + '"'))
    commands.run(
        [
            compiler,
            "protocol-check-public-coin",
            source_path,
            requirement_path,
            report_path,
        ],
        refuses="public-coin-report",
    )
# Paired supplementary scalars and escaped literal backslashes are valid JSON;
# their names simply do not select this admitted ASCII entry.
for name in (r"\uD83D\uDE00", r"\\uD800"):
    requirement_path.write_text(
        json.dumps(shadow_req).replace('"main"', '"' + name + '"')
    )
    commands.run(
        [compiler, "protocol-public-coin", source_path, requirement_path],
        refuses="public-coin-interface",
    )

# Guards between the draw and delivery observe the draw, even before P does.
middle_guard = (
    query()
    + f'%ok=algebra.field_equal %draw,%draw : ({F},{F})->i1\nprotocol.guard %ok {{owner="Checker",site="before_delivery"}}\n'
    + delivery()
)
guarded = analyze(small(middle_guard), shadow_req)
assert len(guard_actions(guarded)) == 1
assert dependencies(guarded, guard_actions(guarded)[0]["stops"])[0]["kind"] == "draw"
unbound_guard = (
    query()
    + delivery()
    + f'%condition=algebra.field_equal %x,%x : ({F},{F})->i1\nprotocol.guard %condition {{owner="Checker",site="unbound"}}\n%ok=arith.constant true'
)
analyze(small(unbound_guard), {**shadow_req, "bound_inputs": []}, "public-coin-unbound-input")
prover_only = shadow.replace(
    'input_roles=[["Prover","Checker"],["Checker"]]',
    'input_roles=[["Prover"],["Checker"]]',
)
analyze(prover_only, {**shadow_req, "bound_inputs": [0]}, "public-coin-interface")
analyze(
    small(
        local.replace('role="Checker"', 'role="Prover"')
        + query()
        + delivery()
        + receive
        + compare,
        declarations=local_declaration,
    ),
    shadow_req,
)


# Ordinary admission charges applications even when they have no action leaves.
def empty_function(name, body=""):
    return f'''"protocol.func"() ({{{body} "protocol.return"() : ()->()}})
    {{sym_name="{name}",function_type=()->(),roles=["Prover","Checker"],input_roles=[],output_roles=[]}} : ()->()'''


def call(callee, site):
    return f'protocol.apply @{callee}() {{roles=["Prover","Checker"],site="{site}"}} : ()->()\n'


diamond = empty_function("f0")
for i in range(1, 19):
    diamond += empty_function(
        f"f{i}", call(f"f{i - 1}", "left") + call(f"f{i - 1}", "right")
    )
analyze(
    small(
        call("f18", "top") + query() + delivery() + receive + compare,
        declarations=diamond,
    ),
    shadow_req,
    "public-coin-module",
)
# A callee's statement cannot silently acquire the caller's acceptance index.
callee_statement = dead_statement.replace('sym_name="main"', 'sym_name="leaf"')
caller = f""""protocol.func"() ({{^bb0(%x:{F},%s:{S}):
%ok=protocol.apply @leaf(%x,%s) {{roles=["Prover","Checker"],site="use"}} : ({F},{S})->i1
"protocol.return"(%ok) : (i1)->()}}) {{sym_name="main",function_type=({F},{S})->i1,roles=["Prover","Checker"],input_roles=[["Prover","Checker"],["Checker"]],output_roles=[["Checker"]]}} : ()->()"""
callee_statement = callee_statement.replace("}) {profile=", caller + "}) {profile=")
analyze(callee_statement, shadow_req, "public-coin-module")
# Factor fixing changes this bundle while preserving the source view. Disabling
# simplification alone currently produces identical bytes on this fixture;
# no change or optimization benefit is assumed for that flag.
assert (OUT / "tables.bundle").read_bytes() != (
    OUT / "tables_factored.bundle"
).read_bytes()

# Bounded action/path storage, and many operations over a wide input basis.
many = (
    query()
    + delivery()
    + "".join(
        f'%m{i}=protocol.exchange %x {{sender="Prover",receiver="Checker",site="r{i}"}} : {F}\n'
        for i in range(2048)
    )
    + "%ok=arith.constant true"
)
analyze(small(many), shadow_req, "public-coin-limit")
wide_args = ",".join(f"%v{i}:{F}" for i in range(1000)) + f",%s:{S}"
wide_types = ",".join([F] * 1000 + [S])
wide_roles = '["Checker"],'
work = (
    query()
    + delivery()
    + "".join(
        f"%a{i}=algebra.field_add %v0,%v1 : ({F},{F})->{F}\n" for i in range(21000)
    )
    + "%ok=arith.constant true"
)
analyze(
    small(
        work,
        args=wide_args,
        types=wide_types,
        roles="[" + wide_roles * 1000 + '["Checker"]]',
    ),
    requirement(list(range(1000)), 1000, [("draw", "coin")]),
    "public-coin-limit",
)

# Executed separately by the Rust consumer; independent inputs and expected
# decisions make the counterexample observable in actual generated code.
(OUT / "execution.json").write_text(
    json.dumps(
        {
            "cases": [
                {
                    "name": "tables",
                    "inputs": [["1", "2", "3", "4"], ["2", "3", "4", "5"], "70"],
                    "tape": ["2", "3"],
                    "decision": True,
                },
                {
                    "name": "tables_plain",
                    "inputs": [["1", "2", "3", "4"], ["2", "3", "4", "5"], "70"],
                    "tape": ["2", "3"],
                    "decision": True,
                },
                {
                    "name": "tables_factored",
                    "inputs": [["1", "2", "3", "4"], ["2", "3", "4", "5"], "70"],
                    "tape": ["2", "3"],
                    "decision": True,
                },
                {"name": "r1cs", "inputs": ["8"], "tape": ["7", "3"], "decision": True},
                {"name": "shadow", "inputs": ["7"], "tape": ["7"], "decision": True},
            ]
        }
    )
)

# A previously unused verifier input remains an explicit binding obligation.
unused = small(query() + delivery() + '%ok=arith.constant true')
analyze(unused, {**shadow_req, "bound_inputs": []}, "public-coin-unbound-input")
unused_view = analyze(unused, shadow_req)
assert decision_dependencies(unused_view) == []
for bad in [
    {k: v for k, v in shadow_req.items() if k != "subject"},
    {**shadow_req, "subject": "prepared"},
    {k: v for k, v in shadow_req.items() if k != "deployment_entries"},
    {**shadow_req, "deployment_entries": ["main", "main"]},
    {**shadow_req, "deployment_entries": []},
    {**shadow_req, "deployment_entries": ["other"]},
]:
    analyze(shadow, bad, "public-coin-requirement")

# Cross-helper exact forwarding and a symbolic repeated round use the same
# shared definitions. Their challenge identities remain separate by context.
helper_draw = f'''"protocol.func"() ({{^entry(%s:{S}):
{query()}
"protocol.return"(%draw) : ({F})->()
}}) {{sym_name="sample",function_type=({S})->{F},roles=["Prover","Checker"],input_roles=[["Checker"]],output_roles=[["Checker"]]}} : ()->()'''
helper_send = f'''"protocol.func"() ({{^entry(%draw:{F}):
{delivery()}
"protocol.return"() : ()->()
}}) {{sym_name="send",function_type=({F})->(),roles=["Prover","Checker"],input_roles=[["Checker"]],output_roles=[]}} : ()->()'''
round_calls = f'''%q=protocol.apply @sample(%s) {{roles=["Prover","Checker"],site="sample_call"}} : ({S})->{F}
protocol.apply @send(%q) {{roles=["Prover","Checker"],site="delivery_call"}} : ({F})->()
'''
repeat = f'''"protocol.repeat"(%n,%s) ({{^loop(%i:ui64,%s:{S}):
{round_calls}
"protocol.yield"() : ()->()
}}) {{site="rounds",carried=0:i64,maximum=1048576:i64,roles=["Prover","Checker"],carried_roles=[]}} : (ui64,{S})->()
%ok=arith.constant true'''
# The explicit repeat body cannot reuse its enclosing SSA name in the parser.
repeat = repeat.replace('^loop(%i:ui64,%s:', '^loop(%i:ui64,%service:').replace('@sample(%s)', '@sample(%service)')
repeated_source = small(repeat, args=f"%n:ui64,%s:{S}", types=f"ui64,{S}",
                        declarations=helper_draw + helper_send)
repeated_req = requirement([0], 1, [("apply_11_sample_call_draw", "apply_13_delivery_call_coin")])
repeated_view = analyze(repeated_source, repeated_req)
repeated_graph = repeated_view["graph"]
assert len(repeated_graph["definitions"]) == 4
assert len(repeated_graph["draws"]) == 1
assert len(repeated_graph["draws"][0]["iteration_coordinates"]) == 1
assert len(repeated_graph["draws"][0]["context"]) == 2
assert root(repeated_view)["may_stop"]  # count/maximum is checked, even at zero
assert dependencies(repeated_view, root(repeated_view)["stops"])[0]["port"] == 0
# Tampering with a child transfer or a coordinate template cannot be hidden by
# preserving the independent selector strings or source digests.
for mutation in (
    lambda v: v["graph"]["draws"][0].update(iteration_coordinates=[]),
    lambda v: v["graph"]["definitions"][1].update(pending={"input": "any", "output": "query"}),
    lambda v: v["graph"]["definitions"][2].update(result_origins=[{"kind": "unknown"}]),
):
    changed = copy.deepcopy(repeated_view)
    mutation(changed)
    report_path.write_text(json.dumps(changed))
    commands.run([compiler, "protocol-check-public-coin", source_path,
                  requirement_path, report_path], refuses="public-coin-report")

# An actual checked Merkle realization selects opening-request transport and
# appends a shape input. Neither a source label nor dependency alone grants it.
realized_source = '''
#K = #protocol.oracle_kind<"table", [!algebra.field<"koala-bear.ext4-binomial3">]>
!F = !algebra.field<"koala-bear.ext4-binomial3">
!D = !data.field_vector<"koala-bear.ext4-binomial3">
!H = !protocol.oracle<#K>
!S = !protocol.service_ref<"random.koala-bear.ext4-binomial3/0">
module { "protocol.module"() ({
 "protocol.func"() ({^entry(%data:!D,%anchor:!H,%s:!S):
  %h="protocol.oracle_input"(%data,%anchor) {holder="P",receivers=["V"],shape_bounds={rows=8:ui64}} : (!D,!H)->!H
  %q="protocol.query"(%s) {owner="V",method="draw",site="draw"} : (!S)->!F
  %d=protocol.exchange %q {sender="V",receiver="P",site="coin"} : !F
  %zero="data.index"() {value=0:ui64} : ()->ui64
  %a="protocol.oracle_query"(%h,%zero) {owner="V",site="read"} : (!H,ui64)->!F
  %ok=algebra.field_equal %a,%a : (!F,!F)->i1
  "protocol.return"(%ok) : (i1)->()
 }) {sym_name="main",function_type=(!D,!H,!S)->i1,roles=["P","V"],input_roles=[["P"],["V"],["V"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
merkle = {"format": "zkc.oracle-selection/0", "roots": {"kind": "uniform", "table": {
    "scheme": "rows.merkle-keccak256.koala-bear.ext4-binomial3/0",
    "grouping": "individual", "order": "natural"}},
    "order": "after-final-draw", "authentication": "atomic-blocks"}
merkle_flags = ("--oracle-realization=" + json.dumps(merkle),)
realized_req = {**requirement([1, 3], 2, [("draw", "coin")], "P", "V"), "subject": "realized"}
realized_view = checked("realized", realized_source, realized_req, *merkle_flags)
assert realized_view["analyzed_ir_sha256"] == realized_view["realized_ir_sha256"]
assert realized_view["source_ir_sha256"] != realized_view["realized_ir_sha256"]
assert realized_view["oracle_policy"] == merkle
assert len(realized_view["interface"]["inputs"]) == 4
assert any(a["data_exchange"] for d in realized_view["graph"]["definitions"] for a in d["actions"])
analyze(realized_source, {**realized_req, "bound_inputs": [1]}, "public-coin-unbound-input", policy=merkle_flags)
analyze(realized_source, {**realized_req, "bound_inputs": [3]}, "public-coin-unbound-input", policy=merkle_flags)
# An independently changed policy refuses; the candidate's policy is not input.
source_path.write_text(realized_source)
requirement_path.write_text(json.dumps(realized_req))
report_path.write_text(json.dumps(realized_view))
commands.run([compiler, "protocol-check-public-coin", source_path, requirement_path,
              report_path, *merkle_flags])
for mutation in (
    lambda v: v.update(oracle_selection={}),
    lambda v: v.update(realization={}),
    lambda v: next(a for d in v["graph"]["definitions"] for a in d["actions"] if a["data_exchange"]).update(data_exchange=False),
):
    changed = copy.deepcopy(realized_view)
    mutation(changed)
    report_path.write_text(json.dumps(changed))
    commands.run([compiler, "protocol-check-public-coin", source_path, requirement_path,
                  report_path, *merkle_flags], refuses="public-coin-report")
# A forged opening-request-looking source label stays an ordinary send.
forged = small(query() + delivery() + delivery("x", "oracle_opening_request") + receive + compare)
analyze(forged, shadow_req, "public-coin-dependence")

# Independent requests stay visible even when they select no actual roots.
for flags in (("--no-calculation-batching",), merkle_flags):
    selected = checked("independent_policy", shadow, shadow_req, *flags)
    report_path.write_text(json.dumps(selected))
    commands.run([compiler, "protocol-check-public-coin", source_path, requirement_path,
                  report_path], refuses="public-coin-report")
