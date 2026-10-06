"""Verifier components, challenge deliveries and independently pinned views."""

import copy
import hashlib
import json
from pathlib import Path

from commands import Commands
from sumcheck_client import composed_sumcheck
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
F = '!algebra.field<"bls12-381.fr">'
S = '!protocol.service_ref<"random.bls12-381.fr/1">'
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513
source_path, requirement_path = OUT / "source.mlir", OUT / "requirement.json"
report_path = OUT / "view.json"


def requirement(bound, service, sites, prover="Prover", verifier="Checker"):
    return {
        "format": "zkc.public-coin-requirement/1",
        "entry": "main",
        "prover": prover,
        "verifier": verifier,
        "service": service,
        "decision": 0,
        "bound_inputs": bound,
        "draws": [{"query_site": q, "delivery_site": d} for q, d in sites],
    }


def analyze(text, req, refuses=None):
    source_path.write_text(text)
    requirement_path.write_text(json.dumps(req))
    output = commands.run(
        [compiler, "protocol-public-coin", source_path, requirement_path],
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
    assert result["format"] == "zkc.checked-run/1"
    record = result["public_coin"]
    assert record["source_sha256"] == hashlib.sha256(text.encode()).hexdigest()
    assert (
        record["bundle_sha256"] == hashlib.sha256(result["bundle"].encode()).hexdigest()
    )
    view = analyze(text, req)
    assert view == record["view"]
    (OUT / f"{name}.bundle").write_text(result["bundle"])
    (OUT / f"{name}.view.json").write_text(json.dumps(view))
    (OUT / f"{name}.mlir").write_text(text)
    (OUT / f"{name}.requirement.json").write_text(json.dumps(req))
    return view


def event_sites(view, end=None):
    return [
        (view["anchors"][i]["kind"], view["anchors"][i].get("site"))
        for i in view["events"][:end]
        if view["anchors"][i]["kind"] != "input"
    ]


def dependencies(view, refs):
    return [view["anchors"][i] for i in refs]


tables = composed_sumcheck()
round_sites = [
    (f"apply_6_reduce_query{i}", f"apply_6_reduce_challenge{i}") for i in range(2)
]
table_req = requirement([0, 1, 2], 3, round_sites)
view = checked("tables", tables, table_req)
assert event_sites(view, view["draws"][0]["prefix_length"]) == [
    ("receive", "apply_6_reduce_round0")
]
assert view["draws"][0]["path"] == ["reduce", "query0"]
assert view["draws"][0]["delivery"]["path"] == ["reduce", "challenge0"]
assert event_sites(view, view["draws"][1]["prefix_length"]) == [
    ("receive", "apply_6_reduce_round0"),
    ("draw", "apply_6_reduce_query0"),
    ("receive", "apply_6_reduce_round1"),
]
assert {
    a["port"]
    for a in dependencies(view, view["decision_dependencies"])
    if a["kind"] == "input"
} == {0, 1}
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
checked("tables_both", tables, table_req, f"--requirements={polynomial_path}")
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
    "zkc.relation.r1cs/1",
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
assert r1cs_view["statement_inputs"] == []
assert r1cs_view["bound_non_statement_inputs"] == [0]
assert event_sites(r1cs_view, r1cs_view["draws"][0]["prefix_length"]) == []
assert event_sites(r1cs_view, r1cs_view["draws"][1]["prefix_length"]) == [
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
assert analyze(public_r1cs, r1cs_req)["statement_inputs"] == [0]


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
shadow_req = requirement([], 1, [("draw", "coin")])
shadow_view = checked("shadow", shadow, shadow_req)
assert {
    a["kind"] for a in dependencies(shadow_view, shadow_view["decision_dependencies"])
} == {"receive", "draw"}
assert shadow_view["draws"][0]["prefix_length"] == 0
assert event_sites(shadow_view) == [("draw", "draw"), ("receive", "reply")]
# A V-only bound port is valid for a V view; it is explicitly unsuitable for a
# shared hash computation until a later construction supplies its P component.
private = small(
    query() + delivery() + f"%ok=algebra.field_equal %x,%draw : ({F},{F})->i1",
    roles='[["Checker"],["Checker"]]',
)
assert analyze(private, {**shadow_req, "bound_inputs": [0]})[
    "prover_unavailable_bound_inputs"
] == [0]
# A syntactic dependence survives an equality folder that knows x == x.
cancelled = small(
    query() + delivery() + f"%ok=algebra.field_equal %x,%x : ({F},{F})->i1"
)
analyze(cancelled, shadow_req, "public-coin-unbound-input")
assert analyze(cancelled, {**shadow_req, "bound_inputs": [0]})[
    "decision_dependencies"
] == [0]
# Exact edge, order, and service failures on otherwise admitted programs.
changed = (
    query()
    + f'%one="algebra.constant"() {{value="1"}} : ()->{F}\n%changed=algebra.field_add %draw,%one : ({F},{F})->{F}\n'
)
analyze(
    small(changed + delivery("changed") + receive + compare),
    shadow_req,
    "public-coin-delivery",
)
analyze(
    small(query() + receive + delivery() + compare), shadow_req, "public-coin-delivery"
)
analyze(small(query() + receive + compare), shadow_req, "public-coin-delivery")
analyze(
    small(query() + delivery() + delivery(site="twice") + receive + compare),
    shadow_req,
    "public-coin-delivery",
)
analyze(
    small(query() + query("other") + delivery() + receive + compare),
    shadow_req,
    "public-coin-delivery",
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
local_declaration = '"local.func"() ({"local.return"() : () -> ()}) {sym_name="empty",function_type=()->(),logical_origin=["empty",[]]} : () -> ()'
local = '"protocol.local_call"() {callee=@empty,site="local",role="Checker"} : ()->()\n'
analyze(
    small(
        local + query() + delivery() + receive + compare, declarations=local_declaration
    ),
    shadow_req,
    "public-coin-verifier-local",
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
    == "zkc.public-coin-checked/1"
)
for change in [
    lambda v: v["draws"][0].update(prefix_length=1),
    lambda v: v["anchors"][-1].update(kind="input", port=0),
    lambda v: v.update(decision_dependencies=[]),
    lambda v: v.update(verifier="Prover"),
    lambda v: v.update(source_ir_sha256="0" * 64),
    lambda v: v["draws"][0].update(path=["unrelated"]),
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
analyze(shadow, {**shadow_req, "entry": "absent"}, "public-coin-interface")
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
# The service-based nonce variant deliberately falls outside this profile;
# an entry nonce tests the same verifier with only its public challenge query.
schnorr = (fixtures / "schnorr-services.mlir").read_text()
schnorr_req = requirement([0, 2], 4, [("draw_challenge", "challenge")], "Alice", "Bob")
analyze(schnorr, schnorr_req, "public-coin-service")
nonce_line = next(
    line for line in schnorr.splitlines() if '%k = "protocol.query"' in line
)
input_nonce = schnorr.replace(nonce_line, "").replace(f"%nonce: {S}", f"%k: {F}")
# Replace just the nonce port in the function signature; query service remains.
signature = input_nonce.index("function_type=")
input_nonce = input_nonce[:signature] + input_nonce[signature:].replace(S, F, 1)
schnorr_view = analyze(input_nonce, schnorr_req)
assert schnorr_view["statement_inputs"] == [0, 2]
assert schnorr_view["bound_non_statement_inputs"] == []
assert {
    a["port"]
    for a in dependencies(schnorr_view, schnorr_view["decision_dependencies"])
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
    [], 1, [("apply_19_apply_5_outer_inner_draw", "apply_19_apply_5_outer_inner_coin")]
)
nested_view = analyze(nested, nested_req)
assert nested_view["draws"][0]["path"] == ["outer", "inner", "draw"]
assert nested_view["draws"][0]["delivery"]["path"] == ["outer", "inner", "coin"]
# An unused statement operand is still mandatory, independent of SSA liveness.
statement = f'relation.declare @predicate {{kind="external",key="view",revision="1",signature=({F})->i1,purposes=["statement"]}}'
bind = f'protocol.statement @predicate(%x) {{selectors=["Checker"],acceptance=0:i64}} : {F}\n'
dead_statement = small(
    bind + query() + delivery() + "%ok=arith.constant true", declarations=statement
)
analyze(dead_statement, shadow_req, "public-coin-statement")
assert (
    analyze(dead_statement, {**shadow_req, "bound_inputs": [0]})[
        "decision_dependencies"
    ]
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
        json.dumps(view).replace('"prefix_length": 0', f'"prefix_length": {token}', 1)
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
    '{"draws":{"nested":1},' + json.dumps(view)[1:],
    json.dumps(view).replace(
        '"prefix_length": 0', '"prefix_length": 1,"prefix_length": 0', 1
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
escaped = {**shadow_req, "entry": 'missing "quote" \\ -1.0'}
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
assert guarded["guards"][0]["prefix_length"] == 1
assert dependencies(guarded, guarded["guards"][0]["dependencies"])[0]["kind"] == "draw"
unbound_guard = (
    query()
    + delivery()
    + f'%condition=algebra.field_equal %x,%x : ({F},{F})->i1\nprotocol.guard %condition {{owner="Checker",site="unbound"}}\n%ok=arith.constant true'
)
analyze(small(unbound_guard), shadow_req, "public-coin-unbound-input")
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
    requirement([], 1000, [("draw", "coin")]),
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
