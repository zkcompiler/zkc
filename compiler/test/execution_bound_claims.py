#!/usr/bin/env python3
"""Source-relative claim custody, independent-authority and hostile controls."""

import copy
import json
from pathlib import Path
import re
from commands import Commands
from tools import compiler, corpus, examples, optimizer, records

fixture = corpus / "claims.pir"


commands = Commands(records())


def call(*args, code=None):
    """A refusal is a diagnostic, never a crash with a stack behind it."""
    printed = commands.run(args, refuses=code)
    if code is not None:
        assert "Stack dump" not in commands.last.stderr, commands.last.stderr
    return printed


def contract_for(catalog):
    """Independent test authority: two ordered subject/context equations."""
    calls = [i for i in catalog["invocations"] if i["callee"] == "Verify"]
    guards = catalog["guards"]
    claims = [[f"g{i}", "guard", [g["value"]]] for i, g in enumerate(guards)]
    rules = []
    for i, invocation in enumerate(calls):
        claims.append([f"equation{i}", "equation", invocation["inputs"]])
        needed = [
            j
            for j, g in enumerate(guards)
            if g["path"].startswith(invocation["path"] + "/")
        ]
        rules.append(
            [
                f"check{i}",
                "equation-law",
                invocation["path"],
                invocation["callee"],
                invocation["inputs"],
                invocation["outputs"],
                [guards[j]["path"] for j in needed],
                [f"g{j}" for j in needed],
                f"equation{i}",
            ]
        )
    types = {v["id"]: v["type"] for v in catalog["values"]}
    return [
        "zkc.claim-contract/1",
        catalog["source_digest"],
        "main",
        "V",
        [
            [
                "equation",
                [types[v] for v in calls[0]["inputs"]],
                "Ordered equality of subject/expected and context/admitted",
            ]
        ],
        claims,
        ["equation0", "equation1"],
        [[f"g{i}", g["path"]] for i, g in enumerate(guards)],
        [
            [
                "equation-law",
                "trust",
                "Caller asserts the exact Equation body implements the two equalities",
            ]
        ],
        rules,
    ]


temp = records()
root = Path(temp)
source, authority, candidate, ir = [
    root / n
    for n in ("source.pir", "contract.json", "candidate.json", "claims.mlir")
]
original = fixture.read_text()
source.write_text(original)
catalog = json.loads(call(compiler, "claim-inspect", source, "main"))
assert len(catalog["guards"]) == 4
c = contract_for(catalog)

def save_contract(value):
    authority.write_text(json.dumps(value))

def save_candidate(value):
    candidate.write_text(json.dumps(value))

save_contract(c)
proof = json.loads(call(compiler, "claim-derive", source, authority))
save_candidate(proof)
call(compiler, "claim-check", source, authority, candidate)
text = call(compiler, "claim-import", source, authority, candidate)
assert (
    '"claim.pending"' in text
    and "!claim.evidence" in text
    and '"claim.rule"' in text
)
ir.write_text(text)
call(compiler, "claim-check-ir", source, authority, ir)
optimized = call(
    optimizer, ir, "--pass-pipeline=builtin.module(canonicalize,cse,symbol-dce)"
)
ir.write_text(optimized)
call(compiler, "claim-check-ir", source, authority, ir)

# Candidate cannot redefine the requirement, authority, rule or source.
for change, code in [
    (lambda p: p.__setitem__(3, []), "claim-unresolved"),
    (lambda p: p.__setitem__(3, ["check0", "check0"]), "claim-unresolved"),
    (lambda p: p.__setitem__(3, ["unknown"]), "claim-rule"),
    (lambda p: p.__setitem__(1, "0" * 64), "claim-certificate-mismatch"),
    (lambda p: p.__setitem__(2, "0" * 64), "claim-certificate-mismatch"),
]:
    p = copy.deepcopy(proof)
    change(p)
    save_candidate(p)
    call(compiler, "claim-check", source, authority, candidate, code=code)
save_candidate(proof)

# Structural MLIR verification alone is deliberately insufficient.
substitutions = [
    (
        "\n".join(
            line for line in text.splitlines() if '"claim.require"' not in line
        ),
        "claim-ir-mismatch",
    ),
    ("module {}", "claim-ir-mismatch"),
    (text.replace('id = "v0"', 'id = "v1"', 1), "claim-ir-mismatch"),
    (text.replace('guard = "$/0/1"', 'guard = "$/1/1"', 1), "claim-ir-mismatch"),
    (
        text.replace("kind = @kind_equation", "kind = @kind_unknown", 1),
        "claim-ir-mismatch",
    ),
]
# Replace actual same-typed operand SSA in pending subject, preserving type.
pending = next(
    line
    for line in text.splitlines()
    if '"claim.pending"' in line and 'id = "equation0"' in line
)
operands = re.search(r"\((.*?)\)", pending).group(1).split(", ")
wrong = pending.replace(
    operands[0] + ", " + operands[1], operands[1] + ", " + operands[0], 1
)
substitutions.append((text.replace(pending, wrong), "claim-ir-mismatch"))
context_wrong = pending.replace(
    operands[2] + ", " + operands[3], operands[3] + ", " + operands[2], 1
)
substitutions.append((text.replace(pending, context_wrong), "claim-ir-mismatch"))
for changed, code in substitutions:
    assert changed != text
    ir.write_text(changed)
    call(compiler, "claim-check-ir", source, authority, ir, code=code)

# Mutating caller contracts is independently revalidated, never admitted by certificate.
for change, code in [
    (lambda x: x[5][0].__setitem__(1, "unknown"), "claim-kind"),
    (
        lambda x: x[4].append(["unused", ["nonexistent"], "bad signature"]),
        "claim-kind",
    ),
    (lambda x: x[5][0].__setitem__(2, ["v0"]), "claim-subject"),
    (lambda x: x[7][0].__setitem__(1, "$/0/0"), "claim-guard"),
    (lambda x: x[7][0].__setitem__(1, "$/1/1"), "claim-guard"),
    (lambda x: x[9][0].__setitem__(1, "invented-law"), "claim-authority"),
    (lambda x: x[9][0].__setitem__(7, ["absent"]), "claim-reference"),
    (lambda x: x[9][0].__setitem__(8, "g0"), "claim-guard"),
    (
        lambda x: x[9][0].__setitem__(4, ["v1", "v0", "v2", "v3"]),
        "claim-invocation",
    ),
    (lambda x: x[9][0].__setitem__(5, ["v6"]), "claim-invocation"),
    (lambda x: x[9][0].__setitem__(6, ["$/1/1"]), "claim-guard"),
    (lambda x: x[5].append(copy.deepcopy(x[5][0])), "claim-duplicate"),
    (lambda x: x.__setitem__(3, "P"), "claim-validator"),
    (
        lambda x: x[8][0].__setitem__(1, "proved-by-this-certificate"),
        "claim-contract-format",
    ),
    (lambda x: x.append("extra"), "claim-contract-format"),
]:
    changed = copy.deepcopy(c)
    change(changed)
    save_contract(changed)
    call(compiler, "claim-derive", source, authority, code=code)

# An acyclic-looking order is insufficient when a premise is unavailable.
ordered = copy.deepcopy(c)
ordered[9][0][7].append("equation1")
save_contract(ordered)
p = json.loads(call(compiler, "claim-derive", source, authority))
assert p[3] == ["check1", "check0"]
p[3].reverse()
save_candidate(p)
call(
    compiler,
    "claim-check",
    source,
    authority,
    candidate,
    code="claim-premise-unavailable",
)
ordered[9][1][7].append("equation0")
save_contract(ordered)
call(compiler, "claim-derive", source, authority, code="claim-unresolved")

# Exact repeated propositions share logical evidence; other subjects do not.
reused = copy.deepcopy(c)
reused[5].append(["same", "equation", c[9][0][4]])
reused[6].append("same")
save_contract(reused)
call(compiler, "claim-derive", source, authority)

save_contract(c)
save_candidate(proof)
for changed in [
    original.replace(
        "field::equal::<F>(subject, expected)", "field::equal::<F>(subject, subject)", 1
    ),
    original.replace("[equation_guard] control::require(ok);", ""),
    original.replace(
        "Verify(x, y, ctx, admitted)", "IgnoreCheck(x, y, ctx, admitted)"
    ),
    original.replace("Verify(x, y, ctx, admitted)", "Verify(y, x, ctx, admitted)"),
    original.replace("Verify(x, y, ctx, admitted)", "Verify(x, y, admitted, ctx)"),
]:
    source.write_text(changed)
    call(
        compiler,
        "claim-check",
        source,
        authority,
        candidate,
        code="claim-source-mismatch",
    )

# Even an explicitly re-admitted digest cannot turn a computation into a guard.
source.write_text(
    original.replace("[equation_guard] control::require(ok);", "")
)
current = json.loads(call(compiler, "claim-inspect", source, "main"))
stale_guard = copy.deepcopy(c)
stale_guard[1] = current["source_digest"]
save_contract(stale_guard)
call(compiler, "claim-derive", source, authority, code="claim-guard")

# Exact per-iteration bindings; nested iterations and zero-trip loops.
loop = """loop [outer] 2 carry () capture (x, y, ctx, admitted) -> () {
      loop [inner] 3 carry () capture (x, y, ctx, admitted) -> () {
        local [check] V: let ok = Verify(x, y, ctx, admitted);
        yield ();
      }
      yield ();
    }"""
prefix = original[: original.index("  protocol Pair")]
loopsource = (
    prefix
    + """  protocol Repeated {
      roles (V);
      inputs (V x: "bls12-381.fr"::Element, V y: "bls12-381.fr"::Element,
              V ctx: "bls12-381.fr"::Element, V admitted: "bls12-381.fr"::Element);
      outputs (); BODY return ();
    }
    instance repeated: Repeated { roles (V = V); }
    entry main = repeated;
    }"""
)
source.write_text(loopsource.replace("BODY", loop))
repeated = json.loads(call(compiler, "claim-inspect", source, "main"))
assert len(repeated["guards"]) == 12
assert sorted(loop["count"] for loop in repeated["loops"]) == [2, 3, 3]
repeated_contract = contract_for(repeated)
repeated_contract[6] = [f"equation{i}" for i in range(6)]
save_contract(repeated_contract)
call(compiler, "claim-derive", source, authority)
source.write_text(
    loopsource.replace("BODY", loop.replace("[outer] 2", "[outer] 0"))
)
zero = json.loads(call(compiler, "claim-inspect", source, "main"))
assert not zero["guards"] and len(zero["invocations"]) == 1
repeated_contract[1] = zero["source_digest"]
save_contract(repeated_contract)
call(compiler, "claim-derive", source, authority, code="claim-subject")
source.write_text(
    loopsource.replace("BODY", loop.replace("[outer] 2", "[outer] 1048576"))
)
call(compiler, "claim-inspect", source, "main", code="execution-expansion-limit")

# An affine resource is not reusable logical evidence.
rng_source = (fixture.parent / "generic-stops.pir").read_text()
source.write_text(rng_source)
rng = json.loads(call(compiler, "claim-inspect", source, "main"))
resource = next(v for v in rng["values"] if v["type"].startswith("rng:"))
rc = [
    "zkc.claim-contract/1",
    rng["source_digest"],
    "main",
    "P",
    [["resource", [resource["type"]], "invalid resource-as-fact"]],
    [["bad", "resource", [resource["id"]]]],
    ["bad"],
    [],
    [],
    [],
]
save_contract(rc)
call(compiler, "claim-derive", source, authority, code="claim-resource-subject")
source.write_text(
    rng_source.replace("return (result, next);", "return (result, rng);")
)
call(compiler, "claim-inspect", source, "main", code="generic-resource-reuse")

# Certificate expansion is bounded independently of the compact rule table.
source.write_text(original)
wide = copy.deepcopy(c)
wide[9][0][7] *= 256
save_contract(wide)
wide_proof = json.loads(call(compiler, "claim-derive", source, authority))
wide_proof[3] = ["check0", "check0", "check1"]
save_candidate(wide_proof)
call(compiler, "claim-check", source, authority, candidate)
wide_proof[3] = ["check0"] * 400 + ["check1"]
save_candidate(wide_proof)
for mode in ("claim-check", "claim-import"):
    call(compiler, mode, source, authority, candidate, code="claim-analysis-limit")

# Empty specifications are caller-selected, not candidate graph deletion.
source.write_text(original)
empty = [
    "zkc.claim-contract/1",
    catalog["source_digest"],
    "main",
    "V",
    [],
    [],
    [],
    [],
    [],
    [],
]
save_contract(empty)
empty_proof = call(compiler, "claim-derive", source, authority)
candidate.write_text(empty_proof)
call(compiler, "claim-check", source, authority, candidate)
ir.write_text("module { ")
call(compiler, "claim-check-ir", source, authority, ir, code="claim-ir")
for deep in (
    "module {\n" * 65 + "}\n" * 65,
    "module attributes {nested = " + "[" * 65 + "0" + "]" * 65 + "} {}",
):
    ir.write_text(deep)
    call(
        compiler,
        "claim-check-ir",
        source,
        authority,
        ir,
        code="claim-ir-depth-limit",
    )
descriptor = root / "descriptor.pir"
descriptor.write_text(
    'construction main { producer P; validator V; random coins at (); accept 0; suite "merlin3.bls12-381.fr64be/1"; }'
)
call(compiler, "claim-inspect", descriptor, "main", code="claim-source")

# Scope and authority boundaries fail closed.
source.write_text(
    original.replace("return (first_ok, second_ok);", "stop V reject;")
)
call(compiler, "claim-inspect", source, "main", code="execution-unsupported-scope")
source.write_text(original)
call(compiler, "claim-inspect", source, "absent", code="execution-entry")
authority.write_text("{}")
call(compiler, "claim-derive", source, authority, code="invalid-shape")
save_contract(c)
candidate.write_text('["zkc.claim-certificate/1"]')
call(
    compiler,
    "claim-check",
    source,
    authority,
    candidate,
    code="claim-certificate-format",
)

# Check an actual nondefault physical candidate against retained source authority.
# These guard-only requirements intentionally make no new PCS body-law claim.
temp = records('lowering')
root = Path(temp)
repository = Path(__file__).resolve().parents[2]
source = root / "source.pir"
text = (corpus / "generic-committed-two-factor.pir").read_text()
text = text.replace(
    ' using (\n    fold_f = "arkworks-msb/poly.fold",\n    fold_g = "arkworks-msb/poly.fold"\n  )', ''
)
source.write_text(text)
descriptor = examples / "committed-two-factor.construction.pir"
catalog = json.loads(call(compiler, "claim-inspect", source, "main"))
guards = [g for g in catalog["guards"] if g["role"] == "V"]
assert guards
contract = [
    "zkc.claim-contract/1", catalog["source_digest"], "main", "V", [],
    [[f"g{i}", "guard", [g["value"]]] for i, g in enumerate(guards)],
    [f"g{i}" for i in range(len(guards))],
    [[f"g{i}", g["path"]] for i, g in enumerate(guards)], [], [],
]
authority, certificate, constructed, common, candidate, choices = [
    root / n for n in ("contract.json", "certificate.json", "constructed.json",
                      "common.json", "physical.json", "choices.json")
]
authority.write_text(json.dumps(contract))
certificate.write_text(call(compiler, "claim-derive", source, authority))
constructed.write_text(call(compiler, "protocol-construct", source, descriptor))
common.write_text(json.dumps(json.loads(constructed.read_text())[2]))
dense = call(compiler, "protocol-compile", common)
bindings = json.loads(dense)[1]
fold = next(b[0] for b in bindings if b[1] == "poly.fold")
selection = [[fold, "arkworks-msb/poly.fold"]]
choices.write_text(json.dumps(selection))
option = "--implementations=" + str(choices)
selected = call(compiler, "protocol-compile", common, option)
assert json.loads(selected) != json.loads(dense)
candidate.write_text(selected)
check = [compiler, "claim-check-lowering", source, authority, certificate,
         descriptor, constructed, candidate]
call(*check, option)
call(*check, code="claim-lowering-mismatch")
candidate.write_text(dense)
call(*check, option, code="claim-lowering-mismatch")
candidate.write_text(selected)
snapshot = json.loads(call(compiler, "protocol-inspect", common))["snapshot"]
choices.write_text(json.dumps(["zkc.implementation-selection/1", snapshot, selection]))
call(*check, option)
call(*check, option, "--linear-contractions")
call(*check, "--linear-contractions", option)
released = call(compiler, "protocol-compile", common, option, "--release-storage")
assert json.loads(released) != json.loads(selected)
candidate.write_text(released)
call(*check, option, "--release-storage")
call(*check, "--release-storage", "--linear-contractions", option)
call(*check, option, code="claim-lowering-mismatch")
candidate.write_text(selected)
call(*check, option, "--release-storage", code="claim-lowering-mismatch")
choices.write_text(json.dumps(["zkc.implementation-selection/1", "0" * 64, selection]))
call(*check, option, code="binding-stale-selection")
# The claim commands honour the same selection contract as protocol-compile,
# whose own four rows are in bound_protocols.py: what this judges is that
# these entry points reach it, and the three option errors below it.
for value, code in [
    (selection * 2, "binding-duplicate-selection"),
    ([[fold, ""]], "binding-stage"),
    ([["missing", "arkworks/poly.fold"]], "binding-unknown-selection"),
    ([[fold, "dalek/poly.fold"]], "binding-implementation"),
]:
    choices.write_text(json.dumps(value))
    call(*check, option, code=code)
call(*check, "--unknown", code="unsupported-option")
call(*check, option, option, code="binding-selection-option")
call(*check, "--linear-contractions", "--linear-contractions", code="duplicate-option")

print(f"claim custody: {commands.save()} tool checks passed")
