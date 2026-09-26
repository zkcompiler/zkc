"""Last-use storage release: what a plan may say a participant no longer holds.

What the independent Lean consumer makes of the same candidates is a separate
test, tests/protocol/test_storage_release_reference.py, because it needs another
build. The malformed candidates both of them refuse are built in one place,
tests/support/release_candidates.py.
"""

import copy
from bls_fixture import nominal
import json
from pathlib import Path
from release_candidates import malformed
from cases import case
from commands import Commands
from tools import corpus, optimizer, records

root = Path(__file__).resolve().parents[2]


commands = Commands(records())


def run(mode, value, *flags, refuses=None):
    return commands.source(mode, value, *flags, refuses=refuses)


source = (corpus / 'storage-release.pir').read_text()
original = json.loads(run("protocol-source", source))
dense = json.loads(run("protocol-compile", source))
released = json.loads(run("protocol-compile", source, "--release-storage"))
body = released[3][0][4]
assert [i[0] for i in body] == ["release", "op", "release", "op", "release", "return"]
args = [p[0] for p in released[3][0][2]]
assert body[0] == ["release", args[:1]]
assert body[2] == ["release", body[1][5]]  # zero-use result, producer still executed
assert body[4] == ["release", args[1:]]  # both uses retained, return escapes


def erase(candidate):
    candidate = copy.deepcopy(candidate)
    for function in candidate[3]:
        function[4] = [i for i in function[4] if i[0] != "release"]
    return candidate


assert erase(released) == dense
ir = run("protocol-physical-ir", source, "--release-storage", "--locations")
assert '"plan.release"' in ir
assert json.loads(run("protocol-export", ir)) == released
assert (
    json.loads(run("protocol-export", run("protocol-import", json.dumps(released))))
    == released
)
planned = commands.run(
    [
        optimizer,
        "--zkc-project-participants",
        "--zkc-plan-participants=release-storage=true",
        "--verify-each",
    ],
    stdin=run("protocol-import", source),
)
assert json.loads(run("protocol-export", planned)) == released
run(
    "protocol-compile",
    source,
    "--release-storage",
    "--release-storage",
    refuses="duplicate-option",
)
run("protocol-source", source, "--release-storage", refuses="unsupported-option")

# A logical body has no storage to release, whatever the release names.
common_bad = copy.deepcopy(original)
common_bad[2][0][4].insert(0, ["release", ["unused"]])
run("protocol-import", json.dumps(common_bad), refuses="interactive-release-context")
logical_ir = run("protocol-import", source)
projected = json.loads(run("protocol-export",
                           commands.run([optimizer, "--zkc-project-participants"],
                                        stdin=logical_ir)))
for code, candidate in malformed(released, projected):
    run("protocol-import", json.dumps(candidate), refuses=code)

# Linear provider tokens cannot be released. Immutable private custody can be
# discarded locally despite having no public message codec.
for ty in ["rng", "transcript", "nonce", "opening_state", "prover_key", "verifier_key"]:
    resource_plan = [
        "zkc.participants/1",
        [],
        "physical",
        [["function", "F", [["r", nominal(ty) + "@" + ("arkworks.multilinear-pcs/1" if ty in ("opening_state", "prover_key", "verifier_key") else "host.resource/1")]], [], [["release", ["r"]], ["return", []]], ["F", []]]],
        [["participant", "p", "root", "P", [], [], [], [["return", []]]]],
        [["entry", "main", [["P", "p"]]]],
    ]
    if ty in ["rng", "transcript", "nonce"]:
        run("protocol-import", json.dumps(resource_plan), refuses="interactive-release-resource")
    else:
        run("protocol-import", json.dumps(resource_plan))

# Readable profile convenience reaches the identical storage-only pass.
profile_text = source.replace('module {\n  bind both = bool.and();',
                              'module "arkworks.multilinear.bls12-381/1" {').replace('= both(', '= bool.and(')
profile_source = json.loads(run("protocol-source", profile_text))
profile_dense = json.loads(run("protocol-compile", json.dumps(profile_source)))
profile_released = json.loads(
    run("protocol-compile", json.dumps(profile_source), "--release-storage")
)
assert erase(profile_released) == profile_dense

# Independently supplied MLIR must reject a release before the later use.
lines = ir.splitlines()
idx = next(i for i, line in enumerate(lines) if '"plan.release"' in line)
last_release = [line for line in lines if '"plan.release"' in line][-1]
lines.insert(idx, last_release)
run("protocol-export", "\n".join(lines), refuses="interactive-release-live")

# Physical representation conversions and both diagonal implementations compose.
fixture = (corpus / "linear-contractions.pir").read_text()
for flags in [[], ["--linear-contractions"]]:
    with case(f"storage release with flags {flags or 'none'}"):
        baseline = json.loads(run("protocol-compile", fixture, *flags))
        candidate = json.loads(
            run("protocol-compile", fixture, *flags, "--release-storage")
        )
        assert erase(candidate) == baseline
        assert (
            json.loads(
                run(
                    "protocol-export",
                    run("protocol-physical-ir", fixture, *flags, "--release-storage"),
                )
            )
            == candidate
        )

print(f"{commands.save()} storage release tool checks passed")
