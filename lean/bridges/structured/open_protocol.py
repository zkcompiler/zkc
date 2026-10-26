#!/usr/bin/env python3
"""Compare ordered participant execution of original MLIR and checked Lean data.

The C++ reference walks native SSA. Lean independently admits the exported
subject. Both use an explicitly additive scalar model for groups in this suite;
generic group/module process theorems are separate. This is bounded comparison
evidence, not correspondence with the production executor or its providers.
"""

import argparse
import copy
import json
from pathlib import Path
import sys

from check import FIELD, MODULUS, ROOT, Suite, definition, fixture, write_json
from bridges.common.native_entry import native_subject
import snapshot as constructors

GROUP = "bls12-381.g1"
SERVICE = "random.bls12-381.fr/0"
FIELD_TYPE = ["field", FIELD]
GROUP_TYPE = ["group", GROUP]
FIXTURES = ROOT / "compiler/test/fixtures"


def reply(action, value=None, stop=None):
    response = ["stop", stop] if stop is not None else (
        ["unit"] if action[0] == "send" else ["value", value])
    return ["reply", action, response]


def events(replies):
    return [event for index, row in enumerate(replies)
            for event in (["request", index, row[1]], ["reply", index, row[2]])]


def returned(values, replies=()):
    return ["zkc.structured-open-result/0", ["returned", values], events(replies), len(replies)]


def stopped(reason, site, consumed=(), pending=None):
    records = events(consumed)
    if pending is not None:
        records.append(["request", len(consumed), pending])
    records.append(["stop", reason, site, len(consumed)])
    return ["zkc.structured-open-result/0", ["stopped", reason, site], records, len(consumed)]


class OpenSuite(Suite):
    def compare_open(self, subject, label, role, inputs, replies, expected):
        original, exported, data = subject
        request = exported.parent / (label + ".request.json")
        write_json(request, ["zkc.structured-open-request/0", role, inputs, list(replies), 1000000])
        native = json.loads(self.command(label + ":ssa",
            [self.tools["reference"], "open", original, data[3], request]))
        formal = json.loads(self.command(label + ":lean",
            [self.tools["lean"], "open", exported, request]))
        if not (native == expected):
            raise AssertionError({"reference": native, "expected": expected})
        if not (formal == expected):
            raise AssertionError({"formal": formal, "expected": expected})

    def authored(self, label, selected_subject, modules, retained=None):
        flags = ["--source-format=zkc", "--subject=" + selected_subject,
                 *[f"--module={name}={source}" for name, source in modules.items()]]
        source, interface_text, interface = native_subject(
            lambda command: self.command(label + ":frontend", command), self.tools["compiler"], flags)
        subject = self.export(label, source, interface["protocol"])
        (subject[1].parent / "interface.json").write_text(interface_text, encoding="utf-8")
        if retained is not None:
            stem, module = retained
            targets = [
                (subject[0], Path(__file__).parent / f"fixtures/{stem}.mlir"),
                (subject[1], Path(__file__).parent / f"fixtures/{stem}.json"),
            ]
            rendered = subject[1].with_suffix(".lean")
            rendered.write_text(constructors.render(subject[2], f"ZkcExamples.Structured.{module}Data"),
                                encoding="utf-8")
            targets.append((rendered, ROOT / f"lean/ZkcExamples/Structured/{module}Data.lean"))
            for generated, maintained in targets:
                if self.args.write_fixtures:
                    maintained.write_bytes(generated.read_bytes())
                if not (generated.read_bytes() == maintained.read_bytes()):
                    raise AssertionError(f"retained subject differs: {maintained}")
        return subject


def component_cases(suite):
    source = (FIXTURES / "structured-source/open-components.mlir").read_text(encoding="utf-8")
    subject = suite.export("components", source)
    for role, inputs, expected in [
        ("P", ["11", "99"], ["11", "11", None, "5"]),
        ("V", ["88", "22"], [None, None, "22", "5"]),
        ("P", ["11", None], ["11", "11", None, "5"]),
    ]:
        label = f"components-{role}-{inputs[1]}"
        suite.case(label, lambda r=role, v=inputs, e=expected, n=label:
                   suite.compare_open(subject, n, r, v, [], returned(e)))
    alternate = suite.export("alternate-roster", source, "other")
    suite.case("alternate-roster", lambda: suite.compare_open(
        alternate, "auditor", "Auditor", ["37"], [], returned(["37"])))

    helper = '''local.func private @halt(%x:!F,%y:!F) attributes {logical_origin=["halt",[]]} {
      "local.stop"() {reason="abort",site="halted"} : ()->()
    }'''
    local = source.replace("  func.func private @first", helper + "\n  func.func private @first", 1)
    local = local.replace("%a = func.call @nested",
        '"protocol.local_call"(%x,%x) {callee=@halt,role="P",site="call"} : (!F,!F)->()\n%a = func.call @nested')
    local_subject = suite.export("owned-local-zero-results", local)
    suite.case("owner-zero-results-stop", lambda: suite.compare_open(
        local_subject, "owner", "P", ["11", "22"], [], stopped("abort", "halted")))
    suite.case("nonowner-zero-results-skip", lambda: suite.compare_open(
        local_subject, "nonowner", "V", ["11", "22"], [], returned([None, None, "22", "5"])))
    suite.case("owner-requires-unused-argument", lambda: suite.compare_open(
        local_subject, "missing", "P", [None, "22"], [], stopped("incomplete", "call")))

    bad = copy.deepcopy(subject[2])
    first = definition(bad, "first")
    # Even an unused intermediate must have a participant at which it exists.
    # Append two result references after the new SSA result shifts the context.
    first[9] = ["block", [[["field.add", FIELD], [0, 1], [FIELD_TYPE], [], ""]],
                ["return", [1]]]
    suite.case("unavailable-unused-intermediate", lambda: suite.refuse_snapshot(
        "unavailable-unused-intermediate", bad))
    wide = copy.deepcopy(subject[2])
    definition(wide, "main")[6][3][0] = ["P", "V"]
    suite.case("unavailable-output-scope", lambda: suite.refuse_snapshot("unavailable-output-scope", wide))


def service_cases(suite):
    subject = suite.export("services", (FIXTURES / "structured-source/open-services.mlir").read_text(encoding="utf-8"))
    for second in ("17", "29"):
        actions = [["draw", site, "P", SERVICE, handle, FIELD]
                   for site, handle in zip(("first", "second"), ("17", second))]
        script = [reply(action, value) for action, value in zip(actions, ("3", "8"))]
        suite.case("handles-" + second, lambda s=script, h=second: suite.compare_open(
            subject, "handles-" + h, "P", ["17", h, True], s, returned(["3", "8", None], s)))
    first = ["draw", "first", "P", SERVICE, "17", FIELD]
    second = ["draw", "second", "P", SERVICE, "17", FIELD]
    script = [reply(first, "3"), reply(second, "8")]
    suite.case("nonowner-services", lambda: suite.compare_open(
        subject, "nonowner-services", "V", [None, None, False], script, returned([None, None, False])))
    suite.case("missing-first-reply", lambda: suite.compare_open(
        subject, "missing-first", "P", ["17", "17", True], [], stopped("incomplete", "first", pending=first)))
    suite.case("missing-second-reply", lambda: suite.compare_open(
        subject, "missing-second", "P", ["17", "17", True], script[:1],
        stopped("incomplete", "second", script[:1], second)))
    for reason in ("abort", "reject", "incomplete", "exhausted", "refused"):
        stop_reply = [reply(first, stop=reason)]
        suite.case("script-stop-" + reason, lambda r=reason, s=stop_reply: suite.compare_open(
            subject, "script-stop-" + r, "P", ["17", "17", True], s, stopped(r, "first", s)))
    for label, bad in [
        ("wrong-handle", reply(["draw", "first", "P", SERVICE, "18", FIELD], "3")),
        ("unit-for-value", ["reply", first, ["unit"]]),
        ("noncanonical-field", reply(first, str(MODULUS))),
        ("absent-reply-value", reply(first, None)),
    ]:
        suite.case(label, lambda n=label, b=bad: suite.compare_open(
            subject, n, "P", ["17", "17", True], [b], stopped("refused", "first", pending=first)))
    suite.case("guard-after-effects", lambda: suite.compare_open(
        subject, "guard", "P", ["17", "17", False], script, stopped("reject", "check", script)))
    suite.case("unused-reply-suffix", lambda: suite.compare_open(
        subject, "suffix", "P", ["17", "17", True], script + [reply(first, "9")],
        returned(["3", "8", None], script)))


def group_cases(suite):
    subject = suite.export("groups", (FIXTURES / "structured-source/open-groups.mlir").read_text(encoding="utf-8"))
    for label, role, inputs, outputs in [
        ("scale", "V", ["7", "3"], ["21", False]),
        ("identity-scale", "V", ["7", "1"], ["7", True]),
        ("field-wrap", "V", [str(MODULUS - 1), "2"], [str(MODULUS - 2), False]),
        ("result-scope", "P", ["0", "3"], ["0", None]),
    ]:
        suite.case("group-" + label, lambda n=label, r=role, v=inputs, e=outputs:
                   suite.compare_open(subject, n, r, v, [], returned(e)))
    for label, descriptor in [
        ("wrong-field", ["group.scale", GROUP, "bn254.fr"]),
        ("wrong-group", ["group.scale", "bn254.g1", FIELD]),
        ("extra-domain", ["group.scale", GROUP, FIELD, "extra"]),
    ]:
        data = copy.deepcopy(subject[2])
        definition(data, "scale")[9][1][1][0] = descriptor
        suite.case(label, lambda n=label, d=data: suite.refuse_snapshot(n, d))
    swapped = copy.deepcopy(subject[2])
    instruction = definition(swapped, "scale")[9][1][1]
    instruction[1] = list(reversed(instruction[1]))
    suite.case("group-scale-swapped-types", lambda: suite.refuse_snapshot("group-scale-swapped-types", swapped))


def vector_receive_cases(suite):
    source = '''!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%x:!V):
    %y = "protocol.exchange"(%x) {sender="P",receiver="V",site="vector"} : (!V)->!V
    "protocol.return"(%y) : (!V)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!V)->!V,roles=["P","V"],
      input_roles=[["P"]],output_roles=[["V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
    subject = suite.export("vector-receive", source)
    action = ["receive", "vector", "P", "V", ["vector", FIELD]]
    maximum = ["0"] * 4096
    script = [reply(action, maximum)]
    suite.case("vector-receive-at-capacity", lambda: suite.compare_open(
        subject, "at-capacity", "V", [None], script, returned([maximum], script)))
    for label, response in [
        ("wrong-element", ["value", [True]]),
        ("malformed-outer", ["value", maximum + ["0"], "extra"]),
    ]:
        script = [["reply", action, response]]
        suite.case("vector-receive-" + label, lambda n=label, s=script: suite.compare_open(
            subject, n, "V", [None], s, stopped("refused", "vector", pending=action)))

    def capacity_error():
        request = subject[1].parent / "over-capacity.request.json"
        write_json(request, ["zkc.structured-open-request/0", "V", [None],
                             [reply(action, maximum + ["0"])], 1000000])
        for label, argv, diagnostic in [
            ("ssa", [suite.tools["reference"], "open", subject[0], "main", request],
             "structured-reference-capacity"),
            ("lean", [suite.tools["lean"], "open", subject[1], request],
             "structured-open-value-limit"),
        ]:
            output = suite.command("vector-capacity-" + label, argv, success=False)
            error = Path(suite.commands[-1]["output"]).with_suffix(".stderr").read_text(encoding="utf-8")
            if diagnostic not in output + error:
                raise AssertionError((label, output, error))

    suite.case("vector-receive-over-capacity-is-observer-error", capacity_error)


def wire_cases(suite):
    subject = suite.export("wire-services", (FIXTURES / "structured-source/open-services.mlir").read_text(encoding="utf-8"))
    mutations = []
    def changed(label, action):
        data = copy.deepcopy(subject[2])
        action(definition(data, "main"), data)
        mutations.append((label, data))
    changed("duplicate-roles", lambda root, _: root[6][1].__setitem__(1, "P"))
    changed("unknown-input-owner", lambda root, _: root[6][2][0].__setitem__(0, "Unknown"))
    changed("shared-service-owner", lambda root, _: root[6][2].__setitem__(0, ["P", "V"]))
    changed("empty-service-owner", lambda root, _: root[6][2].__setitem__(0, []))
    changed("duplicate-query-site", lambda root, _: root[9][1][1].__setitem__(4, root[9][1][0][4]))
    changed("missing-query-site", lambda root, _: root[9][1][0].__setitem__(4, ""))
    changed("wrong-query-owner", lambda root, _: root[9][1][0][0].__setitem__(1, "V"))
    changed("unknown-query-field", lambda root, _: root[9][1][0][0].__setitem__(2, "bn254.fr"))
    changed("protocol-missing-interface", lambda root, _: root.__setitem__(6, []))
    changed("extra-function-field", lambda root, _: root.append("extra"))
    changed("extra-envelope-field", lambda _, data: data.append("extra"))
    for label, data in mutations:
        suite.case("wire-" + label, lambda n=label, d=data: suite.refuse_snapshot("wire-" + n, d))


def schnorr_cases(suite):
    subject = suite.authored("schnorr-interactive", *fixture("schnorr-interactive"))
    root = definition(subject[2], subject[2][3])
    prover, verifier = root[6][1]
    instructions = root[9][1]
    draws = [row for row in instructions if row[0][0] == "draw"]
    exchanges = [row for row in instructions if row[0][0] == "exchange"]
    if not (len(draws) == 2 and len(exchanges) == 3):
        raise AssertionError('bridges/structured/open_protocol.py:260: len(draws) == 2 and len(exchanges) == 3')
    commitment, delivery, response = [row[4] for row in exchanges]
    nonce, challenge = [row[4] for row in draws]
    actions = [
        ["receive", commitment, prover, verifier, GROUP_TYPE],
        ["draw", challenge, verifier, SERVICE, "29", FIELD],
        ["send", delivery, verifier, prover, FIELD_TYPE, "5"],
        ["receive", response, prover, verifier, FIELD_TYPE],
    ]
    script = [reply(action, value) for action, value in zip(actions, ("14", "5", None, "22"))]
    # Additive group equation: 2*22 = 14 + 6*5. Verifier has no witness.
    inputs = ["2", "6", None, None, "29"]
    suite.case("schnorr-verifier-accepts", lambda: suite.compare_open(
        subject, "verifier", verifier, inputs, script, returned([True], script)))
    altered = copy.deepcopy(script)
    altered[-1][2] = ["value", "23"]
    suite.case("schnorr-verifier-rejects", lambda: suite.compare_open(
        subject, "verifier-rejects", verifier, inputs, altered, returned([False], altered)))
    for index, action in enumerate(actions):
        stopped_script = script[:index] + [reply(action, stop="abort")]
        suite.case(f"schnorr-stop-{index}", lambda n=index, a=action, s=stopped_script:
                   suite.compare_open(subject, f"stop-{n}", verifier, inputs, s, stopped("abort", a[1], s)))
    # The prover receives 11 independently of the verifier's challenge 5.
    prover_script = [
        reply(["draw", nonce, prover, SERVICE, "17", FIELD], "7"),
        reply(["send", commitment, prover, verifier, GROUP_TYPE, "14"]),
        reply(["receive", delivery, verifier, prover, FIELD_TYPE], "11"),
        reply(["send", response, prover, verifier, FIELD_TYPE, "40"]),
    ]
    suite.case("schnorr-independent-challenge", lambda: suite.compare_open(
        subject, "independent-challenge", prover, ["2", "6", "3", "17", None], prover_script,
        returned([None], prover_script)))
    # Relation metadata and its dormant mathematical declaration are retained.
    if not (len(subject[2][5]) == 1):
        raise AssertionError('bridges/structured/open_protocol.py:293: len(subject[2][5]) == 1')
    if not (any(row[0] == "function" and row[2] == "math" for row in subject[2][7])):
        raise AssertionError('bridges/structured/open_protocol.py:294: any(row[0] == "function" and row[2] == "math" for row in subject[2][7])')


def schnorr_variant_cases(suite):
    for form in ("Helpers", "Reordered", "EarlyChallenge"):
        stem = {"Helpers": "helpers", "Reordered": "reordered",
                "EarlyChallenge": "early-challenge"}[form]
        subject = suite.authored("schnorr-" + form, *fixture("schnorr-" + stem))
        root = definition(subject[2], subject[2][3])
        prover, verifier = root[6][1]
        instructions = root[9][1]
        query = next(row for row in instructions if row[0][:2] == ["draw", verifier])
        exchanges = [row for row in instructions if row[0][0] == "exchange"]
        commitment, challenge, response = [row[4] for row in exchanges]
        receive = ["receive", commitment, prover, verifier, GROUP_TYPE]
        draw = ["draw", query[4], verifier, SERVICE, "29", FIELD]
        initial = [reply(draw, "5"), reply(receive, "14")] if form == "EarlyChallenge" else [
            reply(receive, "14"), reply(draw, "5")]
        script = initial + [reply(["send", challenge, verifier, prover, FIELD_TYPE, "5"]),
                            reply(["receive", response, prover, verifier, FIELD_TYPE], "22")]
        suite.case("variant-" + form, lambda s=subject, n=form, r=verifier, v=script:
                   suite.compare_open(s, n, r, ["2", "6", None, None, "29"], v, returned([True], v)))
        # The changed order remains observable even though this honest sample accepts.
        suite.case("variant-first-action-" + form, lambda s=subject, n=form, r=verifier, a=script[0][1]:
                   suite.compare_open(s, n + "-first", r, ["2", "6", None, None, "29"], [],
                                      stopped("incomplete", a[1], pending=a)))


def sigma_subject(suite, stem):
    subject = suite.authored(stem, *fixture(stem))
    root = definition(subject[2], subject[2][3])
    prover, verifier = root[6][1]
    instructions = root[9][1]
    draws = [row[4] for row in instructions if row[0][0] == "draw"]
    exchanges = [row[4] for row in instructions if row[0][0] == "exchange"]
    return subject, prover, verifier, draws, exchanges


def schnorr_and_cases(suite):
    subject, prover, verifier, draws, exchanges = sigma_subject(suite, "schnorr-and")
    if not (len(draws) == 3 and len(exchanges) == 5):
        raise AssertionError('bridges/structured/open_protocol.py:334: len(draws) == 3 and len(exchanges) == 5')
    first_nonce, second_nonce, challenge = draws
    first_commitment, second_commitment, delivery, first_response, second_response = exchanges
    actions = [
        ["receive", first_commitment, prover, verifier, GROUP_TYPE],
        ["receive", second_commitment, prover, verifier, GROUP_TYPE],
        ["draw", challenge, verifier, SERVICE, "29", FIELD],
        ["send", delivery, verifier, prover, FIELD_TYPE, "5"],
        ["receive", first_response, prover, verifier, FIELD_TYPE],
        ["receive", second_response, prover, verifier, FIELD_TYPE],
    ]
    # Additive group: 22*2 = 14 + 5*6 and 28*5 = 40 + 5*20 (witnesses 3 and 4).
    script = [reply(action, value) for action, value in zip(actions, ("14", "40", "5", None, "22", "28"))]
    inputs = ["2", "6", "5", "20", None, None, None, "29"]
    suite.case("and-verifier-accepts", lambda: suite.compare_open(
        subject, "and-verifier", verifier, inputs, script, returned([True], script)))
    for index in (4, 5):
        altered = copy.deepcopy(script)
        altered[index][2] = ["value", "23"]
        suite.case(f"and-verifier-rejects-{index}", lambda n=index, a=altered: suite.compare_open(
            subject, f"and-rejects-{n}", verifier, inputs, a, returned([False], a)))
    for index, action in enumerate(actions):
        stopped_script = script[:index] + [reply(action, stop="abort")]
        suite.case(f"and-stop-{index}", lambda n=index, a=action, s=stopped_script:
                   suite.compare_open(subject, f"and-stop-{n}", verifier, inputs, s, stopped("abort", a[1], s)))
    # One challenge reply reaches both responses: 7 + 11*3 and 8 + 11*4.
    prover_script = [
        reply(["draw", first_nonce, prover, SERVICE, "17", FIELD], "7"),
        reply(["draw", second_nonce, prover, SERVICE, "17", FIELD], "8"),
        reply(["send", first_commitment, prover, verifier, GROUP_TYPE, "14"]),
        reply(["send", second_commitment, prover, verifier, GROUP_TYPE, "40"]),
        reply(["receive", delivery, verifier, prover, FIELD_TYPE], "11"),
        reply(["send", first_response, prover, verifier, FIELD_TYPE, "40"]),
        reply(["send", second_response, prover, verifier, FIELD_TYPE, "52"]),
    ]
    suite.case("and-prover", lambda: suite.compare_open(
        subject, "and-prover", prover, ["2", "6", "5", "20", "3", "4", "17", None], prover_script,
        returned([None], prover_script)))
    if not (len(subject[2][5]) == 1):
        raise AssertionError('bridges/structured/open_protocol.py:372: len(subject[2][5]) == 1')


def chaum_pedersen_cases(suite):
    subject, prover, verifier, draws, exchanges = sigma_subject(suite, "chaum-pedersen")
    if not (len(draws) == 2 and len(exchanges) == 4):
        raise AssertionError('bridges/structured/open_protocol.py:377: len(draws) == 2 and len(exchanges) == 4')
    nonce, challenge = draws
    first_commitment, second_commitment, delivery, response = exchanges
    actions = [
        ["receive", first_commitment, prover, verifier, GROUP_TYPE],
        ["receive", second_commitment, prover, verifier, GROUP_TYPE],
        ["draw", challenge, verifier, SERVICE, "29", FIELD],
        ["send", delivery, verifier, prover, FIELD_TYPE, "5"],
        ["receive", response, prover, verifier, FIELD_TYPE],
    ]
    # Additive group: 22*2 = 14 + 5*6 and 22*5 = 35 + 5*15 (one witness 3).
    script = [reply(action, value) for action, value in zip(actions, ("14", "35", "5", None, "22"))]
    suite.case("equality-verifier-accepts", lambda: suite.compare_open(
        subject, "equality-verifier", verifier, ["2", "6", "5", "15", None, None, "29"], script,
        returned([True], script)))
    # The second key uses witness 4; the AND-valid commitment 40 cannot share the response.
    unshared = [reply(action, value) for action, value in zip(actions, ("14", "40", "5", None, "22"))]
    suite.case("equality-rejects-unshared-witness", lambda: suite.compare_open(
        subject, "equality-unshared", verifier, ["2", "6", "5", "20", None, None, "29"], unshared,
        returned([False], unshared)))
    for index, action in enumerate(actions):
        stopped_script = script[:index] + [reply(action, stop="abort")]
        suite.case(f"equality-stop-{index}", lambda n=index, a=action, s=stopped_script: suite.compare_open(
            subject, f"equality-stop-{n}", verifier, ["2", "6", "5", "15", None, None, "29"], s,
            stopped("abort", a[1], s)))
    prover_script = [
        reply(["draw", nonce, prover, SERVICE, "17", FIELD], "7"),
        reply(["send", first_commitment, prover, verifier, GROUP_TYPE, "14"]),
        reply(["send", second_commitment, prover, verifier, GROUP_TYPE, "35"]),
        reply(["receive", delivery, verifier, prover, FIELD_TYPE], "11"),
        reply(["send", response, prover, verifier, FIELD_TYPE, "40"]),
    ]
    suite.case("equality-prover", lambda: suite.compare_open(
        subject, "equality-prover", prover, ["2", "6", "5", "15", "3", "17", None], prover_script,
        returned([None], prover_script)))
    if not (len(subject[2][5]) == 1):
        raise AssertionError('bridges/structured/open_protocol.py:412: len(subject[2][5]) == 1')


def run_cases(suite):
    component_cases(suite)
    service_cases(suite)
    group_cases(suite)
    vector_receive_cases(suite)
    wire_cases(suite)
    schnorr_cases(suite)
    schnorr_variant_cases(suite)
    schnorr_and_cases(suite)
    chaum_pedersen_cases(suite)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--reference", type=Path, default=ROOT / "build/compiler/test/zkc-structured_reference-test")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--write-fixtures", action="store_true")
    args = parser.parse_args()
    args.runtime, args.seed, args.cases = None, 0, 1
    return OpenSuite(args).run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
