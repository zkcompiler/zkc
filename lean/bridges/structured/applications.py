#!/usr/bin/env python3
"""Compare complete retained applications and ordered participant observations."""

import argparse
import copy
import json
from pathlib import Path
import sys

from check import FIELD, ROOT, definition, fixture, write_json
from open_protocol import FIELD_TYPE, SERVICE, OpenSuite, reply, returned, stopped


def authored(suite, label, stem):
    return suite.authored(label, *fixture(stem))


def roles(subject):
    return definition(subject[2], subject[2][3])[6][1]


def applications(suite):
    subject = authored(suite, "application", "application")
    for role_index, inputs, outputs in [
        (0, ["2", "3"], ["6", None]), (1, ["5", "7"], [None, "12"]),
        (0, ["0", "9"], ["0", None]), (1, ["0", "9"], [None, "9"]),
    ]:
        role = roles(subject)[role_index]
        label = f"application-{role}-{'-'.join(inputs)}"
        suite.case(label, lambda n=label, r=role, i=inputs, e=outputs:
                   suite.compare_open(subject, n, r, i, [], returned(e)))
    source = subject[0].read_text(encoding="utf-8")
    leaf = next(row for row in subject[2][7] if row[0] == "function" and
                any(instruction[0][0] == "field.multiply" for instruction in row[9][1]))
    if not (source.count(leaf[1]) == 2):
        raise AssertionError('bridges/structured/applications.py:35: source.count(leaf[1]) == 2')
    if not (source.count('"algebra.field_multiply"') == 1):
        raise AssertionError('bridges/structured/applications.py:36: source.count(\'"algebra.field_multiply"\') == 1')
    for name, changed, value in [
        ("application-renamed", source.replace(leaf[1], "renamed_leaf"), "6"),
        ("application-mutant", source.replace('"algebra.field_multiply"', '"algebra.field_add"'), "5"),
    ]:
        variant = suite.export(name, changed, subject[2][3])
        if not (variant[2][2] != subject[2][2]):
            raise AssertionError('bridges/structured/applications.py:42: variant[2][2] != subject[2][2]')
        suite.case(name, lambda n=name, s=variant, v=value:
                   suite.compare_open(s, n, roles(s)[0], ["2", "3"], [], returned([v, None])))
    return subject


def service_subject(suite, nested):
    if nested:
        subject = authored(suite, "nested-service", "application-wrapper")
        return (subject, *roles(subject), [
                             "apply_2_s0_s0", "apply_13_apply_2_s0_s3_s0",
                             "apply_13_apply_2_s0_s3_s2", "apply_13_apply_2_s0_s3_s5_0",
                             "apply_2_s0_s6"], "apply_2_s0_s2")
    subject = authored(suite, "service-order", "service-order")
    return (subject, *roles(subject), [
                         "s0", "apply_2_s3_s0", "apply_2_s3_s2", "apply_2_s3_s5_0", "s6"], "s2")


def service_cases(suite, nested):
    subject, receiver, owner, sites, guard_site = service_subject(suite, nested)
    label = "nested" if nested else "service"
    receive = ["receive", sites[3], owner, receiver, FIELD_TYPE]
    received = [reply(receive, "19")]
    suite.case(label + "-received-value", lambda: suite.compare_open(
        subject, label + "-received-value", receiver, [None, None, None], received,
        returned(["19", None], received)))
    traces = []
    for alias in (False, True):
        handles = [8, 8 if alias else 17]
        # An independent stateful provider script; the tested evaluators must
        # request these exact handles in this order, including the child call.
        counters = {8: 0, 17: 0}
        responses = []
        draws = []
        for index, handle in enumerate([handles[0], handles[0], handles[1]]):
            counters[handle] += 1
            draws.append(counters[handle])
            responses.append(reply(["draw", sites[index], owner, SERVICE, str(handle), FIELD],
                                   str(counters[handle])))
        message = draws[1] + draws[2]
        responses.append(reply(["send", sites[3], owner, receiver, FIELD_TYPE, str(message)]))
        counters[8] += 1
        responses.append(reply(["draw", sites[4], owner, SERVICE, "8", FIELD], str(counters[8])))
        expected = returned([None, str(draws[0] + message + counters[8])], responses)
        name = label + ("-aliased" if alias else "-distinct")
        inputs = [True, "8", str(handles[1])]
        suite.case(name, lambda n=name, i=inputs, rs=responses, e=expected:
                   suite.compare_open(subject, n, owner, i, rs, e))
        if not (counters == ({8: 4, 17: 0} if alias else {8: 3, 17: 1})):
            raise AssertionError('bridges/structured/applications.py:90: counters == ({8: 4, 17: 0} if alias else {8: 3, 17: 1})')
        traces.append((inputs, responses))
    inputs, responses = traces[1]
    for index, response in enumerate(responses):
        action = response[1]
        prefix = responses[:index]
        tail = [reply(["draw", "unused_suffix", owner, SERVICE, "8", FIELD], "99")]
        aborted = prefix + [reply(action, stop="abort")]
        name = f"{label}-abort-{index}"
        suite.case(name, lambda n=name, rs=aborted, a=action:
                   suite.compare_open(subject, n, owner, inputs, rs + tail,
                                      stopped("abort", a[1], rs)))
        name = f"{label}-missing-{index}"
        suite.case(name, lambda n=name, rs=prefix, a=action:
                   suite.compare_open(subject, n, owner, inputs, rs,
                                      stopped("incomplete", a[1], rs, a)))
        wrong = copy.deepcopy(response)
        wrong[1][1] = "wrong_site"
        name = f"{label}-mismatch-{index}"
        suite.case(name, lambda n=name, rs=prefix, bad=wrong, a=action:
                   suite.compare_open(subject, n, owner, inputs, rs + [bad],
                                      stopped("refused", a[1], rs, a)))
    for go, reason in [(False, "reject"), (None, "incomplete")]:
        name = label + "-guard-" + reason
        suite.case(name, lambda n=name, g=go, why=reason:
                   suite.compare_open(subject, n, owner, [g, "8", "8"], responses,
                                      stopped(why, guard_site, responses[:1])))
    return subject


def wire_controls(suite, subject):
    original = subject[2]
    owner = next(row for row in original[7] if row[0] == "function" and
                 any(instruction[0][0] == "protocol_apply" for instruction in row[9][1]))
    index = next(i for i, row in enumerate(owner[9][1]) if row[0][0] == "protocol_apply")
    source = owner[9][1][index]
    variants = []
    for label, descriptor in [
        ("missing-target", ["protocol_apply", "missing", source[0][2]]),
        ("missing-roles", source[0][:2]),
        ("extra-descriptor", source[0] + ["extra"]),
        ("numeric-role", ["protocol_apply", source[0][1], [0] + source[0][2][1:]]),
        ("foreign-role", ["protocol_apply", source[0][1], ["Foreign"] + source[0][2][1:]]),
        ("short-roster", ["protocol_apply", source[0][1], source[0][2][:-1]]),
        ("duplicate-role", ["protocol_apply", source[0][1], [source[0][2][0]] * len(source[0][2])]),
    ]:
        bad = copy.deepcopy(original)
        definition(bad, owner[1])[9][1][index][0] = descriptor
        variants.append((label, bad))
    for label, slot, replacement in [
        ("extra-region", 3, [[[], [], ["block", [], ["yield", []]]]]),
        ("empty-site", 4, ""), ("wrong-output-abi", 2, []),
    ]:
        bad = copy.deepcopy(original)
        definition(bad, owner[1])[9][1][index][slot] = replacement
        variants.append((label, bad))
    # A retained malformed wire is an independent reader control. Its original
    # digest is not asserted to identify mutated native bytes.
    diagnostics = {
        "missing-target": "structured-unknown-helper",
        "missing-roles": "structured-operation-unsupported",
        "extra-descriptor": "structured-operation-unsupported",
        "numeric-role": "structured-string",
        "foreign-role": "structured-role",
        "short-roster": "structured-role-substitution",
        "duplicate-role": "structured-role-substitution",
        "extra-region": "structured-protocol-region",
        "empty-site": "structured-site",
        "wrong-output-abi": "structured-protocol-apply-signature",
    }
    for label, snapshot in variants:
        suite.case(label, lambda n=label, s=snapshot: suite.refuse_snapshot(n, s, diagnostics[n]))


def local_boundary_cases(suite):
    source = '''!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
  local.func @work(%x:!F,%unused:!F)->!F attributes {logical_origin=["work",[]]} {
    local.return %x : !F
  }
  "protocol.func"() ({
  ^entry(%x:!F,%unused:!F):
    %v = "protocol.local_call"(%x,%unused) {callee=@work,role="P",site="work"} : (!F,!F)->!F
    "protocol.return"(%v) : (!F)->()
  }) {sym_name="child",function_type=(!F,!F)->!F,roles=["P","Q"],
      input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
  "protocol.func"() ({
  ^entry(%x:!F,%unused:!F):
    %v = "protocol.apply"(%x,%unused) {callee=@child,roles=["P","Q"],site="A"} : (!F,!F)->!F
    "protocol.return"(%v) : (!F)->()
  }) {sym_name="main",function_type=(!F,!F)->!F,roles=["P","Q"],
      input_roles=[["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
    subject = suite.export("local-boundary", source)
    for label, role, inputs, expected in [
        ("local-missing-unused", "P", ["7", None], stopped("incomplete", "apply_1_A_work")),
        ("local-present", "P", ["7", "8"], returned(["7"])),
        ("local-nonowner", "Q", [None, None], returned([None])),
    ]:
        suite.case(label, lambda n=label, r=role, i=inputs, e=expected:
                   suite.compare_open(subject, n, r, i, [], e))
    stopping = source.replace('local.return %x : !F',
        '"local.stop"() {reason="abort",site="helper_stop"} : ()->()')
    for site in ("A", "B"):
        variant = suite.export("local-stop-" + site, stopping.replace('site="A"', f'site="{site}"'))
        label = "local-raw-helper-stop-" + site
        suite.case(label, lambda n=label, s=variant:
                   suite.compare_open(s, n, "P", ["7", "8"], [], stopped("abort", "helper_stop")))
        label = "local-missing-before-stop-" + site
        suite.case(label, lambda n=label, s=variant, at=site:
                   suite.compare_open(s, n, "P", ["7", None], [],
                                      stopped("incomplete", f"apply_1_{at}_work")))
    subset = '''!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
  func.func private @identity(%x:!F)->!F { func.return %x : !F }
  local.func @stop() attributes {logical_origin=["stop",[]]} {
    "local.stop"() {reason="abort",site="helper_stop"} : ()->()
  }
  "protocol.func"() ({
    %one = "algebra.constant"() {value="1"} : ()->!F
    %v = func.call @identity(%one) : (!F)->!F
    "protocol.local_call"() {callee=@stop,role="A",site="stop"} : ()->()
    "protocol.return"() : ()->()
  }) {sym_name="child",function_type=()->(),roles=["A"],input_roles=[],output_roles=[]} : ()->()
  "protocol.func"() ({
    "protocol.apply"() {callee=@child,roles=["P"],site="A"} : ()->()
    %answer = "algebra.constant"() {value="7"} : ()->!F
    "protocol.return"(%answer) : (!F)->()
  }) {sym_name="main",function_type=()->!F,roles=["P","Q"],input_roles=[],output_roles=[["Q"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
    subject = suite.export("subset-zero-result", subset)
    for role, expected in [("P", stopped("abort", "helper_stop")), ("Q", returned(["7"]))]:
        label = "subset-zero-result-" + role
        suite.case(label, lambda n=label, r=role, e=expected:
                   suite.compare_open(subject, n, r, [], [], e))


def partial_math_cases(suite):
    source = (ROOT / "compiler/test/fixtures/finite/total-state.mlir").read_text(encoding="utf-8")
    fold = ('"algebra.finite_fold"(%xs,%a,%b) {domain=@items,step=@step} '
            ': (!V,!F,!F)->(!F,!F)')
    wrapper = '''"protocol.func"() ({
      ^entry(%xs:!V,%a:!F,%b:!F,%outside:!F):
        %r:2 = "protocol.apply"(%xs,%a,%b) {callee=@child,roles=["P"],site="fold"}
          : (!V,!F,!F)->(!F,!F)
        "protocol.return"(%r#0,%r#1,%outside) : (!F,!F,!F)->()
      }) {sym_name="main",function_type=(!V,!F,!F,!F)->(!F,!F,!F),roles=["P","Q"],
          input_roles=[["P"],["P"],["P"],["Q"]],output_roles=[["P"],["P"],["Q"]]} : ()->()
    '''
    for indirect in (False, True):
        variant = source
        if indirect:
            variant = variant.replace(fold, 'func.call @fold_helper(%xs,%a,%b) : (!V,!F,!F)->(!F,!F)')
            helper = f'''func.func private @fold_helper(%xs:!V,%a:!F,%b:!F)->(!F,!F) {{
              %r:2 = {fold}
              func.return %r#0,%r#1 : !F,!F
            }}'''
            variant = variant.replace(' "protocol.func"() ({', helper + '\n "protocol.func"() ({', 1)
        variant = variant.replace('sym_name="main"', 'sym_name="child"').replace('["P"]', '["A"]')
        variant = variant.replace('}) {profile=', wrapper + '\n}) {profile=', 1)
        label = "partial-math-" + ("helper" if indirect else "direct")
        subject = suite.export(label, variant)
        # Independent fold rule: each element replaces (a,b) with (b,element).
        # The application belongs only to P; Q does not enter the child at all.
        for name, role, inputs, outputs in [
            ("owner", "P", [["3", "5", "7"], "1", "2", None], ["5", "7", None]),
            ("empty", "P", [[], "1", "2", None], ["1", "2", None]),
            ("outside", "Q", [None, None, None, "41"], [None, None, "41"]),
        ]:
            case_name = label + "-" + name
            suite.case(case_name, lambda n=case_name, s=subject, r=role, i=inputs, o=outputs:
                       suite.compare_open(s, n, r, i, [], returned(o)))


def closed_profile_boundary(suite):
    source = '''!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%x:!F):
    "protocol.return"(%x) : (!F)->()
  }) {sym_name="child",function_type=(!F)->!F,roles=["A"],
      input_roles=[["A"]],output_roles=[["A"]]} : ()->()
  "protocol.func"() ({
  ^entry(%x:!F):
    %y = "protocol.apply"(%x) {callee=@child,roles=["P"],site="child_call"} : (!F)->!F
    "protocol.return"(%y) : (!F)->()
  }) {sym_name="main",function_type=(!F)->!F,roles=["P"],
      input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
'''
    subject = suite.export("closed-profile-boundary", source)
    suite.case("application-open-profile", lambda: suite.compare_open(
        subject, "application-open-profile", "P", ["7"], [], returned(["7"])))

    def check_boundary():
        original, snapshot, _ = subject
        request = snapshot.parent / "closed.inputs.json"
        write_json(request, ["7"])
        native = json.loads(suite.command("application-native-closed",
            [suite.tools["reference"], original, "main", request]))
        if not (native == ["returned", ["7"]]):
            raise AssertionError(native)
        write_json(request, [["field", FIELD, "7"]])
        refusal = json.loads(suite.command("application-formal-closed-profile",
            [suite.tools["lean"], "run", snapshot, request], success=False))
        if not (refusal["status"] == "refused" and refusal["code"] == "structured-open-profile"):
            raise AssertionError(refusal)

    # The native closed observer supports calls; the independent formal closed
    # profile deliberately excludes them. Open observations above are paired.
    suite.case("explicit-closed-profile-boundary", check_boundary)


def run_cases(suite):
    applications(suite)
    service = service_cases(suite, False)
    service_cases(suite, True)
    wire_controls(suite, service)
    local_boundary_cases(suite)
    partial_math_cases(suite)
    closed_profile_boundary(suite)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, default=ROOT / "build/compiler/zkc-compile")
    parser.add_argument("--reference", type=Path, default=ROOT / "build/compiler/test/zkc-structured_reference-test")
    parser.add_argument("--lean", type=Path, default=ROOT / "lean/.lake/build/bin/structured-source")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=1)
    parser.add_argument("--seed", type=int, default=45617)
    parser.add_argument("--write-fixtures", action="store_true")
    args = parser.parse_args()
    args.runtime = None
    return OpenSuite(args).run(run_cases)


if __name__ == "__main__":
    sys.exit(main())
