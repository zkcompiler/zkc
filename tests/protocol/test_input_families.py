"""One compiled compact family, selected from each role's actual entry inputs.

The BP+/OpenVM fixtures exercise shape contracts, not the full cryptographic
protocols. Native participants and Lean's independent common-source interpreter
execute the same admitted stored ingress functions and counted body.
"""

import copy
import hashlib
import json
import struct
from pathlib import Path

import pytest
from journal import Journal, names
from toolchain import Toolchain, records

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests/fixtures/input-families"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


@pytest.fixture(scope="module")
def families(worker_id):
    tools = Toolchain()
    result = {}
    for name in ("counted", "bp-shape", "openvm-shape", "private-inputs"):
        directory = records(case=f"{worker_id}-{name}")
        journal = Journal(directory)
        source = directory / "source.json"
        candidate = directory / "participants.json"
        authored = FIXTURES / f"{name}.pir"
        source.write_text(journal.run([tools.compiler, "protocol-source", authored]))
        candidate.write_text(journal.run([tools.compiler, "protocol-compile", authored]))
        common = journal.run([tools.compiler, "protocol-import", authored])
        projected = journal.run([tools.tool("compiler", "zkc-opt"),
                                 "--zkc-project-participants", "-"], common)
        (directory / "common.mlir").write_text(common)
        (directory / "participants.mlir").write_text(projected)
        assert 'count = "rounds"' in common and 'parameter = true' in common
        assert 'count = "rounds"' in projected and 'parameter = true' in projected
        assert '"ingress"' in common and '"ingress"' in projected
        document = json.loads(source.read_text())
        common_source = document[3] if document[0] == "zkc.library/1" else document
        body = common_source[3][0][7]
        def nodes(code):
            return sum(1 + (nodes(row[5]) if row[0] == "loop" else 0) for row in code)
        loop = next(row for row in body if row[0] == "loop")
        assert loop[2] == ["parameter", "rounds"]
        assert len(common_source[3]) == 1
        assert len(json.loads(candidate.read_text())[4]) == 2
        evidence = {"common_nodes": nodes(body), "round_nodes": nodes(loop[5]),
                    "source_sha256": digest(source), "participants_sha256": digest(candidate)}
        (directory / "compactness.json").write_text(json.dumps(evidence, indent=2))
        journal.run([tools.checker("interactive-protocol"), "--check-generic", source, candidate])
        result[name] = (source, candidate, evidence)
    return result


def ports(name, n, other=None):
    other = n if other is None else other
    if name == "counted":
        return [["P", [["pn", ["index", str(n)]]]],
                ["V", [["vn", ["index", str(other)]]]]]
    if name == "openvm-shape":
        return [["P", [["metadata", ["indices", [str(n), "1"]]]]],
                ["V", [["receivedMetadata", ["indices", [str(other), "1"]]]]]]
    def shape(count):
        rounds = 6 + (count - 1).bit_length() if count else 6
        # Original 32-byte encodings, retained as bytes. Shape admission does
        # not claim subgroup/scalar validity; the external adapter owns it.
        return [["indices", [str(x) for x in ([1] + [0] * 31) * length]]
                for length in (count, rounds, rounds)]
    return [["P", list(zip(("commitments", "left", "right"), shape(n)))],
            ["V", list(zip(("receivedCommitments", "receivedLeft", "receivedRight"), shape(other)))]]


def execute(families, name, supplied, directory, selected=None, resources=None):
    tools = Toolchain()
    source, candidate, evidence = families[name]
    journal = Journal(directory)
    native = directory / "native-inputs.json"
    reference = directory / "reference-inputs.json"
    def wire(value):
        kind, payload = value
        if kind == "rng:bls12-381.fr":
            return ["host", payload[0]]
        if kind == "field:bls12-381.fr":
            return ["field", payload]
        if kind == "index":
            data = b"ZKCV\x01\x1f" + struct.pack("<Q", int(payload))
        else:
            data = b"ZKCV\x01\x20" + struct.pack("<I", len(payload))
            data += b"".join(struct.pack("<Q", int(n)) for n in payload)
        return ["wire", data.hex()]
    native.write_text(json.dumps(["zkc.run/2", "main", "family", [],
        [[role, [["rng", r[0], r[3], "entry"] for r in (resources or []) if r[1] == role],
          [[port, wire(value)] for port, value in values], []]
         for role, values in supplied], []]))
    reference.write_text(json.dumps(["zkc.reference-inputs/1", "main", "family",
                                    [row for row in supplied if selected is None or row[0] == selected],
                                    resources or [], [], []]))
    actual = journal.attempt([tools.runtime, "run-protocol", source, candidate,
                              native, tools.checker("interactive-protocol")], keep="native")
    args = [tools.checker("interactive-protocol"),
            "--generic-reference" if selected is None else "--generic-role", source, reference]
    if selected is not None: args.append(selected)
    expected = journal.attempt(args, keep="reference")
    assert digest(source) == evidence["source_sha256"]
    assert digest(candidate) == evidence["participants_sha256"]
    return actual, expected


@pytest.mark.parametrize("name,n", [(name, n) for name in ("counted", "openvm-shape")
                                    for n in (0, 1, 2, 3, 10)] +
                         [("bp-shape", n) for n in range(1, 17)])
def test_actual_selection(families, directory, name, n):
    actual, expected = execute(families, name, ports(name, n), directory)
    assert actual.returncode == 0, actual.stderr
    assert expected.returncode == 0, expected.stdout
    native, reference = json.loads(actual.stdout), json.loads(expected.stdout)
    rounds = 6 + (n - 1).bit_length() if name == "bp-shape" else n
    assert native["outcome"] == ["returned", {"P": [["index", rounds]], "V": [["index", rounds]]}]
    assert reference[3] == ["returned", [["index", str(rounds)], ["index", str(rounds)]]]
    sends = [event for event in reference[4] if event[0] == "send"]
    assert native["wire"]["messages"] == len(sends) == rounds
    assert [int(event[1][4][0][2]) for event in sends] == list(range(rounds))


@pytest.mark.parametrize("name", ["counted", "openvm-shape", "bp-shape"])
def test_roles_keep_independent_selection(families, directory, name):
    actual, expected = execute(families, name, ports(name, 1, 3), directory)
    assert actual.returncode == 0, actual.stderr
    assert json.loads(actual.stdout)["outcome"] == ["failed", "interactive-family-disagreement"]
    assert json.loads(expected.stdout)[3][1] == "interactive-family-disagreement"


@pytest.mark.parametrize("case", ["bound", "overflow", "missing-metadata", "width",
                                  "empty-commitments", "too-many-commitments", "partial-commitment",
                                  "wrong-left-rounds", "wrong-right-rounds", "non-byte"])
def test_malformed_actual_input(families, directory, case):
    name = "openvm-shape" if case in ("bound", "overflow", "missing-metadata", "width") else "bp-shape"
    supplied = ports(name, 3)
    expected_code = "require"
    if case in ("bound", "overflow"):
        supplied = ports(name, 11 if case == "bound" else 2**64 - 1)
        expected_code = "interactive-family-bound"
    elif case == "missing-metadata": supplied[1][1][0][1][1] = []
    elif case == "width": supplied[1][1][0][1][1][1] = "2"
    elif case == "empty-commitments": supplied = ports(name, 0)
    elif case == "too-many-commitments": supplied = ports(name, 17)
    elif case == "partial-commitment": supplied[1][1][0][1][1].pop()
    elif case == "wrong-left-rounds": supplied[1][1][1][1][1] = ["0"] * 32
    elif case == "wrong-right-rounds": supplied[1][1][2][1][1].extend(["0"] * 32)
    elif case == "non-byte": supplied[1][1][0][1][1][0] = "256"
    actual, expected = execute(families, name, supplied, directory)
    assert actual.returncode == 0, actual.stdout + actual.stderr
    native = json.loads(actual.stdout)
    failed_role = "P" if case in ("bound", "overflow", "empty-commitments", "too-many-commitments") else "V"
    assert native["outcome"][:3] == ["stopped", failed_role, "ingress.rounds"]
    assert native["stop"]["detail"] == (expected_code if expected_code == "interactive-family-bound" else "rejected:require")
    assert native["stop"]["cleanup_errors"] == []
    assert native["wire"]["messages"] == 0
    assert native["resources"] == []
    assert [event["site"] for event in native["ingress"][failed_role]["events"]] == ["ingress.rounds"]
    assert native["ingress"][failed_role]["selected_parameters"] == {}
    assert native["ingress"][failed_role]["stop"] == native["stop"]
    # The ingress byte checks themselves iterate. These reached iterations must
    # survive; none belongs to the protocol member's message loop.
    expected_iterations = {
        "empty-commitments": (384, 384), "too-many-commitments": (1248, 1248),
        "partial-commitment": (612, 607), "wrong-left-rounds": (612, 388),
        "wrong-right-rounds": (612, 644), "non-byte": (612, 1),
    }.get(case, (0, 0))
    for role, iterations in zip(("P", "V"), expected_iterations):
        usage = native["usage"][role]
        assert usage["instructions"] > 0
        assert usage["iterations"] == iterations
        assert usage["live_value_bytes"] == 0
        assert usage["total_value_bytes"] > 0
        assert usage["external_work_spent"] == 0
    observation = json.loads(expected.stdout)
    assert observation[3][1] == expected_code, observation[3]
    assert "ingress.rounds" in json.dumps(observation[3][2])
    assert observation[4] and observation[5] == []
    # Reference joint role order can differ from independently constructed
    # native runners. Compare the reached failing role, not a fabricated global
    # merge of the two logs; earlier native-only attempts remain in the report.
    reference_role = observation[3][2][6]
    iterations = set()
    for event in observation[4]:
        if event[0] != "request" or event[1][1][6] != reference_role:
            continue
        path = event[1][1][4]
        for position, frame in enumerate(path):
            if frame[0] == "for":
                iterations.add(json.dumps(path[:position + 1]))
    assert len(iterations) == native["usage"][reference_role]["iterations"]


REFUSALS = json.loads((FIXTURES / "refusals.json").read_text())


@pytest.mark.parametrize("mutation,code", REFUSALS, ids=[row[0] for row in REFUSALS])
def test_malformed_carrier(families, directory, mutation, code):
    """Each malformed family carrier is refused by both readers under one name.

    The names are shared with the native reader's own family controls, which
    mutate the compiled participants rather than this source. A selector with
    a well-formed body but the wrong result arity is what reaches the
    signature check; an empty result list fails earlier, at the function's own
    return.
    """
    tools = Toolchain()
    source = copy.deepcopy(json.loads(families["counted"][0].read_text()))
    binding = source[4][0][3][0][1]
    if mutation == "bound": binding[1] = "18446744073709551616"
    elif mutation == "wide-bound": binding[1] = "1" * 79
    elif mutation == "noncanonical-bound": binding[1] = "01"
    elif mutation == "missing-role": binding[2].pop()
    elif mutation == "duplicate-role": binding[2].append(binding[2][0])
    elif mutation == "selector": binding[2][0][1] = "Missing"
    elif mutation == "signature":
        selector = source[2][0]
        selector[3] = ["index", "index"]
        selector[4][-1] = ["return", [selector[4][-1][1][0]] * 2]
    elif mutation == "count": source[3][0][7][0][2][1] = "absent"
    elif mutation == "unknown-input": binding[2][0][2] = ["absent"]
    elif mutation == "future-input": binding[2][0][2] = ["x"]
    elif mutation == "cross-role-input": binding[2][0][2] = ["vn"]
    elif mutation == "duplicate-input": binding[2][0][2] = ["pn", "pn"]
    elif mutation == "missing-input": binding[2][0][2] = []
    path = directory / "malformed.json"
    path.write_text(json.dumps(source))
    journal = Journal(directory)
    compiler = journal.attempt([tools.compiler, "protocol-compile", path])
    lean = journal.attempt([tools.checker("interactive-protocol"), "--admit", path])
    assert compiler.returncode > 0 and names(compiler.stderr, code), compiler.stderr
    assert lean.returncode > 0 and json.loads(lean.stdout) == ["refused", code], lean.stdout


@pytest.mark.parametrize("n", [0, 1, 3, 10])
def test_selector_subset_retains_private_ports(families, directory, n):
    supplied = [["P", [["pn", ["index", str(n)]],
                       ["witness", ["field:bls12-381.fr", "7"]],
                       ["coins", ["rng:bls12-381.fr", ["coins", "0"]]]]],
                ["V", [["vn", ["index", str(n)]],
                       ["initial", ["field:bls12-381.fr", "7"]]]]]
    resources = [["coins", "P", "Main", "10", ["rng", ["1"] * 10]]]
    actual, expected = execute(families, "private-inputs", supplied, directory,
                               resources=resources)
    assert actual.returncode == 0, actual.stdout + actual.stderr
    assert expected.returncode == 0, expected.stdout + expected.stderr
    native, reference = json.loads(actual.stdout), json.loads(expected.stdout)
    result = str(7 * 2**n)
    assert native["outcome"] == ["returned", {
        "P": [["field", result], ["private", "rng"]], "V": [["field", result]]}]
    assert reference[3] == ["returned", [["field:bls12-381.fr", result],
        ["rng:bls12-381.fr", ["coins", str(n)]], ["field:bls12-381.fr", result]]]
    assert native["wire"]["messages"] == n
    assert native["resources"][0][2:5] == [n, n, 10 - n]
    assert reference[5][0][3:6] == [str(n), str(n), str(10 - n)]


@pytest.mark.parametrize("port,code", [("coins", "interactive-family-input"),
                                      ("witness", "interactive-family-signature")])
def test_selector_rejects_incompatible_private_ports(families, directory, port, code):
    source = json.loads(families["private-inputs"][0].read_text())
    source[3][4][0][3][0][1][2][0][2] = [port]
    path = directory / "bad-subset.json"
    path.write_text(json.dumps(source))
    tools, journal = Toolchain(), Journal(directory)
    compiler = journal.attempt([tools.compiler, "protocol-compile", path])
    lean = journal.attempt([tools.checker("interactive-protocol"), "--check-generic", path, families["private-inputs"][1]])
    assert compiler.returncode > 0 and names(compiler.stderr, code), compiler.stderr
    assert lean.returncode > 0 and names(lean.stdout + lean.stderr, code), lean.stdout + lean.stderr


def test_family_static_construction_refuses_unbound_count(families, directory):
    tools, journal = Toolchain(), Journal(directory)
    descriptor = directory / "descriptor.json"
    descriptor.write_text(json.dumps(["zkc.construction/1", "main", "P", "V", [],
                                     ["coins", []], "0", "merlin3.bls12-381.fr64be/1", "exact"]))
    result = journal.attempt([tools.compiler, "protocol-construct",
                              families["counted"][0], descriptor])
    assert result.returncode > 0 and names(result.stderr, "construction-family-input-required")


@pytest.mark.parametrize("name", ["counted", "bp-shape", "openvm-shape", "private-inputs"])
def test_family_frontend_roundtrip(families, directory, name):
    tools, journal = Toolchain(), Journal(directory)
    formatted = journal.run([tools.compiler, "protocol-format", FIXTURES / f"{name}.pir"])
    assert formatted == journal.run([tools.compiler, "protocol-format", "-"], formatted)
    source = journal.run([tools.compiler, "protocol-source", "-"], formatted)
    assert json.loads(source) == json.loads(families[name][0].read_text())


@pytest.mark.parametrize("replacement", ['[]', '["pn", "pn"]', '["pn", 1 : i64]'])
def test_malformed_mlir_argument_binding_table(families, directory, replacement):
    tools, journal = Toolchain(), Journal(directory)
    source, _, _ = families["counted"]
    common = (source.parent / "common.mlir").read_text()
    assert 'argument_names = ["pn", "vn"]' in common
    malformed = common.replace('argument_names = ["pn", "vn"]',
                               'argument_names = ' + replacement)
    result = journal.attempt([tools.tool("compiler", "zkc-opt"),
                              "--zkc-project-participants", "-"], malformed)
    assert result.returncode > 0 and names(result.stderr, "interactive-family-argument-names")


@pytest.mark.parametrize("direction", ["outgoing", "incoming"])
def test_dynamic_dependency_refused(families, directory, direction):
    source = json.loads(families["counted"][0].read_text())
    roles = [["P", "P"], ["V", "V"]]
    if direction == "outgoing":
        source[3].append(["protocol", "Helper", ["P", "V"], [], [], [], [], [["return", []]]])
        source[4].append(["instance", "helper", "Helper", [], [], roles])
        source[3][0][6] = [["sub", "Helper", []]]
        source[4][0][4] = [["sub", "helper"]]
    else:
        source[3].append(["protocol", "Parent", ["P", "V"], [],
            [["pn", "P", "index"], ["vn", "V", "index"]],
            [["P", "index"], ["V", "index"]], [["sub", "Family", []]],
            [["call", "child", "sub", ["pn", "vn"], ["x", "y"]], ["return", ["x", "y"]]]])
        source[4].append(["instance", "parent", "Parent", [], [["sub", "Main"]], roles])
        source[5][0][2] = "parent"
    path = directory / "dependency.json"
    path.write_text(json.dumps(source))
    tools, journal = Toolchain(), Journal(directory)
    compiler = journal.attempt([tools.compiler, "protocol-compile", path])
    lean = journal.attempt([tools.checker("interactive-protocol"), "--admit", path])
    assert compiler.returncode > 0 and names(compiler.stderr, "interactive-family-dependency")
    assert lean.returncode > 0 and names(lean.stdout, "interactive-family-dependency")


@pytest.mark.parametrize("role,p,v,count", [("P", 1, 3, 1), ("V", 1, 0, 0)])
def test_open_role_reference_keeps_local_selection(families, directory, role, p, v, count):
    actual, expected = execute(families, "counted", ports("counted", p, v),
                               directory, selected=role)
    assert actual.returncode == expected.returncode == 0
    assert json.loads(actual.stdout)["outcome"] == ["failed", "interactive-family-disagreement"]
    assert json.loads(expected.stdout)[3] == ["returned", [["index", str(count)]]]


@pytest.mark.parametrize("role", ["Worker", "Auditor"])
@pytest.mark.parametrize("first,later", [(98, 1), (99, 1), (11, 1), (1, 98), (1, 99), (1, 11), (1, 2)])
def test_effectful_ingress_retains_partial_observation(directory, role, first, later):
    tools, journal = Toolchain(), Journal(directory)
    authored = (FIXTURES / "effectful-ingress.pir").read_text().replace("Worker", role)
    source = directory / "source.json"
    candidate = directory / "participants.json"
    source.write_text(journal.run([tools.compiler, "protocol-source", "-"], authored))
    candidate.write_text(journal.run([tools.compiler, "protocol-compile", "-"], authored))
    journal.run([tools.checker("interactive-protocol"), "--check-generic", source, candidate])
    compiled = {"effectful": (source, candidate, {
        "source_sha256": digest(source), "participants_sha256": digest(candidate)})}
    supplied = [[role, [["metadata", ["indices", ["1", "2", "3"]]],
                       ["first", ["index", str(first)]], ["later", ["index", str(later)]]]]]
    actual, expected = execute(compiled, "effectful", supplied, directory)
    assert actual.returncode == expected.returncode == 0, actual.stderr + expected.stderr
    native, reference = json.loads(actual.stdout), json.loads(expected.stdout)
    attempts = ["earlier"] if first > 10 else ["earlier", "rounds"]
    selected = {} if first > 10 else {"earlier": first}
    failed = first > 10 or later > 10
    if failed:
        parameter = attempts[-1]
        bad = first if first > 10 else later
        code = {98: "external-invalid-bit-width", 99: "require"}.get(bad, "interactive-family-bound")
        assert native["outcome"][:3] == ["stopped", role, f"ingress.{parameter}"]
        assert native["stop"]["detail"] == ({98: "refused:" + code, 99: "rejected:require"}.get(bad, code))
        assert native["stop"]["cleanup_errors"] == []
        assert reference[3][1] == code
        assert reference[3][0] == ("reject" if bad == 99 else "refused")
        assert f"ingress.{parameter}" in json.dumps(reference[3][2])
        assert native["usage"][role]["iterations"] == 0
    else:
        selected["rounds"] = later
        assert native["outcome"] == ["returned", {role: [["index", first]]}]
        assert reference[3] == ["returned", [["index", str(first)]]]
        assert native["usage"][role]["iterations"] == later
    ingress = native["ingress"][role]
    assert ingress["selected_parameters"] == selected
    assert [event["site"] for event in ingress["events"]] == [f"ingress.{p}" for p in attempts]
    assert all(event["role"] == role for event in ingress["events"])
    # Three overwrite absorbs per reached selector spend exactly three native
    # external-work units. Lean records the transitions but has no such budget.
    assert native["usage"][role]["external_work_spent"] == 3 * len(attempts)
    assert native["usage"][role]["instructions"] > len(attempts)
    assert native["usage"][role]["total_value_bytes"] > 0
    # A successful runner owns its returned index (the native scalar charge is
    # 512 bytes); a stopped runner has released all local/entry bindings.
    assert native["usage"][role]["live_value_bytes"] == (0 if failed else 512)
    assert native["wire"]["messages"] == 0
    assert native["resources"] == reference[5] == []
    assert native["cancelled_roles"] == []
    assert ingress["stop"] == (native["stop"] if failed else None)
    # Native owns ingress attempts, not the backend primitive-event journal.
    # Compare their projection to the independent reference's ordered requests.
    requests = [event[1] for event in reference[4] if event[0] == "request"]
    observes = [request for request in requests if request[2] == "external.openvm.observe"]
    assert len(observes) == len(attempts), requests
    for request, parameter in zip(observes, attempts):
        assert request[1][4][0] == ["local", f"ingress.{parameter}", "Select"]
        assert request[1][6] == role
    responses = [event[2] for event in reference[4]
                 if event[0] == "response" and event[1][2] == "external.openvm.observe"]
    assert responses == [[["indices", list(map(str, [1514881876, 1, 2, 1, 2, 3] + [0] * 13 + [3, 0]))]]] * len(attempts)
    if failed and bad in (98, 99):
        # The failing operation has a request but no fabricated success reply.
        assert reference[4][-1][0] == "request"
        assert reference[4][-1][1][2] == ("external.openvm.sample_bits" if bad == 98 else "control.require")
    assert "no-physical-resource-correspondence" in reference[7]


def test_stopped_ingress_retains_unconsumed_private_resource(families, directory):
    supplied = [["P", [["pn", ["index", "11"]],
                       ["witness", ["field:bls12-381.fr", "7"]],
                       ["coins", ["rng:bls12-381.fr", ["coins", "0"]]]]],
                ["V", [["vn", ["index", "1"]],
                       ["initial", ["field:bls12-381.fr", "7"]]]]]
    resources = [["coins", "P", "Main", "10", ["rng", ["1"] * 10]]]
    actual, expected = execute(families, "private-inputs", supplied, directory,
                               resources=resources)
    assert actual.returncode == expected.returncode == 0
    native, reference = json.loads(actual.stdout), json.loads(expected.stdout)
    assert native["outcome"][:3] == ["stopped", "P", "ingress.rounds"]
    assert native["stop"]["detail"] == reference[3][1] == "interactive-family-bound"
    assert native["resources"][0][:5] == ["P", "coins", 0, 0, 10]
    assert reference[5][0][3:6] == ["0", "0", "10"]
    assert native["cancelled_roles"] == ["V"]
    assert native["ingress"]["P"]["selected_parameters"] == {}
    assert native["ingress"]["V"]["selected_parameters"] == {"rounds": 1}
    assert native["wire"]["messages"] == 0
    assert all(usage["iterations"] == 0 and usage["live_value_bytes"] == 0
               for usage in native["usage"].values())


def test_stopped_ingress_precedes_even_earlier_family_disagreement(directory):
    tools, journal = Toolchain(), Journal(directory)
    source, candidate = directory / "source.json", directory / "participants.json"
    authored = FIXTURES / "multi-ingress.pir"
    source.write_text(journal.run([tools.compiler, "protocol-source", authored]))
    candidate.write_text(journal.run([tools.compiler, "protocol-compile", authored]))
    journal.run([tools.checker("interactive-protocol"), "--check-generic", source, candidate])
    compiled = {"multi": (source, candidate, {
        "source_sha256": digest(source), "participants_sha256": digest(candidate)})}
    supplied = [["P", [["first", ["index", "1"]], ["later", ["index", "11"]]]],
                ["V", [["receivedFirst", ["index", "2"]], ["receivedLater", ["index", "2"]]]]]
    actual, expected = execute(compiled, "multi", supplied, directory, selected="P")
    assert actual.returncode == expected.returncode == 0
    native, reference = json.loads(actual.stdout), json.loads(expected.stdout)
    assert native["outcome"][:3] == ["stopped", "P", "ingress.rounds"]
    assert native["stop"]["detail"] == reference[3][1] == "interactive-family-bound"
    assert native["ingress"]["P"]["selected_parameters"] == {"earlier": 1}
    assert native["ingress"]["V"]["selected_parameters"] == {"earlier": 2, "rounds": 2}
    for role in ("P", "V"):
        assert [event["site"] for event in native["ingress"][role]["events"]] == ["ingress.earlier", "ingress.rounds"]
        assert native["usage"][role]["instructions"] == 2
        assert native["usage"][role]["iterations"] == 0
    assert native["cancelled_roles"] == ["V"]
    assert native["wire"]["messages"] == 0
    # Role-local ingress completes before joint agreement is checked. A stopped
    # later selector therefore takes precedence over an earlier disagreement.
    reference_inputs = directory / "joint-reference-inputs.json"
    reference_inputs.write_text(json.dumps(["zkc.reference-inputs/1", "main", "family", supplied, [], [], []]))
    joint = journal.json([tools.checker("interactive-protocol"), "--generic-reference", source, reference_inputs])
    assert joint[3][:2] == ["refused", "interactive-family-bound"]
