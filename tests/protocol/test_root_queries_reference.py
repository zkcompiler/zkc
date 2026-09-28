"""Independent checking preserves semantic roots and ordered query occurrences."""

import copy
import json
from pathlib import Path

import pytest

from journal import Journal


@pytest.fixture
def root_subject():
    return json.loads((Path(__file__).resolve().parents[1] /
                       "fixtures/mathematical/root-queries.json").read_text())


def projected(toolchain, directory, source):
    return json.loads(Journal(directory).run(
        [toolchain.compiler, "protocol-project", "-"], json.dumps(source)))


def checked(toolchain, directory, source, candidate, error=None):
    journal = Journal(directory)
    source_path = journal.write("source.json", source)
    candidate_path = journal.write("candidate.json", candidate)
    return json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check", source_path, candidate_path,
    ], refuses=error))


@pytest.mark.parametrize("library", [False, True])
def test_root_projection_correspondence(toolchain, directory, root_subject, library):
    if library:
        root_subject = ["zkc.library/1", [], [], root_subject]
    candidate = projected(toolchain, directory, root_subject)
    assert checked(toolchain, directory, root_subject, candidate)[:2] == [
        "checked", "generic-structural-correspondence"]


def test_independent_unreachable_root_instance(toolchain, directory, root_subject):
    candidate = projected(toolchain, directory, root_subject)
    definition = copy.deepcopy(root_subject[3][0])
    definition[1] = "Unreachable"
    root_subject[3].append(definition)
    instance = copy.deepcopy(root_subject[4][0])
    instance[1:3] = ["unused", "Unreachable"]
    root_subject[4].append(instance)
    code = "interactive-roots-unreachable-instance"
    assert checked(toolchain, directory, root_subject, candidate, code) == ["refused", code]


@pytest.mark.parametrize("mutation", ["identity", "service", "owners", "query_root", "merge", "guard", "drop_roots"])
def test_root_candidate_tampering(toolchain, directory, root_subject, mutation):
    candidate = projected(toolchain, directory, root_subject)
    prover = next(p for p in candidate[4] if p[3] == "Prover")[7]
    if mutation == "identity":
        candidate[6][0][1] = "replacement"
    elif mutation == "service":
        # Still a well-formed entropy contract, but changes the reply domain.
        candidate[1][0][1] = "random.draw_nonzero"
    elif mutation == "owners":
        candidate[6][0][3].append("Verifier")
    elif mutation == "query_root":
        prover[1][2] = "challenge"
    elif mutation == "merge":
        prover.pop(1)
        prover[-1][1] = [prover[0][4][0], prover[0][4][0]]
    elif mutation == "guard":
        next(p for p in candidate[4] if p[3] == "Verifier")[7].pop(1)
    else:
        candidate.pop()
    assert checked(toolchain, directory, root_subject, candidate, True)[0] == "refused"


@pytest.mark.parametrize("mutation,code", [
    ("permission", "interactive-query-permission"),
    ("service", "entropy-service-contract"),
    ("guard", "interactive-guard-condition"),
    ("input", "interactive-query-signature"),
    ("roles", "interactive-roots-role-binding"),
    ("rng", "interactive-root-affine-mixing"),
    ("empty", "interactive-empty-roots"),
])
def test_independent_root_admission(toolchain, directory, root_subject, mutation, code):
    candidate = projected(toolchain, directory, root_subject)
    bad = copy.deepcopy(root_subject)
    body = bad[3][0][7]
    if mutation == "permission":
        body[0][2] = "Verifier"
    elif mutation == "service":
        bad[1][0][1] = "field.add"
    elif mutation == "guard":
        body[3][3] = "c"
    elif mutation == "input":
        body[0][4] = ["accept"]
    elif mutation == "roles":
        bad[4][0][5][0][1] = "Other"
    elif mutation == "rng":
        bad[3][0][4][0][2] = "rng:bls12-381.fr"
    else:
        bad[6] = []
    assert checked(toolchain, directory, bad, candidate, code) == ["refused", code]


def physical(toolchain, journal, source):
    path = journal.write("source.json", source)
    return path, json.loads(journal.run([toolchain.compiler, "protocol-compile", path]))


def native_inputs(accepted=True, nonce_budget="2"):
    return ["zkc.run/2", "main", "session", [],
            [["Prover", [], [], []],
             ["Verifier", [], [["accept", ["bool", accepted]]], []]], [],
            [["Prover", "nonce", nonce_budget], ["Verifier", "challenge", "1"]]]


def native(toolchain, journal, source, candidate, inputs, error=None):
    return json.loads(journal.run([
        toolchain.runtime, "run-protocol", source,
        journal.write("candidate.json", candidate), journal.write("inputs.json", inputs),
        toolchain.checker("interactive-protocol"),
    ], refuses=error))


@pytest.mark.parametrize("unused,library", [(False, False), (True, False), (False, True)])
def test_root_realization_checks_actual_state_chains(toolchain, directory, root_subject, unused, library):
    if unused:
        root_subject[6].insert(0, ["root", "unused", "nonce_draw", ["Prover"]])
    if library:
        root_subject = ["zkc.library/1", [], [], root_subject]
    journal = Journal(directory)
    source, candidate = physical(toolchain, journal, root_subject)
    assert len(candidate) == 6
    assert len(candidate[3]) == 2
    assert all(i[0] != "query" for p in candidate[4] for i in p[7])
    result = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check-generic", source,
        journal.write("candidate.json", candidate),
    ]))
    assert [r[2] for r in result[5]] == ["nonce", "challenge"]
    assert [r[-1] for r in result[5]] == ["2", "1"]
    # Repeated queries share the actual helper but retain distinct sites.
    assert result[3][0][2] != result[3][1][2]
    assert result[3][0][3:] == result[3][1][3:]
    report = native(toolchain, journal, source, candidate, native_inputs())
    assert report["outcome"][0] == "returned"
    assert len(report["outcome"][1]["Prover"]) == 2
    assert len(report["outcome"][1]["Verifier"]) == 1
    assert report["root_resources"] == [
        ["Prover", "nonce", 2, 2, 0, "rng"], ["Verifier", "challenge", 1, 1, 0, "rng"]]


@pytest.mark.parametrize("mutation", ["helper", "replayed_state", "reply", "drop_query", "drop_guard", "root_service"])
def test_independent_realization_tampering(toolchain, directory, root_subject, mutation):
    journal = Journal(directory)
    _, candidate = physical(toolchain, journal, root_subject)
    prover = next(p for p in candidate[4] if p[3] == "Prover")
    verifier = next(p for p in candidate[4] if p[3] == "Verifier")
    if mutation == "helper":
        candidate[3][0][4][0][1] = "unrelated_draw"
    elif mutation == "replayed_state":
        prover[7][1][3] = prover[7][0][3]
    elif mutation == "reply":
        prover[7][-1][1][1] = prover[7][-1][1][0]
    elif mutation == "drop_query":
        prover[7].pop(1)
        prover[7][-1][1] = [prover[7][0][4][0]] * 2 + [prover[7][0][4][1]]
    elif mutation == "drop_guard":
        verifier[7].pop(1)
    else:
        root_subject[6][0][2] = "challenge_draw"
    assert checked(toolchain, directory, root_subject, candidate, True)[0] == "refused"


@pytest.mark.parametrize("mutation,code", [("shared", "interactive-root-realization-owners"),
                                          ("loop", "interactive-root-realization-control")])
def test_realization_profile_refusal(toolchain, directory, root_subject, mutation, code):
    journal = Journal(directory)
    _, candidate = physical(toolchain, journal, root_subject)
    if mutation == "shared":
        root_subject[6][0][3].append("Verifier")
    else:
        root_subject[3][0][7].insert(0, ["loop", "repeat", ["constant", "0"], [], [], [["yield", []]], []])
    journal.run([toolchain.compiler, "protocol-compile", "-"], json.dumps(root_subject), refuses=code)
    assert checked(toolchain, directory, root_subject, candidate, code) == ["refused", code]


@pytest.mark.parametrize("mutation,code", [("missing", "host-root-set"), ("wrong_owner", "host-root-set"),
                                          ("duplicate", "host-duplicate-root"), ("alias", "input-host-handle")])
def test_native_root_issuance_is_separate_from_values(toolchain, directory, root_subject, mutation, code):
    journal = Journal(directory)
    source, candidate = physical(toolchain, journal, root_subject)
    inputs = native_inputs()
    if mutation == "missing":
        inputs[6].pop()
    elif mutation == "wrong_owner":
        inputs[6][0][0] = "Verifier"
    elif mutation == "duplicate":
        inputs[6].append(inputs[6][0])
    else:
        inputs[4][1][2][0][1] = ["host", "challenge"]
    native(toolchain, journal, source, candidate, inputs, code)


def test_guard_stops_before_peer_randomness(toolchain, directory, root_subject):
    body = root_subject[3][0][7]
    body.insert(1, body.pop(3))  # nonce_first, guard, nonce_second, challenge
    journal = Journal(directory)
    source, candidate = physical(toolchain, journal, root_subject)
    result = native(toolchain, journal, source, candidate, native_inputs(False))
    assert result["outcome"] == ["stopped", "Verifier", "verification", 'Explicit("reject")']
    assert result["root_resources"] == [
        ["Prover", "nonce", 1, 1, 1, "rng"], ["Verifier", "challenge", 0, 0, 1, "rng"]]


def test_native_failed_draw_retains_consumed_prefix(toolchain, directory, root_subject):
    journal = Journal(directory)
    source, candidate = physical(toolchain, journal, root_subject)
    result = native(toolchain, journal, source, candidate, native_inputs(nonce_budget="1"))
    assert result["outcome"][:3] == ["stopped", "Prover", "nonce_second"]
    assert result["root_resources"] == [
        ["Prover", "nonce", 2, 2, 0, "rng"], ["Verifier", "challenge", 0, 0, 1, "rng"]]


@pytest.mark.parametrize("swap", ["inputs", "results"])
def test_same_owner_roots_follow_table_order_not_query_order(toolchain, directory, root_subject, swap):
    root_subject[6].insert(0, ["root", "second", "nonce_draw", ["Prover"]])
    root_subject[3][0][7][1][3] = "second"
    journal = Journal(directory)
    source, candidate = physical(toolchain, journal, root_subject)
    inputs = native_inputs(nonce_budget="1")
    inputs[6].append(["Prover", "second", "1"])
    result = native(toolchain, journal, source, candidate, inputs)
    assert result["outcome"][0] == "returned"
    assert result["root_resources"] == [
        ["Prover", "nonce", 1, 1, 0, "rng"], ["Prover", "second", 1, 1, 0, "rng"],
        ["Verifier", "challenge", 1, 1, 0, "rng"]]
    # Both states have exactly the same nominal type. Swapping the returned
    # states is well typed but loses semantic root identity.
    prover = next(p for p in candidate[4] if p[3] == "Prover")
    if swap == "results":
        prover[7][-1][1][-2:] = reversed(prover[7][-1][1][-2:])
    else:
        prover[7][0][3], prover[7][1][3] = prover[7][1][3], prover[7][0][3]
    assert checked(toolchain, directory, root_subject, candidate, True)[0] == "refused"


def test_all_roots_unused_have_no_issuance_or_state_interface(toolchain, directory, root_subject):
    protocol = root_subject[3][0]
    protocol[5] = [["Verifier", "bool"]]
    protocol[7] = [["guard", "verification", "Verifier", "accept"], ["return", ["accept"]]]
    journal = Journal(directory)
    source, candidate = physical(toolchain, journal, root_subject)
    assert candidate[3] == []
    inputs = native_inputs()[:6]
    result = native(toolchain, journal, source, candidate, inputs)
    assert result["outcome"] == ["returned", {"Prover": [], "Verifier": [["bool", True]]}]
    assert result["root_resources"] == []
    reference = reference_inputs()
    reference[8] = []
    result = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--generic-reference", source,
        journal.write("reference.json", reference),
    ]))
    assert result[3] == ["returned", [["bool", "true"]]]
    assert result[5] == []
    native(toolchain, journal, source, candidate, native_inputs(), "host-root-set")


def test_source_stop_has_no_returned_root_successor(toolchain, directory, root_subject):
    root_subject[3][0][7][-1] = ["stop", "end", "Prover", "reject"]
    journal = Journal(directory)
    source, candidate = physical(toolchain, journal, root_subject)
    result = native(toolchain, journal, source, candidate, native_inputs())
    assert result["outcome"] == ["stopped", "Prover", "end", 'Explicit("reject")']
    assert result["root_resources"] == [
        ["Prover", "nonce", 2, 2, 0, "rng"], ["Verifier", "challenge", 1, 1, 0, "rng"]]


def reference_inputs(accepted="true", nonce_tape=None, challenge_tape=None):
    return ["zkc.reference-inputs/1", "main", "session",
            [["Prover", []], ["Verifier", [["accept", ["bool", accepted]]]]], [], [], [], [],
            [["nonce", "2", ["7", "7"] if nonce_tape is None else nonce_tape],
             ["challenge", "1", ["0", "5"] if challenge_tape is None else challenge_tape]]]


@pytest.mark.parametrize("failure", [None, "guard", "nonce", "budget", "challenge"])
def test_reference_queries_use_actual_root_state(toolchain, directory, root_subject, failure):
    journal = Journal(directory)
    inputs = reference_inputs()
    if failure == "guard":
        body = root_subject[3][0][7]
        body.insert(1, body.pop(3))
        inputs[3][1][1][0][1][1] = "false"
    elif failure == "nonce":
        inputs[8][0][2] = ["7"]
    elif failure == "budget":
        inputs[8][0][1] = "1"
    elif failure == "challenge":
        inputs[8][1][2] = ["0"] * 128
    source = journal.write("source.json", root_subject)
    result = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--generic-reference", source,
        journal.write("inputs.json", inputs),
    ]))
    if failure is None:
        assert result[3] == ["returned", [["field:bls12-381.fr", "7"],
                                         ["field:bls12-381.fr", "7"],
                                         ["nonzero_field:bls12-381.fr", "5"]]]
        assert [e[2] for e in result[4] if e[0] == "query"] == ["nonce", "nonce", "challenge"]
    else:
        detail = {"guard": "source-guard", "nonce": "test-tape", "budget": "resource-budget",
                  "challenge": "sampling-limit"}[failure]
        assert result[3][1] == detail
    states = {r[0]: r[3:6] for r in result[5]}
    assert states["@root_0"] == (["1", "1", "1"] if failure == "guard" else ["2", "2", "0"])
    assert states["@root_1"] == (["0", "0", "1"] if failure in ("guard", "nonce", "budget") else ["1", "1", "0"])
