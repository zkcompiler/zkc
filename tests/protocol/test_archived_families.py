"""Archived typed proof/config metadata drives ordinary compact PIR selectors.

The archives, the metadata extracted from them by the pinned upstream typed
decoders, and the reconstructed verifying keys are frozen inputs under
tests/fixtures/archived-shapes/; its provenance.json names the upstream repositories
and commits. These tests need only the three zkc builds and that corpus.
"""
import copy
import json
from pathlib import Path

import pytest
import shape_data
from journal import Journal
from toolchain import Toolchain, records
from test_input_families import digest, execute

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "tests/fixtures/archived-shapes"


def archive(name):
    # The BP+ archives are the transcript corpus's own; one copy of each.
    if name.startswith(("ordinary-monero-", "instrumented-monero-")):
        return ROOT / "tests/fixtures/external-transcript" / name
    return DATA / "archives" / name


CORPUS = json.loads((DATA / "corpus.json").read_text())
BP = {r["name"]: r for r in CORPUS["monero"]}
OVM = {r["name"]: r for r in CORPUS["openvm"]}


@pytest.fixture(scope="module")
def archived_families(worker_id):
    tools = Toolchain()
    result = {}
    for name in ("bp-shape", "openvm-archived-shape"):
        directory = records(case=f"{worker_id}-{name}")
        journal = Journal(directory)
        authored = ROOT / "tests/fixtures/input-families" / f"{name}.pir"
        source, candidate = directory / "source.json", directory / "participants.json"
        source.write_text(journal.run([tools.compiler, "protocol-source", authored]))
        candidate.write_text(journal.run([tools.compiler, "protocol-compile", authored]))
        common = journal.run([tools.compiler, "protocol-import", authored])
        projected = journal.run([tools.optimizer, "--zkc-project-participants", "-"], common)
        (directory / "common.mlir").write_text(common)
        (directory / "participants.mlir").write_text(projected)
        for mlir in (common, projected):
            assert 'count = "rounds"' in mlir and 'parameter = true' in mlir
        document = json.loads(source.read_text())
        if document[0] == "zkc.library/1": document = document[3]
        assert len(document[3]) == 1
        body = document[3][0][7]
        loops = [row for row in body if row[0] == "loop"]
        assert len(loops) == 1 and loops[0][2] == ["parameter", "rounds"]
        assert len(body) == 4 and len(loops[0][5]) == 3
        assert len(json.loads(candidate.read_text())[4]) == 2
        evidence = {"source_sha256": digest(source), "participants_sha256": digest(candidate),
                    "protocol_nodes_including_loop_body": 7, "round_nodes": 3,
                    "stored_functions": len(document[2])}
        (directory / "compactness.json").write_text(json.dumps(evidence, indent=2))
        journal.run([tools.checker("interactive-protocol"), "--check-generic", source, candidate])
        result[name] = source, candidate, evidence
    return result


def supplied(name, row, other=None):
    other = row if other is None else other
    if name == "bp-shape":
        names = [("commitments", "left", "right"),
                 ("receivedCommitments", "receivedLeft", "receivedRight")]
        values = [[r[k] for k in ("commitments", "left", "right")] for r in (row, other)]
    else:
        names = [("key", "proof"), ("receivedKey", "receivedProof")]
        values = [[r["packed"][k] for k in ("key", "proof")] for r in (row, other)]
    return [[role, [[port, ["indices", list(map(str, value))]] for port, value in zip(ports, data)]]
            for role, ports, data in zip(("P", "V"), names, values)]


def check_returned(actual, expected, count):
    assert actual.returncode == expected.returncode == 0, actual.stderr + expected.stderr
    native, reference = json.loads(actual.stdout), json.loads(expected.stdout)
    assert native["outcome"] == ["returned", {"P": [["index", count]], "V": [["index", count]]}]
    assert reference[3] == ["returned", [["index", str(count)], ["index", str(count)]]]
    sends = [event for event in reference[4] if event[0] == "send"]
    assert native["wire"]["messages"] == len(sends) == count
    assert [int(event[1][4][0][2]) for event in sends] == list(range(count))
    assert all(v["selected_parameters"] == {"rounds": count} for v in native["ingress"].values())


def check_rejected(actual, expected):
    # Ingress failures use the runtime's shared outcome API.
    assert actual.returncode == expected.returncode == 0, actual.stderr + expected.stderr
    native, reference = json.loads(actual.stdout), json.loads(expected.stdout)
    assert native["outcome"][0:3] == ["stopped", "V", "ingress.rounds"], native
    assert native["stop"]["detail"] == "rejected:require", native
    assert native["wire"]["messages"] == 0
    assert native["ingress"]["V"]["selected_parameters"] == {}
    assert reference[3][:2] == ["reject", "require"], reference[3]
    assert reference[3][2][4][0] == ["local", "ingress.rounds", "Select"]
    assert reference[3][2][6] == "V"
    assert not any(event[0] == "send" for event in reference[4])


@pytest.mark.parametrize("name", BP)
def test_archived_bp_bytes(archived_families, directory, name):
    row = BP[name]
    proof = archive(f"{name}.proof").read_bytes()
    transcript = json.loads(archive(f"{name}.transcript.json").read_text())
    # Independent bounded codec crosscheck of the actual V/L/R bytes used by PIR.
    assert row["commitments"] == list(bytes.fromhex("".join(transcript["V"])))
    cursor = 192  # six fixed 32-byte fields, V excluded by the upstream codec
    for side in ("left", "right"):
        count = proof[cursor]
        assert 6 <= count <= 10
        cursor += 1
        assert row[side] == list(proof[cursor:cursor + 32 * count])
        cursor += 32 * count
    assert cursor == len(proof)
    count = len(row["commitments"]) // 32
    rounds = 6 + (count - 1).bit_length()
    check_returned(*execute(archived_families, "bp-shape", supplied("bp-shape", row), directory), rounds)


# Fixed outcomes are test expectations, never entry metadata used as selectors.
@pytest.mark.parametrize("name,slots", [("openvm-0", 2), ("openvm-1", 1), ("openvm-2", 2),
                                        ("openvm-mixture-1", 9), ("openvm-mixture-4", 12)])
def test_archived_openvm(archived_families, directory, name, slots):
    row = OVM[name]
    assert row["packed"] == shape_data.pack_openvm(row)
    check_returned(*execute(archived_families, "openvm-archived-shape",
                           supplied("openvm-archived-shape", row), directory), slots)


@pytest.mark.parametrize("bad", CORPUS["typed_mutations"], ids=lambda r: r["name"])
def test_upstream_typed_mutations(archived_families, directory, bad):
    assert bad["upstream_accepted"] is False
    assert bad["packed"] == shape_data.pack_openvm(bad)
    original = OVM[bad["original"]]
    check_rejected(*execute(archived_families, "openvm-archived-shape",
                            supplied("openvm-archived-shape", original, bad), directory))


BP_MUTATIONS = ("partial-V", "empty-V", "oversize-V", "nonbyte-V", "nonbyte-L",
                "nonbyte-R", "short-L", "long-R", "wrong-padding")


@pytest.mark.parametrize("mutation", BP_MUTATIONS)
def test_archived_bp_rejects_mutations(archived_families, directory, mutation):
    original = BP["ordinary-monero-3"]
    bad = copy.deepcopy(original)
    if mutation == "partial-V": bad["commitments"].pop()
    elif mutation == "empty-V": bad["commitments"] = []
    elif mutation == "oversize-V": bad["commitments"] = bad["commitments"][:32] * 17
    elif mutation.startswith("nonbyte-"):
        bad[{"V": "commitments", "L": "left", "R": "right"}[mutation[-1]]][0] = 256
    elif mutation == "short-L": bad["left"] = bad["left"][:-32]
    elif mutation == "long-R": bad["right"] += bad["right"][:32]
    elif mutation == "wrong-padding": bad["commitments"] = bad["commitments"][:64]
    check_rejected(*execute(archived_families, "bp-shape", supplied("bp-shape", original, bad), directory))


OPENVM_MUTATIONS = ("absence", "absent-pv", "required-absent", "presence-flag", "all-absent",
                    "height-bound", "preprocessed-height", "cached-count", "public-count",
                    "common-width", "cached-width", "preprocessed-width", "rotation",
                    "interaction-multiplicity", "interaction-zero", "gkr-layers", "gkr-inner",
                    "batch-rounds", "batch-width", "opening-count", "opening-order", "opening-parts",
                    "numerator", "denominator", "univariate", "key-tail", "proof-tail",
                    "key-count", "proof-count", "skip-cap", "degree-cap", "empty-key", "empty-proof")


@pytest.mark.parametrize("mutation", OPENVM_MUTATIONS)
def test_openvm_checks_received_metadata(archived_families, directory, mutation):
    original = OVM["openvm-mixture-1"]
    if mutation in ("absent-pv", "required-absent"):
        original = OVM["openvm-1"]
    bad = copy.deepcopy(original)
    k, p = bad["packed"]["key"], bad["packed"]["proof"]
    n = k[3]
    opening = 9 + 4 * n
    if mutation == "absence": p[9] = 0  # leaves public values/openings behind
    elif mutation == "absent-pv": p[9 + 4 + 3] = 1
    elif mutation == "required-absent": k[4 + 10] = 1
    elif mutation == "presence-flag": p[9] = 2
    elif mutation == "all-absent":
        for i in range(n): p[9 + 4*i:13 + 4*i] = [0, 0, 0, 0]
    elif mutation == "height-bound": p[10] = k[0] + k[1] + 1
    elif mutation == "preprocessed-height": p[9 + 4*5 + 1] += 1
    elif mutation == "cached-count": p[9 + 4*3 + 2] = 0
    elif mutation == "public-count": p[12] -= 1
    elif mutation == "common-width": p[opening + 2] += 1
    elif mutation == "cached-width": p[opening + 6] += 1  # AIR4 cached part
    elif mutation == "preprocessed-width":
        cursor = opening
        while p[cursor] != 5: cursor += 2 + p[cursor + 1]
        p[cursor + 3] += 1
    elif mutation == "rotation": k[4 + 2] = 0
    elif mutation == "interaction-multiplicity": k[4 + 10*6 + 3] = 1024
    elif mutation == "interaction-zero":
        for i in range(n): k[4 + 10*i + 3] = 0
    elif mutation == "gkr-layers": p[7] -= 1
    elif mutation == "gkr-inner": p[-1] -= 1
    elif mutation == "batch-rounds": p[6] += 1
    elif mutation == "batch-width": p[-len(original["proof"]["gkr_widths"]) - 1] -= 1
    elif mutation == "opening-count": p[5] -= 1
    elif mutation == "opening-order": p[opening] = p[opening + 3]
    elif mutation == "opening-parts": p[opening + 1] += 1
    elif mutation == "numerator": p[2] -= 1
    elif mutation == "denominator": p[3] -= 1
    elif mutation == "univariate": p[4] -= 1
    elif mutation == "key-tail": k.append(0)
    elif mutation == "proof-tail": p.append(0)
    elif mutation == "key-count": k[3] = 33
    elif mutation == "proof-count": p[0] -= 1
    elif mutation == "skip-cap": k[0] = 17
    elif mutation == "degree-cap": k[2] = 17
    elif mutation == "empty-key": k.clear()
    elif mutation == "empty-proof": p.clear()
    check_rejected(*execute(archived_families, "openvm-archived-shape",
                            supplied("openvm-archived-shape", original, bad), directory))


def test_different_valid_received_shapes_disagree(archived_families, directory):
    a, b = OVM["openvm-0"], OVM["openvm-1"]
    actual, expected = execute(archived_families, "openvm-archived-shape",
                               supplied("openvm-archived-shape", a, b), directory)
    assert actual.returncode == expected.returncode == 0
    assert json.loads(actual.stdout)["outcome"] == ["failed", "interactive-family-disagreement"]
    assert json.loads(expected.stdout)[3][1] == "interactive-family-disagreement"


def test_shape_provenance_and_coverage():
    provenance = json.loads((DATA / "provenance.json").read_text())
    assert provenance["corpus_sha256"] == digest(DATA / "corpus.json")
    assert set(provenance["upstreams"]) == {"monero", "stark-backend"}
    for row in list(BP.values()) + list(OVM.values()):
        assert row["upstream_accepted"]
        assert digest(archive(row["name"] + ".proof")) == row["proof_sha256"]
        if row["name"] in BP:
            assert digest(archive(row["name"] + ".transcript.json")) == row["statement_sha256"]
        else:
            assert digest(DATA / f"vk-{row['configuration']}.json") == row["vk_sha256"]
    assert len(BP) == 15 and len(OVM) == 5
    assert OVM["openvm-0"]["vk_sha256"] == OVM["openvm-1"]["vk_sha256"] == OVM["openvm-2"]["vk_sha256"]
    assert sum(t is None for r in OVM.values() for t in r["proof"]["trace"]) == 3
    for name in ("openvm-mixture-1", "openvm-mixture-4"):
        row = OVM[name]
        assert any(a["cached_widths"] for a in row["key"]["airs"])
        assert any(a["preprocessed_height"] is not None for a in row["key"]["airs"])
        assert any(a["interactions"] for a in row["key"]["airs"])
        assert any(a["need_rot"] for a in row["key"]["airs"])


@pytest.mark.parametrize("name", OVM)
def test_expected_dimensions_are_vk_derived(name):
    row = OVM[name]
    vk = json.loads((DATA / f"vk-{row['configuration']}.json").read_text())["inner"]
    assert [row["key"][k] for k in ("l_skip", "n_stack", "max_degree")] == [
        vk["params"][k] for k in ("l_skip", "n_stack", "max_constraint_degree")]
    for a, v in zip(row["key"]["airs"], vk["per_air"], strict=True):
        width = v["params"]["width"]
        pdata = v["preprocessed_data"]
        assert a == {
            "required": v["is_required"], "public_values": v["params"]["num_public_values"],
            "need_rot": v["params"]["need_rot"],
            "interactions": len(v["symbolic_constraints"]["interactions"]),
            "preprocessed_height": None if pdata is None else pdata["hypercube_dim"] + row["key"]["l_skip"],
            "common_width": width["common_main"], "preprocessed_width": width["preprocessed"],
            "cached_widths": width["cached_mains"],
        }


def test_wrong_selected_key_refuses_proof_shape(archived_families, directory):
    original = OVM["openvm-0"]
    bad = copy.deepcopy(original)
    bad["packed"]["key"] = OVM["openvm-mixture-1"]["packed"]["key"]
    check_rejected(*execute(archived_families, "openvm-archived-shape",
                            supplied("openvm-archived-shape", original, bad), directory))


def test_count_agreement_does_not_authenticate_metadata(archived_families, directory):
    a, b = OVM["openvm-0"], OVM["openvm-2"]
    assert a["packed"]["proof"] != b["packed"]["proof"]
    check_returned(*execute(archived_families, "openvm-archived-shape",
                            supplied("openvm-archived-shape", a, b), directory), 2)


@pytest.mark.parametrize("multiplicity,layers", [(7, 5), (8, 6)])
def test_interaction_power_of_two_boundary(archived_families, directory, multiplicity, layers):
    # Schema arithmetic control derived from archive metadata; these alterations
    # are not asserted to be valid upstream proofs or authenticated original VKs.
    row = copy.deepcopy(OVM["openvm-mixture-1"])
    for a in row["key"]["airs"]: a["interactions"] = 0
    row["key"]["airs"][1]["interactions"] = multiplicity  # height=2: total 28/32
    row["proof"]["gkr_layers"] = layers
    row["proof"]["gkr_widths"] = list(range(1, layers))
    row["packed"] = shape_data.pack_openvm(row)
    check_returned(*execute(archived_families, "openvm-archived-shape",
                            supplied("openvm-archived-shape", row), directory), 1 + layers)


def test_archived_fixture_frontend_roundtrip(archived_families, directory):
    tools, journal = Toolchain(), Journal(directory)
    fixture = ROOT / "tests/fixtures/input-families/openvm-archived-shape.pir"
    formatted = journal.run([tools.compiler, "protocol-format", fixture])
    assert formatted == journal.run([tools.compiler, "protocol-format", "-"], formatted)
    assert json.loads(journal.run([tools.compiler, "protocol-source", "-"], formatted)) == json.loads(
        archived_families["openvm-archived-shape"][0].read_text())
