#!/usr/bin/env python3
"""Actual /2 artifact production/validation and application authority controls.

The compiler and Lean check admission. The same proof and original source also
run through the independent interpreter, which answers its own requests from
the public primitive service.
"""
import copy
import json
from pathlib import Path

from types import SimpleNamespace

from construction import constructed_plan
from journal import Journal
from run_reference import run_reference
from toolchain import Toolchain, records

# The two Lean references this drives: one consumes the admitted source, the
# other interprets the artifact the runtime produced.
def main():
    CHECKER = "interactive-protocol"
    REFERENCE = "artifact-reference"

    # The runtime's own exporter, which writes the development fixtures this drives.
    EXPORTER = "artifact_fixture"

    a = SimpleNamespace()
    tools = Toolchain()
    a.zkc, a.compiler = tools.runtime, tools.compiler
    a.fixture_exporter = tools.example(EXPORTER)
    a.lean, a.reference = tools.checker(CHECKER), tools.checker(REFERENCE)
    a.primitive = tools.primitive
    journal = Journal(records(), timeout=120)
    out = journal.directory
    root = Path(__file__).resolve().parents[2]
    checks = []
    comparisons = []
    memo = {}

    def load(path):
        return json.loads(Path(path).read_text())

    def compile_json(*args):
        """What the compiler answered, for a step this test requires to work."""
        return journal.json([a.compiler, *args])


    def compile_case(name, source, descriptor):
        src = journal.write(name + ".source.json", source)
        desc = journal.write(name + ".descriptor.json", descriptor)
        return constructed_plan(journal, a.compiler, src, desc, name + ".")




    def run(paths, name, inputs, producer=False, code=None, budget="10000", proof=None):
        inp = journal.write(name + ".input.json", inputs)
        proof = proof or out / (name + ".proof")
        r = journal.attempt([a.zkc, "produce-artifact" if producer else "validate-artifact",
                     *paths, inp, a.compiler, a.lean, proof, budget])
        report = json.loads(r.stdout)
        journal.write(f"report-{len(checks):03d}.json", report)
        if code is None:
            assert r.returncode == 0 and report["status"] == ("produced" if producer else "accepted"), report
            assert report["runtime"]["active_frames"] == 0
        else:
            assert r.returncode == 1 and report["status"] == "refused" and report["code"] == code, report
        checks.append({"name": name, "producer": producer, "code": report["code"]})
        if a.reference and not producer and code in (None, "proof-header", "proof-trailing", "proof-truncated",
                                                    "exhausted:resource-budget", "refused:key-mismatch", "rejected:require",
                                                    "artifact-source-transcript", "artifact-unbound-verifier-input",
                                                    "artifact-verifier-resource", "artifact-public-setup",
                                                    "artifact-receive-coverage", "artifact-input-setup-coverage",
                                                    "artifact-receive-key", "artifact-input-setup-key",
                                                    "artifact-input-setup-port-or-duplicate",
                                                    "artifact-receive-site-or-duplicate"):
            reference_dir = out / f"reference-{len(checks)-1:03d}"
            ref = run_reference(a.reference, a.primitive, paths[0], paths[1], inp, proof,
                                reference_dir, memo=memo, transcript_budget=int(budget))
            if ref[0] == "refused":
                assert report["status"] == "refused" and report.get("events", []) == [], (ref, report)
                assert report["proof_bytes"] == 0, (ref, report)
            else:
                assert ref[0] == "zkc.artifact-observation/1", ref
                assert (ref[1][0] == "accepted") == (report["status"] == "accepted"), (ref[1], report)
                assert ref[2] == report["events"], (name, len(checks)-1, "events", ref[1])
                assert int(ref[4]) == report["proof_bytes"], (name, ref[4], report["proof_bytes"])
                assert int(ref[5]) == sum(e[0] == "challenge" for e in report["events"])
                assert int(ref[6]) == sum(e[0] in ("message", "challenge") for e in report["events"])
            comparisons.append({"check": len(checks)-1, "name": name, "reference": ref[1], "native": report["code"]})
        return report


    def nominal(kind):
        if kind == "bool":
            return kind
        domain = "bls12-381.g1" if kind in ("group", "groups") else (
            "multilinear.kzg.bls12-381/1" if kind in ("commitment", "proof", "verifier_key", "prover_key") else "bls12-381.fr")
        return kind + ":" + domain


    def input2(value, selections=(), receives=()):
        value = copy.deepcopy(value)
        assert value[0] == "zkc.artifact-inputs/1"
        assert value[4][0] == "zkc.public-configuration/1"
        value[4][2:] = [list(selections), list(receives)]
        return value


    def receive_sites(physical, key="vk"):
        def walk(body):
            for op in body:
                if op[0] == "receive" and op[5].split(":")[0] in ("proof", "commitment"):
                    yield op[1]
                if op[0] == "loop":
                    yield from walk(op[5])
        return [[participant[2], participant[3], site, key]
                for participant in physical[4] for site in walk(participant[7])]


    assert journal.attempt([a.fixture_exporter, out]).returncode == 0
    sources = {}
    descriptors = {}
    inputs = {}
    for name in ("dleq", "committed-two-factor"):
        source = compile_json("protocol-source", root / "tests/fixtures" / ("generic-" + name + ".pir"))
        descriptor = load(root / "examples/protocols" / (name + ".construction.json")) if (
            root / "examples/protocols" / (name + ".construction.json")).exists() else compile_json(
                "protocol-source", root / "examples/protocols" / (name + ".construction.pir"))
        # These checks are about exact artifacts: the receive configuration is
        # read from the constructed program's sites, and an unused declaration
        # must change the whole-source root. The normalized host path, which
        # takes the author's receive names, is covered by the identity tests.
        descriptor[8] = "exact"
        paths = compile_case(name, source, descriptor)
        selections = [] if name == "dleq" else [["V", "expected_f", "vk"], ["V", "expected_g", "vk"]]
        receives = receive_sites(load(paths[3]))
        prod, val = [input2(load(out / (name + "." + role + ".json")), selections, receives)
                     for role in ("producer", "validator")]
        proof = out / (name + ".proof")
        journal.write(name + ".honest-producer.json", prod)
        journal.write(name + ".honest-validator.json", val)
        produced = run(paths, name, prod, True)
        accepted = run(paths, name, val)
        assert produced["binding_sha256"] == accepted["binding_sha256"]
        assert produced["events"] == []
        requests = [e[1][4] for e in accepted["events"] if e[0] == "request"]
        assert all(e[1][0] == "zkc.logical-origin/2" for e in accepted["events"] if e[0] == "request")
        if name == "dleq":
            assert any(e[3] == "DLEQDraw" and e[6] == "random.draw" and e[7] == ["bls12-381.fr"] for e in requests)
        old_proof = proof.read_bytes()
        run(paths, name, prod, True, "exhausted:resource-budget", budget="0")
        assert proof.read_bytes() == old_proof
        run(paths, name, val, code="exhausted:resource-budget", budget="0")
        changed = copy.deepcopy(val)
        changed[1] = "01"
        run(paths, name, changed, code="proof-header")
        changed = copy.deepcopy(val)
        changed[2][0][1] = changed[2][0][1].split(":")[0]
        run(paths, name, changed, code="artifact-public-type")
        changed = copy.deepcopy(val)
        changed[0] = "zkc.artifact-inputs/2"
        run(paths, name, changed, code="artifact-input-version")
        for label, candidate, code in (("short", old_proof[:-1], "proof-truncated"),
                                        ("trailing", old_proof + b"x", "proof-trailing")):
            bad = out / (label + ".proof")
            bad.write_bytes(candidate)
            run(paths, name, val, code=code, proof=bad)
        bad = bytearray(old_proof)
        if name == "dleq":
            cursor, last = 40, None
            while cursor < len(bad):
                size = int.from_bytes(bad[cursor:cursor+8], "little")
                last = (cursor+8, size)
                cursor += 8+size
            assert last[1] == 38
            current = int.from_bytes(bad[last[0]+6:last[0]+38], "little")
            bad[last[0]+6:last[0]+38] = (0 if current else 1).to_bytes(32, "little")
        else:
            size = int.from_bytes(bad[40:48], "little")
            second = 48+size
            assert int.from_bytes(bad[second:second+8], "little") == size
            bad[48:48+size] = bad[second+8:second+8+size]
        candidate = out / (name + "-false-equation.proof")
        candidate.write_bytes(bad)
        run(paths, name, val, code="rejected:require", proof=candidate)
        if receives:
            changed = copy.deepcopy(val)
            changed[4][3].pop()
            run(paths, name, changed, code="artifact-receive-coverage")
            changed = copy.deepcopy(val)
            changed[4][2].pop()
            run(paths, name, changed, code="artifact-input-setup-coverage")
            changed = copy.deepcopy(val)
            changed[4][3][0][3] = "unregistered"
            run(paths, name, changed, code="artifact-receive-key")
        # An unused declaration is part of the exact policy's whole-source
        # root, so the old proof no longer matches.
        changed_source = copy.deepcopy(source)
        changed_source[1].append(["generic_function", "Unused", [], [], [], [], [["return", []]]])
        changed_paths = compile_case(name + "-unused", changed_source, descriptor)
        run(changed_paths, name, val, code="proof-header")
        if receives:
            changed = copy.deepcopy(val)
            changed[4][2][0][2] = "unregistered"
            run(paths, name, changed, code="artifact-input-setup-key")
            changed = copy.deepcopy(val)
            changed[3].append(copy.deepcopy(changed[4][1][0]))
            run(paths, name, changed)
            changed[3][-1][2] = changed[3][-1][2][:-2] + "00"
            run(paths, name, changed, code="artifact-configuration-equality")
            changed[3][-1][1] = "verifier_key"
            run(paths, name, changed, code="artifact-input-type")
        sources[name], descriptors[name], inputs[name] = source, descriptor, (prod, val)

    # Artifact profile admission covers the full library, including undemanded
    # signatures; constructor success alone does not grant public-verifier scope.
    for label, kind, code in (("unbound-verifier", nominal("field"), "artifact-unbound-verifier-input"),
                               ("private-verifier", nominal("nonce"), "artifact-verifier-resource")):
        source = copy.deepcopy(sources["dleq"])
        root_binding = source[3][5][0][2]
        root_protocol = next(i[2] for i in source[3][4] if i[1] == root_binding)
        next(p for p in source[3][3] if p[1] == root_protocol)[4].append(["extra", "V", kind])
        paths = compile_case(label, source, descriptors["dleq"])
        run(paths, label, inputs["dleq"][1], code=code, proof=out / "dleq.proof")
    source = copy.deepcopy(sources["dleq"])
    source[1].append(["generic_function", "UnusedTranscript", [["T", "Transcript"]], [],
                      [["t", "transcript:T"]], ["transcript:T"], [["return", ["t"]]]])
    paths = compile_case("unused-transcript", source, descriptors["dleq"])
    run(paths, "unused-transcript", inputs["dleq"][1], code="artifact-source-transcript", proof=out / "dleq.proof")

    # Configuration aliases survive all the way to original-source observations.
    source = copy.deepcopy(sources["dleq"])
    source[2].append(["configure", "DrawAlias", "DLEQDraw", [], []])
    for protocol in source[3][3]:
        def alias(body):
            for op in body:
                if op[0] == "local" and op[3] == "DLEQDraw": op[3] = "DrawAlias"
                if op[0] == "loop": alias(op[5])
        alias(protocol[7])
    descriptor = copy.deepcopy(descriptors["dleq"])
    descriptor[5][1] = [["DrawAlias" if name == "DLEQDraw" else name, site] for name, site in descriptor[5][1]]
    paths = compile_case("aliased-dleq", source, descriptor)
    prod, val = inputs["dleq"]
    run(paths, "aliased-dleq", prod, True)
    report = run(paths, "aliased-dleq", val)
    assert any(e[0] == "request" and e[1][4][3] == "DrawAlias" for e in report["events"])

    # Candidate local symbol renaming must use the checked call map, not a name
    # preservation assumption in the logical observer.
    physical = load(paths[3])
    renames = {f[1]: "physical_function_" + str(i) for i, f in enumerate(physical[3])}
    for function in physical[3]: function[1] = renames[function[1]]
    for participant in physical[4]:
        def rename(body):
            for op in body:
                if op[0] == "local": op[2] = renames[op[2]]
                if op[0] == "loop": rename(op[5])
        rename(participant[7])
    renamed_paths = paths[:3] + [journal.write("renamed-local.physical.json", physical)]
    renamed = run(renamed_paths, "renamed-local", val, proof=out / "aliased-dleq.proof")
    assert renamed["events"] == report["events"]

    # The definition selects the alias, its one materialized configuration, in
    # the constructor and in the independent interpreter alike.
    by_definition = copy.deepcopy(descriptor)
    by_definition[5][1] = [["DLEQDrawAlgorithm" if name == "DrawAlias" else name, site]
                           for name, site in by_definition[5][1]]
    definition_paths = compile_case("definition-dleq", source, by_definition)
    run(definition_paths, "definition-dleq", prod, True)
    selected = run(definition_paths, "definition-dleq", val)
    assert any(e[0] == "request" and e[1][4][3] == "DrawAlias" for e in selected["events"])

    # A nested opening receive exists only under an exact zero-trip loop. Setup
    # policy names original executable coordinates, never generated inactive names.
    source = copy.deepcopy(sources["committed-two-factor"])
    source[1].append(["generic_function", "AcceptAlgorithm", [["F", "Field"]], [["Field", ["F"]]], [], ["bool"], [
        ["op", "zero", "field.constant", ["F"], ["0"], [], ["zero"]],
        ["op", "same", "field.equal", ["F"], [], ["zero", "zero"], ["yes"]], ["return", ["yes"]]]])
    source[2].append(["configure", "Accept", "AcceptAlgorithm", [["F", "bls12-381.fr"]], []])
    commitment = nominal("commitment")
    source[3][3] = [
        ["protocol", "Leaf", ["P", "V"], [], [["payload", "P", commitment]], [["V", commitment]], [], [
            ["message", "commitment", "commitment", "P", "V", "payload", "received"], ["return", ["received"]]]],
        ["protocol", "Outer", ["P", "V"], ["n"], [["payload", "P", commitment], ["vk", "V", nominal("verifier_key")],
            ["coins", "V", nominal("rng")]], [["V", "bool"], ["V", nominal("rng")]], [["child", "Leaf", []]], [
            ["loop", "skipped", ["parameter", "n"], [], ["payload"], [["call", "nested", "child", ["payload"], ["ignored"]], ["yield", []]], []],
            ["local", "accept", "V", "Accept", [], ["yes"]], ["return", ["yes", "coins"]]]]]
    source[3][4] = [["instance", "leaf", "Leaf", [], [], [["P", "P"], ["V", "V"]]],
                      ["instance", "outer", "Outer", [["n", "0"]], [["child", "leaf"]], [["P", "P"], ["V", "V"]]]]
    source[3][5] = [["entry", "main", "outer"]]
    descriptor = ["zkc.construction/1", "main", "P", "V", [["payload", [["P", "payload"]]]], ["coins", []], "0", "merlin3.bls12-381.fr64be/1", "exact"]
    paths = compile_case("zero-trip-receive", source, descriptor)
    material = inputs["committed-two-factor"][1]
    wire = next(row[2] for row in material[2] if row[1] == commitment)
    config = ["zkc.public-configuration/1", material[4][1], [["P", "payload", "vk"]], []]
    value = ["zkc.artifact-inputs/1", "", [["payload", commitment, wire]], [], config]
    run(paths, "zero-trip-receive", value, True)
    report = run(paths, "zero-trip-receive", value)
    assert report["messages"] == 0
    inactive = receive_sites(load(paths[3]))
    assert inactive and inactive[0][0] != "leaf"
    wrong = copy.deepcopy(value)
    wrong[4][3] = inactive
    run(paths, "zero-trip-receive", wrong, code="artifact-receive-site-or-duplicate")

    # Two different authorized setups, shared generic definitions and distinct
    # subprotocol instances. The selected RNG is threaded from the first into the
    # second invocation, rather than issuing another public challenge source.
    name = "two-setups"
    source = copy.deepcopy(sources["committed-two-factor"])
    common = source[3]
    original = next(p for p in common[3] if p[1] == "CommittedTwoFactorArgument")
    source[1].append(["generic_function", "Conjoin", [], [], [["a", "bool"], ["b", "bool"]], ["bool"],
                      [["op", "and", "bool.and", [], [], ["a", "b"], ["both"]], ["return", ["both"]]]])
    source[2].append(["configure", "Both", "Conjoin", [], []])
    ports = []
    for prefix in ("first", "second"):
        ports.extend([[prefix + "_" + n, role, ty] for n, role, ty in original[4] if n != "coins"])
    ports.append(["coins", "V", "rng:bls12-381.fr"])
    def arguments(prefix, coins):
        return [coins if n == "coins" else prefix + "_" + n for n, _, _ in original[4]]
    body = [["call", "first", "first", arguments("first", "coins"), ["first_ok", "after_first"]],
            ["call", "second", "second", arguments("second", "after_first"), ["second_ok", "after_second"]],
            ["local", "both", "V", "Both", ["first_ok", "second_ok"], ["accepted"]],
            ["return", ["accepted", "after_second"]]]
    common[3].append(["protocol", "Pair", ["P", "V"], ["n"], ports,
                      [["V", "bool"], ["V", "rng:bls12-381.fr"]],
                      [[prefix, "CommittedTwoFactorArgument", [["n", "n"]]] for prefix in ("first", "second")], body])
    old_instances = common[4]
    common[4] = []
    for prefix in ("first", "second"):
        for instance in old_instances:
            instance = copy.deepcopy(instance)
            instance[1] = prefix + "_" + instance[1]
            instance[4] = [[dep, prefix + "_" + target] for dep, target in instance[4]]
            common[4].append(instance)
    common[4].append(["instance", "pair", "Pair", [["n", "3"]],
                      [[prefix, prefix + "_interactive"] for prefix in ("first", "second")], [["P", "P"], ["V", "V"]]])
    common[5] = [["entry", "main", "pair"]]
    descriptor = copy.deepcopy(descriptors["committed-two-factor"])
    descriptor[4] = [[prefix + "_" + label, [[role, prefix + "_" + port] for role, port in targets]]
                     for prefix in ("first", "second") for label, targets in descriptor[4]]
    paths = compile_case(name, source, descriptor)
    other_dir = out / "second-setup"
    assert journal.attempt([a.fixture_exporter, other_dir]).returncode == 0
    prod, val = [copy.deepcopy(inputs["committed-two-factor"][i]) for i in range(2)]
    for i, role in enumerate(("producer", "validator")):
        combined = prod if i == 0 else val
        combined[2], combined[3] = [], []
        key_records = []
        for prefix, directory in (("first", out), ("second", other_dir)):
            part = input2(load(directory / ("committed-two-factor." + role + ".json")))
            for record in part[2]:
                record[0] = prefix + "_" + record[0]
            for record in part[3]:
                record[0] = prefix + "_" + record[0]
                if record[1] == "prover_key_file":
                    record[4] = prefix + "_" + record[4]
            combined[2].extend(part[2])
            combined[3].extend(part[3])
            key_records.extend([[prefix + "_" + row[0], *row[1:]] for row in part[4][1]])
        selections = [["V", prefix + "_expected_" + factor, prefix + "_vk"]
                      for prefix in ("first", "second") for factor in ("f", "g")]
        receives = receive_sites(load(paths[3]))
        for record in receives:
            record[3] = record[0].split("_", 1)[0] + "_vk"
        combined[4] = ["zkc.public-configuration/1", key_records, selections, receives]
    assert prod[4][1][0][2] != prod[4][1][1][2]
    journal.write(name + ".honest-producer.json", prod)
    journal.write(name + ".honest-validator.json", val)
    produced = run(paths, name, prod, True)
    accepted = run(paths, name, val)
    assert produced["binding_sha256"] == accepted["binding_sha256"]
    assert accepted["messages"] == 18
    # A selection changed in only the verifier changes the application root.
    wrong = copy.deepcopy(val)
    wrong[4][3][0][3] = "second_vk"
    run(paths, name, wrong, code="proof-header")
    # Even when producer and validator bind the same wrong choice, the payload may
    # not pick its own authorized key. Production succeeds; decoding rejects it.
    wrong_prod = copy.deepcopy(prod)
    wrong_prod[4] = wrong[4]
    wrong_proof = out / "wrong-selection.proof"
    run(paths, name, wrong_prod, True, proof=wrong_proof)
    run(paths, name, wrong, code="refused:key-mismatch", proof=wrong_proof)
    wrong = copy.deepcopy(val)
    wrong[4][2][0][2] = "second_vk"
    run(paths, name, wrong, code="refused:key-mismatch")
    wrong = copy.deepcopy(prod)
    wrong[3][0][4] = "second_vk"
    run(paths, name, wrong, True, code="key-mismatch")
    # One public equality label cannot authorize different setups at its targets.
    shared_descriptor = copy.deepcopy(descriptor)
    shared = [b for b in shared_descriptor[4] if any(port.endswith("_expected_f") for _, port in b[1])]
    assert len(shared) == 2, shared_descriptor[4]
    shared[0][1].extend(shared[1][1])
    shared_descriptor[4].remove(shared[1])
    shared_paths = compile_case("mixed-public-setups", source, shared_descriptor)
    shared_inputs = copy.deepcopy(val)
    shared_inputs[2] = [r for r in shared_inputs[2] if r[0] != shared[1][0]]
    run(shared_paths, "mixed-public-setups", shared_inputs, code="artifact-public-setup", proof=out / "two-setups.proof")

    # Duplicate policy rows are refused, including otherwise byte-identical choices.
    for column, code in ((2, "artifact-input-setup-port-or-duplicate"), (3, "artifact-receive-site-or-duplicate")):
        wrong = copy.deepcopy(val)
        wrong[4][column].append(copy.deepcopy(wrong[4][column][0]))
        run(paths, name, wrong, code=code)


    journal.write("checks.json", checks)
    journal.write("comparisons.json", comparisons)
    print(json.dumps({"status": "passed", "checks": len(checks), "comparisons": len(comparisons)}))



def test_artifact_explicit():
    main()


if __name__ == "__main__":
    main()
