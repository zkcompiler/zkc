"""Bounded native contract observations across C++, Rust admission and backends.

Consumers independently admit their installed types and signatures. Declaration
terms supply expected closed spellings, never a reader's installation facts.
These checks do not execute kernels or establish semantic/security laws.
"""
import json
import subprocess
from copy import deepcopy
from hashlib import sha256

import pytest
from toolchain import ROOT
import contract_inventory as INVENTORY

FIXTURES = ROOT / "tests/fixtures/contracts"


def covered(counts):
    return all(count > 0 for count in counts.values())


def run(command, data=None):
    result = subprocess.run(command, input=data, capture_output=True, timeout=60, check=False)
    assert result.returncode == 0, (command, result.returncode, result.stderr.decode(errors="replace"))
    return result.stdout


@pytest.fixture(scope="module")
def inventory(toolchain):
    declarations = json.loads(run([
        toolchain.tool("compiler", "zkc-tblgen"), "--dump-contract-declarations",
        "-I", ROOT / "compiler/include", ROOT / "compiler/include/zkc/Contracts/Declarations.td"]))
    assert declarations["format"] == "zkc.contract-declarations/0"
    operation_fields = {"name", "scope", "stage", "commonGeneric", "parameters",
                        "inputs", "outputs", "requirements", "facets"}
    for operation in declarations["operations"]:
        assert operation_fields <= operation.keys()
        assert operation.keys() <= operation_fields | {"derivedCounterpart"}
    catalog = json.loads(run([toolchain.tool("compiler", "test/zkc-contract_inventory-test")]))
    assert catalog["profile"] == "zkc.contract-catalog"
    profile = json.loads((FIXTURES / "coverage.json").read_text())
    INVENTORY.dispositions(profile, declarations)
    return declarations, catalog, profile


@pytest.fixture(scope="module")
def drivers(toolchain):
    return {
        "cpp": toolchain.tool("compiler", "test/zkc-contract_conformance-test"),
        "rust": toolchain.example("contract_conformance"),
    }


@pytest.fixture(scope="module")
def physical_drivers(toolchain, drivers):
    return {**drivers, "backend": toolchain.example("backend_contract_conformance")}


def query(drivers, requests, directory, *, arguments=None):
    """One bounded batch per consumer, preserving complete disagreement evidence."""
    directory.mkdir(parents=True, exist_ok=True)
    wire = b"".join((request if isinstance(request, bytes) else
                     json.dumps(request, separators=(",", ":")).encode()) + b"\n"
                    for request in requests)
    (directory / "requests.jsonl").write_bytes(wire)
    results = {}
    for name, executable in drivers.items():
        output = run([executable, *(arguments or {}).get(name, ())], wire)
        (directory / f"{name}.jsonl").write_bytes(output)
        rows = [json.loads(line) for line in output.splitlines()]
        assert len(rows) == len(requests), (name, len(rows), len(requests))
        for row in rows:
            assert type(row.get("accepted")) is bool, (name, row)
            if not row["accepted"]:
                assert row == {"accepted": False}, (name, row)
        results[name] = rows
    return results


def agreements(results, requests):
    failures = []
    for i, request in enumerate(requests):
        active = [rows[i] for rows in results.values()]
        if any(row != active[0] for row in active):
            failures.append({"request": request,
                             "replies": {name: rows[i] for name, rows in results.items()}})
    return failures


def finish(directory, failures):
    (directory / "disagreements.json").write_text(json.dumps(failures, indent=2) + "\n")
    assert not failures, f"{len(failures)} disagreements; {directory / 'disagreements.json'}; {failures[:3]}"


def binding(contract, arguments=(), implementation="", physical=False):
    return {"contract": contract, "arguments": list(arguments),
            "implementation": implementation, "physical": physical}


def required_atomic_types():
    # Independent coverage floor for installed atomic types. Additional types
    # are exercised from the complete catalog below.
    families = {
        "": "bool index indices",
        "bls12-381.fr": "field vector polynomial round matrix table point rng nonce",
        "ristretto255.scalar": "field vector polynomial round matrix rng nonce",
        "bn254.fr": "field vector polynomial round matrix rng",
        "koala-bear": "field vector polynomial round matrix",
        "koala-bear.ext8-binomial3": "field vector polynomial round matrix rng",
        "bls12-381.g1": "group groups",
        "ristretto255.group": "group groups",
        "bn254.g1": "group groups",
        "bn254.g2": "group groups",
        "multilinear.kzg.bls12-381/0": "commitment proof opening_state prover_key verifier_key",
        "rows.merkle-keccak256.koala-bear/0": "commitment proof opening_state commitments opening_states",
        "rows.merkle-keccak256.koala-bear.ext8-binomial3/0": "commitment proof opening_state commitments opening_states",
        "merlin3.bls12-381.fr64be/0": "transcript",
        "merlin3.ristretto255.scalar64le/0": "transcript",
        "spongefish0.7.4.keccak.bls12-381.fr64be/0": "transcript",
        "merlin3.koala-bear.ext8-binomial3.rejection31le/0": "transcript",
    }
    result = {(kind, domain) for domain, kinds in families.items() for kind in kinds.split()}
    assert len(result) == 63
    return result


def test_atomic_formation_and_properties(inventory, drivers, directory):
    declarations, catalog, profile = inventory
    pairs = {(t["kind"], t["domain"]) for t in catalog["logical_types"]}
    assert required_atomic_types() <= pairs, "missing required logical types"
    assert len(pairs) == len(catalog["logical_types"]), "duplicate catalog pairs"
    candidates = pairs | {(kind, domain["identity"])
                          for kind in profile["types"]["atomic"]
                          for domain in catalog["domains"]}
    candidates |= {(kind, "") for kind in profile["types"]["outside_common_carrier"]}
    candidates = sorted(candidates)
    requests = [{"type": kind + (":" + domain if domain else "")} for kind, domain in candidates]
    replies = query(drivers, requests, directory)
    failures = agreements(replies, requests)
    descriptors = INVENTORY.indexed(declarations["types"])
    defaults = {(r["kind"], r["domain"]): r["representation"]
                for r in catalog["atomic_representations"] if r["default"]}
    for i, (kind, domain) in enumerate(candidates):
        accepted = (kind, domain) in pairs
        for consumer, rows in replies.items():
            actual = rows[i]
            if actual["accepted"] != accepted:
                failures.append({"consumer": consumer, "type": requests[i], "expected_admitted": accepted})
            elif accepted:
                expected = {"copy": descriptors[kind]["copy"], "drop": descriptors[kind]["drop"],
                            "serializable": descriptors[kind]["custody"] == "PublicValue",
                            "canonical": requests[i]["type"]}
                if any(actual[key] != value for key, value in expected.items()):
                    failures.append({"consumer": consumer, "actual": actual, "expected": expected})
                representation = defaults.get((kind, domain))
                physical = requests[i]["type"] + "@" + representation if representation else None
                if actual["default_physical"] != physical:
                    failures.append({"consumer": consumer, "actual": actual,
                                     "expected_default": physical})
    finish(directory, failures)


def test_atomic_representations(inventory, drivers, directory):
    _, catalog, _ = inventory
    rows = catalog["atomic_representations"]
    keys = {(r["kind"], r["domain"], r["representation"]) for r in rows}
    assert len(keys) == len(rows), "duplicate atomic representation"
    defaults = [(r["kind"], r["domain"]) for r in rows if r["default"]]
    assert len(set(defaults)) == len(defaults), "ambiguous atomic default"
    probes = set(keys)
    for row in catalog["logical_types"]:
        names = {r["representation"] for r in rows if r["kind"] == row["kind"]}
        names.add("unknown.representation/0")
        probes.update((row["kind"], row["domain"], name) for name in names)
    requests, expected = [], []
    for kind, domain, representation in sorted(probes):
        spelling = kind + (":" + domain if domain else "") + "@" + representation
        requests.append({"physical_type": spelling})
        expected.append({"accepted": True, "canonical": spelling}
                        if (kind, domain, representation) in keys else {"accepted": False})
    assert len(requests) <= 1024, "review atomic representation probe growth"
    replies = query(drivers, requests, directory)
    failures = agreements(replies, requests)
    for consumer, actual in replies.items():
        failures.extend({"consumer": consumer, "request": request,
                         "actual": response, "expected": want}
                        for request, response, want in zip(requests, actual, expected)
                        if response != want)
    finish(directory, failures)


def test_structural_formation_permissions_and_refusals(drivers, directory):
    def fixed(element, n=4):
        return f"fixed_vector<{element},{n}>"

    accepted = [
        (fixed("field:koala-bear", n), True, True, "plonky3.fixed-vector/0")
        for n in (0, 1, 4, 1048576)
    ] + [
        (fixed("field:bls12-381.fr"), True, True, None),
        (fixed(fixed("field:koala-bear"), 2), True, True, None),
        ("resource_unit:Ticket", False, True, "logical.resource_unit/0"),
        (fixed("resource_unit:Ticket", 0), False, True, None),
        (fixed("resource_unit:Ticket"), False, True, None),
        (fixed("rng:bls12-381.fr", 0), False, False, None),
        (fixed("transcript:merlin3.bls12-381.fr64be/0"), False, False, None),
        (fixed(fixed("rng:bls12-381.fr")), False, False, None),
    ]
    deepest = "field:koala-bear"
    for _ in range(8):
        deepest = fixed(deepest, 1)
    accepted.append((deepest, True, True, None))
    refused = [
        "", "unknown", "unknown<field:\"koala-bear\",4>", "field<\"koala-bear\">",
        "fixed_vector", "fixed_vector:field:koala-bear,4", "fixed_vector<>",
        "fixed_vector<field:\"koala-bear\">", "fixed_vector<field:\"koala-bear\",4,4>",
        "fixed_vector<\"koala-bear\",4>", "fixed_vector<4,field:\"koala-bear\">",
        "fixed_vector<field:unknown,4>", "fixed_vector<field:\"koala-bear\", 4>",
        "fixed_vector<field:\"koala-bear\"@plonky3.koala-bear/0,4>",
        fixed("field:koala-bear") + "@plonky3.fixed-vector/0",
        fixed("field:koala-bear", "04"), fixed("field:koala-bear", "-1"),
        fixed("field:koala-bear", "+4"), fixed("field:koala-bear", "1.0"),
        fixed("field:koala-bear", "1048577"), fixed("field:koala-bear", "18446744073709551616"),
        fixed(deepest, 1), "x" * 4097, "resource_unit:0Ticket", "resource_unit:",
    ]
    requests = [{"type": row[0]} for row in accepted] + [{"type": text} for text in refused]
    replies = query(drivers, requests, directory)
    failures = agreements(replies, requests)
    expected = [{"accepted": True, "canonical": text, "copy": copy, "drop": drop,
                 "serializable": False, "default_physical": text + "@" + rep if rep else None}
                for text, copy, drop, rep in accepted] + [{"accepted": False}] * len(refused)
    for consumer, rows in replies.items():
        failures.extend({"consumer": consumer, "request": request, "actual": actual, "expected": want}
                        for request, actual, want in zip(requests, rows, expected) if actual != want)
    finish(directory, failures)


def candidates(inventory):
    declarations, catalog, profile = inventory
    domains = catalog["domains"]
    by_sort = {sort: [d for d in domains if d["sort"] == sort]
               for sort in ("Field", "Group", "Commitment", "Transcript")}
    dispositions = INVENTORY.dispositions(profile, declarations)
    rows = []
    for operation in declarations["operations"]:
        name = operation["name"]
        group = dispositions[name]
        if group == "resource":
            choices = [(["Ticket"], "logical")]
        elif group == "nullary":
            choices = [([], "native" if name.startswith(("index.", "indices.", "external.")) else "arkworks")]
        elif group == "sequence":
            choices = [([payload], "native") for payload in
                       ["index", "field:bn254.fr", "group:bn254.g2", "field:koala-bear",
                        "sequence<field:ristretto255.scalar>", "rng:bls12-381.fr"]]
        elif group == "native_data_observation":
            choices = [([t["identity"], payload], t["provider"])
                       for t in by_sort["Transcript"] for payload in
                       ["bool", "vector:bls12-381.fr", "groups:bls12-381.g1", "indices",
                        "vector:bn254.fr", "rng:bls12-381.fr", "matrix:bls12-381.fr",
                        "field:bn254.fr", "group:bn254.g1", "group:bn254.g2",
                        "field:koala-bear", "field:koala-bear.ext8-binomial3",
                        "field:ristretto255.scalar", "group:ristretto255.group",
                        "sequence<group:bn254.g2>", "group:bn254.gt", "sequence<group:bn254.gt>",
                        "vector:koala-bear", "vector:koala-bear.ext8-binomial3",
                        "matrix:bn254.fr", "matrix:koala-bear.ext8-binomial3",
                        "groups:bn254.g2", "groups:ristretto255.group",
                        "commitment:rows.merkle-keccak256.koala-bear/0",
                        "proof:rows.merkle-keccak256.koala-bear/0",
                        "proof:rows.merkle-keccak256.koala-bear.ext8-binomial3/0",
                        "opening_state:rows.merkle-keccak256.koala-bear/0",
                        "commitments:rows.merkle-keccak256.koala-bear/0"]]
        else:
            sort = {"field": "Field", "fixed": "Field", "array": "Field", "group": "Group",
                    "commitment": "Commitment", "transcript": "Transcript"}[group]
            choices = [([d["identity"]] + (["4"] if group in ("fixed", "array") else []),
                        "plonky3" if group == "fixed" else d["provider"]) for d in by_sort[sort]]
        assert choices, f"no closed candidates for {name}"
        for arguments, provider in choices:
            assert provider, (name, arguments, "no explicit catalog provider")
            rows.append((operation, arguments, f"{provider}/{name}"))
    assert len(rows) < 1500, "review enumeration growth; avoid combinatorial testing"
    return rows


def expected_ports(operation, arguments, inventory):
    # resource_unit is an explicitly documented non-generic core carrier. Its
    # nominal slot is not represented by the generated generic scope.
    if operation["name"].startswith("resource_unit."):
        return {direction: ["resource_unit:" + arguments[0] for _ in operation[direction]]
                for direction in ("inputs", "outputs")}
    return INVENTORY.instantiate(operation, arguments, inventory[0], inventory[1])


@pytest.fixture(scope="module")
def installed_identities(physical_drivers):
    """Each executable discovers its own owners, without an input name list.

Ordinary resolver acceptance establishes a supported closed binding.
Every installed row needs an accepted closed-binding witness. C++ handles
physical relayout and resource-unit adapters outside its ordinary catalog;
those exact identities are still independently observed by the Rust owners.
"""
    result = {}
    for consumer, executable in physical_drivers.items():
        reply = json.loads(run([executable], b'{"implementations":true}\n'))
        assert reply["accepted"] is True
        assert reply["discovery"] == {
            "cpp": "physical-catalog", "rust": "physical-registry",
            "backend": "physical-registry"}[consumer]
        entries = reply["implementations"]
        assert entries and all(set(row) == {"contract", "implementation"} and
                               all(isinstance(value, str) and value for value in row.values())
                               for row in entries), (consumer, reply)
        pairs = {(row["contract"], row["implementation"]) for row in entries}
        assert len(pairs) == len(entries), (consumer, "duplicate implementation identities")
        result[consumer] = pairs
    return result


def implementation_arguments(inventory):
    arguments = {}
    for operation, args, _ in candidates(inventory):
        arguments.setdefault(operation["name"], set()).add(tuple(args))
    # This physical adapter deliberately has no logical declaration. Exercise
    # both directions, identity transforms and wrong domains independently.
    tables = {row["representation"] for row in inventory[1]["atomic_representations"]
              if row["kind"] == "table"}
    fields = {row["identity"] for row in inventory[1]["domains"] if row["sort"] == "Field"}
    arguments["table.relayout"] = {(field, source, target)
                                   for field in fields for source in tables for target in tables}
    return arguments


def implementation_requests(inventory, installed_identities):
    arguments = implementation_arguments(inventory)
    pairs = set.union(*installed_identities.values())
    assert {contract for contract, _ in pairs} == arguments.keys(), (
        "new owner requires closed-argument coverage", {c for c, _ in pairs} ^ arguments.keys())
    requests = [binding(contract, args, implementation, physical)
                for contract, implementation in sorted(pairs)
                for args in sorted(arguments[contract]) for physical in (False, True)]
    assert len(requests) < 100000, "review implementation probe growth"
    return requests


def installed_failures(replies, requests, installed_identities):
    failures = agreements(replies, requests)
    for consumer, rows in replies.items():
        for request, response in zip(requests, rows):
            pair = request["contract"], request["implementation"]
            # These compiler binding paths bypass its physical catalog; their
            # exact identities are still discovered by the other owners
            # and their full signatures are compared in the same probe union.
            bypass = consumer == "cpp" and (pair[0].startswith("resource_unit.") or
                                             pair[0] == "table.relayout")
            if response["accepted"] and pair not in installed_identities[consumer] and not bypass:
                failures.append({"consumer": consumer, "accepted_but_not_discovered": request})
    return failures


def test_installed_implementation_union(inventory, drivers, installed_identities, directory):
    requests = implementation_requests(inventory, installed_identities)
    replies = query(drivers, requests, directory)
    failures = installed_failures(replies, requests, installed_identities)
    declarations = INVENTORY.indexed(inventory[0]["operations"])
    coverage = {}
    for consumer, rows in replies.items():
        accepted = set()
        for request, response in zip(requests, rows):
            if not response["accepted"]:
                continue
            accepted.add((request["contract"], request["implementation"]))
            if request["contract"] in declarations:
                expected = expected_ports(declarations[request["contract"]], request["arguments"], inventory)
                actual = {direction: [text.split("@")[0] for text in response[direction]]
                          for direction in ("inputs", "outputs")}
                if actual != expected or response["physical"] != request["physical"]:
                    failures.append({"consumer": consumer, "request": request,
                                     "actual": response, "expected_ports": expected})
        inactive = installed_identities[consumer] - accepted
        if inactive:
            failures.append({"consumer": consumer, "unwitnessed_installed_identities": sorted(inactive)})
        coverage[consumer] = {"discovered": sorted(installed_identities[consumer]),
                              "resolved": sorted(accepted),
                              "inactive_in_probe_domains": sorted(installed_identities[consumer] - accepted)}
    (directory / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    finish(directory, failures)


def test_executing_backend_physical_signatures(inventory, physical_drivers, installed_identities, directory):
    requests = [r for r in implementation_requests(inventory, installed_identities) if r["physical"]]
    replies = query(physical_drivers, requests, directory)
    failures = installed_failures(replies, requests, installed_identities)
    accepted = {(request["contract"], request["implementation"])
                for request, response in zip(requests, replies["backend"]) if response["accepted"]}
    missing = installed_identities["backend"] - accepted
    if missing:
        failures.append({"consumer": "backend", "unwitnessed_installed_identities": sorted(missing)})
    (directory / "coverage.json").write_text(json.dumps({
        "discovered": sorted(installed_identities["backend"]), "resolved": sorted(accepted),
        "inactive_in_probe_domains": sorted(installed_identities["backend"] - accepted)}, indent=2) + "\n")
    finish(directory, failures)


def test_alternative_eligibility_boundaries(inventory, drivers, physical_drivers, installed_identities, directory):
    positive_directory = directory / "discovery"
    positive_directory.mkdir()
    probes = implementation_requests(inventory, installed_identities)
    replies = query(drivers, probes, positive_directory)
    finish(positive_directory, installed_failures(replies, probes, installed_identities))
    accepted = {(request["contract"], request["implementation"])
                for request, response in zip(probes, replies["cpp"]) if response["accepted"]}
    defaults = {(op["name"], implementation) for op, _, implementation in candidates(inventory)}
    # This subtraction classifies already independently discovered and resolved
    # names. It does not supply any alternative identity to a reader.
    alternatives = accepted - defaults - {("table.relayout", "arkworks/table.relayout")}
    assert alternatives, "the alternative implementation path must be exercised"
    arguments = implementation_arguments(inventory)
    requests, coverage = [], []
    for contract, implementation in sorted(alternatives):
        good, bad = [], []
        for request, response in zip(probes, replies["cpp"]):
            if (request["contract"], request["implementation"]) == (contract, implementation):
                (good if response["accepted"] else bad).append(request)
        assert all(any(request["physical"] == physical for request in good) for physical in (False, True))
        assert all(any(request["physical"] == physical for request in bad) for physical in (False, True)), (
            implementation, "add an ineligible domain witness")
        coverage.append({"contract": contract, "implementation": implementation,
                         "accepted": good, "wrong_domains": bad})
        for other, choices in sorted(arguments.items()):
            if (other, implementation) in accepted:
                continue
            requests.extend(binding(other, args, implementation, physical)
                            for args in sorted(choices) for physical in (False, True))
        for request in good:
            requests.append({**request, "implementation": implementation + "/unknown"})
            requests.append({**request, "contract": contract + ".unknown"})
            requests.append({**request, "arguments": ["unknown.domain", *request["arguments"][1:]]})
    assert len(requests) < 50000, "review alternative negative probe growth"
    actual = query(drivers, requests, directory)
    failures = [{"consumer": consumer, "request": request, "unexpected_acceptance": response}
                for consumer, rows in actual.items() for request, response in zip(requests, rows)
                if response != {"accepted": False}]
    backend_directory = directory / "backend"
    backend_directory.mkdir()
    physical = [request for request in requests if request["physical"]]
    native = query({"backend": physical_drivers["backend"]}, physical, backend_directory)
    failures.extend({"consumer": "backend", "request": request, "unexpected_acceptance": response}
                    for request, response in zip(physical, native["backend"])
                    if response != {"accepted": False})
    (directory / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    finish(directory, failures)


@pytest.mark.parametrize("physical", [False, True], ids=["logical-with-implementation", "physical"])
def test_declared_signatures(inventory, drivers, directory, physical):
    cases = candidates(inventory)
    requests = [binding(op["name"], args, impl, physical) for op, args, impl in cases]
    replies = query(drivers, requests, directory)
    failures = agreements(replies, requests)
    coverage = {name: {consumer: 0 for consumer in drivers}
                for name in INVENTORY.indexed(inventory[0]["operations"])}
    for i, (op, args, _) in enumerate(cases):
        for consumer, results in replies.items():
            response = results[i]
            if not response["accepted"]:
                continue
            coverage[op["name"]][consumer] += 1
            expected = expected_ports(op, args, inventory)
            actual = {direction: [text.split("@")[0] for text in response[direction]]
                      for direction in ("inputs", "outputs")}
            if actual != expected or response["physical"] != physical:
                failures.append({"consumer": consumer, "request": requests[i],
                                 "expected_ports": expected, "actual": response})
    for name, counts in coverage.items():
        if not covered(counts):
            failures.append({"unexercised_declaration": name, "accepted_counts": counts})
    (directory / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    finish(directory, failures)


def test_logical_signatures_without_implementation(inventory, drivers, directory):
    cases = candidates(inventory)
    requests = [binding(op["name"], args) for op, args, _ in cases]
    replies = query(drivers, requests, directory)
    failures = []
    coverage = {name: {consumer: 0 for consumer in drivers}
                for name in INVENTORY.indexed(inventory[0]["operations"])}
    for i, (op, args, _) in enumerate(cases):
        actual = {consumer: results[i] for consumer, results in replies.items()}
        for consumer, response in actual.items():
            coverage[op["name"]][consumer] += response["accepted"]
        expected = ({"accepted": True, "physical": False, **expected_ports(op, args, inventory)}
                    if actual["cpp"]["accepted"] else {"accepted": False})
        if any(response != expected
               for consumer, response in actual.items()):
            failures.append({"request": requests[i], "replies": actual, "expected": expected})
    for name, counts in coverage.items():
        if not covered(counts):
            failures.append({"unexercised_declaration": name, "accepted_counts": counts})
    (directory / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    finish(directory, failures)


def test_explicit_semantic_witnesses(drivers, directory):
    # Independently authored signatures keep a shared inventory error visible.
    witnesses = [
        ("field.add", ["koala-bear"], ["field:koala-bear"] * 2, ["field:koala-bear"]),
        ("poly.univariate_evaluate", ["bls12-381.fr"],
         ["polynomial:bls12-381.fr", "field:bls12-381.fr"], ["field:bls12-381.fr"]),
        ("poly.evaluate", ["bls12-381.fr"],
         ["table:bls12-381.fr", "point:bls12-381.fr"], ["field:bls12-381.fr"]),
        ("curve.scale", ["bn254.g2"], ["group:bn254.g2", "field:bn254.fr"], ["group:bn254.g2"]),
        ("pairing.check", ["bn254.fr"], ["groups:bn254.g1", "groups:bn254.g2"], ["bool"]),
        ("pairing.apply", ["bn254.fr"], ["group:bn254.g1", "group:bn254.g2"], ["group:bn254.gt"]),
        ("vector.equal", ["bn254.fr"], ["vector:bn254.fr", "vector:bn254.fr"], ["bool"]),
        ("pcs.check", ["multilinear.kzg.bls12-381/0"],
         ["verifier_key:multilinear.kzg.bls12-381/0", "commitment:multilinear.kzg.bls12-381/0",
          "point:bls12-381.fr", "field:bls12-381.fr", "proof:multilinear.kzg.bls12-381/0"], ["bool"]),
        ("oracle.commit", ["rows.merkle-keccak256.koala-bear/0"], ["vector:koala-bear", "index"],
         ["commitment:rows.merkle-keccak256.koala-bear/0", "opening_state:rows.merkle-keccak256.koala-bear/0"]),
        ("transcript.native.indexed.challenge", ["merlin3.bls12-381.fr64be/0"],
         ["transcript:merlin3.bls12-381.fr64be/0", "indices"],
         ["field:bls12-381.fr", "transcript:merlin3.bls12-381.fr64be/0"]),
    ]
    requests = [binding(name, args) for name, args, _, _ in witnesses]
    expected = [{"accepted": True, "physical": False, "inputs": inputs, "outputs": outputs}
                for _, _, inputs, outputs in witnesses]
    for field in ("koala-bear", "bls12-381.fr"):
        fixed = f"fixed_vector<field:{field},4>"
        for name, inputs, outputs in [
            ("from_vector", [f"vector:{field}"], [fixed]),
            ("to_vector", [fixed], [f"vector:{field}"]),
            ("dot", [fixed, fixed], [f"field:{field}"]),
        ]:
            requests.append(binding("fixed_vector." + name, [field, "4"]))
            expected.append({"accepted": True, "physical": False, "inputs": inputs, "outputs": outputs})
    # Physical Type/Nat applicability and exact representation spellings are
    # enumerated from the installed pattern catalog in a separate check.
    replies = query(drivers, requests, directory)
    failures = []
    for consumer, results in replies.items():
        failures.extend({"consumer": consumer, "request": req, "actual": actual, "expected": want}
                        for req, actual, want in zip(requests, results, expected) if actual != want)
    finish(directory, failures)


def test_unknowns_and_malformed_arguments(drivers, directory):
    requests = []
    for physical in (False, True):
        for contract, args in [
            ("unknown.operation", []), ("fixed_vector.unknown", ["koala-bear", "4"]),
            ("fixed_vector.dot", []), ("fixed_vector.dot", ["koala-bear"]),
            ("fixed_vector.dot", ["koala-bear", "4", "4"]),
            ("fixed_vector.dot", ["bn254.g1", "4"]),
            ("fixed_vector.dot", ["field:koala-bear", "4"]),
            ("fixed_vector.dot", ["unknown", "4"]),
            ("fixed_vector.dot", ["koala-bear", "04"]),
            ("fixed_vector.dot", ["koala-bear", "1048577"]),
            ("transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0"]),
            ("transcript.native.indexed.observe.data", ["unknown.suite", "field:bls12-381.fr"]),
            ("transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0",
                                                      "field_array<bls12-381.g1,4>"]),
            ("transcript.native.indexed.observe.data", ["merlin3.bls12-381.fr64be/0",
                                                      "field:bls12-381.fr", "invented.codec"]),
            ("resource_unit.create", ["0bad"]),
            ("field.add", ["koala-bear", "koala-bear"]),
        ]:
            requests.append(binding(contract, args, "plonky3/" + contract if physical else "", physical))
        requests.append(binding("fixed_vector.dot", ["koala-bear", "4"], "unknown/fixed_vector.dot", physical))
    replies = query(drivers, requests, directory)
    failures = [{"consumer": consumer, "request": request, "unexpected_acceptance": response}
                for consumer, results in replies.items() for request, response in zip(requests, results)
                if response != {"accepted": False}]
    finish(directory, failures)


@pytest.mark.parametrize("unchanged,divergent", [
    ("cpp", "rust"), ("rust", "cpp"),
])
def test_independently_authored_signature_drift(inventory, drivers, directory, unchanged, divergent):
    # The same installed declaration inventory supplies identical requests to
    # both processes. The flag selects a typed resolver in a conformance tool;
    # no signatures, registrations or expected results are sent on the wire.
    requests = [binding(op["name"], args, selected_implementation, physical)
                for op, args, implementation in candidates(inventory)
                for selected_implementation, physical in
                (("", False), (implementation, False), (implementation, True))]
    requests += [
        binding("field.add", ["koala-bear"], "plonky3/field.add"),
        binding("field.add", ["koala-bear"], "plonky3/field.add", True),
        binding("field.add", []), binding("field.add", ["unknown"]),
        binding("field.add", ["koala-bear"], "unknown/field.add"),
        binding("field.addition", ["koala-bear"]),
        {"type": "bool"}, {"facets": "field.add", "arguments": ["koala-bear"]},
        binding("field.mul", ["koala-bear"]),
    ]
    selected = {name: drivers[name] for name in (unchanged, divergent)}
    baseline_directory = directory / "baseline"
    baseline_directory.mkdir()
    baseline = query(selected, requests, baseline_directory)
    assert {request["contract"] for request, response in zip(requests, baseline[divergent])
            if "contract" in request and response["accepted"]} == {
                op["name"] for op in inventory[0]["operations"]}
    # Facet support is deliberately consumer-specific, unlike signatures.
    comparable = [i for i, request in enumerate(requests) if "facets" not in request]
    finish(baseline_directory, agreements(
        {name: [rows[i] for i in comparable] for name, rows in baseline.items()},
        [requests[i] for i in comparable]))
    actual = query(selected, requests, directory,
                   arguments={divergent: ["--divergent-logical-field-add"]})
    assert actual[unchanged] == baseline[unchanged]
    changed = []
    for i, (request, before, after) in enumerate(zip(
            requests, baseline[divergent], actual[divergent])):
        if request.get("contract") == "field.add" and not request["physical"] and before["accepted"]:
            assert before["inputs"] == ["field:" + request["arguments"][0]] * 2
            assert before["outputs"] == ["field:" + request["arguments"][0]]
            assert after == {**before, "outputs": ["bool"]}
            # Inventory, admission, input types and port arities cannot catch
            # this change. Both output types are independently well formed.
            assert len(before["outputs"]) == len(after["outputs"])
            changed.append(i)
        else:
            assert after == before, (request, before, after)
    assert changed, "the divergent resolver must actually be exercised"
    assert actual[divergent][-3]["accepted"], "bool must be a valid logical type"
    assert actual[divergent][-1]["accepted"], "the neighboring operation must still resolve"
    disagreements = agreements(
        {name: [rows[i] for i in comparable] for name, rows in actual.items()},
        [requests[i] for i in comparable])
    (directory / "expected-disagreements.json").write_text(json.dumps(disagreements, indent=2) + "\n")
    assert [row["request"] for row in disagreements] == [requests[i] for i in changed]


def test_uninstalled_envelope_vocabulary_refuses(drivers, directory):
    # compiler/examples/domain contributes this valid logical vocabulary only
    # to its separate compiler installation. Unchanged readers must not infer
    # its admission or semantics from familiar nested types or contract shape.
    requests = [
        {"type": "envelope<field:\"koala-bear\",4>"},
        {"type": "envelope<bool,2>"},
        {"type": "fixed_vector<envelope<bool,2>,3>"},
        binding("envelope.keep", ["field:koala-bear", "4"]),
        {"facets": "envelope.keep", "arguments": ["field:koala-bear", "4"]},
    ]
    requests = [item for unknown in requests for item in
                (unknown, binding("field.add", ["koala-bear"]))]
    replies = query(drivers, requests, directory)
    expected = {"accepted": True, "physical": False,
                "inputs": ["field:koala-bear"] * 2, "outputs": ["field:koala-bear"]}
    for consumer, results in replies.items():
        for i, result in enumerate(results):
            assert result == (expected if i % 2 else {"accepted": False}), (consumer, i, result)


@pytest.mark.parametrize("arguments", [
    ["--unknown"], ["--divergent-logical-field-add", "extra"],
])
def test_conformance_tool_options_refuse_unknowns(physical_drivers, arguments):
    for consumer, executable in physical_drivers.items():
        result = subprocess.run([executable, *arguments], input=b'{"type":"bool"}\n',
                                capture_output=True, timeout=60, check=False)
        assert result.returncode == 2, (consumer, result)
        assert not result.stdout, (consumer, result)
        assert b"usage:" in result.stderr, (consumer, result)


def test_bounded_json_lines_protocol(physical_drivers, directory):
    invalid = [b"", b"[]", b"null", b"{", b'{"type":true}', b'{"type":"bool","copy":true}',
               {"implementations": False}, {"implementations": 1}, {"implementations": []},
               {"implementations": True, "type": "bool"},
               b'{"type":"bool","type":"bool"}', b'{"ty\\u0070e":"bool","type":"bool"}',
               b'{"type":"bool","inputs":[]}', b'{"contract":"field.add"}',
               {"physical_type": 1}, {"physical_type": "bool", "type": "bool"},
               {"facets": "field.add"}, {"facets": 1, "arguments": []},
               {"facets": "field.add", "arguments": ["koala-bear"], "publicReplay": True},
               {"facets": "field.add", "arguments": ["koala-bear"] * 17},
               b'{"type":"bool"} garbage', b'{"type":"\xff"}', b'[' * 32 + b']' * 32,
               b" " * 16385, binding("field.add", ["koala-bear"] * 17),
               {**binding("field.add", ["koala-bear"]), "physical": 0},
               {**binding("field.add", ["koala-bear"]), "arguments": [1]},
               {**binding("field.add", ["koala-bear"]), "implementation": None},
               {**binding("field.add", ["koala-bear"]), "signature": {"inputs": [], "outputs": []}}]
    # Every refusal must preserve framing and permit the next independent line.
    good = binding("field.add", ["koala-bear"], "plonky3/field.add", True)
    requests = [item for bad in invalid for item in (bad, good)]
    replies = query(physical_drivers, requests, directory)
    for consumer, results in replies.items():
        for i, result in enumerate(results):
            assert result["accepted"] == bool(i % 2), (consumer, i, result)
    # EOF without a newline is one request; an exactly-full line is not oversized.
    wire = json.dumps(good).encode()
    for consumer, executable in physical_drivers.items():
        for suffix in (b"", b" " * (16384 - len(wire))):
            reply = json.loads(run([executable], wire + suffix))
            assert reply["accepted"], (consumer, reply)


def expected_facets(operation, group, declarations, policy):
    """Expected classifications from inert declarations, never consumer authority."""
    result = {name: False for name in policy["declared_fields"].values()}
    for facet in operation["facets"]:
        kind = facet["kind"]
        assert kind in policy["declared_fields"] or kind in policy["uncompared_declarations"], (
            operation["name"], "facet has no conformance disposition", facet)
        if kind in policy["declared_fields"]:
            result[policy["declared_fields"][kind]] = True
    if group == "native_data_observation":
        # The construction observer has a complete Type input and an explicit
        # Observation facet. Its closed grammar is independently bound below.
        assert result["observation"]
        result["unclassifiedProviderEffect"] = False
        return result
    if group == "sequence":
        # The declaration's open Type root has no copy bound. This is a
        # conservative declaration facet, independent of closed admission.
        result["unclassifiedProviderEffect"] = bool(operation["inputs"])
        return result
    # Current covered declarations have no open or affine nested Type terms.
    # Verify that restriction before using input-head custody as the expected
    # effect flag. The actual C++ API propagates Type-argument uncertainty too.
    assert not any(root["parameter"]["kind"] == "Type" for root in INVENTORY.roots(operation)), (
        operation["name"], "review instantiated provider-effect classification for Type roots")
    types = INVENTORY.indexed(declarations["types"])
    assert all("arguments" in term and types[term["name"]]["copy"]
               for term in operation["scope"] if term["parameter"]["kind"] == "Type"), (
        operation["name"], "review provider-effect expectations for affine nested Type terms")
    result["unclassifiedProviderEffect"] = not (result["sampling"] or result["observation"]) and (
        group == "resource" or any(types[port["constructor"]]["custody"] == "Affine"
                                   for port in operation["inputs"]))
    return result


def test_declared_semantic_facets(inventory, drivers, directory):
    declarations, _, profile = inventory
    policy = json.loads((FIXTURES / "facet-policy.json").read_text())
    assert policy["profile"] == "zkc.contract-facet-comparison"
    assert policy["consumer_fields"].keys() == drivers.keys()
    dispositions = INVENTORY.dispositions(profile, declarations)
    expected = {operation["name"]: expected_facets(
        operation, dispositions[operation["name"]], declarations, policy)
        for operation in declarations["operations"]}
    fields = set().union(*[set(row) for row in expected.values()])
    assert all(set(names) <= fields and len(names) == len(set(names))
               for names in policy["consumer_fields"].values())
    shared = set.intersection(*map(set, policy["consumer_fields"].values()))
    assert shared == {"history"}, "review the exact independently comparable subset"
    cases = candidates(inventory)
    requests = [{"facets": op["name"], "arguments": args} for op, args, _ in cases]
    requests += [{"facets": name, "arguments": []}
                 for name in ("unknown.operation", "transcript.unknown", "external.openvm.unknown")]
    replies = query(drivers, requests, directory)
    failures = []
    coverage = {name: {consumer: 0 for consumer in drivers} for name in expected}
    for i, request in enumerate(requests):
        admission = {consumer: results[i]["accepted"] for consumer, results in replies.items()}
        if len(set(admission.values())) != 1:
            failures.append({"request": request, "admission_disagreement": admission})
        for consumer, results in replies.items():
            actual = results[i]
            if not actual["accepted"]:
                continue
            name = request["facets"]
            if name not in expected:
                failures.append({"consumer": consumer, "unknown_accepted": request, "actual": actual})
                continue
            coverage[name][consumer] += 1
            selected = policy["consumer_fields"][consumer]
            want = {"accepted": True, "facets": {key: expected[name][key] for key in selected},
                    "unsupported": sorted(fields - set(selected))}
            normalized = {**actual, "unsupported": sorted(actual.get("unsupported", []))}
            if normalized != want or any(type(value) is not bool
                                         for value in actual.get("facets", {}).values()):
                failures.append({"consumer": consumer, "request": request, "actual": actual, "expected": want})
    for name, counts in coverage.items():
        if not covered(counts):
            failures.append({"unexercised_facet_declaration": name, "accepted_counts": counts})
    (directory / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    finish(directory, failures)


def applied_spelling(constructor, arguments):
    return f"{constructor}<{','.join(arguments)}>"


def pattern_matches(pattern, constructor, arguments):
    """Only an expected catalog-pattern match; never installed in a consumer."""
    if pattern["constructor"] != constructor or len(pattern["arguments"]) != len(arguments):
        return False
    for argument, value in zip(pattern["arguments"], arguments):
        if argument["kind"] == "Nat":
            if not value.isascii() or not value.isdecimal() or str(int(value)) != value:
                return False
            if not argument["minimum"] <= int(value) <= argument["maximum"]:
                return False
        elif value != argument["exact"]:
            return False
    return True


def applied_probes(declarations, catalog):
    """Linear boundary/exact-argument witnesses, not a product of argument ranges."""
    patterns = catalog["applied_representations"]
    types = INVENTORY.indexed(declarations["types"])
    assert patterns, "applied realization coverage cannot pass with an empty catalog"
    assert len({json.dumps(p, sort_keys=True) for p in patterns}) == len(patterns), "duplicate pattern"
    probes, coverage = set(), []
    for pattern in patterns:
        assert set(pattern) == {"constructor", "arguments", "representation", "default"}
        assert type(pattern["default"]) is bool
        assert pattern["representation"]
        constructor = pattern["constructor"]
        assert [p["kind"] for p in pattern["arguments"]] == [p["kind"] for p in types[constructor]["parameters"]]
        base, maximum = [], []
        for argument in pattern["arguments"]:
            if argument["kind"] == "Nat":
                assert set(argument) == {"kind", "minimum", "maximum"}
                assert type(argument["minimum"]) is int and type(argument["maximum"]) is int
                assert 0 <= argument["minimum"] <= argument["maximum"]
                base.append(str(argument["minimum"]))
                maximum.append(str(argument["maximum"]))
            else:
                assert argument["kind"] in ("Type", "Domain")
                assert set(argument) == {"kind", "exact"} and argument["exact"]
                base.append(argument["exact"])
                maximum.append(argument["exact"])
        local = {tuple(base), tuple(maximum)}
        for i, argument in enumerate(pattern["arguments"]):
            if argument["kind"] == "Nat":
                low, high = argument["minimum"], argument["maximum"]
                values = {str(n) for n in (low - 1, low, min(low + 1, high), max(low, high - 1), high, high + 1)}
            elif argument["kind"] == "Type":
                # Every installed atomic type with the same head discriminates
                # exact complete-Type matching from a head-only match.
                head = argument["exact"].split(":")[0].split("<")[0]
                values = {p["kind"] + (":" + p["domain"] if p["domain"] else "")
                          for p in catalog["logical_types"] if p["kind"] == head}
                values.add("unknown.logical_type")
            else:
                domain = next(d for d in catalog["domains"] if d["identity"] == argument["exact"])
                values = {d["identity"] for d in catalog["domains"] if d["sort"] == domain["sort"]}
                values.add("unknown.domain")
            for value in values:
                args = base.copy()
                args[i] = value
                local.add(tuple(args))
        probes.update((constructor, args) for args in local)
        positives = [applied_spelling(constructor, args) for args in sorted(local)
                     if pattern_matches(pattern, constructor, args)]
        assert positives, (pattern, "no positive pattern witness")
        coverage.append({"pattern": pattern, "positive_types": positives,
                         "boundary_and_exact_argument_types": [applied_spelling(constructor, args)
                                                               for args in sorted(local)]})
    assert len(probes) <= 256, "review applied pattern enumeration growth"
    return patterns, sorted(probes), coverage


def test_generated_applied_representations(inventory, drivers, directory):
    declarations, catalog, _ = inventory
    patterns, probes, coverage = applied_probes(declarations, catalog)
    requests, wanted = [], []
    for constructor, args in probes:
        logical = applied_spelling(constructor, args)
        matches = [p for p in patterns if pattern_matches(p, constructor, args)]
        defaults = [p for p in matches if p["default"]]
        assert len(defaults) <= 1, (logical, "ambiguous default catalog patterns")
        requests.append({"type": logical})
        wanted.append({"kind": "logical", "required": bool(matches),
                       "default": logical + "@" + defaults[0]["representation"] if defaults else None})
        representations = {p["representation"] for p in patterns if p["constructor"] == constructor}
        representations.add("unknown.representation/0")
        for representation in sorted(representations):
            physical = logical + "@" + representation
            requests.append({"physical_type": physical})
            accepted = len([p for p in matches if p["representation"] == representation]) == 1
            wanted.append({"kind": "physical", "response": {"accepted": True, "canonical": physical}
                           if accepted else {"accepted": False}})
    assert len(requests) <= 1024, "review applied physical probe growth"
    replies = query(drivers, requests, directory)
    failures = agreements(replies, requests)
    for consumer, results in replies.items():
        for request, response, want in zip(requests, results, wanted):
            if want["kind"] == "physical":
                if response != want["response"]:
                    failures.append({"consumer": consumer, "request": request,
                                     "actual": response, "expected": want["response"]})
            elif want["required"] and not response["accepted"]:
                failures.append({"consumer": consumer, "pattern_type_refused": request})
            elif response["accepted"] and (response["canonical"] != request["type"] or
                                           response["default_physical"] != want["default"]):
                failures.append({"consumer": consumer, "request": request,
                                 "actual": response, "expected_default": want["default"]})
    (directory / "coverage.json").write_text(json.dumps(coverage, indent=2) + "\n")
    finish(directory, failures)


def test_native_array_signature_witnesses(drivers, directory):
    field = "field:bls12-381.fr"
    array = "field_array<bls12-381.fr,4>"
    requests = [binding("field_array.from_vector", ["bls12-381.fr", "4"]),
                binding("field_array.at", ["bls12-381.fr", "4"]),
                {"type": "field_array<bls12-381.g1,4>"},
                binding("transcript.native.indexed.observe.data",
                        ["merlin3.bls12-381.fr64be/0", "field_array<bls12-381.g1,4>"])]
    expected = [{"accepted": True, "physical": False, "inputs": ["vector:bls12-381.fr"], "outputs": [array]},
                {"accepted": True, "physical": False, "inputs": [array], "outputs": [field]},
                {"accepted": False}, {"accepted": False}]
    replies = query(drivers, requests, directory)
    for consumer, rows in replies.items():
        assert rows == expected, (consumer, rows)


def test_native_shape_signature_witnesses(drivers, directory):
    requests = [binding("matrix.dimension", ["bls12-381.fr"]),
                binding("poly.table_arity", ["bls12-381.fr"])]
    expected = [{"accepted": True, "physical": False, "inputs": ["matrix:bls12-381.fr"], "outputs": ["index"]},
                {"accepted": True, "physical": False, "inputs": ["table:bls12-381.fr"], "outputs": ["index"]}]
    replies = query(drivers, requests, directory)
    for consumer, rows in replies.items():
        assert rows == expected, (consumer, rows)


def attribute_request(case):
    return {**binding(case["contract"], case["arguments"], case["implementation"], True),
            "attributes": case["attributes"]}


def admission_failures(cases, replies):
    failures = []
    for consumer, rows in replies.items():
        for case, response in zip(cases, rows):
            if not response["accepted"] or response.get("admitted") != case["admitted"]:
                failures.append({"consumer": consumer, "case": case, "actual": response})
            elif (not case["admitted"] and consumer == "rust"
                  and response.get("error") != case.get("rust_error", "Attributes")):
                # A malformed program or missing implementation must never stand
                # in for rejection by the actual operation attribute validator.
                failures.append({"consumer": consumer, "case": case,
                                 "wrong_refusal_boundary": response})
    return failures


def test_actual_parameter_and_program_admission(drivers, directory):
    cases = json.loads((FIXTURES / "attribute-admission.json").read_text())
    assert len({case["name"] for case in cases}) == len(cases)
    assert 60 <= len(cases) <= 100, "review the bounded attribute witness set"
    replies = query(drivers, [attribute_request(case) for case in cases], directory)
    finish(directory, admission_failures(cases, replies))


def origin_tree(value):
    """Independent literal string/array framing, not a production origin encoder."""
    if isinstance(value, str):
        data = value.encode("ascii")
        return b"\0" + len(data).to_bytes(8, "little") + data
    return b"\1" + len(value).to_bytes(8, "little") + b"".join(map(origin_tree, value))


def test_actual_origin_template_admission(drivers, directory):
    def template(kind, *, path=(), port="input_2", entry="main", tail=()):
        event = (["query", "Round", "draw", port, "random.bls12-381.fr/0", "draw", "V"]
                 if kind == "query" else ["message", "Round", "response", "response", "P", "V"])
        return ["zkc.native-origin-template/0", entry, list(path), list(tail), event]

    query_origin = template("query", path=[["repeat", "main", "rounds"], ["apply", "main", "step"]])
    message_origin = template("message")
    q, m = origin_tree(query_origin).hex(), origin_tree(message_origin).hex()
    specimens = [("query", "query-valid", [q], True), ("message", "message-valid", [m], True),
                 ("message", "wrong-query-kind", [q], False), ("query", "wrong-message-kind", [m], False),
                 ("query", "missing", [], False), ("query", "extra", [q, q], False),
                 ("query", "uppercase", [q.upper()], False), ("query", "truncated", [q[:-2]], False),
                 ("query", "odd-hex", [q[:-1]], False), ("query", "trailing-byte", [q + "00"], False),
                 ("query", "size-ceiling", ["00" * 2049], False)]
    for port in ("input_0", "input_18446744073709551615", "input_01", "input_", "service_2",
                 "input_18446744073709551616"):
        specimens.append(("query", port, [origin_tree(template("query", port=port)).hex()],
                          port in ("input_0", "input_18446744073709551615")))
    for name, tree in [("bad-step", template("query", path=[["call", "main", "step"]])),
                       ("empty-entry", template("query", entry="")),
                       ("space-entry", template("query", entry="has space")),
                       ("nonempty-reserved", template("query", tail=["unexpected"]))]:
        specimens.append(("query", name, [origin_tree(tree).hex()], False))
    malformed = deepcopy(query_origin)
    malformed[0] = "invalid.native-origin-template"
    specimens.append(("query", "unknown-origin-tag", [origin_tree(malformed).hex()], False))
    cases = []
    for kind, name, attributes, expected in specimens:
        contract = "transcript.native.indexed." + ("challenge" if kind == "query" else "observe.data")
        arguments = ["merlin3.bls12-381.fr64be/0"] + (["bool"] if kind == "message" else [])
        cases.append({"name": name, "contract": contract, "arguments": arguments,
                      "implementation": "arkworks/" + contract, "attributes": attributes, "admitted": expected})
        if name == "size-ceiling":
            # Program's independent string ceiling precedes attribute admission.
            cases[-1]["rust_error"] = "Limit"
    assert len(cases) <= 32
    replies = query(drivers, [attribute_request(case) for case in cases], directory)
    finish(directory, admission_failures(cases, replies))


def test_attribute_transport_refuses_keyed_extra_and_duplicate_fields(drivers, directory):
    request = {**binding("field.add", ["bls12-381.fr"], "arkworks/field.add", True), "attributes": []}
    requests = [dict(request, attributes={"value": "0"}), dict(request, extra="0"),
                dict(request, attributes=[0]), dict(request, attributes=[None]),
                json.dumps(request).replace('"attributes": []', '"attributes": [], "attributes": []').encode()]
    replies = query(drivers, requests, directory)
    assert all(rows == [{"accepted": False}] * len(requests) for rows in replies.values()), replies


def test_parameter_drift_is_observed(drivers, directory):
    cases = [{"name": "no-attributes", "contract": "field.add", "arguments": ["bls12-381.fr"],
              "implementation": "arkworks/field.add", "attributes": [], "admitted": True},
             {"name": "control", "contract": "field.constant", "arguments": ["bls12-381.fr"],
              "implementation": "arkworks/field.constant", "attributes": ["0"], "admitted": True}]
    replies = query(drivers, [attribute_request(case) for case in cases], directory,
                    arguments={"cpp": ["--divergent-field-add-attributes"]})
    failures = admission_failures(cases, replies)
    assert len(failures) == 1 and failures[0]["consumer"] == "cpp", failures
    assert failures[0]["case"]["name"] == "no-attributes", failures


def test_backend_attribute_drift_refuses_installation(physical_drivers, directory):
    replies = query({"backend": physical_drivers["backend"]},
                    [{"attribute_drift": False}, {"attribute_drift": True}], directory)["backend"]
    assert replies == [
        {"accepted": True, "admitted": True, "error": None, "same_ports": True, "same_attributes": False},
        {"accepted": True, "admitted": False, "error": "Backend", "same_ports": True, "same_attributes": False},
    ]


def entry_schema(kind, spelling, permissions):
    return {"kind": kind, "identity": sha256(spelling.encode()).hexdigest(), "type": spelling,
            "custody": False, "permissions": permissions, "leaves": [spelling], "fields": [], "alternatives": []}


def entry_record(child, *, custody=False, permissions=None, name="Record"):
    identity = sha256(name.encode()).hexdigest()
    prefix = ["resource_unit:zkl_resource_" + identity] if custody else []
    return {"kind": "record", "identity": identity, "type": name, "custody": custody,
            "permissions": child["permissions"] if permissions is None else permissions,
            "leaves": prefix + child["leaves"],
            "fields": [{"name": "value", "offset": len(prefix), "schema": child}], "alternatives": []}


def entry_request(schema, roles, *, setup=False):
    document = {
        "format": "zkc.language-interface/0", "capture": "1" * 64,
        "original": sha256(b"conformance original").hexdigest(), "toolchain": "conformance",
        "entry": "test::Main", "protocol": "Main", "relations": [], "job": {"kind": "run"},
        "setups": ([{"name": "setup", "inputs": [{"port": 0, "path": []}]}] if setup else []),
        "protocols": [{"symbol": "Main", "roles": ["P", "V"], "outputs": [], "services": [], "clauses": [],
                       "inputs": [{"name": "value", "index": 0, "type": schema["type"], "roles": roles,
                                   "native": list(range(len(schema["leaves"]))), "schema": schema}]}],
    }
    # The transport carries a string, so duplicate keys and recursive metadata
    # remain the actual Entry reader's responsibility.
    return {"entry_interface": json.dumps(document, separators=(",", ":"))}


def share_witnesses():
    # Independently chosen source policy witnesses, never a generated permission
    # inventory. Native formation and Entry schema availability are distinct.
    return [
        ("bool", "boolean", True, True, True, False),
        ("field:koala-bear", "field", True, True, True, False),
        ("polynomial:bls12-381.fr", "builtin", True, True, True, False),
        ("field_array<bls12-381.fr,0>", "builtin", True, True, True, False),
        ("sequence<sequence<field:koala-bear>>", "builtin", True, True, True, False),
        ("prover_key:multilinear.kzg.bls12-381/0", "builtin", False, True, True, True),
        ("sequence<prover_key:multilinear.kzg.bls12-381/0>", "builtin", False, True, True, True),
        ("opening_state:rows.merkle-keccak256.koala-bear/0", "builtin", False, True, True, False),
        ("sequence<fixed_vector<field:koala-bear,4>>", "builtin", False, True, True, False),
        ("fixed_vector<field:koala-bear,0>", "builtin", False, True, False, False),
        ("fixed_vector<fixed_vector<field:koala-bear,4>,2>", "builtin", False, True, False, False),
        ("fixed_vector<rng:bls12-381.fr,0>", "builtin", False, False, False, False),
    ]


def test_native_share_against_actual_entry_inputs(drivers, directory):
    witnesses = share_witnesses()
    policy = query({"cpp": drivers["cpp"]}, [{"native_policy": row[0]} for row in witnesses], directory / "policy")["cpp"]
    requests, expected = [], []
    failures = []
    for (spelling, kind, shared, copy, entry_available, setup), facts in zip(witnesses, policy):
        if not facts["accepted"] or facts.get("share") != shared or facts.get("copy") != copy:
            failures.append({"type": spelling, "native_policy": facts, "expected_share": shared, "expected_copy": copy})
        for nested in (False, True):
            for multi in (False, True):
                schema = entry_schema(kind, spelling, ["Copy", "Drop", "Share"] if multi else [])
                if nested:
                    schema = entry_record(entry_record(schema, name="Inner"), name="Outer")
                requests.append(entry_request(schema, ["P", "V"] if multi else ["P"], setup=setup))
                expected.append((spelling, nested, multi, entry_available and (not multi or shared)))
    assert len(requests) <= 64
    replies = query({"rust": drivers["rust"]}, requests, directory / "entry")["rust"]
    for (spelling, nested, multi, admitted), reply in zip(expected, replies):
        if not reply["accepted"] or reply.get("admitted") != admitted or (
                not admitted and reply.get("error") != "entry-interface-schema"):
            failures.append({"type": spelling, "nested": nested, "multi_role": multi,
                             "expected": admitted, "entry": reply})
    finish(directory, failures)


def entry_custody_witnesses():
    scalar = entry_schema("field", "field:koala-bear", ["Copy", "Drop", "Share"])
    custody = entry_record(scalar, custody=True, permissions=["Drop", "Share"], name="Ticket")
    token = custody["leaves"][0]
    copied = deepcopy(custody)
    copied["permissions"] = ["Copy", "Drop", "Share"]
    forged = deepcopy(custody)
    forged["leaves"][0] = "resource_unit:Other"
    offset = deepcopy(custody)
    offset["fields"][0]["offset"] = 0
    wrong_kind = deepcopy(custody)
    wrong_kind["kind"] = "tuple"
    restricted_child = entry_record(entry_schema("field", "field:koala-bear", ["Copy", "Drop"]),
                                    permissions=["Copy", "Drop", "Share"])
    cases = [("custody-local", custody, ["P"], True),
             ("nested-custody-local", entry_record(custody, name="Outer"), ["P"], True),
             ("custody-multi-role", custody, ["P", "V"], False),
             ("copied-custody", copied, ["P"], False),
             ("forged-custody", forged, ["P"], False),
             ("custody-offset", offset, ["P"], False),
             ("custody-kind", wrong_kind, ["P"], False),
             ("nested-missing-share", restricted_child, ["P", "V"], False)]
    return token, cases


def test_entry_custody_and_nested_permission_refusals(drivers, directory):
    token, cases = entry_custody_witnesses()
    policy = query({"cpp": drivers["cpp"]}, [{"native_policy": token}], directory / "policy")["cpp"]
    assert policy == [{"accepted": True, "share": False, "affine": True, "copy": False, "drop": True}]
    replies = query({"rust": drivers["rust"]}, [entry_request(s, roles) for _, s, roles, _ in cases], directory / "entry")["rust"]
    failures = [{"case": name, "expected": admitted, "entry": reply}
                for (name, _, _, admitted), reply in zip(cases, replies)
                if not reply["accepted"] or reply.get("admitted") != admitted or (
                    not admitted and reply.get("error") != "entry-interface-schema")]
    finish(directory, failures)


def test_share_policy_drift_is_observed(drivers, directory):
    facts = query({"cpp": drivers["cpp"]}, [{"native_policy": "field:koala-bear"}], directory / "policy",
                  arguments={"cpp": ["--divergent-field-share"]})["cpp"][0]
    schema = entry_schema("field", "field:koala-bear", ["Copy", "Drop", "Share"])
    entry = query({"rust": drivers["rust"]}, [entry_request(schema, ["P", "V"])], directory / "entry")["rust"][0]
    assert facts["accepted"] and entry["accepted"] and entry["admitted"]
    assert facts["share"] is False, "the native policy drift must disagree with real Entry admission"


def variant_share_witnesses():
    requests, spellings, expected = [], [], []
    for leaf, kind, shared in [("field:koala-bear", "field", True),
                               ("opening_state:rows.merkle-keccak256.koala-bear/0", "builtin", False)]:
        # A literal canonical postorder graph for Choice = Empty | Value(leaf).
        # No production variant builder supplies this independently authored graph.
        nodes = ["zkc.language", "test::Choice", ["0", "1"], "Empty", [], ["3", "4"],
                 "Value", leaf, ["7"], ["6", "8"], ["5", "9"], ["2", "10"]]
        spelling = "variant:" + json.dumps(["zkc.variant/0", nodes], separators=(",", ":")).encode().hex()
        spellings.append(spelling)
        for multi in (False, True):
            permissions = ["Copy", "Drop", "Share"] if multi else ["Copy", "Drop"]
            schema = entry_schema("variant", "test::Choice", permissions)
            schema["leaves"] = [spelling]
            schema["alternatives"] = [
                {"name": "Empty", "fields": []},
                {"name": "Value", "fields": [{"name": "0", "offset": 0,
                                                 "schema": entry_schema(kind, leaf, permissions)}]},
            ]
            requests.append(entry_request(entry_record(schema), ["P", "V"] if multi else ["P"]))
            expected.append(shared or not multi)
    return spellings, requests, expected


def test_variant_share_checks_every_arm_in_native_policy_and_entry(drivers, directory):
    spellings, requests, expected = variant_share_witnesses()
    policies = query({"cpp": drivers["cpp"]}, [{"native_policy": s} for s in spellings],
                     directory / "policy")["cpp"]
    assert [p.get("share") for p in policies] == [True, False], policies
    replies = query({"rust": drivers["rust"]}, requests, directory / "entry")["rust"]
    assert [row.get("admitted") for row in replies] == expected, replies
    assert replies[-1]["error"] == "entry-interface-schema", replies
