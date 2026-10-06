"""Exact algorithm selection over unchanged BLS ports and reference equations."""
import copy
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/contracts/provider-alternative.pir"
DEFAULT = "arkworks/vector.dot"
PAIRWISE = "arkworks-pairwise/vector.dot"
MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
ORDINARY = '''
  use zkc::algebra::Vector;
  bind dot = "vector.dot"("bls12-381.fr");
  fn Dot(left: Vector<"bls12-381.fr"::Element>, right: Vector<"bls12-381.fr"::Element>)
      -> "bls12-381.fr"::Element {
    let result = dot(left, right); return result;
  }
  protocol InnerProduct {
    roles (P, V);
    inputs (P left: Vector<"bls12-381.fr"::Element>, P right: Vector<"bls12-381.fr"::Element>);
    outputs (V "bls12-381.fr"::Element);
    local P: let product = Dot(left, right);
    message result: P(product) -> V(received);
    return received;
  }
  instance concrete: InnerProduct { roles (P = P, V = V); }
  entry main = concrete;
'''


def write(directory, name, value):
    path = directory / name
    path.write_text(json.dumps(value))
    return path


def source_file(directory, text):
    path = directory / "example.pir"
    path.write_text(text)
    return path


def wire_vector(values):
    return (b"ZKCV\x01\x0b" + len(values).to_bytes(4, "little")
            + b"".join(x.to_bytes(32, "little") for x in values)).hex()


def execute(toolchain, directory, journal, source, physical, left, right, outputs):
    checker = toolchain.checker("interactive-protocol")
    values = [("left", left), ("right", right)]
    native_inputs = write(directory, "native-inputs.json", [
        "zkc.run/2", "main", "provider-dot", [],
        [["P", [], [[name, ["wire", wire_vector(value)]] for name, value in values], []],
         ["V", [], [], []]], []])
    reference_inputs = write(directory, "reference-inputs.json", [
        "zkc.reference-inputs/1", "main", "provider-dot",
        [["P", [[name, ["vector:bls12-381.fr", list(map(str, value))]] for name, value in values]],
         ["V", []]], [], [], []])
    actual = journal.json([toolchain.runtime, "run-protocol", source, physical,
                           native_inputs, checker])
    observed = journal.attempt([checker, "--reference", source, reference_inputs])
    assert observed.returncode in (0, 1), observed.stderr
    reference = json.loads(observed.stdout)
    if len(left) != len(right):
        assert actual["stop"]["detail"] == "refused:length-mismatch"
        assert reference[3][:2] == ["refused", "vector-shape"]
        assert actual["wire"]["messages"] == 0
    else:
        expected = sum(x * y for x, y in zip(left, right)) % MODULUS
        assert actual["outcome"] == ["returned", {"P": [], "V": [["field", str(expected)]] * outputs}]
        assert reference[3] == ["returned", [["field:bls12-381.fr", str(expected)]] * outputs]
        assert actual["wire"]["messages"] == outputs
        assert actual["wire"]["payload_bytes"] == 38 * outputs
        requests = [event[1][2] for event in reference[4] if event[0] == "request"]
        assert requests == ["vector.dot"] * outputs
    assert actual["resources"] == reference[5] == []


def test_helper_specialization_retains_exact_identity(toolchain, directory, journal):
    compiler = toolchain.compiler
    checker = toolchain.checker("interactive-protocol")
    # Import the ordinary source helper through the existing source-module path.
    text = FIXTURE.read_text()
    helper, rest = text.split("configure Default", 1)
    (directory / "helpers.pir").write_text(helper)
    app = source_file(directory, 'use zkc::algebra::Vector; mod helpers; '
                      'use helpers::Dot;\n  configure Default' + rest)
    original = write(directory, "source.json", journal.json([compiler, "protocol-source", app]))
    physical = journal.json([compiler, "protocol-compile", app])
    assert {binding[3] for binding in physical[1]} == {DEFAULT, PAIRWISE}
    assert all(binding[1:3] == ["vector.dot", ["bls12-381.fr"]] for binding in physical[1])
    functions = physical[3]
    assert len(functions) == 2
    assert len({function[1] for function in functions}) == 2
    for function in functions:
        assert [port[1] for port in function[2]] == ["vector:bls12-381.fr@arkworks.fr-vector/1"] * 2
        assert function[3] == ["field:bls12-381.fr@arkworks.fr/1"]
    assert functions[0][5] == functions[1][5]
    bindings = {binding[0]: binding[3] for binding in physical[1]}
    assert {bindings[function[4][0][2]] for function in functions} == {DEFAULT, PAIRWISE}
    # The common-IR-only route retains the exact choice as well.
    logical_ir = journal.run([compiler, "protocol-import", app])
    logical = journal.json([compiler, "protocol-export", "-"], logical_ir)
    assert len(logical[2]) == 2
    assert PAIRWISE in {binding[3] for binding in logical[1]}
    logical_path = write(directory, "logical.json", logical)
    assert journal.json([compiler, "protocol-compile", logical_path]) == physical
    physical_ir = journal.run([compiler, "protocol-physical-ir", app])
    assert PAIRWISE in physical_ir
    assert journal.json([compiler, "protocol-export", "-"], physical_ir) == physical
    candidate = write(directory, "physical.json", physical)
    assert journal.json([checker, "--check", logical_path, candidate])[0] == "checked"
    assert journal.json([checker, "--admit", original])[0] == "checked"
    assert journal.json([checker, "--check", original, candidate])[0] == "checked"
    execute(toolchain, directory, journal, original, candidate, [1, 2, 3], [5, 7, 11], 2)
    # Removing the one fixed choice makes the two configurations share code.
    configured = app.read_text()
    choice = f'using (product = "{PAIRWISE}")'
    assert configured.count(choice) == 1
    app.write_text(configured.replace(choice, ""))
    shared = journal.json([compiler, "protocol-compile", app])
    assert len(shared[3]) == 1
    assert {binding[3] for binding in shared[1]} == {DEFAULT}


@pytest.mark.parametrize("left,right", [
    ([], []), ([7], [9]), ([2, 3], [5, 11]),
    ([1, 2, 3], [5, 7, 11]),
    ([MODULUS - 1, MODULUS - 2, 3], [MODULUS - 1, 7, MODULUS - 4]),
    (list(range(257)), list(reversed(range(257)))),
])
def test_helper_results_match_reference(toolchain, directory, journal, left, right):
    compiler = toolchain.compiler
    source = write(directory, "source.json", journal.json([compiler, "protocol-source", FIXTURE]))
    physical = write(directory, "physical.json", journal.json([compiler, "protocol-compile", source]))
    execute(toolchain, directory, journal, source, physical, left, right, 2)


@pytest.mark.parametrize("implementation", [DEFAULT, PAIRWISE])
@pytest.mark.parametrize("left,right", [([MODULUS - 1, 2, 3], [2, 5, 7]), ([1], [])])
def test_ordinary_source_selection(toolchain, directory, journal, implementation, left, right):
    compiler = toolchain.compiler
    app = source_file(directory, ORDINARY)
    source = write(directory, "source.json", journal.json([compiler, "protocol-source", app]))
    selection = write(directory, "selection.json", [["dot", implementation]])
    physical_value = journal.json([compiler, "protocol-compile", app, f"--implementations={selection}"])
    assert physical_value[1][0][3] == implementation
    default = journal.json([compiler, "protocol-compile", app])
    assert default[1][0][3] == DEFAULT
    normalized = copy.deepcopy(physical_value)
    normalized[1][0][3] = DEFAULT
    assert normalized == default
    physical = write(directory, "physical.json", physical_value)
    execute(toolchain, directory, journal, source, physical, left, right, 1)


@pytest.mark.parametrize("contract,domain,implementation", [
    ("vector.dot", "bn254.fr", PAIRWISE),
    ("vector.dot", "ristretto255.scalar", PAIRWISE),
    ("vector.dot", "koala-bear", PAIRWISE),
    ("vector.dot", "koala-bear.ext8-binomial3", PAIRWISE),
    ("vector.mul", "bls12-381.fr", PAIRWISE),
    ("vector.sum", "bls12-381.fr", PAIRWISE),
    ("vector.dot", "bls12-381.fr", PAIRWISE + "/1"),
])
def test_exact_admission_refuses_other_contracts_and_domains(
        toolchain, directory, journal, contract, domain, implementation):
    compiler = toolchain.compiler
    source = journal.json([compiler, "protocol-source", "-"], ORDINARY)
    good_source = write(directory, "source.json", source)
    candidate = journal.json([compiler, "protocol-compile", good_source])
    # Retention is sufficient: an unused binding must still be admitted.
    invalid = ["unused", contract, [domain], implementation]
    source[1].append(invalid)
    bad = write(directory, "bad-source.json", source)
    journal.run([compiler, "protocol-source", bad], refuses="binding-implementation")
    result = journal.attempt([toolchain.checker("interactive-protocol"), "--admit", bad])
    assert result.returncode == 1
    assert json.loads(result.stdout) == ["refused", "binding-implementation"]
    candidate[1].append(invalid)
    bad_candidate = write(directory, "bad-candidate.json", candidate)
    result = journal.attempt([toolchain.checker("interactive-protocol"), "--check",
                              good_source, bad_candidate])
    assert result.returncode == 1
    assert json.loads(result.stdout) == ["refused", "binding-implementation"]


def test_static_parameter_is_not_a_qualified_definition_name(toolchain, directory, journal):
    source = journal.json([toolchain.compiler, "protocol-source", FIXTURE])
    source[1][0][2][0][0] = "helpers.F"
    path = write(directory, "bad-parameter.json", source)
    result = journal.attempt([toolchain.checker("interactive-protocol"), "--admit", path])
    assert result.returncode == 1
    assert json.loads(result.stdout) == ["refused", "generic-binder"]


def test_qualified_definitions_still_require_unique_names(toolchain, directory, journal):
    source = journal.json([toolchain.compiler, "protocol-source", FIXTURE])
    source[1][0][1] = "helpers.Dot"
    source[1].append(copy.deepcopy(source[1][0]))
    path = write(directory, "duplicate-definition.json", source)
    result = journal.attempt([toolchain.checker("interactive-protocol"), "--admit", path])
    assert result.returncode == 1
    assert json.loads(result.stdout) == ["refused", "generic-duplicate-name"]
