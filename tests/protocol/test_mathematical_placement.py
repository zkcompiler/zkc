"""Check retained mathematical placement through independent Lean and execution."""

import copy
import hashlib
import json
import runpy

import pytest

from journal import Journal
from toolchain import ROOT


@pytest.fixture
def placed_comparison(toolchain, directory):
    return json.loads(Journal(directory).run([
        toolchain.native_test("zkc-mathematical_placement-test"), "--emit"
    ]))


def test_independent_installed_package_descriptors(toolchain, directory, placed_comparison):
    encoding = runpy.run_path(str(ROOT / "tests/fixtures/mathematical/encoding.py"))
    journal = Journal(directory)
    encoded = bytes.fromhex(journal.run([
        toolchain.checker("mathematical-reference"), "installation"
    ]).strip())
    descriptors = encoding["decode"](encoded)
    assert len(descriptors) == 15
    installed = {}
    for identity, descriptor in descriptors:
        name, version, digest = identity
        assert hashlib.sha256(
            b"zkc.math.installation.v1\0" + encoding["encode"](descriptor)
        ).hexdigest() == digest, name
        assert (name, version) not in installed
        installed[name, version] = digest
    for subject in [placed_comparison["mathematical"], json.loads(journal.run([
            toolchain.native_test("zkc-mathematical_placement-test"), "--sigma"
    ]))["mathematical"]]:
        for table in subject["manifest"].values():
            for identity in table:
                assert installed[identity["name"], identity["version"]] == identity["digest"]


def test_captured_sigma_has_independent_lean_admission(toolchain, directory, placed_sigma):
    encoding = runpy.run_path(str(ROOT / "tests/fixtures/mathematical/encoding.py"))
    journal = Journal(directory)
    source = directory / "subject.math"
    source.write_bytes(encoding["encode"](placed_sigma["mathematical"]))
    result = encoding["decode"](bytes.fromhex(journal.run([
        toolchain.checker("mathematical-reference"), "admit", source
    ]).strip()))
    assert result == ["admitted", "zkc.math.bls/1", 1]


def test_canonical_sigma_is_the_actual_frontend_subject(toolchain, directory):
    journal = Journal(directory)
    encoding = runpy.run_path(str(ROOT / "tests/fixtures/mathematical/encoding.py"))
    report = json.loads(journal.run([
        toolchain.compiler, "protocol-inspect", ROOT / "tests/fixtures/mathematical/sigma.pir"
    ]))
    canonical = bytes.fromhex(journal.run([
        toolchain.checker("mathematical-reference"), "sigma"
    ]).strip())
    assert canonical == encoding["encode"](report["mathematical_placement"]["mathematical"])


def test_retained_sigma_has_one_independent_checking_path(toolchain, directory, placed_sigma):
    journal = Journal(directory)
    source = journal.write("located.json", placed_sigma["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", source
    ])))
    response = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check-mathematical",
        journal.write("capture.json", placed_sigma), source, candidate
    ]))
    assert response[:2] == ["pending-hashes", "mathematical-structural-correspondence"]
    assert response[2][:2] == ["checked", "generic-structural-correspondence"]
    assert len(response[3]) == 17
    for request, expected in response[3]:
        assert request[:2] == ["zkc.hash/1", "sha256"]
        assert hashlib.sha256(bytes.fromhex(request[2])).hexdigest() == expected


@pytest.mark.parametrize("mutation", [
    "missing-component", "extra-component", "scope", "operation", "root", "guard",
    "receive", "site-kind", "role-map", "wire-map", "duplicate-key", "fraction", "custody",
])
def test_independent_placement_refuses_forged_correspondence(toolchain, directory, mutation):
    journal = Journal(directory)
    capture = json.loads(journal.run([
        toolchain.compiler, "protocol-inspect", ROOT / "tests/fixtures/mathematical/sigma.pir"
    ]))["mathematical_placement"]
    source = journal.write("located.json", capture["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", source
    ])))
    witness = capture["witness"]
    body = capture["located"][3][0][7]
    if mutation == "missing-component":
        witness["components"].pop()
    elif mutation == "extra-component":
        witness["components"].append(copy.deepcopy(witness["components"][0]))
    elif mutation == "scope":
        witness["components"][-1]["target"]["regions"] = []
    elif mutation == "operation":
        next(b for b in capture["located"][1] if b[1] == "field.mul")[1] = "field.add"
    elif mutation == "root":
        body[0][3] = "challenge"
    elif mutation == "guard":
        body.pop(-2)
    elif mutation == "receive":
        verifier = [i for i in body if i[0] == "pure"][-1]
        # Keep the same group type while replacing the received commitment
        # with a shared public input in the verifier's actual algebra.
        verifier[4][-3][4][0] = "statement_at_Verifier"
    elif mutation == "site-kind":
        witness["sites"][0]["kind"] = "guard"
    elif mutation == "role-map":
        witness["instances"][0]["roles"] = [1, 0]
    elif mutation == "wire-map":
        witness["wires"][0]["schema"] = "different"
    elif mutation == "custody":
        altered = copy.deepcopy(capture["located"])
        altered[5][0][1] = "different"
        source = journal.write("located.json", altered)
    path = journal.write("capture.json", capture)
    if mutation == "duplicate-key":
        text = path.read_text()
        path.write_text('{"format":"zkc.mathematical-placement/1",' + text.lstrip()[1:])
    elif mutation == "fraction":
        path.write_text(path.read_text().replace('"binding": 0', '"binding": 0.0', 1))
    response = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check-mathematical", path, source, candidate
    ], refuses=True))
    assert response[0] == "refused"


@pytest.mark.parametrize("old,new,scope", [
    ("generator_at_Prover", "statement_at_Prover", None),
    ("value_3_role_0", "witness_at_Prover", None),
    ("value_5_role_1", "statement_at_Verifier", None),
    ("value_4_role_0", "generator_at_Prover", None),
    ("node_2", "generator_at_Prover", [1, 0]),
    ("node_8", "node_6", [7, 0]),
])
def test_self_consistent_witness_cannot_alias_distinct_bindings(toolchain, directory, old, new, scope):
    journal = Journal(directory)
    capture = json.loads(journal.run([
        toolchain.compiler, "protocol-inspect", ROOT / "tests/fixtures/mathematical/sigma.pir"
    ]))["mathematical_placement"]
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", journal.write("original.json", capture["located"])
    ])))

    def rename(value):
        if isinstance(value, list):
            return [rename(child) for child in value]
        return new if value == old else value

    if scope is None:
        capture["located"] = rename(capture["located"])
    else:
        code = capture["located"][3][0][7][scope[0]][4]
        capture["located"][3][0][7][scope[0]][4] = rename(code)
    changed = 0
    for component in capture["witness"]["components"]:
        target = component["target"]
        if target["name"] == old and (scope is None or target["regions"] == scope):
            target["name"] = new
            changed += 1
    assert changed
    response = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check-mathematical",
        journal.write("capture.json", capture), journal.write("located.json", capture["located"]), candidate
    ], refuses=True))
    assert response[0] == "refused"
    # Fail before candidate comparison: source admission or placement must
    # reject the self-consistent binding collision itself.
    assert not response[1].startswith("participant-")


@pytest.mark.parametrize("replacement", ["null", "-1", "1e1000000000", '"\\ud800"', '"\\udc00"', '"\\udc00\\ud800"'])
def test_mathematical_json_refuses_unsupported_scalars_before_admission(toolchain, directory, replacement):
    journal = Journal(directory)
    capture = json.loads(journal.run([
        toolchain.compiler, "protocol-inspect", ROOT / "tests/fixtures/mathematical/sigma.pir"
    ]))["mathematical_placement"]
    source = journal.write("located.json", capture["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", source
    ])))
    path = journal.write("capture.json", capture)
    text = path.read_text()
    assert '"binding": 0' in text
    path.write_text(text.replace('"binding": 0', '"binding": ' + replacement, 1))
    response = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check-mathematical", path, source, candidate
    ], refuses=True))
    assert response[0] == "refused"


@pytest.mark.parametrize("identity", ["source", "target"])
def test_runtime_checks_retained_capture_digest(toolchain, directory, placed_comparison, identity):
    journal = Journal(directory)
    source = journal.write("located.json", placed_comparison["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", source
    ])))
    inputs = journal.write("inputs.json", [
        "zkc.run/2", "main", "session", [],
        [["prover", [], [["value_0_role_0", ["field", "3"]],
                         ["value_1_role_0", ["field", "17"]]], []],
         ["verifier", [], [["value_0_role_1", ["field", "3"]]], []]], []
    ])
    subject_pin = placed_comparison["witness"]["source"]
    placed_comparison["witness"][identity] = "0" * 64
    journal.run([
        toolchain.runtime, "run-protocol", journal.write("capture.json", placed_comparison),
        candidate, inputs, toolchain.checker("interactive-protocol"), subject_pin
    ], refuses="checker-mathematical-digest")


@pytest.mark.parametrize("pin_mode", ["missing", "different", "malformed", "array"])
def test_runtime_requires_caller_selected_mathematical_subject(toolchain, directory, placed_comparison, pin_mode):
    journal = Journal(directory)
    source = journal.write("located.json", placed_comparison["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", source
    ])))
    inputs = journal.write("inputs.json", ["zkc.run/2", "main", "session", [], [], []])
    # The replacement capture and all its pins are internally valid. The caller
    # selected the independently encoded canonical Sigma, not this comparison.
    canonical = bytes.fromhex(journal.run([
        toolchain.checker("mathematical-reference"), "sigma"
    ]).strip())
    selected = hashlib.sha256(b"zkc.math.subject.v1\0" + canonical).hexdigest()
    pin = [] if pin_mode == "missing" else [selected if pin_mode == "different" else "bad-pin"]
    capture = source if pin_mode == "array" else journal.write("capture.json", placed_comparison)
    refusal = {"missing": "host-mathematical-source-pin-required",
               "array": "host-mathematical-source-pin-unexpected"}.get(pin_mode, "checker-mathematical-source-pin")
    journal.run([
        toolchain.runtime, "run-protocol", capture,
        candidate, inputs, toolchain.checker("interactive-protocol"), *pin
    ], refuses=refusal)


@pytest.mark.parametrize("mutation", ["pin", "purity", "challenge", "prerequisite"])
def test_independent_math_admission_refusals(toolchain, directory, mutation):
    journal = Journal(directory)
    encoding = runpy.run_path(str(ROOT / "tests/fixtures/mathematical/encoding.py"))
    report = json.loads(journal.run([
        toolchain.compiler, "protocol-inspect", ROOT / "tests/fixtures/mathematical/sigma.pir"
    ]))
    source = copy.deepcopy(report["mathematical_placement"]["mathematical"])
    if mutation == "pin":
        source["manifest"]["operations"][0]["digest"] = "0" * 64
    elif mutation == "purity":
        source["module"]["operations"][0]["purity"] = "ordered"
    elif mutation == "challenge":
        source["module"]["capabilityTypes"][1]["result"] = {
            "type": 1, "statics": []
        }
    else:
        source["manifest"]["domains"].pop(0)
    path = directory / "subject.math"
    path.write_bytes(encoding["encode"](source))
    journal.run([
        toolchain.checker("mathematical-reference"), "admit", path
    ], refuses="math-admission-refused")


@pytest.mark.parametrize("mode", ["protocol-project", "protocol-compile"])
def test_placed_target_uses_existing_projection(toolchain, directory, placed_comparison, mode):
    journal = Journal(directory)
    source = journal.write("located.json", placed_comparison["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, mode, source
    ])))
    checked = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check", source, candidate
    ]))
    assert checked[:2] == ["checked", "generic-structural-correspondence"]


@pytest.mark.parametrize("public,expected", [("3", True), ("4", False)])
def test_placed_algebra_executes_actual_received_component(
        toolchain, directory, placed_comparison, public, expected):
    journal = Journal(directory)
    source = journal.write("located.json", placed_comparison["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", source
    ])))
    inputs = journal.write("inputs.json", [
        "zkc.run/2", "main", "session", [],
        [["prover", [], [["value_0_role_0", ["field", "3"]],
                         ["value_1_role_0", ["field", "17"]]], []],
         ["verifier", [], [["value_0_role_1", ["field", public]]], []]], []
    ])
    result = json.loads(journal.run([
        toolchain.runtime, "run-protocol", journal.write("capture.json", placed_comparison), candidate, inputs,
        toolchain.checker("interactive-protocol"), placed_comparison["witness"]["source"]
    ]))
    assert result["outcome"] == ["returned", {
        "prover": [["field", "3"]],
        "verifier": [["bool", expected], ["field", "3"]]
    }]
    assert result["wire"]["messages"] == 1


def test_placed_helper_cannot_replace_receive_with_public_input(
        toolchain, directory, placed_comparison):
    journal = Journal(directory)
    source = journal.write("located.json", placed_comparison["located"])
    candidate = json.loads(journal.run([toolchain.compiler, "protocol-compile", source]))
    helper = next(f for f in candidate[3] if len(f[2]) == 3)
    # Both are the same scalar type and owned by the verifier. Substitution
    # would nevertheless erase the equality check on a dishonest received value.
    first_scale = helper[4][0]
    first_scale[4][1] = helper[2][2][0]
    response = json.loads(journal.run([
        toolchain.checker("interactive-protocol"), "--check", source,
        journal.write("candidate.json", candidate)
    ], refuses=True))
    assert response[0] == "refused"


@pytest.fixture(params=["raw", "authored", "permuted"])
def placed_sigma(toolchain, directory, request):
    journal = Journal(directory)
    if request.param == "raw":
        return json.loads(journal.run([
            toolchain.native_test("zkc-mathematical_placement-test"), "--sigma"
        ]))
    authored = ROOT / "tests/fixtures/mathematical/sigma.pir"
    if request.param == "permuted":
        text = authored.read_text().replace(
            "Prover = Prover, Verifier = Verifier", "Verifier = Alice, Prover = Bob"
        ).replace(
            "  query [nonce_sample]", """  let doubled = group_add(generator, generator);
  let shared_ok = equal(doubled, doubled);
  guard [shared_prover] Prover(shared_ok);
  guard [shared_verifier] Verifier(shared_ok);
  query [nonce_sample]"""
        )
        authored = journal.directory / "permuted.pir"
        authored.write_text(text)
    report = json.loads(journal.run([toolchain.compiler, "protocol-inspect", authored]))
    assert report["mathematical_correspondence"] == "unchecked"
    captured = report["mathematical_placement"]
    assert captured["format"] == "zkc.mathematical-placement/1"
    assert captured["located"] == report["source"]
    located = journal.write("captured.json", captured["located"])
    assert journal.run([toolchain.compiler, "protocol-compile", authored]) == journal.run([
        toolchain.compiler, "protocol-compile", located
    ])
    body = captured["located"][3][0][7]
    pure = [i for i in body if i[0] == "pure"]
    assert [len(i[4]) - 1 for i in pure] == (
        [2, 2, 1, 3, 5] if request.param == "permuted" else [1, 3, 5]
    )
    if request.param == "permuted":
        assert captured["mathematical"]["module"]["roles"] == ["Alice", "Bob"]
        assert captured["witness"]["instances"][0]["roles"] == [1, 0]
        assert [i[2] for i in pure[:2]] == ["Alice", "Bob"]
    ports = captured["located"][3][0][4]
    assert any(p[0] == ("witness_at_Bob" if request.param == "permuted"
                        else "witness_at_Prover") for p in ports)
    assert [i[2] for i in body if i[0] == "message"] == [
        "commitment", "challenge", "response"
    ]
    return captured


@pytest.mark.parametrize("statement_scalar,accepted", [(3, True), (4, False)])
def test_complete_sigma_uses_nonzero_challenge_and_verifier_guard(
        toolchain, directory, placed_sigma, statement_scalar, accepted):
    journal = Journal(directory)

    def primitive(name, values):
        request = journal.write(name + ".json", [
            "zkc.public-primitive/1", [], name, ["bls12-381.g1"], [], values
        ])
        response = json.loads(journal.run([toolchain.primitive, request]))
        assert response[0] == "ok"
        return response[1]

    generator = primitive("curve.generator", [])
    scalar = ["field:bls12-381.fr",
              "5a4b43560101" + statement_scalar.to_bytes(32, "little").hex()]
    statement = primitive("curve.scale", [generator, scalar])
    source = journal.write("sigma.json", placed_sigma["located"])
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", source
    ])))
    roles = placed_sigma["mathematical"]["module"]["roles"]
    witness = placed_sigma["witness"]
    components = {(c["source"]["binding"], c["role"]): c["target"]["name"]
                  for c in witness["components"] if not c["source"]["regions"]}
    roots = [root["target"] for root in witness["roots"]]
    guard = next(site["targetSite"] for site in reversed(witness["sites"])
                 if site["kind"] == "guard")
    prover, verifier = witness["instances"][0]["roles"]
    values = []
    for ordinal, role in enumerate(roles):
        ports = [
            [components[1, ordinal], ["wire", generator[1]]],
            [components[2, ordinal], ["wire", statement[1]]],
        ]
        if ordinal == prover:
            ports.insert(0, [components[0, prover], ["field", "3"]])
        values.append([role, [], ports, []])
    inputs = journal.write("inputs.json", [
        "zkc.run/2", "main", "session", [], values, [],
        [[roles[prover], roots[0], "1"], [roles[verifier], roots[1], "1"]]
    ])
    report = json.loads(journal.run([
        toolchain.runtime, "run-protocol", journal.write("capture.json", placed_sigma), candidate, inputs,
        toolchain.checker("interactive-protocol"), placed_sigma["witness"]["source"]
    ]))
    assert report["assurance"][0] == "mathematical-structural-correspondence"
    assert report["mathematical"] == {"source": witness["source"], "target": witness["target"]}
    if accepted:
        assert report["outcome"] == ["returned", {role: [] for role in roles}]
    else:
        assert report["outcome"] == [
            "stopped", roles[verifier], guard, 'Explicit("reject")'
        ]
    assert report["wire"]["messages"] == 3
    assert sorted(report["root_resources"]) == sorted([
        [roles[prover], roots[0], 1, 1, 0, "rng"],
        [roles[verifier], roots[1], 1, 1, 0, "rng"],
    ])


@pytest.mark.parametrize("before,after,code", [
    ("let left = scale(generator, received_response);", "let left = scale(generator, witness);", "math-availability"),
    ('"random.draw_nonzero"', '"random.draw"', "math-operand-type"),
    ("let product = mul(scalar_challenge, witness);", "let product = 3;", "source-mathematical-expression"),
    ("mathematical protocol Sigma", "protocol Sigma", "source-syntax"),
    ("Verifier challenge -> (c)", "Prover challenge -> (c)", "math-capability-permission"),
    ("query [nonce_sample]", "query [verification]", "interactive-site"),
])
def test_authored_sigma_refuses_invalid_graphs(toolchain, directory, before, after, code):
    journal = Journal(directory)
    text = (ROOT / "tests/fixtures/mathematical/sigma.pir").read_text()
    assert before in text
    path = journal.directory / "invalid.pir"
    path.write_text(text.replace(before, after))
    journal.run([toolchain.compiler, "protocol-source", path], refuses=code)


def test_authored_sigma_formatter_preserves_captured_graph(toolchain, directory):
    journal = Journal(directory)
    path = ROOT / "tests/fixtures/mathematical/sigma.pir"
    formatted = journal.directory / "formatted.pir"
    formatted.write_text(journal.run([toolchain.compiler, "protocol-format", path]))
    before = json.loads(journal.run([toolchain.compiler, "protocol-inspect", path]))
    after = json.loads(journal.run([toolchain.compiler, "protocol-inspect", formatted]))
    assert before["mathematical_placement"] == after["mathematical_placement"]


@pytest.mark.parametrize("before,after,expected_line,code", [
    ("let left = scale(generator, received_response);",
     "let left = scale(generator, witness);", "guard [verification]", "math-availability"),
    ('"random.draw_nonzero"', '"random.draw"',
     "let scalar_challenge", "math-operand-type"),
    ("Verifier challenge -> (c)", "Prover challenge -> (c)",
     "query [challenge_sample]", "math-capability-permission"),
    ("query [nonce_sample]", "query [verification]",
     "guard [verification]", "interactive-site"),
])
def test_authored_admission_reports_actual_instruction(
        toolchain, directory, before, after, expected_line, code):
    journal = Journal(directory)
    text = (ROOT / "tests/fixtures/mathematical/sigma.pir").read_text().replace(before, after)
    path = journal.directory / "diagnostic.pir"
    path.write_text(text)
    journal.run([toolchain.compiler, "protocol-source", path], refuses=code)
    line = next(i for i, text in enumerate(text.splitlines(), 1) if expected_line in text)
    assert f"diagnostic.pir:{line}:" in journal.last.stderr


def test_authored_alias_receive_and_schema_identity(toolchain, directory):
    journal = Journal(directory)
    path = journal.directory / "aliases.pir"
    path.write_text("""
mathematical protocol Forward {
  roles (A, B);
  inputs (A x: bool);
  outputs (A bool, B bool);
  message [first_send] first: A(x) -> B(received);
  let alias = received;
  message [second_send] second: A(alias) -> B(second_received);
  return (alias, second_received);
}
instance forward: Forward { roles (A = A, B = B); }
entry main = forward;
""")
    report = json.loads(journal.run([toolchain.compiler, "protocol-inspect", path]))
    source = report["source"]
    body = source[3][0][7]
    assert [i[2] for i in body if i[0] == "message"] == ["first", "second"]
    assert [len(i[4]) for i in body if i[0] == "pure"] == [1]
    candidate = journal.write("candidate.json", json.loads(journal.run([
        toolchain.compiler, "protocol-compile", path
    ])))
    inputs = journal.write("inputs.json", [
        "zkc.run/2", "main", "session", [],
        [["A", [], [["x_at_A", ["bool", True]]], []], ["B", [], [], []]], []
    ])
    run = json.loads(journal.run([
        toolchain.runtime, "run-protocol", journal.write("capture.json", report["mathematical_placement"]),
        candidate, inputs, toolchain.checker("interactive-protocol"), report["mathematical_placement"]["witness"]["source"]
    ]))
    assert run["outcome"] == ["returned", {"A": [["bool", True]], "B": [["bool", True]]}]
    assert run["wire"]["messages"] == 2


def test_authored_mathematical_refuses_unconsumed_function(toolchain, directory):
    journal = Journal(directory)
    path = journal.directory / "extra.pir"
    path.write_text((ROOT / "tests/fixtures/mathematical/sigma.pir").read_text() +
                    "\nfn Unused(x: bool) -> bool { return x; }\n")
    journal.run([toolchain.compiler, "protocol-source", path],
                refuses="source-mathematical-profile")



def test_authored_sigma_elaborates_written_capture_indices(toolchain, directory):
    journal = Journal(directory)
    report = json.loads(journal.run([
        toolchain.compiler, "protocol-inspect",
        ROOT / "tests/fixtures/mathematical/sigma.pir"
    ]))
    source = report["mathematical_placement"]["mathematical"]
    body = source["module"]["definitions"][0]["body"]
    # Manually derived from newest-block-first body bindings and newest-node-
    # first region bindings. These expected indices are not copied from a
    # placer or inferred from the candidate target.
    commitment, response, verification = [step[1] for step in body["steps"]
                                          if step[0] == "pure"]
    assert commitment["captures"] == [2, 0]  # generator, nonce
    assert response["captures"] == [0, 5, 4]  # received challenge, witness, nonce
    assert [node[4] for node in response["nodes"]] == [[0], [0, 2], [4, 0]]
    assert response["outputs"] == [2, 1, 0]  # conversion, product, response
    assert verification["captures"] == [5, 10, 0, 11, 6]  # c, g, received z, y, received a
    assert [node[4] for node in verification["nodes"]] == [
        [0], [2, 3], [5, 1], [7, 0], [2, 0]
    ]
    assert verification["outputs"] == [4, 3, 2, 1, 0]
