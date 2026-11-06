#!/usr/bin/env python3
"""Strict shared bridge readers, exact textual controls and carrier ceilings.

These controls need no compiler. They exercise the one decoder of each shared
format (`zkc.native-proof-policy/0`, `zkc.language-interface/0`), the glue's
association of published inputs, the intent bridge's schema comparison, the
executable renderer's carrier ceilings and the exact replacement every textual
bridge control uses.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from types import SimpleNamespace

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
sys.path.insert(0, str(LEAN))
sys.path.insert(0, str(LEAN / "bridges/common"))
from bridges.common import interface as language_interface  # noqa: E402
from bridges.common import lean_render  # noqa: E402
from bridges.common.schema import origin_structure  # noqa: E402
from bridges.common import policy as native_policy  # noqa: E402
from bridges.common.lean_render import Refused  # noqa: E402
from bridges.common.replacement import ReplacementError, replace_exactly_once  # noqa: E402
from bridges.construction import render as participant  # noqa: E402
from bridges.executable import render as executable  # noqa: E402
from bridges.pipeline import glue  # noqa: E402
import intent  # noqa: E402
from intent_association_tests import scalar_fixture  # noqa: E402
from request_support import Obligation as IntentObligation  # noqa: E402
from bridges.common import check as scalar_controls  # noqa: E402
from bridges.common.request_support import Obligation, check_lean_resources  # noqa: E402

SUITE = "merlin3.bls12-381.fr64be/0"
FIELD = ["apply", "field", [["domain", "Field", "bls12-381.fr"]]]
OTHER_FIELD = ["apply", "field", [["domain", "Field", "bn254.fr"]]]
BOOLEAN = ["apply", "bool", []]
SERVICE = ["service", "random.bls12-381.fr/0"]
NATIVE_ROLES = ["role00000000", "role00000001"]
INTERFACE_FIXTURES = ROOT / "compiler/test/fixtures/language-interface"


def native(public=("0", "1", "2"), gates=(), suite=SUITE, services=("4",), draws=(("query", "delivery"),),
           construction=""):
    return ["zkc.native-proof-policy/0", "main", NATIVE_ROLES[0], NATIVE_ROLES[1], "0", suite,
            list(services), list(public), [list(pair) for pair in draws], "zkc.framed/0", construction,
            [list(gate) for gate in gates]]


def scalar_schema(kind="field", identity="1" * 64, display="field<bls12-381.fr>", leaf="field:bls12-381.fr"):
    return {"kind": kind, "identity": identity, "generated": None, "type": display, "custody": 0,
            "sealed": False, "roles": [], "element": None, "constructible": True,
            "permissions": ["Copy", "Drop"], "fields": [], "alternatives": [], "leaves": [leaf]}


def record_schema(fields):
    offset, rows, leaves = 0, [], []
    for name, schema in fields:
        rows.append({"name": name, "offset": offset, "public": True, "placement": None, "schema": schema})
        offset += len(schema["leaves"])
        leaves += schema["leaves"]
    return {**scalar_schema(kind="record", identity="2" * 64, display="example::Offset"),
            "fields": rows, "leaves": leaves}


def port(name, index, natives, schema, roles):
    if schema["fields"]:
        paths = [([ordinal], leaf) for ordinal, child in enumerate(schema["fields"])
                 for leaf in range(len(child["schema"]["leaves"]))]
    else:
        paths = [([], leaf) for leaf in range(len(schema["leaves"]))]
    components = [{"path": path, "leaf": leaf, "role": role, "facet": "data", "native": natives[position]}
                  for position, (path, leaf) in enumerate(paths) for role in roles]
    return {"name": name, "type": schema["type"], "index": index, "native": list(natives), "schema": schema,
            "placement": {"kind": "data", "roles": list(roles)}, "components": components}


def proof_interface():
    """A record proof: public `offset` (two fields) and `shift`, secret `guess`."""
    field = scalar_schema()
    protocol = {
        "symbol": "main", "roles": ["P", "V"],
        "inputs": [port("offset", 0, [0, 1], record_schema([("a", field), ("b", field)]), [0, 1]),
                   port("shift", 1, [2], field, [0, 1]), port("guess", 2, [3], field, [0])],
        "outputs": [port("accepted", 0, [0], scalar_schema("boolean", "3" * 64, "bool", "bool"), [1])],
        "services": [{"name": "challenges", "contract": "random.bls12-381.fr/0", "owner": "V", "native": 4}],
        "clauses": [], "common_input_requirements": []}
    return {"format": language_interface.FORMAT, "capture": "0" * 64, "original": "0" * 64,
            "toolchain": "0" * 64, "entry": "example::Proof", "protocol": "main", "protocols": [protocol],
            "relations": [], "setups": [],
            "job": {"kind": "proof", "prover": "P", "verifier": "V",
                    "public": [{"port": 0, "path": [], "role": "V"}, {"port": 1, "path": [], "role": "V"}],
                    "acceptance": {"direction": "output", "port": 0, "role": "V", "path": []},
                    "completion": None, "target": None, "gates": [],
                    "construction": {"kind": "fiat_shamir", "format": "zkc.framed/0", "suite": SUITE,
                                     "services": [0]}}}


def original(inputs=(FIELD, FIELD, FIELD, FIELD, SERVICE), outputs=(BOOLEAN,)):
    scopes = [NATIVE_ROLES, NATIVE_ROLES, NATIVE_ROLES, NATIVE_ROLES[:1], NATIVE_ROLES[1:]][:len(inputs)]
    root = ["function", "main", "protocol", "public", list(inputs), list(outputs),
            ["protocol", NATIVE_ROLES, scopes, [NATIVE_ROLES[1:]]], [], ["main", []],
            ["block", [], ["return", []]]]
    return ["zkc.structured-source/0", "original", "sha256:" + "0" * 64, "main", [], [], [], [root],
            [["main", []]], [[], []], [[], [], []]]


def exported(policy):
    return ["zkc.constructed-participant/0", "sha256:" + "0" * 64, "sha256:" + "0" * 64, policy, "validator",
            [], [], [], [], [], [[], []]]


class SubjectRoleSelection(unittest.TestCase):
    def test_changed_public_inputs_refuse_at_policy_or_selection(self):
        from bridges.subject import Driver
        for public in ((), ("0",), ("0", "1", "2")):
            with self.subTest(public=public):
                driver = Driver(SimpleNamespace(output=Path(".")))
                deployment = [None, None, [None, native(public=public)], None, None, None,
                              [[NATIVE_ROLES[1], "validator", [[index, None] for index in public],
                                [["0", None]], None, "0"]]]
                driver.role_map(SimpleNamespace(name="role-control"), deployment)
                self.assertTrue(all(check["passed"] for check in driver.checks))
                self.assertEqual(driver.checks[-1]["name"], "role-control:role-map-refuses-other-inputs")


class LeanProcessFailures(unittest.TestCase):
    def test_resource_failures_cannot_be_correspondence_refusals(self):
        for message in ("maximum number of heartbeats", "(deterministic) timeout", "maximum recursion depth",
                        "out of memory", "excessive memory consumption"):
            with self.subTest(message=message), self.assertRaises(Obligation) as raised:
                check_lean_resources(SimpleNamespace(returncode=1, stdout="Type mismatch\n" + message), "control")
            self.assertEqual(raised.exception.code, "proof-budget")
        with self.assertRaises(Obligation) as raised:
            check_lean_resources(SimpleNamespace(returncode=-9, stdout=""), "control")
        self.assertEqual(raised.exception.code, "proof-interrupted")

    def test_ordinary_diagnostics_remain_for_the_callers_check(self):
        check_lean_resources(SimpleNamespace(returncode=1, stdout="Type mismatch"), "control")
        check_lean_resources(SimpleNamespace(returncode=0, stdout="checked"), "control")


class ScalarReplyValues(unittest.TestCase):
    def test_values_follow_logical_types_in_requests_and_inputs(self):
        suite = scalar_controls.Suite(SimpleNamespace(seed=20261012), Path("unused"))
        for _ in range(20):
            self.assertIs(type(suite.value(BOOLEAN)), bool)
            self.assertIs(type(suite.value(FIELD)), int)
            self.assertIs(type(suite.value(SERVICE)), int)


class ExactReplacement(unittest.TestCase):
    def test_single_occurrence_is_replaced(self):
        self.assertEqual(replace_exactly_once("a b c", "b", "x"), "a x c")

    def test_absent_repeated_empty_or_unchanging_patterns_refuse(self):
        for text, old, new in [("a b c", "z", "x"), ("b a b", "b", "x"), ("abc", "", "x"), ("a b c", "b", "b")]:
            with self.subTest(text=text, old=old, new=new), self.assertRaises(ReplacementError):
                replace_exactly_once(text, old, new)

    def test_the_named_structured_controls_apply_to_current_fixtures(self):
        aliased = (ROOT / "compiler/test/fixtures/structured-source/aliased-indices.mlir").read_text()
        for old in ['"data.finite_fold"(%xs, %xs, %seed)', "    func.func private @read(",
                    "^entry(%xs: !V, %ys: !V):", "function_type = (!V, !V) -> !data.domain<ui64>",
                    ': (!V, !V, !F) -> !F\n      "protocol.return"']:
            with self.subTest(pattern=old):
                self.assertNotEqual(replace_exactly_once(aliased, old, "changed"), aliased)


class PolicyReader(unittest.TestCase):
    def test_profiles(self):
        decoded = native_policy.decode(native())
        self.assertEqual((decoded.profile, decoded.acceptance, decoded.services, decoded.public, decoded.draws),
                         (native_policy.NATIVE, 0, (4,), (0, 1, 2), (("query", "delivery"),)))
        authored = native_policy.decode(native(suite="", services=(), draws=()))
        self.assertEqual(authored.profile, native_policy.AUTHORED)
        programmable = native_policy.decode(native(suite="", draws=(), construction="plan"))
        self.assertEqual(programmable.profile, native_policy.PROGRAMMABLE)
        gated = native_policy.decode(native(gates=[("query", "64")]))
        self.assertEqual(gated.gates, (("query", 64),))

    def test_version_and_arity(self):
        for value in [native()[:-1], native() + [[]], ["zkc.native-proof-policy/1", *native()[1:]], {}]:
            with self.subTest(value=value), self.assertRaisesRegex(Refused, "array of size 12"):
                native_policy.decode(value)

    def test_field_kinds_and_indices(self):
        changes = [(4, "01"), (4, "1024"), (4, 0), (6, ["4", "4"]), (7, ["2", "1"]), (7, "0"),
                   (1, ""), (2, 7), (5, None), (9, "json"), (10, None), (8, [["query"]]),
                   (8, [["query", ""]]), (8, [["q", "d"]] * 65)]
        for position, value in changes:
            policy = native()
            policy[position] = value
            with self.subTest(position=position, value=value), self.assertRaises(Refused):
                native_policy.decode(policy)

    def test_gates(self):
        for gates in [[("other", "1")], [("query", "1"), ("query", "2")], [("query", "65")],
                      [("query", "01")], [("query", 1)], [("query",)], [["query", "1", "x"]]]:
            with self.subTest(gates=gates), self.assertRaisesRegex(Refused, "policy gates"):
                native_policy.decode(native(gates=gates))
        with self.assertRaisesRegex(Refused, "only a native construction selects gates"):
            native_policy.decode(native(suite="", draws=(("query", "delivery"),), construction="plan",
                                        gates=[("query", "1")]))

    def test_profile_shapes(self):
        for policy in [native(services=("4", "5")), native(draws=()), native(suite="", services=()),
                       native(suite="", services=(), draws=(("query", "delivery"),)),
                       native(suite="", services=(), construction="plan")]:
            with self.subTest(policy=policy), self.assertRaises(Refused):
                native_policy.decode(policy)

    def test_consumers_state_their_profiles(self):
        with self.assertRaisesRegex(Refused, "unsupported policy gates"):
            participant.policy(native(gates=[("query", "1")]))
        with self.assertRaisesRegex(Refused, "unsupported construction profile"):
            participant.policy(native(suite="", draws=(), construction="plan"))
        self.assertEqual(participant.policy(native(suite="", services=(), draws=())),
                         '⟨"main", "role00000000", "role00000001", 0, "", [], [0, 1, 2], [], "zkc.framed/0", ""⟩')
        for policy, message in [(native(gates=[("query", "1")]), "unsupported policy gates"),
                                (native(suite="", draws=(), construction="plan"),
                                 "unsupported construction profile")]:
            with self.subTest(message=message), self.assertRaisesRegex(Refused, message):
                executable.render(deployment(policy=policy), "Control")


class InterfaceReader(unittest.TestCase):
    def test_producer_fixtures_decode(self):
        for path in sorted(INTERFACE_FIXTURES.glob("*-records.json")):
            with self.subTest(path=path.name):
                language_interface.loads(path.read_text())
        language_interface.decode(proof_interface())

    def test_exact_member_sets(self):
        locations = {
            "interface": lambda value: value,
            "job": lambda value: value["job"],
            "construction": lambda value: value["job"]["construction"],
            "public": lambda value: value["job"]["public"][0],
            "protocol": lambda value: value["protocols"][0],
            "port": lambda value: value["protocols"][0]["inputs"][0],
            "schema": lambda value: value["protocols"][0]["inputs"][0]["schema"],
            "field": lambda value: value["protocols"][0]["inputs"][0]["schema"]["fields"][0],
            "placement": lambda value: value["protocols"][0]["inputs"][0]["placement"],
            "component": lambda value: value["protocols"][0]["inputs"][0]["components"][0],
            "service": lambda value: value["protocols"][0]["services"][0],
        }
        for name, select in locations.items():
            with self.subTest(location=name, change="extra"), self.assertRaisesRegex(Refused, "unexpected"):
                value = proof_interface()
                select(value)["extra"] = None
                language_interface.decode(value)
            with self.subTest(location=name, change="missing"), self.assertRaisesRegex(Refused, "missing"):
                value = proof_interface()
                target = select(value)
                del target[next(key for key in target if key != "kind")]
                language_interface.decode(value)

    def test_duplicate_keys_refuse(self):
        text = json.dumps(proof_interface())
        with self.assertRaisesRegex(Refused, "duplicate member"):
            language_interface.loads(text[:-1] + ', "entry": "other"}')

    def test_structure(self):
        def changed(edit):
            value = proof_interface()
            edit(value)
            return value
        controls = [
            changed(lambda value: value.__setitem__("protocol", "missing")),
            changed(lambda value: value["protocols"].append(deepcopy(value["protocols"][0]))),
            changed(lambda value: value["protocols"][0]["inputs"][1].__setitem__("index", 2)),
            changed(lambda value: value["job"]["public"].reverse()),
            changed(lambda value: value["job"]["public"].append({"port": 1, "path": [], "role": "V"})),
            changed(lambda value: value["job"]["public"].insert(1, {"port": 0, "path": [0], "role": "V"})),
            changed(lambda value: value["protocols"][0]["inputs"][1].__setitem__("maximum_rows", None)),
            changed(lambda value: value["job"]["construction"].__setitem__("services", [0, 1])),
            changed(lambda value: value["job"]["construction"].__setitem__("kind", "native")),
            changed(lambda value: value["job"].__setitem__("gates", [{"path": ["q"], "bits": 65}])),
            changed(lambda value: value["job"].__setitem__("gates", [{"path": [], "bits": 1}])),
            changed(lambda value: value["job"].__setitem__("kind", "check")),
            changed(lambda value: value["protocols"][0]["inputs"][1]["schema"].__setitem__("kind", "scalar")),
            changed(lambda value: value["protocols"][0]["inputs"][1]["schema"].__setitem__("custody", True)),
            changed(lambda value: value["protocols"][0]["common_input_requirements"].append(
                {"components": [], "observation": {"kind": "extent"}})),
        ]
        for index, value in enumerate(controls):
            with self.subTest(control=index), self.assertRaises(Refused):
                language_interface.decode(value)
        language_interface.decode(changed(lambda value: value["job"].__setitem__(
            "gates", [{"path": ["q"], "bits": 64}])))


class GluePublishedInputs(unittest.TestCase):
    def test_record_leaves_are_named_by_port_and_field(self):
        entry = glue.Entry(original(), exported(native()), proof_interface())
        self.assertEqual(entry.source_names, ["offset.a", "offset.b", "shift"])
        self.assertEqual(entry.names, ["offsetA", "offsetB", "shift"])
        self.assertEqual(entry.slots(), [("held", 0), ("held", 1), ("held", 2), ("absent", None),
                                         ("service", None)])

    def test_unsupported_or_inconsistent_inputs_refuse(self):
        swapped = proof_interface()
        swapped["job"].update(prover="V", verifier="P")
        cases = [
            ("authored", native(suite="", services=(), draws=()), proof_interface()),
            ("gated", native(gates=[("query", "1")]), proof_interface()),
            ("programmable", native(suite="", draws=(), construction="plan"), proof_interface()),
            ("public-mismatch", native(public=("0", "1")), proof_interface()),
            ("roles", native(), swapped),
        ]
        for label, policy, interface in cases:
            with self.subTest(label=label), self.assertRaises(Refused):
                glue.Entry(original(), exported(policy), interface)


class IntentSchemas(unittest.TestCase):
    """Port types are compared by schema and typed leaf, never by display text."""

    def resolve(self, data, interface, spec):
        with tempfile.TemporaryDirectory() as directory:
            return intent.resolve(spec, data, interface, None, Path(directory))

    def test_harmless_display_changes_still_match(self):
        data, interface, spec = scalar_fixture()
        protocol = interface["protocols"][0]
        witness = protocol["inputs"][2]
        witness["type"] = witness["schema"]["type"] = "Fr"
        for spelling in ("Bool", "boolean"):
            output = protocol["outputs"][0]
            output["type"] = output["schema"]["type"] = spelling
            self.resolve(data, interface, spec)

    def test_distinct_nominal_types_spelled_alike_do_not_match(self):
        for mutation in ("identity", "domain", "native-leaf", "decision"):
            data, interface, spec = scalar_fixture()
            protocol = interface["protocols"][0]
            witness = protocol["inputs"][2]
            formal = interface["relations"][0]["inputs"][2]
            witness["type"] = witness["schema"]["type"] = formal["schema"]["type"] = "Fr"
            if mutation == "identity":
                formal["schema"]["identity"] = "4" * 64
            elif mutation == "domain":
                spec["wiring"]["fieldDomain"] = "bn254.fr"
            elif mutation == "native-leaf":
                root = next(row for row in data[7] if row[1] == data[3])
                root[4][2] = deepcopy(OTHER_FIELD)
            else:
                output = protocol["outputs"][0]
                output["schema"] = deepcopy(witness["schema"])
                output["type"] = output["schema"]["type"] = "bool"
            with self.subTest(mutation=mutation), self.assertRaises(IntentObligation):
                self.resolve(data, interface, spec)


def deployment(parameter="0", site="site", policy=None):
    binding = ["operation", "numerical.map", ["bls12-381.fr", "1"], "arkworks/numerical.map", []]
    function = ["function", "helper", [], [], [["op", site, "operation", [parameter], [], []], ["ret", []]], None]
    validator = ["participant", "validator", "main", NATIVE_ROLES[1], [], [],
                 [["local", "call", "helper", [], []], ["return", []]], []]
    program = json.dumps(["zkc.program/0", [binding], [function], [validator],
                          [["entry", "main", [[NATIVE_ROLES[1], "validator"]]]]])
    return ["zkc.native-proof/0", "", ["", policy or native(suite="", services=(), draws=())], "", program,
            hashlib.sha256(program.encode()).hexdigest(), None, None, None]


class ExecutableCeilings(unittest.TestCase):
    def test_parameter_and_string_ceilings(self):
        executable.render(deployment("x" * executable.PARAMETER_BYTES), "Control")
        with self.assertRaisesRegex(Refused, "at most 16384 bytes"):
            executable.render(deployment("x" * (executable.PARAMETER_BYTES + 1)), "Control")
        executable.render(deployment(site="s" * executable.STRING_BYTES), "Control")
        with self.assertRaisesRegex(Refused, "at most 4096 bytes"):
            executable.render(deployment(site="s" * (executable.STRING_BYTES + 1)), "Control")

    def test_operation_attribute_count_ceiling(self):
        """One operation carries up to the carrier's 16,384 attributes."""
        def program(count):
            value = json.loads(deployment()[4])
            value[2][0][4][0][3] = ["0"] * count
            value[2][0][5] = ["helper", []]
            return value
        executable.render_program(program(executable.OPERATION_ATTRIBUTES), "Control")
        with self.assertRaisesRegex(Refused, "bounded array"):
            executable.render_program(program(executable.OPERATION_ATTRIBUTES + 1), "Control")


def control_deployment(body, functions=None):
    """A deployment whose validator has the given participant body; every
    function listed is declared, called or not."""
    boolean = "bool@native.bool/0"
    functions = functions or [
        ["function", name, [["x", boolean]], [boolean], [["return", ["x"]]], [name, []]]
        for name in ("in_then", "in_else", "in_arm", "in_loop", "unused")]
    validator = ["participant", "validator", "main", NATIVE_ROLES[1],
                 [["flag", boolean], ["value", boolean]], [boolean], body, []]
    program = json.dumps(["zkc.program/0", [], functions, [validator],
                          [["entry", "main", [[NATIVE_ROLES[1], "validator"]]]]])
    return ["zkc.native-proof/0", "", ["", native(suite="", services=(), draws=())], "", program,
            hashlib.sha256(program.encode()).hexdigest(), None, None, None]


def conditional(rows, yes=(("yield", ["a"]),), no=(("yield", ["a"]),)):
    return ["if", "choose", "flag", rows, [list(item) for item in yes], [list(item) for item in no], ["out"]]


class ExecutableControl(unittest.TestCase):
    """Participant capture rows and selected control, decoded by body kind."""

    def render(self, body, functions=None):
        return executable.render(control_deployment(body, functions), "Control")

    def test_participant_rows_render_as_rows(self):
        text = self.render([conditional([["a", "value"], ["b", "value"]]), ["return", ["out"]]])
        self.assertIn('.cond "choose" "flag" [⟨"a", "value"⟩, ⟨"b", "value"⟩] [.yield ["a"]] [.yield ["a"]] ["out"]',
                      text)
        loop = ["loop", "rounds", ["value", "value", "4", "i"], [["acc", "flag"]], [["f", "value"]],
                [["yield", ["acc"]]], ["out"]]
        self.assertIn('[("acc", "flag")] [⟨"f", "value"⟩] [.yield ["acc"]] ["out"]',
                      self.render([loop, ["return", ["out"]]]))

    def test_participant_name_lists_and_malformed_rows_refuse(self):
        for rows in (["value"], [["a"]], [["a", "value", "extra"]], [["a", 1]], [["", "value"]], "value"):
            with self.subTest(rows=rows), self.assertRaisesRegex(Refused, "capture rows|array of size"):
                self.render([conditional(rows), ["return", ["out"]]])
            loop = ["loop", "rounds", ["value", "value", "4", "i"], [], rows, [["yield", []]], []]
            with self.subTest(loop=rows), self.assertRaisesRegex(Refused, "capture rows|array of size"):
                self.render([loop, ["return", ["out"]]])

    def test_local_control_keeps_names(self):
        boolean = "bool@native.bool/0"
        local = ["function", "in_arm", [["x", boolean]], [boolean],
                 [["if", "inner", "x", ["x"], [["yield", ["x"]]], [["yield", ["x"]]], ["y"]], ["return", ["y"]]],
                 ["in_arm", []]]
        body = [["local", "call", "in_arm", ["value"], ["out"]], ["return", ["out"]]]
        self.assertIn('.cond "inner" "x" ["x"]', self.render(body, [local]))
        local[4][0][3] = [["x", "x"]]
        with self.assertRaisesRegex(Refused, "value names"):
            self.render(body, [local])

    def test_match_arms_render_in_order(self):
        arms = [["some", ["payload"], [["yield", ["payload"]]]], ["none", [], [["yield", ["a"]]]]]
        text = self.render([["match", "select", "value", [["a", "flag"]], arms, ["out"]], ["return", ["out"]]])
        self.assertIn('.select "select" "value" [⟨"a", "flag"⟩] [("some", ["payload"], [.yield ["payload"]]), '
                      '("none", [], [.yield ["a"]])] ["out"]', text)
        for bad in ([["some", ["payload"]]], [["some", "payload", []]], "arms"):
            with self.subTest(arms=bad), self.assertRaises(Refused):
                self.render([["match", "select", "value", [], bad, ["out"]], ["return", ["out"]]])

    def test_branch_records_have_exact_arity(self):
        with self.assertRaisesRegex(Refused, "array of size 7"):
            self.render([conditional([]) + ["extra"], ["return", ["out"]]])
        with self.assertRaisesRegex(Refused, "array of size 6"):
            self.render([["match", "select", "value", [], [], ["out"], "extra"], ["return", ["out"]]])

    def test_functions_called_only_from_arms_are_rendered(self):
        arms = [["some", [], [["local", "arm_call", "in_arm", ["a"], ["b"]], ["yield", ["b"]]]]]
        body = [conditional([["a", "value"]], yes=(("local", "then_call", "in_then", ["a"], ["b"]), ("yield", ["b"])),
                            no=(("local", "else_call", "in_else", ["a"], ["b"]), ("yield", ["b"]))),
                ["loop", "rounds", ["value", "value", "4", "i"], [], [["a", "flag"]],
                 [["match", "select", "a", [["a", "a"]], arms, ["c"]],
                  ["local", "loop_call", "in_loop", ["c"], ["d"]], ["yield", []]], []],
                ["return", ["out"]]]
        text = self.render(body)
        for name in ("in_then", "in_else", "in_arm", "in_loop"):
            self.assertIn(f'/-- The local function `{name}`. -/', text)
        self.assertNotIn("`unused`", text)
        self.assertEqual(executable.called(body), {"in_then", "in_else", "in_arm", "in_loop"})


class OriginSteps(unittest.TestCase):
    """Application and repeat steps have three fields; a branch step has four,
    the last its exact arm label."""

    def template(self, steps):
        return lean_render.encode_tree(["zkc.native-origin-template/0", "main", steps, [],
                                        ["message", "main", "site", "site", "P", "V"]]).hex()

    def test_three_field_and_branch_steps_render(self):
        steps = [["apply", "main", "call"], ["repeat", "child", "rounds"], ["branch", "child", "choose", "then"]]
        self.assertEqual(lean_render.origin(self.template(steps)),
                         '⟨"main", [.apply "main" "call", .repeat "child" "rounds", .branch "child" "choose" "then"], '
                         '["message", "main", "site", "site", "P", "V"]⟩')
        tree = lean_render.template(self.template(steps))
        origin_structure(tree)

    def test_other_step_shapes_refuse(self):
        for step in (["apply", "main", "call", "then"], ["repeat", "main"], ["branch", "main", "choose"],
                     ["branch", "main", "choose", "then", "extra"], ["loop", "main", "site"],
                     ["branch", "main", "choose", ["then"]]):
            with self.subTest(step=step):
                with self.assertRaisesRegex(Refused, "origin step"):
                    lean_render.origin_step(step)
                if all(isinstance(item, str) for item in step):
                    with self.assertRaisesRegex(ValueError, "origin"):
                        origin_structure(["zkc.native-origin-template/0", "main", [step], [],
                                                 ["message", "main", "site", "site", "P", "V"]])

    def test_generated_protocol_requires_a_canonical_identity_and_a_message(self):
        tree = lean_render.template(self.template([["apply", "main", "call"]]))
        generated = "zkc.oracle." + "a" * 64
        tree[4][1] = generated
        self.assertIn(generated, lean_render.origin(lean_render.encode_tree(tree).hex()))
        for invalid in ("zkc.oracle.", generated[:-1], generated.upper().replace("ZKC.ORACLE.", "zkc.oracle.")):
            for location in (tree[4], tree[2][0]):
                previous, location[1] = location[1], invalid
                with self.assertRaisesRegex(ValueError, "generated origin protocol"):
                    lean_render.origin(lean_render.encode_tree(tree).hex())
                location[1] = previous
        tree[4] = ["query", generated, "draw", "input_0", "random.test/0", "draw", "V"]
        with self.assertRaisesRegex(ValueError, "generated origin event"):
            lean_render.origin(lean_render.encode_tree(tree).hex())

    def test_branch_labels_are_origin_identifiers(self):
        with self.assertRaisesRegex(ValueError, "origin identifier"):
            origin_structure(["zkc.native-origin-template/0", "main", [["branch", "main", "choose", ""]], [],
                                     ["message", "main", "site", "site", "P", "V"]])


if __name__ == "__main__":
    unittest.main()
