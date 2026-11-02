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
import unittest

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
sys.path.insert(0, str(LEAN))
sys.path.insert(0, str(LEAN / "bridges/common"))
from bridges.common import interface as language_interface  # noqa: E402
from bridges.common import policy as native_policy  # noqa: E402
from bridges.common.lean_render import Refused  # noqa: E402
from bridges.common.replacement import ReplacementError, replace_exactly_once  # noqa: E402
from bridges.construction import render as participant  # noqa: E402
from bridges.executable import render as executable  # noqa: E402
from bridges.pipeline import glue  # noqa: E402
import intent  # noqa: E402

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
            [["main", []]], [[], []], [[], []]]


def exported(policy):
    return ["zkc.constructed-participant/0", "sha256:" + "0" * 64, "sha256:" + "0" * 64, policy, "validator",
            [], [], [], [], []]


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

    def setUp(self):
        self.data = original(inputs=(FIELD, FIELD, FIELD, FIELD), outputs=(BOOLEAN,))
        interface = proof_interface()
        self.output = interface["protocols"][0]["outputs"][0]
        self.witness = interface["protocols"][0]["inputs"][2]
        self.formal = {"name": "secret", "purpose": "witness", "native": [3],
                       "schema": deepcopy(self.witness["schema"])}

    def test_harmless_display_changes_still_match(self):
        for spelling in ("Bool", "boolean"):
            self.output["type"] = self.output["schema"]["type"] = spelling
            self.assertTrue(intent.boolean_decision(self.output, self.data))
        self.witness["type"] = self.witness["schema"]["type"] = "Fr"
        self.assertTrue(intent.witness_field(self.witness, self.formal, self.data, "bls12-381.fr"))

    def test_distinct_nominal_types_spelled_alike_do_not_match(self):
        self.witness["type"] = self.witness["schema"]["type"] = "Fr"
        other = deepcopy(self.formal)
        other["schema"]["identity"] = "4" * 64
        other["schema"]["type"] = "Fr"
        self.assertFalse(intent.witness_field(self.witness, other, self.data, "bls12-381.fr"))
        # The typed native leaf decides the field, whatever either display says.
        self.assertFalse(intent.witness_field(self.witness, self.formal, self.data, "bn254.fr"))
        self.assertFalse(intent.witness_field(
            self.witness, self.formal, original(inputs=(FIELD, FIELD, FIELD, OTHER_FIELD)), "bls12-381.fr"))
        # A field port spelled `bool` is not a Boolean decision.
        self.output["schema"] = scalar_schema(display="bool")
        self.output["type"] = "bool"
        self.assertFalse(intent.boolean_decision(self.output, self.data))


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


if __name__ == "__main__":
    unittest.main()
