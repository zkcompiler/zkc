#!/usr/bin/env python3
"""Independent foundation shape, signature and consumer-profile controls."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from bridges.common import schema  # noqa: E402
from bridges.construction import render as participant  # noqa: E402
from bridges.pipeline import mutations  # noqa: E402
from bridges.structured import snapshot  # noqa: E402

BOOLEAN = ["apply", "bool", []]
INDEX = ["apply", "index", []]
FIELD = ["apply", "field", [["domain", "Field", "example.F"]]]
VECTOR = ["apply", "vector", [["domain", "Field", "example.F"]]]
KIND = ["table", [["type", FIELD], ["nat", "16"]]]
ORACLE = ["oracle", *KIND]
NOMINAL = ["tuple", [["atom", "example.Record"], ["atom", "phantom.F"]]]
PRODUCT = ["variant", NOMINAL, [["make", [BOOLEAN, FIELD]]]]


def source(bindings, definitions=None):
    return ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
            "main", [], [], bindings, definitions or [], [], [[], []], [[], []]]


class NeutralSchema(unittest.TestCase):
    def test_complete_types_and_kinded_arguments(self):
        for value in [BOOLEAN, FIELD, VECTOR, PRODUCT, ORACLE,
                      ["oracle_sequence", *KIND, "18446744073709551615"],
                      ["apply", "fixed_vector", [["type", PRODUCT], ["nat", "7"]]],
                      ["apply", "field_array", [["domain", "Field", "example.F"], ["nat", "0"]]]]:
            with self.subTest(value=value):
                self.assertEqual(schema.logical_type(value), value)
        self.assertEqual(snapshot.ty(FIELD), '.field "example.F"')
        self.assertEqual(participant.sort(FIELD), ('.data (.field "example.F")', ("field", "example.F")))
        self.assertEqual(schema.argument(["mask", [True, False]], mask=True), ["mask", [True, False]])

    def test_identifier_grammars_before_lowering(self):
        for name in ["_", "make.Tag-0", "a" * 128]:
            value = ["variant", ["atom", "R"], [[name, []]]]
            self.assertEqual(schema.logical_type(value), value)
            snapshot.ty(value)
        for sort in schema.declarations()["sorts"]:
            maximum = 128 if sort == "Slot" else 256
            for name in ["a" * maximum, "resource_0"]:
                schema.argument(["domain", sort, name])
            invalid = ["", "a" * (maximum + 1), "0name", "bad name", "bad:name", "é"]
            if sort == "Slot":
                invalid += ["_slot", "bad/name"]
            else:
                schema.argument(["domain", sort, "_domain/0"])
                invalid += ["/name"]
            for name in invalid:
                with self.subTest(sort=sort, name=name), self.assertRaises(ValueError):
                    schema.argument(["domain", sort, name])
        malformed = [["variant", ["atom", "R"], [[name, []]]]
                     for name in ["bad/name", "a" * 129, "0make", "bad name", "é"]]
        malformed += [["apply", "field", [["domain", "Field", name]]]
                      for name in ["a" * 257, "0field", "bad:field", "/field"]]
        for value in malformed:
            for renderer in [snapshot.ty, participant.sort]:
                with self.subTest(value=value, renderer=renderer.__name__), self.assertRaises(ValueError):
                    renderer(value)
            # A malformed type in an uncalled definition must not disappear
            # through lowering or depend on the selected Entry reaching it.
            dormant = ["function", "unused", "local", "private", [value], [value],
                       [], [], ["unused", []], ["block", [], ["return", [0]]]]
            with self.subTest(unused=value), self.assertRaises(ValueError):
                snapshot.render(source([], [dormant]), "InvalidDormantType")

    def test_nominal_identity_is_complete_and_not_normalized(self):
        projected = schema.interpreted_type(PRODUCT)
        self.assertEqual(projected[1], '["example.Record","phantom.F"]')
        for nominal in [["atom", "example.Record"],
                        ["tuple", [["atom", "example.Record"], ["atom", "phantom.G"]]],
                        ["tuple", list(reversed(NOMINAL[1]))]]:
            changed = ["variant", nominal, PRODUCT[2]]
            self.assertNotEqual(schema.interpreted_type(changed), projected)
        self.assertNotEqual(schema.identity(["atom", "é"]), schema.identity(["atom", "e\u0301"]))
        empty = ["variant", ["tuple", []], [["make", []]]]
        self.assertEqual(schema.interpreted_type(empty), ["product", '[]', "make", []])
        self.assertNotEqual(schema.interpreted_identity(["atom", "[]"]),
                            schema.interpreted_identity(["tuple", []]))

    def test_old_and_malformed_types_refuse(self):
        values = ["i1", '!algebra.field<"example.F">', ["bool"], ["field", "example.F"],
                  ["product", '"nominal"', "make", []], ["apply", "unknown", []],
                  ["apply", "field", [["domain", "Group", "example.F"]]],
                  ["apply", "sequence", [["nat", "7"]]],
                  ["apply", "index", [["nat", "0"]]], ["apply", "field", ["example.F"]],
                  ["variant", "example.Record", [["make", []]]],
                  ["variant", ["atom", ""], [["make", []]]],
                  ["variant", ["atom", "\ud800"], [["make", []]]],
                  ["variant", ["atom", "R"], [["make", []], ["make", []]]],
                  ["oracle", "table", [["type", FIELD], ["nat", "016"]]],
                  ["oracle", "table", [["type", FIELD], ["nat", "18446744073709551616"]]],
                  ["oracle", "table", [["domain", "Field", "example.F"]]],
                  ["oracle", KIND], ["oracle_sequence", *KIND, 1]]
        for value in values:
            with self.subTest(value=value), self.assertRaises(ValueError):
                schema.logical_type(value)

    def test_recursively_excluded_handles_and_uninterpreted_types(self):
        for handle in [ORACLE, ["service", "random.example.F/0"],
                       ["apply", "transcript", [["domain", "Transcript", "suite"]]]]:
            for value in [handle, ["apply", "sequence", [["type", handle]]],
                          ["variant", ["atom", "R"], [["make", [handle]]]]]:
                with self.subTest(value=value), self.assertRaises(ValueError):
                    schema.interpreted_type(value, payload=True)
        # Wire formation is deliberately broader than mathematical installation.
        fixed = ["apply", "fixed_vector", [["type", FIELD], ["nat", "2"]]]
        schema.logical_type(fixed)
        with self.assertRaisesRegex(ValueError, "no installed formal interpretation"):
            schema.interpreted_type(fixed)

    def test_attribute_algebra_and_integer_interpretations(self):
        attributes = [["a", ["array", [["type", PRODUCT], ["bool", True],
                                      ["parameter", ["natural", "3"]]]]],
                      ["d", ["dictionary", [["field", ["string", "x"]]]]],
                      ["i", ["integer", "signed", "8", "-128"]],
                      ["s", ["symbol", ["root", "nested"]]]]
        self.assertEqual(schema.attributes(attributes)["s"], ["symbol", ["root", "nested"]])
        for value in [["integer", "unsigned", "8", "255"],
                      ["integer", "signless", "1", "1"],
                      ["integer", "signed", "1", "-1"]]:
            schema.attribute(value)
        malformed = [["integer", "0"], ["integer", "signed", "8", "128"],
                     ["integer", "unsigned", "8", "256"], ["integer", "signless", "8", "-1"],
                     ["integer", "signed", "8", "-0"], ["integer", "signed", "08", "0"],
                     ["integer", "signed", "0", "0"], ["integer", "signed", "4097", "0"],
                     ["integer", "signed", 8, "0"], ["bool", 1], ["symbol", "root"],
                     ["symbol", []], ["symbol", [""]], ["strings", []], ["text", "escape"],
                     ["dictionary", [["z", ["bool", True]], ["a", ["bool", False]]]],
                     ["dictionary", [["x", ["bool", True]], ["x", ["bool", False]]]]]
        for value in malformed:
            with self.subTest(value=value), self.assertRaises(ValueError):
                schema.attribute(value)
        for value in [attributes[::-1], attributes + [attributes[-1]]]:
            with self.assertRaises(ValueError):
                schema.attributes(value)

    def test_invocation_parameters_preserve_structure(self):
        for value in [["natural", "18446744073709551615"],
                      ["field_literal", "example.F", "natural", "7"],
                      ["field_literal", "example.Binary", "bits", "0xff"],
                      ["asset", "zkc.matrix/0", "a" * 64],
                      ["expression", ["zkc.ring/0", [], [["constant", "example.F", "3"]], [0]]]]:
            self.assertEqual(schema.parameter(value), value)
        for value in [["natural", 1], ["natural", "01"], ["natural", "18446744073709551616"],
                      ["field_literal", "F", "bits", "0x01"], ["field_literal", "F", "bits", "0x1"],
                      ["asset", "zkc.matrix/0", "sha256:" + "a" * 64],
                      ["expression", '{"tag":"constant"}'], ["origin", "hex"], ["text", "escape"]]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                schema.parameter(value)
        natural = {"validator": "Natural", "minimum": 1, "maximum": 1}
        schema.validate_parameters([["natural", "3"]], natural)
        for values in [[], [["natural", "0"], ["natural", "1"]], [["asset", "a", "0" * 64]]]:
            with self.assertRaises(ValueError):
                schema.validate_parameters(values, natural)
        with self.assertRaises(ValueError):
            snapshot.render_parameter(["asset", "zkc.matrix/0", "a" * 64])

    def test_native_origin_structure_and_method(self):
        tree = ["zkc.native-origin-template/0", "main", [], [],
                ["query", "main", "draw", "input_0", "random.example.F/0", "draw", "P"]]
        self.assertIn('.observe', participant.operation(
            "exec.apply", participant.attributes([
                ["binding", ["symbol", ["observe"]]],
                ["parameters", ["array", [["parameter", ["origin", [
                    "zkc.native-origin-template/0", "main", [], [], ["message", "main", "send", "schema", "P", "V"]]]]]]],
                ["site", ["string", "send"]]]),
            ["transcript.native.indexed.observe.data", [
                ["domain", "Transcript", "merlin3.bls12-381.fr64be/0"], ["type", FIELD]], "", [
                    ["apply", "transcript", [["domain", "Transcript", "merlin3.bls12-381.fr64be/0"]]],
                    FIELD, ["apply", "indices", []]], [
                    ["apply", "transcript", [["domain", "Transcript", "merlin3.bls12-381.fr64be/0"]]]]],
            [("transcript", "merlin3.bls12-381.fr64be/0"), ("field", "example.F"), ("indices", None)],
            [("transcript", "merlin3.bls12-381.fr64be/0")]))
        schema.origin_hex(["origin", tree])
        suite = "merlin3.bls12-381.fr64be/0"
        transcript = ["apply", "transcript", [["domain", "Transcript", suite]]]
        scalar = ["apply", "field", [["domain", "Field", "bls12-381.fr"]]]
        indices = ["apply", "indices", []]
        binding = ["transcript.native.indexed.challenge", [["domain", "Transcript", suite]],
                   "", [transcript, indices], [scalar, transcript]]
        def challenge(origin_tree):
            attrs = participant.attributes([
                ["binding", ["symbol", ["challenge"]]],
                ["parameters", ["array", [["parameter", ["origin", origin_tree]]]]],
                ["site", ["string", "draw"]]])
            return participant.operation("exec.apply", attrs, binding,
                [("transcript", suite), ("indices", None)], [("field", "bls12-381.fr"), ("transcript", suite)])
        self.assertIn(".challenge", challenge(tree))
        wrong_method = deepcopy(tree)
        wrong_method[4][5] = "index"
        with self.assertRaisesRegex(ValueError, "origin method"):
            challenge(wrong_method)
        tree[3] = ["1"]
        with self.assertRaises(ValueError):
            schema.origin_hex(["origin", tree])

    def test_signature_is_rederived_and_not_inferred_from_name(self):
        binding = ["vector.split", [["domain", "Field", "example.F"]], "", [VECTOR], [VECTOR, VECTOR]]
        schema.resolve_signature(binding, allowed={"vector.split"})
        mutations = [lambda b: b[1][0].__setitem__(1, "Group"),
                     lambda b: b[1][0].__setitem__(2, "other.F"),
                     lambda b: b[3].append(INDEX), lambda b: b[4].pop(),
                     lambda b: b.__setitem__(0, "vector.append")]
        for mutate in mutations:
            changed = deepcopy(binding)
            mutate(changed)
            with self.assertRaises(ValueError):
                schema.resolve_signature(changed, allowed={"vector.split"})
        with self.assertRaises(ValueError):
            schema.binding(binding[:3])
        with self.assertRaises(ValueError):
            schema.binding(["binding", "b", *binding[:3]], source=True)

    def test_associated_members_require_independent_resolution(self):
        extension = ["apply", "field", [["domain", "Field", "example.E"]]]
        binding = ["field.embed", [["domain", "Field", "example.E"]], "", [FIELD], [extension]]
        with self.assertRaises(ValueError):
            schema.resolve_signature(binding)
        schema.resolve_signature(binding, lambda parent, member: ["domain", "Field", "example.F"])
        with self.assertRaisesRegex(ValueError, "signature mismatch"):
            schema.resolve_signature(binding, lambda parent, member: ["domain", "Field", "other.F"])

    def test_dormant_source_binding_profile_and_ports(self):
        binding = ["binding", "unused", "index.add", [], "", [INDEX, INDEX], [INDEX]]
        rendered = snapshot.render(source([binding]), "Dormant")
        self.assertIn('"unused", "index.add"', rendered)
        for mutate in [lambda b: b.pop(), lambda b: b.__setitem__(4, "native/index.add"),
                       lambda b: b.__setitem__(5, [BOOLEAN, INDEX]),
                       lambda b: b.__setitem__(6, [BOOLEAN]),
                       lambda b: b.__setitem__(3, [["nat", "1"]]),
                       lambda b: b.__setitem__(2, "field.add")]:
            changed = deepcopy(binding)
            mutate(changed)
            with self.assertRaises(ValueError):
                snapshot.render(source([changed]), "DormantBad")

    def test_source_associated_capability_and_parameter_admission(self):
        extension = ["apply", "field", [["domain", "Field", "example.E"]]]
        binding = ["binding", "embed", "field.embed", [["domain", "Field", "example.E"]],
                   "", [FIELD], [extension]]
        data = source([binding])
        data[9] = [[["nominal", "example.E", "Field", [["BaseField", "example.F"]],
                     ["Field", "ExtensionField"], "17"],
                    ["nominal", "example.F", "Field", [], ["Field"], "17"]], []]
        self.assertIn('"embed", "field.embed", ["example.E"]', snapshot.render(data, "Extension"))
        for mutate in [lambda d: d[9][0][0].__setitem__(4, ["Field"]),
                       lambda d: d[9][0][0][3][0].__setitem__(1, "other.F")]:
            changed = deepcopy(data)
            mutate(changed)
            with self.assertRaises(ValueError):
                snapshot.render(changed, "BadExtension")
        constant = ["binding", "constant", "index.constant", [], "", [], [INDEX]]
        function = ["function", "limit", "local", "private", [], [INDEX], [], [], ["limit", []],
                    ["block", [[["exec", "exec.apply", "constant", [["natural", "7"]]],
                                [], [INDEX], [], "literal"]], ["return", [0]]]]
        data = source([constant], [function])
        self.assertIn('.exec "exec.apply" "constant" ["7"]', snapshot.render(data, "Constant"))
        for parameters in [[], ["7"], [["natural", "01"]], [["asset", "format", "0" * 64]]]:
            changed = deepcopy(data)
            changed[7][0][9][1][0][0][3] = parameters
            with self.assertRaises(ValueError):
                snapshot.render(changed, "BadConstant")

    def test_signature_order_is_independent_of_supplied_ports(self):
        suite = ["domain", "Transcript", "suite"]
        transcript = ["apply", "transcript", [suite]]
        indices = ["apply", "indices", []]
        binding = ["transcript.native.indexed.observe.data", [suite, ["type", FIELD]],
                   "", [transcript, FIELD, indices], [transcript]]
        schema.resolve_signature(binding)
        changed = deepcopy(binding)
        changed[3] = [FIELD, transcript, indices]
        with self.assertRaisesRegex(ValueError, "signature mismatch"):
            schema.resolve_signature(changed)
        changed = deepcopy(binding)
        changed[1][1][1] = ["apply", "field", [["domain", "Field", "other.F"]]]
        with self.assertRaisesRegex(ValueError, "signature mismatch"):
            schema.resolve_signature(changed)

    def test_sampled_probe_conversion_preserves_role_slots(self):
        # This driver is also executable directly, with sibling-script imports.
        sibling = str(Path(__file__).resolve().parents[1] / "bridges/structured")
        sys.path.insert(0, sibling)
        try:
            from bridges.structured import participant as sampled
        finally:
            sys.path.remove(sibling)
        root = ["function", "main", "protocol", "public", [FIELD, ["service", "random.example.F/0"]],
                [BOOLEAN], ["protocol", ["P", "V"], [["P", "V"], ["P"]], [["V"]]],
                [], ["main", []], ["block", [], ["return", []]]]
        data = source([], [root])
        projection = ('"protocol.projection"() {source = "main", entries = ['
                      '{inputs = [0], outputs = [], participant = @prover, role = "P", service_inputs = [1]}, '
                      '{inputs = [0], outputs = [0], participant = @verifier, role = "V", service_inputs = []}]}')
        bindings = sampled.projection_binding(projection, data)
        self.assertEqual(bindings["P"]["input_types"], [["field", "example.F"], ["service", "random.example.F/0"]])
        self.assertEqual(bindings["V"]["output_types"], [["bool"]])
        self.assertEqual(bindings["P"]["service_inputs"], [1])
        self.assertEqual(bindings["V"]["service_inputs"], [])
        with self.assertRaises(sampled.Mismatch):
            sampled.projection_binding(projection.replace('inputs = [0]', 'inputs = []', 1), data)
        changed = deepcopy(data)
        changed[7][0][4][0] = ["field", "example.F"]
        with self.assertRaises(ValueError):
            sampled.projection_binding(projection, changed)

    def test_realization_references_and_handle_boundaries(self):
        types = schema.RealizationTypes([FIELD, ORACLE])
        self.assertEqual(types.reference(0, payload=True), FIELD)
        self.assertEqual(types.reference(1), ORACLE)
        types.finish()
        with self.assertRaises(ValueError):
            types.reference(1, payload=True)
        for index in [True, "0", -1, 2]:
            with self.subTest(index=index), self.assertRaises(ValueError):
                types.reference(index)
        with self.assertRaisesRegex(ValueError, "first-use"):
            schema.RealizationTypes([FIELD, BOOLEAN]).reference(1)
        with self.assertRaisesRegex(ValueError, "unused"):
            schema.RealizationTypes([FIELD]).finish()
        with self.assertRaisesRegex(ValueError, "duplicate"):
            schema.RealizationTypes([FIELD, deepcopy(FIELD)])

    def test_bounds_apply_to_expanded_work(self):
        value = FIELD
        for _ in range(65):
            value = ["apply", "sequence", [["type", value]]]
        with self.assertRaisesRegex(ValueError, "depth"):
            schema.logical_type(value)
        with self.assertRaisesRegex(ValueError, "node"):
            schema.logical_type(PRODUCT, budget=schema.Budget(nodes=3))
        with self.assertRaisesRegex(ValueError, "metadata"):
            schema.logical_type(FIELD, budget=schema.Budget(bytes_=10))

    def test_strict_json(self):
        self.assertEqual(schema.loads('["apply","index",[]]'), INDEX)
        for encoded in ['{"x":0,"x":1}', '[NaN]', '[1.0]', '["\\ud800"]', '[' * 65 + '0' + ']' * 65]:
            with self.subTest(encoded=encoded), self.assertRaises(ValueError):
                schema.loads(encoded)


class PolicyControls(unittest.TestCase):
    def test_current_policy_preserves_supported_projection(self):
        policy = ["zkc.native-proof-policy/0", "main", "P", "V", "0", "suite",
                  ["1"], ["0"], [["query", "delivery"]], "zkc.framed/0", "", []]
        self.assertEqual(participant.policy(policy),
                         '⟨"main", "P", "V", 0, "suite", [1], [0], '
                         '[("query", "delivery")], "zkc.framed/0", ""⟩')

    def test_policy_requires_exact_width_and_empty_gates(self):
        policy = ["zkc.native-proof-policy/0", "main", "P", "V", "0", "suite",
                  ["1"], ["0"], [["query", "delivery"]], "zkc.framed/0", "", []]
        for value in [policy[:-1], policy[:-2], policy + [[]]]:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "array of size 12"):
                participant.policy(value)
        for gates in [None, False, 0, "", {}, (), [["query", "0"]],
                      [["query", "1"]], [["query"]], ["query", "0"], [[]]]:
            with self.subTest(gates=gates), self.assertRaisesRegex(ValueError, "policy gates"):
                participant.policy(policy[:-1] + [gates])


class MutationControls(unittest.TestCase):
    def fixture(self):
        suite = "merlin3.bls12-381.fr64be/0"
        field = ["apply", "field", [["domain", "Field", "bls12-381.fr"]]]
        transcript = ["apply", "transcript", [["domain", "Transcript", suite]]]
        indices = ["apply", "indices", []]
        message = ["zkc.native-origin-template/0", "main", [], [],
                   ["message", "main", "message", "schema", "P", "V"]]
        query = ["zkc.native-origin-template/0", "main", [], [],
                 ["query", "main", "query", "input_1", "random.bls12-381.fr/0", "draw", "V"]]
        delivery = ["zkc.native-origin-template/0", "main", [], [],
                    ["message", "main", "delivery", "schema", "V", "P"]]

        def invoke(contract, arguments, inputs, outputs, operands, parameters):
            return ["exec.apply", [["binding", ["symbol", ["b"]]],
                    ["parameters", ["array", [["parameter", p] for p in parameters]]],
                    ["site", ["string", "transition"]]],
                    [contract, arguments, "", inputs, outputs], operands, outputs, []]

        instructions = [
            invoke("indices.empty", [], [], [indices], [], []),
            ["protocol.receive", [["peer", ["string", "P"]], ["schema", ["string", "schema"]],
                                  ["site", ["string", "message"]]], [], [], [field], []],
            invoke(mutations.OBSERVE, [["domain", "Transcript", suite], ["type", field]],
                   [transcript, field, indices], [transcript], [1, 3, 2], [["origin", message]]),
            invoke(mutations.CHALLENGE, [["domain", "Transcript", suite]],
                   [transcript, indices], [field, transcript], [4, 2], [["origin", query]]),
            invoke(mutations.OBSERVE, [["domain", "Transcript", suite], ["type", field]],
                   [transcript, field, indices], [transcript], [6, 5, 2], [["origin", delivery]]),
            ["algebra.field_equal", [], [], [0, 5], [BOOLEAN], []]]
        policy = ["zkc.native-proof-policy/0", "main", "P", "V", "0", suite,
                  ["1"], ["0"], [["query", "delivery"]], "zkc.framed/0", "", []]
        return [participant.FORMAT, "sha256:" + "0" * 64, "sha256:" + "1" * 64, policy,
                "verifier", [field, transcript], [BOOLEAN, transcript], instructions, [8, 7], []]

    def test_transcript_controls_remain_applicable_and_readable(self):
        data = self.fixture()
        original = deepcopy(data)
        participant.render(data, "Before")
        for mutate in [mutations.observe_reads_input, mutations.challenge_reads_host,
                       mutations.challenge_names_delivery]:
            variants = mutate(data)
            with self.subTest(control=mutate.__name__):
                self.assertEqual(len(variants), 1)
                self.assertNotEqual(variants[0], data)
                participant.render(variants[0], "After")
        changed = mutations.challenge_names_delivery(data)[0]
        expected = deepcopy(data)
        expected[7][3][1][1][1][1][0][1][1][4][2] = "delivery"
        self.assertEqual(changed, expected)
        self.assertEqual(data, original)
        legacy = deepcopy(data[7][3])
        legacy[2] = legacy[2][:3]
        with self.assertRaises(ValueError):
            mutations.bound(legacy, mutations.CHALLENGE)
        legacy = deepcopy(data[7][3])
        legacy[1][1][1] = ["array", [["string", "retired-hex-template"]]]
        with self.assertRaises(ValueError):
            mutations.template_tree(legacy)

    def test_observation_does_not_reuse_a_sibling_scope(self):
        data = self.fixture()
        observe = data[7][2]
        first = deepcopy(observe)
        second = deepcopy(observe)
        # Reference 2 in the first sibling is not reference 2 in the second,
        # even when their logical types agree. The second observes reference 3.
        first[3][1], second[3][1] = 2, 3
        field = data[5][0]
        data[7] = [["protocol.loop", [], [], [], [], [[[field], [first], []]]],
                   ["protocol.loop", [], [], [], [], [[[field, field], [second], []]]]]
        self.assertEqual(mutations.observe_repeats_value(data), [])
        # Within one scope, a previous observation remains an available control.
        data = self.fixture()
        first = deepcopy(data[7][2])
        first[3][1] = 0
        data[7].insert(2, first)
        variants = mutations.observe_repeats_value(data)
        self.assertEqual(len(variants), 1)
        self.assertEqual(variants[0][7][3][3][1], 0)

    def test_native_origin_edit_preserves_path_and_unrelated_fields(self):
        data = self.fixture()
        tree = mutations.template_tree(data[7][3])
        tree[2] = [["repeat", "main", "rounds"]]
        mutations.set_template(data[7][3], tree)
        candidate = ('parameters = [#runtime.origin<"main" path[<repeat, "main", "rounds">], '
                     '#runtime.query_origin<"main", "query", 1, "random.bls12-381.fr/0", "draw", "V">>], '
                     'site = "transition"')
        variants = mutations.native_domain_separator(candidate, data)
        self.assertEqual(variants, [candidate.replace('"main", "query", 1', '"main", "delivery", 1')])
        self.assertEqual(mutations.native_domain_separator(candidate + candidate, data), [])
        self.assertEqual(mutations.native_domain_separator('parameters = ["retired-hex"]', data), [])

    def test_helper_symbols_and_native_naturals_remain_separate_from_bytes(self):
        data = self.fixture()
        data[7].append(["func.call", [["callee", ["symbol", ["helper"]]],
                       ["runtime.site", ["string", "call"]]], [], [], [], []])
        self.assertEqual(mutations.helper_names(data), {"helper"})
        candidate = ('    func.func private @helper() {\n'
                     '      parameters = [18446744073709551615 : ui64]\n'
                     '    }\n')
        self.assertEqual(mutations.native_helper_constant(candidate, data),
                         [candidate.replace('18446744073709551615', '0')])
        self.assertEqual(mutations.native_helper_constant(candidate.replace(
            '18446744073709551615 : ui64', '"7"'), data), [])
        data[7][-1][1][0][1][1] = ["root", "helper"]
        with self.assertRaises(ValueError):
            mutations.helper_names(data)

    def test_subject_driver_retains_all_occurrence_encoding_obligations(self):
        from bridges import subject
        from bridges.common.lean_render import encode_tree

        exported = self.fixture()
        generated = []

        class RenderedOnly(Exception):
            pass

        def capture(_subject, _path, text):
            generated.append(text)
            raise RenderedOnly

        selection = SimpleNamespace(
            name="fixture", construction_namespace="Fixture.Construction",
            module_name=lambda key: "Fixture." + key.title(),
            get=lambda _section, _key, default: default)
        driver = object.__new__(subject.Driver)
        with patch.object(driver, "lean", capture), self.assertRaises(RenderedOnly):
            driver.construction_rule(selection, {"exported": exported, "original": source([])}, {})
        trees = [["zkc.native-origin-template/0", "main", [], [], event] for event in [
            ["message", "main", "message", "schema", "P", "V"],
            ["query", "main", "query", "input_1", "random.bls12-381.fr/0", "draw", "V"],
            ["message", "main", "delivery", "schema", "V", "P"]]]
        expected = json.dumps([list(encode_tree(tree)) for tree in trees])
        self.assertIn(f"(Zkc.Construction.templateTree template).encode) = {expected}", generated[0])

    def test_scoped_native_request_keeps_index_decimal_encoding(self):
        sibling = str(Path(__file__).resolve().parents[1] / "bridges/structured")
        sys.path.insert(0, sibling)
        try:
            from bridges.structured.scoped import ScopedSuite
        finally:
            sys.path.remove(sibling)
        suite = object.__new__(ScopedSuite)
        suite.tools = {"lean": "unused-lean", "reference": "unused-reference"}
        requests = []

        def command(label, arguments):
            requests.append(json.loads(arguments[-1].read_text()))
            result = ["returned", ["7"]] if label.endswith(":ssa") else [
                "returned", [["field", "bls12-381.fr", "7"]]]
            return json.dumps(result)

        suite.command = command
        function = ["function", "main", "protocol", "public", [INDEX, BOOLEAN], [], [], [], [], []]
        data = source([], [function])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.json"
            suite.evaluate((path.with_suffix(".mlir"), path, data), "indices", [2**64 - 1, True], 7)
        self.assertEqual(requests, [[["index", 2**64 - 1], ["bool", True]],
                                    ["18446744073709551615", True]])


if __name__ == "__main__":
    unittest.main()
