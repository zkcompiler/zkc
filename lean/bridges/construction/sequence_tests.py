#!/usr/bin/env python3
"""Exact static Type roots, persistent sequence ports, and Math/Local meanings."""
import copy
import unittest

from render import operation, sort

INDEX = ["apply", "index", []]
BOOL = ["apply", "bool", []]
RECORD = ["variant", ["tuple", [["atom", "test.record"]]], [["Record", [INDEX, INDEX]]]]
SEQUENCE = ["apply", "sequence", [["type", RECORD]]]
ATTRS = {"binding": ("symbol", ["installed"]), "parameters": ("array", []), "site": ("string", "access")}


class Sequences(unittest.TestCase):
    def checked(self, contract, inputs, outputs, element=RECORD):
        return operation("exec.apply", ATTRS, [contract, [["type", element]], "", inputs, outputs],
                         [sort(ty)[1] for ty in inputs], [sort(ty)[1] for ty in outputs], [[], []])

    def test_checked_sequence_ports(self):
        for contract, inputs, outputs, expected in [
                ("sequence.empty", [], [SEQUENCE], "sequenceEmpty"),
                ("sequence.append", [SEQUENCE, RECORD], [SEQUENCE], "sequenceAppend"),
                ("sequence.length", [SEQUENCE], [INDEX], "sequenceLength"),
                ("sequence.at", [SEQUENCE, INDEX], [RECORD], "sequenceAt")]:
            with self.subTest(contract=contract):
                result = self.checked(contract, inputs, outputs)
                self.assertTrue(result.startswith(f".execute (.{expected} (.product "))

    def test_same_carrier_does_not_erase_element_identity(self):
        for changed in [BOOL, copy.deepcopy(RECORD)]:
            if changed != BOOL:
                changed[1][1][0][1] = "another.record"
            with self.subTest(element=changed), self.assertRaises(ValueError):
                self.checked("sequence.at", [SEQUENCE, INDEX], [RECORD], changed)
        changed = copy.deepcopy(RECORD)
        changed[2][0][0] = "AnotherConstructor"
        with self.assertRaises(ValueError):
            self.checked("sequence.append", [SEQUENCE, changed], [SEQUENCE])

    def test_index_and_element_ports_are_checked(self):
        for inputs, outputs in [([SEQUENCE, BOOL], [RECORD]), ([SEQUENCE, INDEX], [BOOL]),
                                ([INDEX, SEQUENCE], [RECORD])]:
            with self.subTest(inputs=inputs), self.assertRaises(ValueError):
                self.checked("sequence.at", inputs, outputs)

    def test_math_and_local_are_separate(self):
        for name, inputs, outputs, constructor in [
                ("data.sequence_empty", [], [SEQUENCE], "sequenceEmpty"),
                ("data.sequence_append", [SEQUENCE, RECORD], [SEQUENCE], "sequenceAppend"),
                ("data.sequence_length", [SEQUENCE], [INDEX], "sequenceLength")]:
            with self.subTest(name=name):
                result = operation(name, {}, [], [sort(ty)[1] for ty in inputs],
                                   [sort(ty)[1] for ty in outputs], [[], []])
                self.assertTrue(result.startswith(f".calculate (.{constructor} (.product "))
                with self.assertRaises(ValueError):
                    operation(name, {"other": ("bool", True)}, [],
                              [sort(ty)[1] for ty in inputs], [sort(ty)[1] for ty in outputs], [[], []])
        with self.assertRaises(ValueError):
            operation("data.sequence_append", {}, [], [sort(SEQUENCE)[1], sort(BOOL)[1]],
                      [sort(SEQUENCE)[1]], [[], []])

    def test_logical_handle_is_not_sequence_payload(self):
        handle = ["apply", "service", [["domain", "Service", "secret"]]]
        with self.assertRaises(ValueError):
            self.checked("sequence.empty", [], [["apply", "sequence", [["type", handle]]]], handle)


if __name__ == "__main__":
    unittest.main()
