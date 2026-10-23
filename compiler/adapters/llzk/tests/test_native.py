#!/usr/bin/env python3
"""Check actual normalized relations, bindings and auxiliary assignments."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ADAPTER = Path(sys.argv.pop(1)).resolve()
NATIVE = Path(sys.argv.pop(1)).resolve()
HERE = Path(__file__).resolve().parents[1]
P = 52435875175126190479447740508185965837690552500527637822603658699938581184513


class Native(unittest.TestCase):
    def setUp(self):
        self.workspace = tempfile.TemporaryDirectory(prefix='zkc-llzk-native-')
        self.addCleanup(self.workspace.cleanup)
        self.root = Path(self.workspace.name)

    def imported(self, name, text, inputs='a', outputs='out', refuses=None):
        source = self.root / (name + '.llzk')
        source.write_text(text)
        out = self.root / name
        command = [sys.executable, str(HERE / 'import_relation.py'), str(source),
                   '--adapter', str(ADAPTER), '--native', str(NATIVE),
                   '--field', 'bls12381', '--entry', 'Main',
                   '--outputs', outputs, '--public-inputs', inputs, '--output', str(out)]
        result = subprocess.run(command, text=True, capture_output=True, timeout=90)
        if refuses:
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(refuses, result.stderr)
            self.assertFalse(out.exists())
            return None
        self.assertEqual(result.returncode, 0, result.stderr)
        receipt = json.loads((out / 'receipt.json').read_text())
        self.assertEqual(receipt['source_sha256'], hashlib.sha256(source.read_bytes()).hexdigest())
        return out

    def evaluate(self, out, assignment, statement=None):
        statement = assignment[1:3] if statement is None else statement
        sp, ap = self.root / 'statement.json', self.root / 'assignment.json'
        sp.write_text(json.dumps(list(map(str, statement))))
        ap.write_text(json.dumps(list(map(str, assignment))))
        result = subprocess.run([str(NATIVE), 'relation-evaluate', str(out / 'relation.json'),
                                 str(sp), str(ap)], text=True, capture_output=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)

    def test_cubic_witness_extension_and_dishonest_auxiliaries(self):
        out = self.imported('cubic', (HERE / 'fixtures/cubic.llzk').read_text())
        binding = json.loads((out / 'native-binding.json').read_text())
        self.assertEqual(int(binding['columns']), 4)
        self.assertEqual(int(binding['constraints']), 2)
        # This fixture's checked layout is ONE, out, a, square. Honest
        # extension is distinct from checking arbitrary auxiliary values.
        for a in [0, 1, 2, 7, P - 1]:
            square, cube = a*a % P, a*a*a % P
            self.assertTrue(self.evaluate(out, [1, cube, a, square])['satisfied'])
            self.assertFalse(self.evaluate(out, [1, cube, a, (square + 1) % P])['satisfied'])
            self.assertFalse(self.evaluate(out, [1, (cube + 1) % P, a, square])['satisfied'])
        # Finite arbitrary-assignment projection control, not a general proof.
        for a in range(4):
            for square in range(10):
                for claimed in [a**3 % P, (a**3 + 1) % P]:
                    accepted = self.evaluate(out, [1, claimed, a, square])['satisfied']
                    self.assertEqual(accepted, square == a*a and claimed == a**3)

    def test_one_and_public_prefix_are_separate_checks(self):
        out = self.imported('cubic', (HERE / 'fixtures/cubic.llzk').read_text())
        for assignment, statement in [([0, 8, 2, 4], [8, 2]),
                                      ([1, 8, 2, 4], [9, 2]),
                                      ([1, 8, 2, 4], [2, 8])]:
            report = self.evaluate(out, assignment, statement)
            self.assertFalse(report['bound'])
            self.assertFalse(report['satisfied'])

    def test_source_identity_is_distinct_from_target_identity(self):
        text = (HERE / 'fixtures/cubic.llzk').read_text()
        left = self.imported('original', text)
        right = self.imported('comment', '// exact source bytes changed\n' + text)
        lreceipt = json.loads((left / 'receipt.json').read_text())
        rreceipt = json.loads((right / 'receipt.json').read_text())
        self.assertNotEqual(lreceipt['source_sha256'], rreceipt['source_sha256'])
        lbound = json.loads((left / 'native-binding.json').read_text())
        rbound = json.loads((right / 'native-binding.json').read_text())
        self.assertEqual(lbound['subject'], rbound['subject'])

    def test_wrong_public_names_refuse_before_publication(self):
        text = (HERE / 'fixtures/cubic.llzk').read_text()
        self.imported('input', text, inputs='other', refuses='llzk-public-inputs')
        self.imported('output', text, outputs='other', refuses='llzk-public-outputs')

    def test_zero_equations_do_not_use_compute_as_constraints(self):
        text = (HERE / 'fixtures/cubic.llzk').read_text().replace(
            '      constrain.eq %out, %cube : !felt.type<"bls12381">\n', '')
        out = self.imported('unconstrained', text)
        binding = json.loads((out / 'native-binding.json').read_text())
        self.assertEqual(int(binding['columns']), 3)
        self.assertEqual(int(binding['constraints']), 0)
        # compute(2) returns 8, but the source has no acceptance constraint.
        self.assertTrue(self.evaluate(out, [1, 123, 2])['satisfied'])
        self.assertFalse(self.evaluate(out, [0, 123, 2])['satisfied'])
        self.assertFalse(self.evaluate(out, [1, 123, 2], [8, 2])['satisfied'])

    def test_unused_public_input_keeps_its_ordered_wire(self):
        text = (HERE / 'fixtures/cubic.llzk').read_text().replace(
            'function.arg_name = "a", llzk.pub})',
            'function.arg_name = "a", llzk.pub}, '
            '%b: !felt.type<"bls12381"> {function.arg_name = "b", llzk.pub})')
        out = self.imported('unused', text, inputs='a,b')
        binding = json.loads((out / 'native-binding.json').read_text())
        self.assertEqual(int(binding['columns']), 5)
        self.assertEqual(binding['public_inputs'], ['a', 'b'])
        self.assertTrue(self.evaluate(out, [1, 8, 2, 5, 4], [8, 2, 5])['satisfied'])
        self.assertFalse(self.evaluate(out, [1, 8, 2, 5, 4], [8, 5, 2])['satisfied'])
        self.imported('reordered', text, inputs='b,a', refuses='llzk-public-inputs')


if __name__ == '__main__':
    unittest.main()
