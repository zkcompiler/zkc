#!/usr/bin/env python3
"""Fresh scoped Func/CF compared with independent native SSA and checked Lean.

These are bounded logical outcomes. They do not prove CFG correspondence,
resource equivalence, native execution, or cryptographic security.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import sys

from check import MODULUS, ROOT, Suite, definition, typed_value, write_json


class ScopedSuite(Suite):
    def tool_names(self):
        return ('compiler', 'reference', 'lean')

    def subject(self, name):
        fixture = ROOT / 'compiler/test/fixtures/structured-source/scoped-control.zkc'
        original = self.command(name + ':emit', [
            self.tools['compiler'], 'language-emit', '--source-format=zkc',
            f'--module=scoped_control={fixture}', '--subject=scoped_control::' + name])
        symbol = re.search(r'"protocol.func"[^\n]*sym_name = "([^"]+)"', original)[1]
        return self.export(name, original, symbol)

    def evaluate(self, subject, label, values, expected):
        entry = definition(subject[2], subject[2][3])
        request = subject[1].parent / (label + '.inputs.json')
        write_json(request, [typed_value(ty, value)
                            for ty, value in zip(entry[4], values, strict=True)])
        actual = json.loads(self.command(label, [self.tools['lean'], 'run', subject[1], request]))
        result = ['stopped', 'reject'] if expected is None else [
            'returned', [['field', 'bls12-381.fr', str(expected)]]]
        if actual != result:
            raise AssertionError({'expected': result, 'actual': actual})
        native_request = request.with_suffix('.native.json')
        native_inputs = [str(value) if ty == ['index'] else value
                         for ty, value in zip(entry[4], values, strict=True)]
        write_json(native_request, native_inputs)
        native = json.loads(self.command(label + ':ssa', [self.tools['reference'],
                            subject[0], subject[2][3], native_request]))
        native_expected = ['stopped', 'reject'] if expected is None else ['returned', [str(expected)]]
        if native != native_expected:
            raise AssertionError({'expected': native_expected, 'native': native})


def domain_cases(suite):
    fixtures = ROOT / 'compiler/test/fixtures/structured-source'
    source = (fixtures / 'tuple-domains.mlir').read_text()
    for kind in ('product', 'zip'):
        subject = suite.export('domain-' + kind, source.replace('domain_product', 'domain_' + kind))
        for index, (left, right) in enumerate([([], []), ([], [3]), ([2, 7], [1, 4]), ([2], [1, 4])]):
            expected = ['stopped', 'refused']
            if kind == 'product' or len(left) == len(right):
                pairs = [(a, b) for a in left for b in right] if kind == 'product' else zip(left, right)
                result = 5
                for a, b in pairs:
                    result = (result * 10 + a - b) % MODULUS
                expected = ['returned', [str(result)]]
            inputs = [list(map(str, left)), list(map(str, right)), '5']
            label = f'{kind}-tuples-{index}'
            suite.case(label, lambda s=subject, n=label, i=inputs, e=expected: suite.compare(s, n, i, e))
        if kind == 'product':
            request = suite.directory / 'product-capacity.json'
            write_json(request, [['1'] * 70, ['2'] * 70, '5'])
            def capacity_refusal():
                number = len(suite.commands)
                output = suite.command('product-capacity', [suite.tools['reference'],
                    subject[0], subject[2][3], request], success=False)
                diagnostic = (suite.directory / f'command-{number:04d}.stderr').read_text()
                if output.strip() or 'structured-reference-capacity' not in diagnostic:
                    raise AssertionError({'output': output, 'diagnostic': diagnostic})
            suite.case('product-capacity-is-diagnostic', capacity_refusal)
    unused = source.replace('    %pairs =',
        '    %unused = "data.domain_zip"(%left,%right) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>\n    %pairs =')
    subject = suite.export('unused-domain-admission', unused)
    suite.case('unused-domain-admission', lambda: suite.compare(subject, 'unused-domain-admission',
        [[], ['3'], '5'], ['stopped', 'refused']))
    subject = suite.export('domain-range', (fixtures / 'range-domain.mlir').read_text())
    for lower, upper, expected in [(0, 0, 42), (3, 2, 42), (4, 8, 7), (2**64-2, 2**64-1, 2**64-2)]:
        label = f'range-{lower}-{upper}'
        suite.case(label, lambda n=label, lo=lower, hi=upper, e=expected:
                   suite.compare(subject, n, [str(lo), str(hi), '42'], ['returned', [str(e)]]))


def run_cases(suite):
    subjects = {name: suite.subject(name)
                for name in ('Choose', 'Replace', 'Require', 'Compute', 'Last')}
    for name, values, expected in [
        ('Choose', ['7', '11', True], 7),
        ('Choose', ['7', '11', False], 11),
        ('Replace', ['7', '11', 0], 7),
        ('Replace', ['7', '11', 3], 11),
        ('Require', ['7', True], 7),
        ('Require', ['7', False], None),
        ('Compute', ['7', '11'], 18),
        ('Last', [[], '7', False], 7),
        ('Last', [['11', '13'], '7', True], 13),
        ('Last', [['11', '13'], '7', False], None),
    ]:
        label = f'{name}-{len(suite.checks)}'
        suite.case(label, lambda n=name, label=label, v=values, e=expected:
                   suite.evaluate(subjects[n], label, v, e))
    for i in range(suite.args.cases):
        x, y = (suite.rng.randrange(10000) for _ in range(2))
        count = suite.rng.randrange(8)
        suite.case(f'loop-{i}', lambda i=i, x=x, y=y, n=count:
                   suite.evaluate(subjects['Replace'], f'loop-{i}',
                                  [str(x), str(y), n], x if n == 0 else y))
    source = subjects['Choose'][0].read_text()
    call = re.search(r'"protocol.local_call"\(([^)]+)\)', source)
    operands = call[1].split(', ')
    swapped = source[:call.start(1)] + ', '.join([operands[1], operands[0], *operands[2:]]) + source[call.end(1):]
    helpers = re.findall(r'"func.call"[^\n]*callee = @([^}>]+)', source)
    if len(helpers) != 2 or helpers[0] == helpers[1]:
        raise AssertionError('expected two distinct branch callbacks')
    redirected = source.replace('callee = @' + helpers[0], 'callee = @temporary_swap', 1)
    redirected = redirected.replace('callee = @' + helpers[1], 'callee = @' + helpers[0], 1)
    redirected = redirected.replace('callee = @temporary_swap', 'callee = @' + helpers[1], 1)
    for label, changed in [('swapped-entry-operands', swapped), ('retargeted-branch', redirected)]:
        subject = suite.export(label, changed, subjects['Choose'][2][3])
        suite.case(label, lambda s=subject, n=label: suite.evaluate(s, n, ['7', '11', True], 11))

    # Native formation accepts this unused Math helper. The independent Fr-only
    # observer must still reject its unsupported field before evaluating Choose.
    marker = '    "protocol.func"'
    helper = '''    func.func private @dormant_field() -> !algebra.field<"bn254.fr"> {
      %value = "algebra.constant"() <{value = "1"}> : () -> !algebra.field<"bn254.fr">
      func.return %value : !algebra.field<"bn254.fr">
    }
'''
    dormant = source.replace(marker, helper + marker, 1)
    path = suite.directory / 'dormant-instruction.mlir'
    path.write_text(dormant)
    request = suite.directory / 'dormant-inputs.json'
    write_json(request, ['7', '11', True])
    def dormant_refusal():
        number = len(suite.commands)
        suite.command('dormant-native-instruction', [suite.tools['reference'], path,
                      subjects['Choose'][2][3], request], success=False)
        diagnostic = (suite.directory / f'command-{number:04d}.stderr').read_text()
        if 'structured-reference-unsupported' not in diagnostic:
            raise AssertionError(diagnostic)
    suite.case('dormant-native-instruction', dormant_refusal)
    snapshot = subjects['Choose'][2]
    local = next(d for d in snapshot[7] if d[2] == 'local')
    for label, mutate in [
        ('out-of-scope-formal', lambda d: d[9][1][0][3][0][2][2][1].__setitem__(0, 99)),
        ('wrong-branch-result-sort', lambda d: d[9][1][0][3][0][1].__setitem__(0, ['bool'])),
        ('missing-occurrence', lambda d: d[9][1][0].__setitem__(4, '')),
        ('unchecked-scope-port', lambda d: d[4].insert(0, ['scope'])),
    ]:
        changed = copy.deepcopy(snapshot)
        mutate(definition(changed, local[1]))
        suite.case(label, lambda label=label, s=changed: suite.refuse_snapshot(label, s))
    domain_cases(suite)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--lean', type=Path, default=ROOT / 'lean/.lake/build/bin/structured-source')
    parser.add_argument('--reference', type=Path,
                        default=ROOT / 'build/compiler/test/zkc-structured_reference-test')
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--cases', type=int, default=16)
    parser.add_argument('--seed', type=int, default=73829)
    return ScopedSuite(parser.parse_args()).run(run_cases)


if __name__ == '__main__':
    sys.exit(main())
