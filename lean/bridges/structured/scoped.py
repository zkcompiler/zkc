#!/usr/bin/env python3
"""Fresh scoped Func/CF exports checked and evaluated by independent Lean.

These are bounded logical outcomes. They do not prove CFG correspondence,
resource equivalence, native execution, or cryptographic security.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import sys

from check import ROOT, Suite, definition, typed_value, write_json


class ScopedSuite(Suite):
    def tool_names(self):
        return ('compiler', 'lean')

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
        suite.case(label, lambda n=name, l=label, v=values, e=expected:
                   suite.evaluate(subjects[n], l, v, e))
    for i in range(suite.args.cases):
        x, y = (suite.rng.randrange(10000) for _ in range(2))
        count = suite.rng.randrange(8)
        suite.case(f'loop-{i}', lambda i=i, x=x, y=y, n=count:
                   suite.evaluate(subjects['Replace'], f'loop-{i}',
                                  [str(x), str(y), n], x if n == 0 else y))
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
        suite.case(label, lambda l=label, s=changed: suite.refuse_snapshot(l, s))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--lean', type=Path, default=ROOT / 'lean/.lake/build/bin/structured-source')
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--cases', type=int, default=16)
    parser.add_argument('--seed', type=int, default=73829)
    return ScopedSuite(parser.parse_args()).run(run_cases)


if __name__ == '__main__':
    sys.exit(main())
