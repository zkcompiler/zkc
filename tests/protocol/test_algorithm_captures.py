"""Inlining must coalesce duplicable capture aliases in every local region."""
import json

import pytest
from journal import Journal
from variant_codec import descriptor


@pytest.mark.parametrize('kind', ['if', 'match', 'for', 'nested'])
def test_inlined_capture_aliases(toolchain, directory, kind):
    conditional = ['if', 'branch', 'ok', ['x', 'y'],
                   [['yield', ['x']]], [['yield', ['y']]], ['out']]
    body = [['apply', 'alias', 'Identity', [], ['x'], ['y']]]
    if kind == 'if':
        body.append(conditional)
    elif kind == 'nested':
        # Rewriting the parent's arguments must also reach inner captures.
        body.append(['if', 'outer', 'ok', ['x', 'y', 'ok'],
                     [conditional, ['yield', ['out']]], [['yield', ['y']]], ['result']])
    elif kind == 'match':
        ty = descriptor('Choice', [['Here', []], ['There', []]])
        body += [['variant', 'tag', ty, 'Here', [], 'tag'],
                 ['match', 'choose', 'tag', ['x', 'y'],
                  [['Here', [], [['yield', ['x']]]],
                   ['There', [], [['yield', ['y']]]]], ['out']]]
    else:
        body.append(['for', 'repeat', 'i', 'lo', 'hi', [['acc', 'x']], ['x', 'y'],
                     [['yield', ['y']]], ['out']])
    body.append(['return', ['result' if kind == 'nested' else 'out']])
    inputs = [['x', 'index'], ['lo', 'index'], ['hi', 'index'], ['ok', 'bool']]
    source = ['zkc.protocol/1', [],
              [['function', 'Identity', [['x', 'index']], ['index'], [['return', ['x']]], ['Identity', []]],
               ['function', 'Work', inputs, ['index'], body, ['Work', []]]],
              [['protocol', 'Main', ['P'], [], [], [], [], []]], [], []]
    source[3][0][4] = [[name, 'P', ty] for name, ty in inputs]
    source[3][0][5] = [['P', 'index']]
    source[3][0][7] = [['local', 'run', 'P', 'Work', [p[0] for p in inputs], ['answer']], ['return', ['answer']]]
    source[4] = [['instance', 'concrete', 'Main', [], [], [['P', 'P']]]]
    source[5] = [['entry', 'main', 'concrete']]
    journal = Journal(directory)
    path = journal.write('source.json', source)
    expanded = json.loads(journal.run([toolchain.compiler, 'protocol-expand', path]))
    def check(body):
        for ins in body:
            if ins[0] == 'if':
                assert len(ins[3]) == len(set(ins[3]))
                check(ins[4]); check(ins[5])
            elif ins[0] == 'match':
                assert len(ins[3]) == len(set(ins[3]))
                for arm in ins[4]: check(arm[2])
            elif ins[0] == 'for':
                assert len(ins[6]) == len(set(ins[6]))
                check(ins[7])
    check(next(f[4] for f in expanded[2] if f[1] == 'Work'))
    physical = json.loads(journal.run([toolchain.compiler, 'protocol-compile', path]))
    plan = journal.write('physical.json', physical)
    result = json.loads(journal.run([toolchain.checker('interactive-protocol'), '--check', path, plan]))
    assert result[0] == 'checked'
    journal.save()
