#!/usr/bin/env python3
"""Render actual export data as transparent Lean constructors, without proof axioms."""
import json
import re


def array(value, length=None):
    if not isinstance(value, list) or (length is not None and len(value) != length):
        raise ValueError('constructed-source-shape')
    if len(value) > 2048:
        raise ValueError('constructed-source-limit')
    return value


def text(value):
    if not isinstance(value, str) or len(value) > 262144 or not value.isascii():
        raise ValueError('constructed-source-string')
    if any(ord(c) < 32 and c not in '\n\r\t' for c in value):
        raise ValueError('constructed-source-string')
    return json.dumps(value)


def natural(value):
    if type(value) is not int or not 0 <= value <= 8192:
        raise ValueError('constructed-source-natural')
    return str(value)


def seq(values, render=text):
    return '[' + ', '.join(render(v) for v in array(values)) + ']'


def primitive(value):
    name, attrs, binding, origin, args, results = array(value, 6)
    return '⟨' + ', '.join([text(name), text(attrs), text(binding), text(origin), seq(args), seq(results)]) + '⟩'


def instruction(value):
    array(value)
    if value and value[0] == 'apply':
        _, op, args = array(value, 3)
        return f'.apply ({primitive(op)}) {seq(args, natural)}'
    if value and value[0] == 'project':
        _, types, index, ref = array(value, 4)
        return f'.project {seq(types)} {natural(index)} {natural(ref)}'
    if value and value[0] == 'guard':
        _, ref, attrs = array(value, 3)
        return f'.guard {natural(ref)} {text(attrs)}'
    if value and value[0] == 'stop':
        _, reason, attrs = array(value, 3)
        if reason not in ('reject', 'abort', 'exhausted', 'incomplete', 'refused'):
            raise ValueError('constructed-source-stop')
        return f'.stop .{reason} {text(attrs)}'
    raise ValueError('constructed-source-instruction')


def handler(value):
    return '⟨' + ', '.join(text(v) for v in array(value, 3)) + '⟩'


def render(data, namespace):
    array(data, 12)
    if data[0] != 'zkc.constructed-source/0':
        raise ValueError('constructed-source-format')
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)*', namespace):
        raise ValueError('constructed-source-namespace')
    fields = list(zip(['source', 'candidate', 'entry', 'role', 'participant', 'policy'],
                      map(text, data[1:7])))
    fields += [('handlers', seq(data[7], handler)), ('inputs', seq(data[8])),
               ('outputs', seq(data[9])), ('instructions', seq(data[10], instruction)),
               ('returned', seq(data[11], natural))]
    return ('module\n\npublic import Zkc.Source.Constructed\n\n@[expose] public section\n\n'
            '/-! Generated from the actual checked native candidate. -/\n'
            'set_option autoImplicit false\n\n'
            f'namespace {namespace}\nopen Zkc.Source.Constructed\n\n'
            'def snapshot : Snapshot where\n' +
            '\n'.join(f'  {key} := {value}' for key, value in fields) +
            '\n\nset_option maxRecDepth 8192 in\n'
            'set_option maxHeartbeats 2000000 in\n'
            'theorem admitted : snapshot.check.isOk = true := by decide +kernel\n'
            '\ndef imported : Imported snapshot := snapshot.imported admitted\n'
            '\ntheorem imported_checked : snapshot.check = .ok imported :=\n'
            '  snapshot.imported_checked admitted\n'
            f'\nend {namespace}\n')
