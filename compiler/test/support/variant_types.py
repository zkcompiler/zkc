"""Independent structured MLIR aggregate fixtures, not an admission checker."""
import json


def identity(value):
    if isinstance(value, str):
        return ['atom', value]
    return ['tuple', [identity(child) for child in value]]


def logical_type(value):
    if isinstance(value, list):
        return variant(*value)
    if value in ('bool', 'index'):
        return 'i1' if value == 'bool' else 'ui64'
    head, domain = value.split(':', 1)
    constructors = {
        'field': 'algebra.field', 'group': 'algebra.group',
        'vector': 'algebra.field_vector', 'matrix': 'algebra.field_matrix',
        'point': 'poly.point', 'table': 'poly.multilinear',
    }
    if head == 'proof':
        return f'!commitment.polynomial<{json.dumps(domain)}, "proof">'
    return f'!{constructors[head]}<{json.dumps(domain)}>'


def variant(nominal, alternatives):
    term = json.dumps(identity(nominal), ensure_ascii=False, separators=(', ', ': '))
    arms = []
    for label, payload in alternatives:
        fields = ', [' + ', '.join(map(logical_type, payload)) + ']' if payload else ''
        arms.append(f'#data.alternative<{json.dumps(label)}{fields}>')
    return '!data.variant<#data.identity<' + term + '>, [' + ', '.join(arms) + ']>'
