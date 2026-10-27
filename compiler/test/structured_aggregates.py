"""Nominal products and ordered sequences in the structured source profile."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records
from variant_codec import descriptor

commands = Commands(records())
source = (Path(__file__).parent / 'fixtures/structured-source/aggregate-fold.mlir').read_text()


def export(text, refusal=None):
    result = commands.source('protocol-structured', text, '--symbol=main', refuses=refusal)
    return None if refusal else json.loads(result)


with case('sequence fold retains exact nominal product and components'):
    snapshot = export(source)
    definitions = {definition[1]: definition for definition in snapshot[7]}
    query = ['product', '["query","bls12-381.fr"]', 'value',
             [['bool'], ['field', 'bls12-381.fr']]]
    sequence = ['sequence', query]
    assert definitions['main'][4] == [sequence]
    assert snapshot[4] == [['domain', 'queries', [sequence], [['elements', 0]], 0]]
    assert definitions['step'][4] == [['bool'], query, sequence]
    body = definitions['step'][9][1]
    assert body[0][:4] == [['product.get', 0], [1], [['bool']], []]
    assert body[1][:4] == [['product.get', 1], [2], [['field', 'bls12-381.fr']], []]
    assert definitions['make'][9][1][0][:4] == [
        ['product.make', 'value'], [0, 1], [query], []]

with case('same shape different product identity remains distinct'):
    old = descriptor(['query', 'bls12-381.fr'], [('value', ['bool', 'field:bls12-381.fr'])])
    new = descriptor(['other', 'bls12-381.fr'], [('value', ['bool', 'field:bls12-381.fr'])])
    changed = source.replace(old, new)
    assert changed != source
    snapshot = export(changed)
    definitions = {definition[1]: definition for definition in snapshot[7]}
    assert definitions['main'][4][0][1][1] == '["other","bls12-381.fr"]'

for name, before, after in [
    ('wrong component type', 'index=0:i64', 'index=1:i64'),
    ('missing component', 'index=1:i64', 'index=2:i64'),
    ('wrong constructor', 'alternative="value"', 'alternative="absent"'),
]:
    with case(name):
        export(source.replace(before, after), 'structured-source-original')

with case('multi constructor variants require a separate admitted profile'):
    new = descriptor(['query', 'bls12-381.fr'], [('value', ['bool', 'field:bls12-381.fr']), ('none', [])])
    # A valid unused declaration still belongs to whole-unit admission.
    unused = f'func.func private @unused(%x:!data.variant<{json.dumps(new)}>)->!data.variant<{json.dumps(new)}> {{ return %x : !data.variant<{json.dumps(new)}> }}'
    export(source.replace('  func.func private @make', unused + '\n  func.func private @make'),
           'structured-source-product')

with case('product identity obeys the wire string bound'):
    old = descriptor(['query', 'bls12-381.fr'], [('value', ['bool', 'field:bls12-381.fr'])])
    new = descriptor(['query', 'q' * 600], [('value', ['bool', 'field:bls12-381.fr'])])
    export(source.replace(old, new), 'structured-source-limit')

counted()
