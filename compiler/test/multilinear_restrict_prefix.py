"""Total prefix restriction: source formation, exact export and checked recipe."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import records

commands = Commands(records())
fixture = Path(__file__).parent / 'fixtures/structured-source/restrict_prefix.zkc'
flags = ['--source-format=zkc', '--entry=sample::Demo', f'--module=sample={fixture}']
child = compile_run_package(commands, *flags)
source = child['original']
interface = json.loads(child['interface'])
symbol = interface['protocol']

with case('exact-total-descriptor-and-native-recipe'):
    snapshot = json.loads(commands.source('protocol-structured', source, '--symbol=' + symbol))
    descriptors = [instruction[0] for row in snapshot[7] if row[0] == 'function'
                   for instruction in row[9][1]]
    assert ['multilinear.restrict_prefix', 'bls12-381.fr'] in descriptors
    assert 'multilinear.restrict_prefix' in child['artifact']
    assert 'algebra.multilinear_restrict_prefix' in source
    (commands.directory / 'restriction.json').write_text(json.dumps(snapshot))

with case('intrinsic-and-primitive-authoring-agree'):
    alternate = commands.directory / 'intrinsic.zkc'
    alternate.write_text(fixture.read_text().replace('residual=restrict_prefix(values,point)',
                                                     'residual=restrict_intrinsic(values,point)'))
    other = compile_run_package(commands, '--source-format=zkc', '--entry=sample::Demo',
                                f'--module=sample={alternate}')
    exported = json.loads(commands.source('protocol-structured', other['original'], '--symbol=' +
                                          json.loads(other['interface'])['protocol']))
    assert any(instruction[0] == ['multilinear.restrict_prefix', 'bls12-381.fr']
               for row in exported[7] if row[0] == 'function' for instruction in row[9][1])

with case('source-residual-relation-with-explicit-shape'):
    target = compile_run_package(commands, '--source-format=zkc', '--entry=sample::Check',
                                 f'--module=sample={fixture}')
    relation_snapshot = json.loads(commands.source('protocol-structured', target['original'],
        '--symbol=' + json.loads(target['interface'])['protocol']))
    assert len(relation_snapshot[5]) == 1
    assert relation_snapshot[5][0][3] == 'zkc.language.formula/0'
    assert len(relation_snapshot[5][0]) == 11 and relation_snapshot[5][0][6] == []
    assert relation_snapshot[5][0][9] == ['parameter', 'statement', 'statement', 'statement']
    assert 'multilinear.restrict_prefix' in json.dumps(relation_snapshot)
    (commands.directory / 'relation.json').write_text(json.dumps(relation_snapshot))


with case('exact-math-formation-and-export-refusals'):
    operation = '"algebra.multilinear_restrict_prefix"'
    assert operation in source
    # The Math profile rejects every attribute on this total operation.
    start = source.index(operation)
    at = source.index(' : ', start)
    bad = source[:at] + ' {unexpected = true}' + source[at:]
    commands.source('protocol-structured', bad, '--symbol=' + symbol,
                    refuses='mathematical-formation')
    # Installed Field vectors still require nominal agreement at every port.
    for inputs, output in [(('bls12-381.fr', 'bn254.fr'), 'bls12-381.fr'),
                           (('bls12-381.fr', 'bls12-381.fr'), 'bn254.fr')]:
        left, right = (f'!data.field_vector<"{d}">' for d in inputs)
        result = f'!data.field_vector<"{output}">'
        bad = f'''module {{
          func.func @bad(%xs:{left},%point:{right})->{result} {{
            %r = "algebra.multilinear_restrict_prefix"(%xs,%point) : ({left},{right})->{result}
            return %r : {result}
          }}
        }}'''
        commands.verified(bad, 'mathematical-formation')

commands.save()
print(f'multilinear-restrict-prefix: {counted()} cases; evidence: {commands.directory}')
