"""Declaration contracts are retained, checked metadata with unchanged execution."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, records

commands = Commands(records())
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
serial = 0


def selector(direction, port, role):
    return f'["{direction}", {port} : i64, "{role}"]'


def application(left, right, relation='Equal'):
    return f'[@{relation}, [{left}, {right}]]'


inputs = application(selector('input', 0, 'P'), selector('input', 1, 'Q'))
outputs = application(selector('output', 0, 'P'), selector('output', 1, 'Q'))
decision = selector('output', 2, 'Q')
clauses = [f'["target", "proof", {inputs}, unit, {decision}]',
           f'["input", "premise", {inputs}, unit, unit]',
           f'["output", "result", {outputs}, unit, unit]',
           f'["continuation", "reduction", {inputs}, {outputs}, {decision}]']
inventory = '[' + ', '.join(clauses) + ']'
helper = '''func.func private @predicate(%x:i1,%y:i1)->i1 {
  %equal = arith.cmpi eq, %x, %y : i1
  return %equal : i1
}'''
relation = '''relation.declare @Equal {kind="zkc.language.formula/0", key="Equal",
  revision="authored", signature=(i1,i1)->i1, purposes=["statement","witness"],
  formula=@predicate}'''
child = '''"protocol.func"() ({ ^entry(%x:i1,%y:i1,%n:ui64):
  %yes = arith.constant true
  "protocol.return"(%x,%y,%yes) : (i1,i1,i1)->()
}) {sym_name="child",origin=["child",[]], function_type=(i1,i1,ui64)->(i1,i1,i1),
  roles=["P","Q"], input_roles=[["P"],["Q"],["Q"]],
  output_roles=[["P"],["Q"],["Q"]], contracts=''' + inventory + '''} : ()->()'''
caller = '''"protocol.func"() ({ ^entry(%x:i1,%y:i1,%n:ui64):
  %a:3 = protocol.apply @child(%x,%y,%n) {roles=["A","B"],site="call"}
    : (i1,i1,ui64)->(i1,i1,i1)
  "protocol.return"(%a#0,%a#1,%a#2) : (i1,i1,i1)->()
}) {sym_name="main",origin=["main",[]], function_type=(i1,i1,ui64)->(i1,i1,i1),
  roles=["A","B"], input_roles=[["A"],["B"],["B"]],
  output_roles=[["A"],["B"],["B"]]} : ()->()'''


def module(*definitions):
    return 'module { "protocol.module"() ({\n' + '\n'.join(definitions) + \
        '\n}) {profile=#protocol.profile<protocol>} : ()->() }'


source = module(helper, relation, child, caller)


def export(text, refusal=None, symbol='main'):
    output = commands.source('protocol-structured', text, '--symbol=' + symbol,
                             refuses=refusal)
    return None if refusal else json.loads(output)


def run(text, refusal=None):
    global serial
    serial += 1
    path = commands.directory / f'contracts-{serial}.mlir'
    path.write_text(text)
    request = commands.write(f'contracts-{serial}.json',
                             ['zkc.structured-open-request/0', 'B',
                              [None, False, '7'], [], 1000000])
    output = commands.run([reference, 'open', path, 'main', request], refuses=refusal)
    return None if refusal else json.loads(output)


with case('source-component-contracts-use-the-existing-product-layout'):
    fixture = Path(__file__).parent / 'fixtures/structured-source/declaration-contracts.zkc'
    flags = ['--source-format=zkc', '--entry=sample::Demo', f'--module=sample={fixture}']
    package = compile_run_package(commands, *flags)
    emitted = package['original']
    interface = json.loads(package['interface'])
    snapshot = export(emitted, symbol=interface['protocol'])
    owners = dict(snapshot[8])
    assert owners[interface['protocol']] == []
    retained = next(clauses for clauses in owners.values() if clauses)
    assert [clause[0] for clause in retained] == ['target', 'input', 'output', 'continuation']
    assert retained[0][2][1] == [['input', 0, 'role00000000'],
                                ['input', 1, 'role00000000'],
                                ['input', 2, 'role00000001']]
    assert retained[3][3][1] == [['output', 0, 'role00000000'],
                                ['output', 1, 'role00000000'],
                                ['output', 2, 'role00000001']]
    assert retained[3][4] == ['output', 3, 'role00000001']
    assert snapshot[5][0][9] == interface['relations'][0]['definition']['function']
    prepared = commands.verified(emitted, None, '--zkc-prepare-protocol')
    assert export(prepared, symbol=interface['protocol'])[8] == snapshot[8]


with case('all-contracts-and-explicit-formula-independent-of-selected-entry'):
    snapshot = export(source)
    assert len(snapshot) == 10 and len(snapshot[5][0]) == 10
    assert snapshot[5][0][-1] == 'predicate'
    assert [row[0] for row in snapshot[8]] == ['child', 'main']
    table = dict(snapshot[8])
    assert table['main'] == []
    assert table['child'] == [
        ['target', 'proof', ['Equal', [['input', 0, 'P'], ['input', 1, 'Q']]],
         None, ['output', 2, 'Q']],
        ['input', 'premise', ['Equal', [['input', 0, 'P'], ['input', 1, 'Q']]], None, None],
        ['output', 'result', ['Equal', [['output', 0, 'P'], ['output', 1, 'Q']]], None, None],
        ['continuation', 'reduction', ['Equal', [['input', 0, 'P'], ['input', 1, 'Q']]],
         ['Equal', [['output', 0, 'P'], ['output', 1, 'Q']]], ['output', 2, 'Q']]]
    assert export(source, symbol='child')[8] == snapshot[8]
    assert all(op[0][0] != 'statement' for definition in snapshot[7]
               if definition[0] == 'function' for op in definition[9][1])
    assert run(source) == ['zkc.structured-open-result/0',
                           ['returned', [None, False, True]], [], 0]
    assert run(source.replace(', contracts=' + inventory, '')) == run(source)

with case('exact-helper-rename-survives-without-hash-name-inference'):
    renamed = source.replace('@predicate', '@arbitrary_exact_helper')
    assert export(renamed)[5][0][-1] == 'arbitrary_exact_helper'
    assert run(renamed) == run(source)

with case('two-proof-entries-retain-exact-target-and-decision-role'):
    fixture = Path(__file__).parent / 'fixtures/structured-source/selected-targets.zkc'
    selections = {}
    for entry, target, role in [('Left', 'left', 'role00000000'),
                                ('Right', 'right', 'role00000001')]:
        flags = ['--source-format=zkc', f'--entry=sample::{entry}',
                 f'--module=sample={fixture}']
        emitted = commands.run([compiler, 'language-emit', *flags])
        interface = json.loads(commands.run([compiler, 'language-interface', *flags]))
        owner = interface['protocol']
        snapshot = export(emitted, symbol=owner)
        definition = next(row for row in snapshot[7] if row[1] == owner)
        descriptor = definition[9][1][0][0]
        assert len(descriptor) == 5 and descriptor[0] == 'statement'
        assert descriptor[4] == target
        clause = next(row for row in dict(snapshot[8])[owner] if row[1] == target)
        assert clause[4] == ['output', 0, role]
        prepared = commands.verified(emitted, None, '--zkc-prepare-protocol')
        prepared_snapshot = export(prepared, symbol=owner)
        prepared_owner = next(row for row in prepared_snapshot[7] if row[1] == owner)
        assert prepared_owner[9][1][0][0] == descriptor
        projected = commands.verified(prepared, None, '--zkc-project-protocol')
        assert f'target = "{target}"' not in projected
        assert 'contracts =' not in projected
        selections[target] = emitted, snapshot, descriptor, projected
    assert selections['left'][0] != selections['right'][0]
    assert selections['left'][1] != selections['right'][1]
    assert selections['left'][1][8] == selections['right'][1][8]
    assert selections['left'][2][:4] == selections['right'][2][:4]
    assert selections['left'][3] == selections['right'][3]

with case('non-root-continuation-survives-application-expansion-and-export'):
    prepared = commands.verified(source, None, '--zkc-prepare-protocol')
    assert export(prepared)[8] == export(source)[8]
    assert 'protocol.apply' not in prepared
    assert run(prepared) == run(source)
    projected = commands.verified(prepared, None, '--zkc-project-protocol')
    assert 'contracts =' not in projected and 'formula =' not in projected
    executable = commands.verified(projected, None, '--zkc-lower-math')
    without_contracts = source.replace(', contracts=' + inventory, '')
    unchanged = commands.verified(without_contracts, None, '--zkc-prepare-protocol',
                                  '--zkc-project-protocol', '--zkc-lower-math')
    assert executable == unchanged

with case('structured-contract-inventory-bound'):
    many = '[' + ', '.join(clauses[1].replace('"premise"', f'"premise{i}"')
                           for i in range(513)) + ']'
    changed = source.replace(inventory, many)
    commands.verified(changed)
    export(changed, 'structured-source-limit')
    run(changed, 'structured-reference-capacity')

for label, changed in [
    ('missing-formula', source.replace(',\n  formula=@predicate', '')),
    ('absent-helper', source.replace('formula=@predicate', 'formula=@missing')),
    ('wrong-helper-kind', source.replace('formula=@predicate', 'formula=@child')),
    ('local-is-not-math', source.replace(helper, '''local.func @predicate(%x:i1,%y:i1)->i1 {
       local.return %x : i1 }''')),
    ('full-input-abi', source.replace(helper, '''func.func private @predicate(%x:i1)->i1 {
       return %x : i1 }''')),
    ('full-output-abi', source.replace(helper, '''func.func private @predicate(%x:i1,%y:i1)->(i1,i1) {
       return %x,%y : i1,i1 }''')),
    ('external-helper', source.replace(helper, 'func.func private @predicate(i1,i1)->i1')),
    ('opaque-formula-link', source.replace('zkc.language.formula/0', 'external')),
]:
    with case(label):
        commands.verified(changed, 'relation-formula')
        export(changed, 'structured-source-original')
        run(changed, 'structured-reference-source')

mutations = [
    ('wrong-clause-owner', inventory.replace('"P"', '"A"')),
    ('unavailable-role', inventory.replace(selector('input', 0, 'P'), selector('input', 0, 'Q'))),
    ('absent-role', inventory.replace('"P"', '"Missing"')),
    ('wrong-type', inventory.replace(selector('input', 1, 'Q'), selector('input', 2, 'Q'))),
    ('out-of-range-port', inventory.replace('0 : i64', '9 : i64')),
    ('negative-port', inventory.replace('0 : i64', '-1 : i64')),
    ('port-width', inventory.replace('0 : i64', '0 : i32')),
    ('wrong-relation', inventory.replace('@Equal', '@predicate')),
    ('missing-relation', inventory.replace('@Equal', '@Missing')),
    ('missing-operand', inventory.replace(inputs, '[@Equal, []]')),
    ('malformed-kind', inventory.replace('"continuation"', '"unknown"')),
    ('malformed-direction', inventory.replace('"input", 0', '"unknown", 0')),
    ('missing-residual', inventory.replace(', ' + outputs + ', ' + decision, ', unit, ' + decision)),
    ('residual-without-output', inventory.replace(', ' + outputs + ', ' + decision, ', ' + inputs + ', ' + decision)),
    ('input-with-output', inventory.replace(clauses[1], f'["input", "premise", {outputs}, unit, unit]')),
    ('output-without-output', inventory.replace(clauses[2], f'["output", "result", {inputs}, unit, unit]')),
    ('noncontinuation-residual', inventory.replace(clauses[0], f'["target", "proof", {inputs}, {outputs}, {decision}]')),
    ('missing-target-decision', inventory.replace(clauses[0], f'["target", "proof", {inputs}, unit, unit]')),
    ('input-decision', inventory.replace(clauses[1], f'["input", "premise", {inputs}, unit, {decision}]')),
    ('decision-input', inventory.replace(decision, selector('input', 1, 'Q'))),
    ('decision-unavailable', inventory.replace(decision, selector('output', 2, 'P'))),
    ('duplicate-clause', '[' + clauses[0] + ', ' + clauses[0] + ']'),
    ('extra-clause-field', '[' + clauses[0][:-1] + ', unit]]'),
    ('extra-selector-field', inventory.replace('0 : i64, "P"]', '0 : i64, "P", unit]')),
]
for label, changed in mutations:
    with case(label):
        malformed = source.replace(inventory, changed)
        commands.verified(malformed, 'protocol-contract')
        export(malformed, 'structured-source-original')
        run(malformed, 'structured-reference-source')

with case('contracts-on-math-helper-refused'):
    changed = source.replace('->i1 {', '->i1 attributes {contracts=[]} {', 1)
    export(changed, 'structured-source-original')
    run(changed, 'structured-reference-source')

with case('nonboolean-decision-refused'):
    changed = source.replace('(%x,%y,%yes)', '(%x,%y,%n)').replace(
        '(i1,i1,i1)', '(i1,i1,ui64)')
    commands.verified(changed, 'protocol-contract')
    export(changed, 'structured-source-original')
    run(changed, 'structured-reference-source')

statement = '"protocol.statement"(%x,%y) {relation=@Equal, selectors=["P","Q"], acceptance=2:i64, target="proof"} : (i1,i1)->()'
selected = module(helper, relation, child.replace('%yes =', statement + '\n%yes ='))
with case('selected-entry-statement-agrees-with-retained-target'):
    snapshot = export(selected, symbol='child')
    assert snapshot[8][0][1][0][1] == 'proof'
    assert next(row for row in snapshot[7] if row[1] == 'child')[9][1][0][0][-1] == 'proof'

for label, contract in [('no-contract-attribute', None),
                        ('only-nontarget-clauses', '[' + clauses[1] + ']'),
                        ('matching-target', inventory)]:
    with case('unnamed-standalone-statement-' + label):
        standalone = selected.replace(', target="proof"', '')
        standalone = standalone.replace(', contracts=' + inventory,
                                         '' if contract is None else ', contracts=' + contract)
        snapshot = export(standalone, symbol='child')
        assert next(row for row in snapshot[7] if row[1] == 'child')[9][1][0][0][-1] is None

for label, changed in [
    ('missing-name', selected.replace('target="proof"', 'target="missing"')),
    ('empty-name', selected.replace('target="proof"', 'target=""')),
    ('wrong-clause-kind', selected.replace('target="proof"', 'target="premise"')),
    ('omitted-contract-attribute', selected.replace(', contracts=' + inventory, '')),
    ('empty-contract-inventory', selected.replace(inventory, '[]')),
    ('dormant-owner', module(helper, relation,
                            child.replace(', contracts=' + inventory, '').replace(
                                '%yes =', statement + '\n%yes ='),
                            child.replace('sym_name="child"', 'sym_name="dormant"'))),
]:
    with case('named-target-' + label):
        commands.verified(changed, 'protocol-contract-statement')
        export(changed, 'structured-source-original', 'child')

with case('unnamed-statement-still-refuses-mismatching-retained-targets'):
    changed = selected.replace(', target="proof"', '').replace('acceptance=2', 'acceptance=1')
    commands.verified(changed, 'protocol-contract-statement')
    export(changed, 'structured-source-original', 'child')

with case('dormant-selected-target-does-not-select-the-export-root'):
    dormant = child.replace('%yes =', statement + '\n%yes =')
    root = child.replace('sym_name="child"', 'sym_name="main"').replace(inventory, '[]')
    snapshot = export(module(helper, relation, dormant, root))
    assert snapshot[3] == 'main' and dict(snapshot[8])['main'] == []
    definitions = {row[1]: row for row in snapshot[7]}
    assert definitions['child'][9][1][0][0][-1] == 'proof'
    assert not any(op[0][0] == 'statement' for op in definitions['main'][9][1])

for name in ['plain', 'claim.with.dot', 'bad name', '証明', 'x' * 512]:
    with case('native-selected-clause-name-' + name[:16]):
        changed = selected.replace('"proof"', json.dumps(name, ensure_ascii=False))
        snapshot = export(changed, symbol='child')
        assert snapshot[8][0][1][0][1] == name
        assert next(row for row in snapshot[7] if row[1] == 'child')[9][1][0][0][-1] == name

for name in ['', 'x' * 513, '証' * 171]:
    with case('invalid-native-clause-name-bytes-' + str(len(name.encode()))):
        changed = selected.replace('"proof"', json.dumps(name, ensure_ascii=False))
        commands.verified(changed, 'protocol-contract')
        export(changed, 'structured-source-original', 'child')

for label, changed in [
    ('acceptance', selected.replace('acceptance=2', 'acceptance=1')),
    ('operand', selected.replace('"protocol.statement"(%x,%y)', '"protocol.statement"(%x,%x)').replace('selectors=["P","Q"]', 'selectors=["P","P"]')),
    ('relation', selected.replace('relation=@Equal', 'relation=@Other').replace(relation, relation + '\n' + relation.replace('@Equal', '@Other').replace('key="Equal"', 'key="Other"'))),
]:
    with case('selected-entry-mismatch-' + label):
        commands.verified(changed, 'protocol-contract-statement')
        export(changed, 'structured-source-original', 'child')

commands.save()
print(f'structured-contracts: {counted()} cases')
