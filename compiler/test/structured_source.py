"""Original structured export, exact coordinates and strict profile refusals."""
import hashlib
import json
import re
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records

commands = Commands(records())
fixtures = Path(__file__).parent / 'fixtures'
field = ['field', 'bls12-381.fr']
vector = ['vector', 'bls12-381.fr']
boolean = ['bool']
index = ['index']
total = (fixtures / 'finite/total-state.mlir').read_text()
unit = (fixtures / 'finite/unit-state.mlir').read_text()
loops = (fixtures / 'structured-source/loops-and-captures.mlir').read_text()
math = (fixtures / 'structured-source/math-operations.mlir').read_text()
bls_rows = [
    ['nominal', 'bls12-381.fr', 'Field',
     [['PairingG1', 'bls12-381.g1'], ['PairingG2', 'bls12-381.g2'], ['PairingGT', 'bls12-381.gt']],
     ['Field', 'CommRing', 'PrimeField', 'CharacteristicNotTwo', 'PairingField'],
     '52435875175126190479447740508185965837690552500527637822603658699938581184513'],
    ['nominal', 'bls12-381.g2', 'Group', [['Scalar', 'bls12-381.fr']], ['Group', 'ScalarAction'], None],
    ['nominal', 'bls12-381.gt', 'Group', [['Scalar', 'bls12-381.fr']], ['Group', 'ScalarAction'], None],
    ['nominal', 'bls12-381.g1', 'Group', [['Scalar', 'bls12-381.fr']], ['Group', 'ScalarAction'], None],
]
bls_service = ['service', 'random.bls12-381.fr/0', 'bls12-381.fr', ['draw']]


def export(source, refusal=None, symbol='main'):
    result = commands.source('protocol-structured', source, '--symbol=' + symbol,
                             refuses=refusal)
    return None if refusal else json.loads(result)


def table(snapshot):
    return {definition[1]: definition for definition in snapshot[7]}


def instructions(definition):
    return definition[9][1]


def mutate(source, before, after, count=-1):
    assert before in source, f"missing mutation target: {before}"
    return source.replace(before, after, count)


def helper_body(source, name, body):
    """Replace one scoped body, retaining its exact declared ports."""
    header = re.search(r'(?m)^( *)func.func[^\n]*@' + re.escape(name) + r'\([^\n]* \{\n', source)
    assert header, name
    end = source.index('\n' + header[1] + '}', header.end())
    return source[:header.end()] + body + source[end:]


def simple(declarations='', body='', result='%flag'):
    return '''module { "protocol.module"() ({
''' + declarations + '''
"protocol.func"() ({ ^entry(%flag:i1):
''' + body + '''
"protocol.return"(''' + result + ''') : (i1)->()
}) {sym_name="main",origin=["main",[]],function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }'''


with case('original-total-state-and-exact-ssa-order'):
    data = export(total)
    assert len(data) == 11
    # The catalogue slot carries the rows of every identity used, closed under
    # associated members, in native catalogue order.
    assert data[9] == [bls_rows, []]
    assert data[:2] == ['zkc.structured-source/0', 'original']
    assert data[2] == 'sha256:' + hashlib.sha256(total.encode()).hexdigest()
    assert data[3] == 'main' and data[5] == []
    assert table(data)['main'][6] == ['protocol', ['P'], [['P'], ['P'], ['P']], [['P'], ['P']]]
    assert data[4] == [['domain', 'items', [vector], [['indices', 0, 0]], 0]]
    defs = table(data)
    assert list(defs) == ['step', 'main']
    assert defs['step'][2:4] == ['math', 'private']
    assert defs['step'][7:9] == [[['index_bound', 2, 3, 0]], []]
    assert defs['step'][9] == ['block', [
        [['bounded_at', 'bls12-381.fr'], [3, 2], [field], [], '']
    ], ['return', [2, 0]]]
    assert defs['main'][9] == ['block', [
        [['fold', 'items', 'step', ''], [0, 1, 2], [field, field], [], '']
    ], ['return', [0, 1]]]
    assert export(total + '\n')[2] != data[2]

with case('original-unit-state-keeps-zero-result-effects-and-origin'):
    data = export(unit)
    defs = table(data)
    assert data[4] == [['domain', 'items', [vector], [['elements', 0]], 0]]
    assert defs['_finite_admission_0'] == ['finite', '_finite_admission_0', 'private', [vector, boolean], [],
                            'items', 'step', 'predicate']
    assert defs['step'][8:] == [['step', []], ['block', [], ['stop', 'abort', 'body_stop']]]
    assert defs['predicate'][9][2] == ['return', [2]]
    assert defs['work'][9] == ['block', [
        [['apply', '_finite_admission_0'], [0, 1], [], [], 'fold']
    ], ['return', [1]]]
    assert instructions(defs['main'])[0][0] == ['local_call', 'work', 'P']

with case('semantic-mutations-remain-distinct-accepted-subjects'):
    reversed_data = export(total.replace('func.return %b,%v', 'func.return %v,%b'))
    assert table(reversed_data)['step'][9][2] == ['return', [0, 2]]
    assert table(export(unit.replace('reason="abort"', 'reason="reject"')))['step'][9][2][1] == 'reject'
    normal = helper_body(unit, 'step', '   %ok = \"exec.returned\"() : ()->!exec.outcome<>\n   func.return %ok : !exec.outcome<>')
    assert table(export(normal))['step'][9][2] == ['return', []]

with case('nested-multi-result-and-zero-result-conditionals'):
    data = export((fixtures / 'structured-source/nested-controls.mlir').read_text())
    defs = table(data)
    outer = instructions(defs['step'])[0]
    assert outer[0] == ['if'] and outer[1] == [4, 0, 1, 2, 4]
    assert outer[2] == [field, field]
    assert outer[3][0][0] == [field, field, field, boolean]
    inner = outer[3][0][2][1][0]
    assert inner[1] == [3, 0, 1, 2]
    assert inner[3][0][2][2] == ['yield', [1, 2]]
    empty = instructions(defs['work'])[1]
    assert empty[2] == [] and empty[1] == [5]
    assert empty[3][0] == [[], [], ['block', [], ['yield', []]]]
    assert empty[3][1][2][2] == ['stop', 'abort', 'disabled']

with case('ordinary-and-conditional-for-exact-captures-and-zero-state'):
    defs = table(export(loops, symbol='entry'))
    assert defs['swap'][8] == ['original_swap', [['Field', 'bls12-381.fr'], ['Group', 'bls12-381.g1']]]
    ops = instructions(defs['control'])
    loop = ops[0]
    assert loop[0] == ['for'] and loop[1] == [4, 5, 0, 1, 2, 3, 6]
    region = loop[3][0]
    assert region[:2] == [[index, field, field, field, field, boolean],
                           [field, field, field, field, boolean]]
    assert region[2][1][0][1] == [5, 1, 2, 3, 4]
    assert region[2][2] == ['yield', [1, 0, 5, 6, 7]]
    empty = ops[1]
    assert empty[2] == [] and empty[1] == [6, 7, 8]
    assert empty[3][0][:2] == [[index, boolean], [boolean]]
    assert empty[3][0][2][1][0][:3] == [['if'], [1], []]
    assert empty[3][0][2][1][0][3][1][2][2] == ['stop', 'reject', 'check_failed']
    conditional = ops[2]
    assert conditional[0] == ['for_condition']
    assert conditional[3][0][1] == [boolean, field, field, field, field, boolean]
    assert conditional[3][0][2][2] == ['condition', [5, 2, 1, 3, 4, 5]]
    assert ops[3][0] == ops[4][0] == ['apply', 'swap']
    assert ops[3][1] == [0, 1] and ops[4][1] == [8, 9]
    assert defs['control'][9][2] == ['return', [2, 1]]

with case('stop-only-loop-keeps-enclosing-output-abi'):
    stopped = mutate(loops,
        '%8 = "exec.complete"(%arg0, %7, %6) : (!S, !F, !F) -> !exec.outcome<(!F, !F)>\n      return %8 : !exec.outcome<(!F, !F)>',
        '%abort = "exec.reject"(%arg0) {reason="abort",site="loop_stop"} : (!S)->!exec.stop\n      cf.br ^bb2(%abort : !exec.stop)')
    region = instructions(table(export(stopped, symbol='entry'))['control'])[0][3][0]
    assert region[1] == [field, field, field, field, boolean]
    assert region[2][2] == ['stop', 'abort', 'loop_stop']

with case('shared-fold-retained-once-with-distinct-actuals'):
    defs = table(export((fixtures / 'structured-source/shared-fold.mlir').read_text()))
    folds = instructions(defs['main'])
    assert folds[0][0] == folds[1][0] == ['fold', 'items', 'step', '']
    assert folds[0][1] != folds[1][1]
    assert list(defs).count('step') == 1

with case('math-vocabulary-and-shared-multi-result-helper'):
    defs = table(export(math))
    ops = instructions(defs['arithmetic'])
    assert [op[0][0] for op in ops] == [
        'field.constant', 'field.add', 'field.subtract', 'field.multiply',
        'field.equal', 'bool.constant', 'bool.and', 'bool.or', 'bool.xor',
        'bool.equal', 'bool.not_equal', 'select']
    assert ops[0][0] == ['field.constant', 'bls12-381.fr', '1']
    assert all(op[4] == '' for op in ops)
    calls = instructions(defs['main'])
    assert calls[0][1] == [0, 1, 2] and calls[1][1] == [3, 2, 4]
    assert defs['main'][9][2] == ['return', [2, 0, 3, 1]]

with case('unused-definitions-retained-and-names-not-special'):
    dead = 'func.func private @unused(%x:i1) -> i1 { return %x : i1 }'
    data = export(simple(dead).replace('sym_name="main"', 'sym_name="alternate"'), symbol='alternate')
    assert list(table(data)) == ['unused', 'alternate']
    assert table(data)['unused'][9] == ['block', [], ['return', [0]]]

with case('domain-extra-formals-and-selected-container-retained'):
    changed = total.replace('^entry(%xs:!V):', '^entry(%other:!V,%xs:!V):').replace(
        'function_type=(!V)->!data.domain<ui64>', 'function_type=(!V,!V)->!data.domain<ui64>')
    changed = changed.replace('%i:ui64,%xs:!V)', '%i:ui64,%other:!V,%xs:!V)').replace(
        '#data.index_bound<2,3,0>', '#data.index_bound<2,4,0>')
    changed = changed.replace('"algebra.finite_fold"(%xs,%a,%b)', '"algebra.finite_fold"(%xs,%xs,%a,%b)').replace(
        ': (!V,!F,!F)->(!F,!F)', ': (!V,!V,!F,!F)->(!F,!F)')
    data = export(changed)
    assert data[4][0][2:] == [[vector, vector], [['indices', 1, 0]], 0]
    assert table(data)['step'][7] == [['index_bound', 2, 4, 0]]

with case('scoped-boolean-constant-site-retained'):
    literal = helper_body(unit, 'predicate', '''   %literal = "exec.boolean"(%scope) {value=true,site="literal"} : (!runtime.scope)->!exec.outcome<(i1)>
   "exec.dispatch"(%literal)[^done,^failed] : (!exec.outcome<(i1)>)->()
 ^done(%yes:i1):
   %result = "exec.returned"(%yes) : (i1)->!exec.outcome<(i1)>
   func.return %result : !exec.outcome<(i1)>
 ^failed(%cause:!exec.stop):
   %failed = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(i1)>
   func.return %failed : !exec.outcome<(i1)>''')
    assert instructions(table(export(literal))['predicate']) == [
        [['bool.constant', True], [], [boolean], [], 'literal']]

recursive = helper_body(unit, 'predicate', '''   %call = func.call @predicate(%scope,%item,%xs,%enabled) {runtime.site="recurse"}
       : (!runtime.scope,!F,!V,i1)->!exec.outcome<(i1)>
   "exec.dispatch"(%call)[^done,^failed] : (!exec.outcome<(i1)>)->()
 ^done(%yes:i1):
   %result = "exec.returned"(%yes) : (i1)->!exec.outcome<(i1)>
   func.return %result : !exec.outcome<(i1)>
 ^failed(%cause:!exec.stop):
   %failed = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(i1)>
   func.return %failed : !exec.outcome<(i1)>''')

# Require actual source mutations and retain the failure at its owning boundary.
for name, source, code in [
    ('missing-precondition', total.replace(' attributes {data.preconditions=[#data.index_bound<2,3,0>]}', ''), 'finite-bound'),
    ('wrong-bound-position', total.replace('index_bound<2,3,0>', 'index_bound<0,3,0>'), 'finite-bound'),
    ('wrong-axis', total.replace('axis=0:i64', 'axis=1:i64'), 'finite-domain'),
    ('unused-malformed-helper', simple('func.func private @dead(%x:i1) -> i1 { return }'), 'structured-source-original'),
    ('loop-capture-identity', mutate(loops, 'call @control_0(%18, %15, %16#0, %16#1, %arg3, %arg4, %arg7)', 'call @control_0(%18, %15, %16#0, %16#1, %arg4, %arg3, %arg7)'), 'structured-source-original'),
    ('dormant-arm-yield', mutate(loops, '"exec.complete"(%arg0, %arg1, %arg4) : (!S, !F, !F)', '"exec.complete"(%arg0, %arg1) : (!S, !F)'), 'structured-source-original'),
    ('duplicate-site', mutate(loops, 'runtime.site = "second"', 'runtime.site = "first"'), 'structured-source-original'),
    ('malformed-origin', mutate(unit, 'runtime.origin=["work",[]]', 'runtime.origin=["work"]'), 'structured-source-original'),
    ('cycle', recursive, 'structured-source-original'),
]:
    with case(name):
        export(source, code, 'entry' if re.search(r'sym_name\s*=\s*"entry"', source) else 'main')

for name, source, code in [
    ('unknown-symbol', total, 'structured-source-symbol'),
    ('wrong-profile', 'module { module {} }', 'structured-source-profile'),
    ('multiple-units', 'module { module {} module {} }', 'structured-source-module'),
    ('whole-original-first', 'module { malformed }', 'structured-source-original'),
    ('outer-attribute', simple().replace('module {', 'module attributes {source.unexpected=true} {', 1), 'structured-source-attribute'),
    ('unit-attribute', simple().replace('profile=#protocol.profile<protocol>', 'profile=#protocol.profile<protocol>,unexpected=true'), 'structured-source-original'),
    ('function-attribute', simple().replace('sym_name="main"', 'unexpected=true,sym_name="main"'), 'structured-source-original'),
    ('return-attribute', simple().replace('"protocol.return"(%flag)', '"protocol.return"(%flag) {unexpected=true}'), 'structured-source-original'),
    ('unused-math-attribute', simple('func.func private @dead(%x:i1) -> i1 attributes {unexpected=true} { return %x : i1 }'), 'structured-source-original'),
    ('math-operation-attribute', simple(body='%x = arith.xori %flag,%flag {unexpected=true} : i1'), 'structured-source-original'),

    ('unsupported-type', simple('func.func private @dead(%x:!data.bytes) -> !data.bytes { return %x : !data.bytes }'), 'structured-source-type'),
    ('unsupported-comparison', simple(body='%x = arith.cmpi ult,%flag,%flag : i1'), 'structured-source-original'),
    ('role-count-limit', simple().replace('roles=["P"]', 'roles=[' + ','.join(json.dumps(x) for x in ['P'] + [f'R{i}' for i in range(16)]) + ']', 1), 'structured-source-role'),
    ('long-name', simple().replace('sym_name="main"', 'sym_name="' + 'x' * 513 + '"'), 'structured-source-limit'),
    # Complete source definition admission rejects these before export begins.
    ('empty-symbol', simple('func.func private @""(%x:i1) -> i1 { return %x : i1 }'), 'structured-source-original'),
    ('used-empty-symbol', simple('func.func private @""(%x:i1) -> i1 { return %x : i1 }',
                                '%r = func.call @""(%flag) : (i1)->i1', '%r'), 'structured-source-original'),
    ('depth-limit', 'module {' * 66 + '}' * 66, 'mlir-depth-limit'),
    ('instruction-limit', simple(body='\n'.join(f'%x{i} = arith.xori %flag,%flag : i1' for i in range(4097))), 'structured-source-limit'),
    ('definition-limit', simple('\n'.join(f'func.func private @h{i}(%x:i1) -> i1 {{ return %x : i1 }}' for i in range(128))), 'structured-source-limit'),
]:
    with case(name):
        symbol = 'absent' if name == 'unknown-symbol' else 'x' * 513 if name == 'long-name' else 'main'
        export(source, code, symbol)

with case('stored-unused-domain-constructor-is-retained'):
    source = mutate(total, '%d = "data.domain_indices"',
        '%extra = "data.domain_indices"(%xs) {axis=0:i64} : (!V)->!data.domain<ui64>\n%d = "data.domain_indices"')
    assert export(source)[4] == [['domain', 'items', [vector],
                                 [['indices', 0, 0], ['indices', 0, 0]], 0]]

with case('strict-command-options'):
    for options in [[], ['--symbol='], ['--symbol=main', '--no-simplify'],
                    ['--symbol=main', '--symbol=main']]:
        commands.source('protocol-structured', total, *options, refuses='unsupported-option')

indexed = (fixtures / 'structured-source/indexed-helper.mlir').read_text()
with case('bounded-read-preconditions-instantiated-through-helper'):
    defs = table(export(indexed))
    assert defs['read'][7] == [['index_bound', 1, 0, 0]]
    assert defs['step'][7] == [['index_bound', 1, 2, 0]]
    assert instructions(defs['step'])[0] == [['call', 'read'], [2, 1], [field], [], '']

with case('same-typed-wrong-container-at-call'):
    export(indexed.replace('func.call @read(%xs,%i)', 'func.call @read(%other,%i)'), 'finite-bound')

with case('native-origin-bindings-retained-exactly'):
    changed = mutate(unit, 'runtime.origin=["work",[]]', 'runtime.origin=["work",[["Field","bls12-381.fr"]]]')
    assert table(export(changed))['work'][8] == ['work', [['Field', 'bls12-381.fr']]]

with case('condition-native-type-check-precedes-export-profile'):
    source = mutate(loops, '"exec.test"(%arg0, %arg6) <{site = "choose"}> : (!S, i1)',
                     '"exec.test"(%arg0, %arg2) <{site = "choose"}> : (!S, !F)')
    export(source, 'structured-source-original', 'entry')

with case('unused-unsupported-provider-declaration'):
    binding = '"runtime.binding"() {sym_name="product",contract="vector.product",arguments=["bls12-381.fr"],implementation="",function_type=(!runtime.scope, !algebra.field_vector<"bls12-381.fr">) -> !exec.outcome<(!algebra.field<"bls12-381.fr">)>} : ()->()'
    export(simple(binding), 'structured-source-binding')

with case('unsupported-collect'):
    export((fixtures / 'finite/total-collect.mlir').read_text(), 'structured-source-operation')

with case('unsupported-affine-helper-signature'):
    helper = '''func.func private @resource(%scope:!runtime.scope,%s:!runtime.capability<rng, "bls12-381.fr">)
        ->!exec.outcome<(!runtime.capability<rng, "bls12-381.fr">)> attributes {no_inline,runtime.origin=["resource",[]]} {
      %r = "exec.returned"(%s) : (!runtime.capability<rng, "bls12-381.fr">)->!exec.outcome<(!runtime.capability<rng, "bls12-381.fr">)>
      func.return %r : !exec.outcome<(!runtime.capability<rng, "bls12-381.fr">)>
    }'''
    export(simple(helper), 'structured-source-type')

with case('other-installed-identities-export-their-rows'):
    # Natively admitted identities export with their rows; Lean admits only the
    # rows of its own catalogue.
    group = simple('func.func private @dead(%x:!algebra.group<"bn254.g1">) -> !algebra.group<"bn254.g1"> { return %x : !algebra.group<"bn254.g1"> }')
    nominals, services = export(group)[9]
    assert [row[1] for row in nominals] == ['bn254.fr', 'bn254.g1', 'bn254.g2', 'bn254.gt'] and services == []
    assert nominals[1] == ['nominal', 'bn254.g1', 'Group', [['Scalar', 'bn254.fr']], ['Group', 'ScalarAction'], None]
    source = simple().replace('^entry(%flag:i1)', '^entry(%flag:i1,%service:!protocol.service_ref<"random.bn254.fr/0">)').replace(
        'function_type=(i1)->i1', 'function_type=(i1,!protocol.service_ref<"random.bn254.fr/0">)->i1').replace(
        'input_roles=[["P"]]', 'input_roles=[["P"],["P"]]')
    nominals, services = export(source)[9]
    assert services == [['service', 'random.bn254.fr/0', 'bn254.fr', ['draw']]]
    assert [row[1] for row in nominals] == ['bn254.fr', 'bn254.g1', 'bn254.g2', 'bn254.gt']

with case('binary-and-extension-identities-export-their-rows'):
    # Rows are native data whatever the characteristic: a binary field records
    # its characteristic as its modulus, and an extension exports its base.
    def dead(identity):
        value = f'!algebra.field<"{identity}">'
        return simple(f'func.func private @dead(%x:{value}) -> {value} {{ return %x : {value} }}')
    binary = 'gf2-64.pentanomial-4-3-1'
    nominals, services = export(dead(binary + '.ext3-trinomial1'))[9]
    assert nominals == [
        ['nominal', binary, 'Field', [], ['Field', 'CommRing'], '2'],
        ['nominal', binary + '.ext3-trinomial1', 'Field', [['BaseField', binary]],
         ['ExtensionField', 'Field', 'CommRing'], '2']] and services == []
    nominals, _ = export(dead('koala-bear.ext4-binomial3'))[9]
    assert {row[1] for row in nominals} == {'koala-bear.ext4-binomial3', 'koala-bear'}
    extension = next(row for row in nominals if row[1] == 'koala-bear.ext4-binomial3')
    assert extension[3:] == [[['BaseField', 'koala-bear']],
                               ['TwoAdicField', 'Field', 'CommRing', 'CharacteristicNotTwo', 'ExtensionField'],
                               '2130706433']

with case('field-embedding-retains-nominal-binding-and-ports'):
    base, extension = 'koala-bear', 'koala-bear.ext4-binomial3'
    base_type, extension_type = f'!algebra.field<"{base}">', f'!algebra.field<"{extension}">'
    declarations = f'''
"runtime.binding"() {{sym_name="embed",contract="field.embed",arguments=["{extension}"],implementation="",function_type=(!runtime.scope,{base_type})->!exec.outcome<({extension_type})>}} : ()->()
func.func private @embed_helper(%scope:!runtime.scope,%x:{base_type}) -> !exec.outcome<({extension_type})>
    attributes {{no_inline,runtime.origin=["embed_helper",[]]}} {{
  %r = "exec.apply"(%scope,%x) {{binding=@embed,parameters=[],site="embedding"}} : (!runtime.scope,{base_type})->!exec.outcome<({extension_type})>
  "exec.dispatch"(%r)[^done,^failed] : (!exec.outcome<({extension_type})>)->()
^done(%y:{extension_type}):
  %ok = "exec.returned"(%y) : ({extension_type})->!exec.outcome<({extension_type})>
  func.return %ok : !exec.outcome<({extension_type})>
^failed(%cause:!exec.stop):
  %bad = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<({extension_type})>
  func.return %bad : !exec.outcome<({extension_type})>
}}
'''
    data = export(simple(declarations))
    assert data[6] == [['binding', 'embed', 'field.embed', [extension], '']]
    assert table(data)['embed_helper'][4:6] == [[['field', base]], [['field', extension]]]
    assert instructions(table(data)['embed_helper']) == [
        [['exec', 'exec.apply', 'embed', []], [0], [['field', extension]], [], 'embedding']]

with case('unsupported-service-contract'):
    source = simple().replace('^entry(%flag:i1)', '^entry(%flag:i1,%service:!protocol.service_ref<"random.other/0">)').replace(
        'function_type=(i1)->i1', 'function_type=(i1,!protocol.service_ref<"random.other/0">)->i1').replace(
        'input_roles=[["P"]]', 'input_roles=[["P"],["P"]]')
    export(source, 'structured-source-original')

with case('communication-and-statement-retained'):
    data = export((fixtures / 'mathematical/schnorr-services.mlir').read_text())
    assert len(data[5]) == 1
    assert instructions(table(data)['main'])[0][0] == ['statement', 'schnorr_relation', ['Bob', 'Bob', 'Alice'], 0, None]

with case('unsupported-static-relation-annotation'):
    helper = 'func.func private @equal(%a:!algebra.field_vector<"bls12-381.fr">,%b:!algebra.field_vector<"bls12-381.fr">) -> i1 attributes {data.preconditions=[#data.equal_extent<0,0,1,0>]} { %yes = arith.constant true\n return %yes : i1 }'
    export(simple(helper), 'structured-source-precondition')

with case('invalid-utf8-must-not-crash-or-repair-json'):
    helper = r'func.func private @"\FF"(%x:i1) -> i1 { return %x : i1 }'
    export(simple(helper), 'structured-source-string')

with case('source-byte-limit'):
    export('//' + ' ' * (16 * 1024 * 1024), 'byte-limit')

with case('signature-limit'):
    args = ','.join(f'%a{i}:i1' for i in range(513))
    export(simple(f'func.func private @wide({args}) -> i1 {{ return %a0 : i1 }}'), 'structured-source-limit')

with case('maximum-instruction-and-reference-coordinate'):
    body = '\n'.join(f'%x{i} = arith.xori %flag,%flag : i1' for i in range(4096))
    data = export(simple(body=body))
    assert len(instructions(table(data)['main'])) == 4096
    assert table(data)['main'][9][2] == ['return', [4096]]

with case('reference-coordinate-limit-with-multiple-results'):
    helper = 'func.func private @pair(%x:i1) -> (i1,i1) { return %x,%x : i1,i1 }'
    body = '\n'.join(f'%r{i}:2 = func.call @pair(%flag) : (i1)->(i1,i1)' for i in range(2050))
    export(simple(helper, body), 'structured-source-limit')

with case('domain-table-limit'):
    declaration = total[total.index(' "data.domain"'):total.index(' func.func')]
    additions = '\n'.join(declaration.replace('sym_name="items"', f'sym_name="unused{i}"') for i in range(128))
    export(total.replace(' func.func', additions + '\n func.func', 1), 'structured-source-limit')

with case('wire-depth-counts-all-arrays'):
    nested = '{}'
    for _ in range(15):
        nested = 'if flag { ' + nested + ' } else {}'
    source = commands.directory / 'nested-wire.zkc'
    source.write_text('module nested; fn work(flag:bool)->bool { ' + nested + '; return flag; }\n'
                     'protocol Run roles(P)(flag:bool@P)->(r:bool@P) { return work(flag); }')
    actual = commands.run([commands.tool, 'language-emit', '--source-format=zkc',
                           f'--module=nested={source}', '--subject=nested::Run'])
    symbol = re.search(r'"protocol.func"[^\n]*sym_name = "([^"]+)"', actual)[1]
    export(actual, 'structured-source-limit', symbol)

with case('helper-dag-keeps-shared-definitions-once'):
    helpers = ['func.func private @h0(%x:i1) -> i1 { return %x : i1 }']
    for i in range(1, 11):
        helpers.append(f'func.func private @h{i}(%x:i1) -> i1 {{ %a = func.call @h{i-1}(%x) : (i1)->i1\n %b = func.call @h{i-1}(%a) : (i1)->i1\n return %b : i1 }}')
    data = export(simple('\n'.join(helpers), '%r = func.call @h10(%flag) : (i1)->i1', '%r'))
    assert len(data[7]) == 12
    assert sum(len(instructions(d)) for d in data[7]) == 21
    assert len(json.dumps(data)) < 10000

with case('snapshot-byte-limit'):
    args = ','.join(f'%a{i}:i1' for i in range(512))
    results = ','.join(['i1'] * 512)
    values = ','.join(f'%a{i}' for i in range(512))
    helpers = '\n'.join(f'func.func private @h{i}({args}) -> ({results}) {{ return {values} : {results} }}' for i in range(110))
    export(simple(helpers), 'structured-source-limit')

with case('exact-file-byte-limit-includes-final-newline'):
    args = ','.join(f'%a{i}:i1' for i in range(512))
    results = ','.join(['i1'] * 512)
    values = ','.join(f'%a{i}' for i in range(512))
    names = [f'h{i}' for i in range(93)]
    def sized_source():
        return simple('\n'.join(f'func.func private @{name}({args}) -> ({results}) '
                                f'{{ return {values} : {results} }}' for name in names))
    base = commands.source('protocol-structured', sized_source(), '--symbol=main')
    padding = 1024 * 1024 - len(base.encode())
    assert 0 <= padding <= sum(512 - len(name) for name in names)
    for i, name in enumerate(names):
        size = min(padding, 512 - len(name))
        names[i] += 'x' * size
        padding -= size
    exact = commands.source('protocol-structured', sized_source(), '--symbol=main')
    assert exact.endswith('\n') and len(exact.encode()) == 1024 * 1024
    names[-1] += 'y'
    assert len(names[-1]) <= 512
    export(sized_source(), 'structured-source-limit')

with case('all-native-stop-reasons-preserved'):
    for reason in ['abort', 'reject', 'exhausted', 'incomplete', 'refused']:
        defs = table(export(unit.replace('reason="abort"', 'reason="' + reason + '"')))
        assert defs['step'][9][2] == ['stop', reason, 'body_stop']

with case('only-protocol-root-can-be-selected'):
    export(total, 'structured-source-symbol', 'step')

with case('ordinary-zero-result-math-call-is-retained'):
    helper = 'func.func private @empty(%x:i1) { func.return }'
    data = export(simple(helper, 'func.call @empty(%flag) : (i1)->()'))
    assert table(data)['empty'][5] == []
    assert instructions(table(data)['main']) == [[['call', 'empty'], [0], [], [], '']]

with case('ordinary-zero-result-local-helper-sharing'):
    helper = '''func.func private @empty(%scope:!runtime.scope,%flag:i1)->!exec.outcome<>
        attributes {no_inline,runtime.origin=["empty",[]]} {
      %ok = "exec.returned"() : ()->!exec.outcome<>
      func.return %ok : !exec.outcome<>
    }
'''
    source = mutate(unit, ' func.func @work', helper + ' func.func @work')
    source = helper_body(source, 'work', '''   %first = func.call @empty(%scope,%enabled) {runtime.site="first"} : (!runtime.scope,i1)->!exec.outcome<>
   "exec.dispatch"(%first)[^second,^failed] : (!exec.outcome<>)->()
 ^second:
   %second = func.call @empty(%scope,%enabled) {runtime.site="second"} : (!runtime.scope,i1)->!exec.outcome<>
   "exec.dispatch"(%second)[^done,^failed] : (!exec.outcome<>)->()
 ^done:
   %ok = "exec.returned"(%enabled) : (i1)->!exec.outcome<(i1)>
   func.return %ok : !exec.outcome<(i1)>
 ^failed(%cause:!exec.stop):
   %bad = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(i1)>
   func.return %bad : !exec.outcome<(i1)>''')
    defs = table(export(source))
    assert defs['empty'][9] == ['block', [], ['return', []]]
    assert instructions(defs['work']) == [
        [['apply', 'empty'], [1], [], [], 'first'],
        [['apply', 'empty'], [1], [], [], 'second']]
    assert defs['work'][9][2] == ['return', [1]]

with case('origin-binding-order-is-subject-data'):
    changed = mutate(loops, '[["Field", "bls12-381.fr"], ["Group", "bls12-381.g1"]]',
                      '[["Group", "bls12-381.g1"], ["Field", "bls12-381.fr"]]')
    defs = table(export(changed, symbol='entry'))
    assert defs['swap'][8] == ['original_swap', [['Group', 'bls12-381.g1'], ['Field', 'bls12-381.fr']]]

with case('original-protocol-guard-retains-owner-and-site'):
    guarded = (fixtures / 'structured-source/guards.mlir').read_text()
    body = table(export(guarded))['main'][9]
    assert body[1][0] == [['guard', 'P'], [0], [], [], 'check']

with case('precondition-count-boundary'):
    bound = '#data.index_bound<2,3,0>'
    assert bound in total
    export(total.replace(bound, ','.join([bound] * 512)))
    export(total.replace(bound, ','.join([bound] * 513)), 'structured-source-limit')

for name in ('forwarded-bounds', 'aliased-indices'):
    with case('native-exact-provenance-' + name):
        data = export((fixtures / 'structured-source' / (name + '.mlir')).read_text())
        assert data[3] == 'main'
        assert len({definition[1] for definition in data[7]}) == len(data[7])

with case('protocol-origin-is-a-typed-tree-and-has-a-separate-path-cap'):
    origin = ['library::Run', [['F', ['field', 'bls12-381.fr']],
                ['T', ['formal', 'polynomial', [['field', 'bls12-381.fr'], ['nat', '1']]]],
                ['Max', ['nat', '4']]]]
    source = simple().replace('origin=["main",[]]', 'origin=' + json.dumps(origin))
    assert table(export(source))['main'][8] == origin
    long_path = 'p' * 2048
    assert table(export(simple().replace('origin=["main",[]]',
        'origin=' + json.dumps([long_path, []]))))['main'][8] == [long_path, []]
    export(simple().replace(',origin=["main",[]]', ''), 'source.protocol-origin')

for label, origin in [
    ('empty', []), ('old-string-binding', ['main', [['F', 'bls12-381.fr']]]),
    ('unbound-parameter', ['main', [['T', ['parameter', 'T']]]]),
    ('duplicate-name', ['main', [['T', ['bool']], ['T', ['index']]]]),
    ('bad-decimal', ['main', [['Max', ['nat', '04']]]]),
    ('unknown-kind', ['main', [['T', ['nominal', 'unknown', 'x', []]]]]),
    ('non-NFC', ['cafe\u0301::Run', []]), ('path-limit', ['p' * 2049, []]),
    ('string-limit', ['main', [['F', ['field', 'f' * 513]]]]),
]:
    with case('malformed-protocol-origin-' + label):
        changed = simple().replace('origin=["main",[]]', 'origin=' + json.dumps(origin, ensure_ascii=False))
        export(changed, 'mathematical-formation')

commands.save()
print(f"structured-source: {counted()} cases")
