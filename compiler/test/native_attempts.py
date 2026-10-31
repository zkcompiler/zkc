"""Native retries are returned data, with persistent RNG/service authority."""
import json
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/mathematical'
SUITES = ['merlin3.bls12-381.fr64be/0', 'spongefish0.8.0.keccak.bls12-381.fr64be/0']
manifest = []
f = '!algebra.field<"bls12-381.fr">'
schnorr = (FIXTURES / 'schnorr-services.mlir').read_text()
schnorr = schnorr.replace('"protocol.return"(%ok) : (i1)',
                         '"protocol.return"(%ok,%complete) : (i1,i1)')
schnorr = schnorr.replace('%r =',
                         f'%zero = algebra.field_subtract %x,%x : ({f},{f})->{f}\n'
                         f'%empty = algebra.field_equal %k,%zero : ({f},{f})->i1\n'
                         '%yes = arith.constant true\n%complete = arith.xori %empty,%yes : i1\n%r =')
schnorr = schnorr.replace(' -> (i1), roles=', ' -> (i1,i1), roles=')
schnorr = schnorr.replace('output_roles=[["Bob"]]', 'output_roles=[["Bob"],["Alice"]]')
fold = (FIXTURES / 'fold-attempt.mlir').read_text()
for family, source in [('service', schnorr), ('fold', fold)]:
    for i, suite in enumerate(SUITES):
        policy = (['zkc.native-proof-policy/0', 'main', 'Alice', 'Bob', '0', suite,
                   ['4'], ['0', '2'], [['draw_challenge', 'challenge']], "zkc.framed/0", "", []] if family == 'service' else
                  ['zkc.native-proof-policy/0', 'main', 'P', 'V', '0', suite,
                   ['3'], ['0', '1'], [['draw', 'challenge']], "zkc.framed/0", "", []])
        for suffix, options in [('', []), ('_plain', ['--no-simplify']),
                                ('_release', ['--release-storage'])]:
            name = f'{family}_{i}{suffix}'
            with case(name):
                src, pol = OUT / f'{name}.mlir', OUT / f'{name}.policy'
                src.write_text(source)
                pol.write_text(json.dumps(policy))
                (OUT / f'{name}.deployment').write_text(commands.run(
                    [compiler, 'protocol-proof', src, pol, *options]))
                manifest.append(dict(name=name, family=family))
        with case(f'{family} production entropy retries suite {i}'):
            name = f'{family}_production_{i}'
            retry = source.replace('%complete = arith.xori %empty,%yes : i1', '%complete = arith.constant false').replace('%complete = arith.xori %iszero,%yes : i1', '%complete = arith.constant false')
            src, pol = OUT / f'{name}.mlir', OUT / f'{name}.policy'
            src.write_text(retry)
            pol.write_text(json.dumps(policy))
            (OUT / f'{name}.deployment').write_text(commands.run([compiler, 'protocol-proof', src, pol]))
            manifest.append(dict(name=name, family=family, production=True))
        with case(f'{family} fatal stop suite {i}'):
            name = f'{family}_fatal_{i}'
            fatal = (source.replace('%cx =', 'protocol.guard %complete {owner="Alice",site="fatal"}\n%cx =')
                     if family == 'service' else source.replace('   %n =',
                     '   protocol.guard %complete {owner="P",site="fatal"}\n   %n ='))
            src, pol = OUT / f'{name}.mlir', OUT / f'{name}.policy'
            src.write_text(fatal)
            pol.write_text(json.dumps(policy))
            (OUT / f'{name}.deployment').write_text(commands.run([compiler, 'protocol-proof', src, pol]))
            manifest.append(dict(name=name, family=family, fatal=True))
# Conditional entry completion keeps the already emitted prefix and affine state.
for fixture in ['attempt-abandonment', 'attempt-abandonment-silent']:
    for i, suite in enumerate(SUITES):
        for suffix, options in [('', []), ('_plain', ['--no-simplify']),
                                ('_release', ['--release-storage'])]:
            name = f'{fixture}_{i}{suffix}'
            with case(name):
                pol = OUT / f'{name}.policy'
                pol.write_text(json.dumps(['zkc.native-proof-policy/0', 'main', 'P', 'V', '0', suite,
                                          ['3'], ['0', '1'], [['draw', 'challenge']], "zkc.framed/0", "", []]))
                (OUT / f'{name}.deployment').write_text(commands.run([
                    compiler, 'protocol-proof', FIXTURES / f'{fixture}.mlir', pol, *options]))
                manifest.append(dict(name=name, family='fold', abandonment=True,
                                     silent=fixture.endswith('silent')))

for i, suite in enumerate(SUITES):
    with case(f'long discarded prefix and shorter completion suite {i}'):
        helper = '''    "runtime.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "index",function_type=(!runtime.scope) -> !exec.outcome<(ui64)>}> : () -> ()
    func.func @count(%arg0: !runtime.scope, %arg1: i1) -> !exec.outcome<(ui64)> attributes {no_inline, runtime.origin = ["count", []]} {
      %0 = "exec.test"(%arg0, %arg1) <{site = "count"}> : (!runtime.scope, i1) -> !exec.outcome<(i1)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(i1)>) -> ()
    ^bb1(%1: i1):  // pred: ^bb0
      cf.cond_br %1, ^bb3, ^bb4
    ^bb2(%2: !exec.stop):  // 7 preds: ^bb0, ^bb3, ^bb4, ^bb6, ^bb7, ^bb9, ^bb10
      %3 = "exec.failed"(%2) : (!exec.stop) -> !exec.outcome<(ui64)>
      return %3 : !exec.outcome<(ui64)>
    ^bb3:  // pred: ^bb1
      %4 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "then", site = "count"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%4)[^bb6, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb4:  // pred: ^bb1
      %5 = "runtime.enter_scope"(%arg0) <{kind = "conditional", operandSegmentSizes = array<i32: 1, 0, 0>, selection = "else", site = "count"}> : (!runtime.scope) -> !exec.outcome<(!runtime.scope)>
      "exec.dispatch"(%5)[^bb9, ^bb2] : (!exec.outcome<(!runtime.scope)>) -> ()
    ^bb5(%6: ui64):  // 2 preds: ^bb8, ^bb11
      %7 = "exec.returned"(%6) : (ui64) -> !exec.outcome<(ui64)>
      return %7 : !exec.outcome<(ui64)>
    ^bb6(%8: !runtime.scope):  // pred: ^bb3
      %9 = call @count_arm_0(%8) : (!runtime.scope) -> !exec.outcome<(ui64)>
      %10 = "runtime.exit_scope"(%8, %9) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%10)[^bb7, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb7(%11: !runtime.transfer<(ui64)>):  // pred: ^bb6
      %12 = "runtime.accept_transfer"(%arg0, %11) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%12)[^bb8, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb8(%13: ui64):  // pred: ^bb7
      cf.br ^bb5(%13 : ui64)
    ^bb9(%14: !runtime.scope):  // pred: ^bb4
      %15 = call @count_arm_1(%14) : (!runtime.scope) -> !exec.outcome<(ui64)>
      %16 = "runtime.exit_scope"(%14, %15) : (!runtime.scope, !exec.outcome<(ui64)>) -> !exec.outcome<(!runtime.transfer<(ui64)>)>
      "exec.dispatch"(%16)[^bb10, ^bb2] : (!exec.outcome<(!runtime.transfer<(ui64)>)>) -> ()
    ^bb10(%17: !runtime.transfer<(ui64)>):  // pred: ^bb9
      %18 = "runtime.accept_transfer"(%arg0, %17) : (!runtime.scope, !runtime.transfer<(ui64)>) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%18)[^bb11, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb11(%19: ui64):  // pred: ^bb10
      cf.br ^bb5(%19 : ui64)
    }
    func.func private @count_arm_0(%arg0: !runtime.scope) -> !exec.outcome<(ui64)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index, parameters = [2 : ui64], site = "two"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      return %2 : !exec.outcome<(ui64)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64)>
      return %4 : !exec.outcome<(ui64)>
    }
    func.func private @count_arm_1(%arg0: !runtime.scope) -> !exec.outcome<(ui64)> attributes {no_inline, runtime.region} {
      %0 = "exec.apply"(%arg0) <{binding = @index, parameters = [1 : ui64], site = "one"}> : (!runtime.scope) -> !exec.outcome<(ui64)>
      "exec.dispatch"(%0)[^bb1, ^bb2] : (!exec.outcome<(ui64)>) -> ()
    ^bb1(%1: ui64):  // pred: ^bb0
      %2 = "exec.complete"(%arg0, %1) : (!runtime.scope, ui64) -> !exec.outcome<(ui64)>
      return %2 : !exec.outcome<(ui64)>
    ^bb2(%3: !exec.stop):  // pred: ^bb0
      %4 = "exec.failed"(%3) : (!exec.stop) -> !exec.outcome<(ui64)>
      return %4 : !exec.outcome<(ui64)>
    }
'''
        source = fold.replace(' "protocol.func"', helper + ' "protocol.func"', 1)
        source = source.replace('%n = "data.index"() {value=2 : ui64} : ()->ui64',
                                '%n = "protocol.local_call"(%iszero) {callee=@count,role="P",site="count"} : (i1)->ui64\n'
                                '   %received_count = protocol.exchange %n {sender="P",receiver="V",site="count_message"} : ui64')
        source = source.replace('"protocol.repeat"(%n,', '"protocol.repeat"(%received_count,')
        policy = ['zkc.native-proof-policy/0', 'main', 'P', 'V', '0', suite,
                  ['3'], ['0', '1'], [['draw', 'challenge']], "zkc.framed/0", "", []]
        src, pol = OUT / f'varying_{i}.mlir', OUT / f'varying_{i}.policy'
        src.write_text(source); pol.write_text(json.dumps(policy))
        (OUT / f'varying_{i}.deployment').write_text(commands.run([compiler, 'protocol-proof', src, pol]))
with case('wrong same-typed RNG result mapping stays a custody refusal'):
    source = fold.replace('%coins:!s):', '%coins:!s,%other:!r):')
    source = source.replace('(%accepted,%complete,%prepared#1) : (i1,i1,!r)',
                            '(%accepted,%complete,%other,%prepared#1) : (i1,i1,!r,!r)')
    source = source.replace('function_type=(!f,!f,!r,!s)->(i1,i1,!r)',
                            'function_type=(!f,!f,!r,!s,!r)->(i1,i1,!r,!r)')
    source = source.replace('[["P","V"],["P","V"],["P"],["V"]]',
                            '[["P","V"],["P","V"],["P"],["V"],["P"]]')
    source = source.replace('output_roles=[["V"],["P"],["P"]]',
                            'output_roles=[["V"],["P"],["P"],["P"]]')
    policy = ['zkc.native-proof-policy/0', 'main', 'P', 'V', '0', SUITES[0],
              ['3'], ['0', '1'], [['draw', 'challenge']], "zkc.framed/0", "", []]
    src, pol = OUT / 'swapped.mlir', OUT / 'swapped.policy'
    src.write_text(source); pol.write_text(json.dumps(policy))
    (OUT / 'swapped.deployment').write_text(commands.run([compiler, 'protocol-proof', src, pol]))
with case('one-shot nonce is not silently reissued by attempts'):
    source = (FIXTURES / 'schnorr-affine.mlir').read_text()
    source = source.replace('"protocol.return"(%ok) : (i1)',
                            '%complete = arith.constant true\n"protocol.return"(%ok,%complete) : (i1,i1)')
    source = source.replace(' -> (i1), roles=', ' -> (i1,i1), roles=')
    source = source.replace('output_roles=[["Bob"]]', 'output_roles=[["Bob"],["Alice"]]')
    policy = ['zkc.native-proof-policy/0', 'main', 'Alice', 'Bob', '0', SUITES[0],
              ['4'], ['0', '2'], [['draw_challenge', 'challenge']], "zkc.framed/0", "", []]
    src, pol = OUT / 'nonce.mlir', OUT / 'nonce.policy'
    src.write_text(source); pol.write_text(json.dumps(policy))
    (OUT / 'nonce.deployment').write_text(commands.run([compiler, 'protocol-proof', src, pol]))
with case('transcript-free header-only proof and deterministic retry boundary'):
    source = '''module { "protocol.module"() ({
      "protocol.func"() ({ ^entry(%complete:i1):
        %accepted = arith.constant true
        %unused = arith.constant false
        "protocol.return"(%accepted,%unused,%complete) : (i1,i1,i1)->()
      }) {sym_name="main",function_type=(i1)->(i1,i1,i1),roles=["P","V"],input_roles=[["P"]],output_roles=[["V"],["P"],["P"]]} : ()->()
    }) {profile=#protocol.profile<protocol>} : ()->() }
'''
    policy = ['zkc.native-proof-policy/0', 'main', 'P', 'V', '0', '', [], [], [], "zkc.framed/0", "", []]
    src, pol = OUT / 'empty.mlir', OUT / 'empty.policy'
    src.write_text(source); pol.write_text(json.dumps(policy))
    (OUT / 'empty.deployment').write_text(commands.run([compiler, 'protocol-proof', src, pol]))
for i, suite in enumerate(SUITES):
    with case(f'RNG and service custody coexist across attempts suite {i}'):
        source = fold.replace('%coins:!s):', '%coins:!s,%extra:!s):')
        source = source.replace('   %zero =',
                                '   %unused = "protocol.query"(%extra) {method="draw",owner="P",site="extra_draw"} : (!s)->!f\n   %zero =')
        source = source.replace('function_type=(!f,!f,!r,!s)', 'function_type=(!f,!f,!r,!s,!s)')
        source = source.replace('[["P","V"],["P","V"],["P"],["V"]]',
                                '[["P","V"],["P","V"],["P"],["V"],["P"]]')
        policy = ['zkc.native-proof-policy/0', 'main', 'P', 'V', '0', suite,
                  ['3'], ['0', '1'], [['draw', 'challenge']], "zkc.framed/0", "", []]
        src, pol = OUT / f'mixed_{i}.mlir', OUT / f'mixed_{i}.policy'
        src.write_text(source); pol.write_text(json.dumps(policy))
        (OUT / f'mixed_{i}.deployment').write_text(commands.run([compiler, 'protocol-proof', src, pol]))
(OUT / 'manifest.json').write_text(json.dumps(manifest))
counted()
