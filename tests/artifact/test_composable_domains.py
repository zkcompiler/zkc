#!/usr/bin/env python3
"""Source/native resource parity and suite-specific artifact/reference integration.

Every binary is digested before and after, so a rebuild in the middle is a
failure rather than a result. Resource tests compare counters only: native
entropy is OS randomness and Lean uses an explicit finite tape. Artifact tests
compare the full validator observation on the same proof. No source checker is
mocked.
"""
import hashlib
import json
from types import SimpleNamespace

from run_reference import run_reference
from construction import constructed_plan
from journal import Journal
from toolchain import Toolchain, records

# The two Lean references this drives: one consumes the admitted source, the
# other interprets the artifact the runtime produced.
def main():
    CHECKER = "interactive-protocol"
    REFERENCE = "artifact-reference"

    tools = Toolchain()
    a = SimpleNamespace(zkc=tools.runtime, compiler=tools.compiler,
                           lean=tools.checker(CHECKER), reference=tools.checker(REFERENCE),
                           primitive=tools.primitive)
    journal = Journal(records(), timeout=120)

    checks = []
    pins = {k: {'path': str(v.resolve()), 'sha256': hashlib.sha256(v.read_bytes()).hexdigest()}
            for k, v in vars(a).items() if k != 'output_dir'}
    (journal.directory / 'binaries.json').write_text(json.dumps(pins, indent=2))

    def call(name, argv, success=True):
        """Run one step of a case, keeping its output under that step's name."""
        result = journal.attempt(argv, text=False, keep=name)
        if success:
            assert result.returncode == 0, (name, result.stderr.decode(), result.stdout.decode())
        return json.loads(result.stdout)

    def module(bindings, functions, ports, outputs, body, roles=('P',)):
        return ['zkc.protocol/1', bindings, functions,
                [['protocol', 'Main', list(roles), [], ports, outputs, [], body]],
                [['instance', 'root', 'Main', [], [], [[r, r] for r in roles]]],
                [['entry', 'main', 'root']]]

    def function(name, inputs, outputs, body):
        return ['function', name, inputs, outputs, body, [name, []]]

    def op(site, binding, attrs, inputs, outputs):
        return ['op', site, binding, attrs, inputs, outputs]

    for field in ('bls12-381.fr', 'ristretto255.scalar'):
        short = 'ristretto' if field.startswith('ristretto') else 'bls'
        rng, vector, scalar = [t + ':' + field for t in ('rng', 'vector', 'field')]
        for n, budget in ((0, 0), (1, 1), (4, 7), (3, 0), (3, 2)):
            name = f'{short}-vector-{n}-budget-{budget}'
            source = module([['draw', 'random.vector', [field], '']],
                [function('Mask', [['rng', rng]], [vector, rng],
                    [op('draw', 'draw', [str(n)], ['rng'], ['v', 'next']), ['return', ['v', 'next']]])],
                [['rng', 'P', rng]], [['P', vector], ['P', rng]],
                [['local', 'mask', 'P', 'Mask', ['rng'], ['v', 'next']], ['return', ['v', 'next']]])
            src = journal.write(name + '.source.json', source)
            physical = journal.write(name + '.physical.json', call(name + '.compile', [a.compiler, 'protocol-compile', src]))
            config = journal.write(name + '.native-inputs.json', ['zkc.run/2', 'main', 'vector-test', [],
                [['P', [[rng if short == 'ristretto' else 'rng', 'rng', str(budget), 'session']],
                  [['rng', ['host', 'rng']]], []]], []])
            native = call(name + '.native', [a.zkc, 'run-protocol', src, physical, config, a.lean])
            reference_inputs = journal.write(name + '.reference-inputs.json', ['zkc.reference-inputs/1', 'main', 'vector-test',
                [['P', [['rng', [rng, ['rng', '0']]]]]],
                [['rng', 'P', [], str(budget), [rng if short == 'ristretto' else 'rng', ['2', '3', '4', '5']]]], [], []])
            ref = call(name + '.reference', [a.lean, '--generic-reference', src, reference_inputs])
            expected = [1, n, budget - n] if budget >= n else [0, 0, budget]
            assert native['resources'][0][2:5] == expected, native
            assert list(map(int, ref[5][0][3:6])) == expected, ref
            assert native['resources'][0][5] == ref[5][0][6] == 'rng'
            if budget < n:
                assert native['stop']['detail'] == 'exhausted:resource-budget', native
                assert ref[3][:2] == ['exhausted', 'resource-budget'], ref
            else:
                assert ref[3][0] == 'returned', ref
            checks.append({'name': name, 'snapshot': expected + ['rng'], 'scope': 'source/native counters; distinct entropy'})

        # Compile and execute one shared producer with two consumers in the same
        # local function. Default selection stays off; both outputs and the exact
        # increase in retained-backing charge are compared at sufficient capacity.
        group = 'ristretto255.group'
        backing = 'groups:' + group if short == 'ristretto' else vector
        result_type = 'group:' + group if short == 'ristretto' else scalar
        producer, consumer = ('curve.scale_each', 'curve.msm') if short == 'ristretto' else ('vector.mul', 'vector.dot')
        nominal = group if short == 'ristretto' else field
        source = module([['producer', producer, [nominal], ''], ['consumer', consumer, [nominal], '']],
            [function('Pair', [['f', vector], ['v', backing], ['w', vector]], [result_type, result_type],
                [op('producer', 'producer', [], ['f', 'v'], ['d']),
                 op('first', 'consumer', [], ['w', 'd'], ['a']),
                 op('second', 'consumer', [], ['f', 'd'], ['b']), ['return', ['a', 'b']]])],
            [['f', 'P', vector], ['v', 'P', backing], ['w', 'P', vector]], [['P', result_type], ['P', result_type]],
            [['local', 'pair', 'P', 'Pair', ['f', 'v', 'w'], ['a', 'b']], ['return', ['a', 'b']]])
        src = journal.write(short + '-shared.source.json', source)
        if short == 'ristretto':
            req = journal.write('basepoint.request.json', ['zkc.public-primitive/1', [], 'curve.generator', [group], [], []])
            point = call('basepoint', [a.primitive, req])[1][1][12:]
            values = ['wire', '5a4b43560111' + '02000000' + point * 2]
        else:
            values = ['vector', ['2', '4']]
        cfg = journal.write(short + '-shared.inputs.json', ['zkc.run/2', 'main', 'shared-test', [],
                   [['P', [], [['f', ['vector', ['3', '5']]], ['v', values], ['w', ['vector', ['11', '13']]]], []]], []])
        reports = []
        for selected in (False, True):
            name = short + '-shared-' + ('diagonal' if selected else 'dense')
            candidate = call(name + '.compile', [a.compiler, 'protocol-compile', src, *(['--linear-contractions'] if selected else [])])
            installed = {b[0]: b[3] for b in candidate[1]}
            operations = [op for op in candidate[3][0][4] if op[0] == 'op']
            assert len(operations) == 3
            assert all(('-diagonal/' in installed[op[2]]) == selected for op in operations), candidate
            physical = journal.write(name + '.physical.json', candidate)
            reports.append(call(name + '.native', [a.zkc, 'run-protocol', src, physical, cfg, a.lean]))
        assert reports[0]['outcome'] == reports[1]['outcome'] and reports[0]['outcome'][0] == 'returned', reports
        charged = [r['usage']['P']['total_value_bytes'] for r in reports]
        assert charged[1] - charged[0] == 576, charged
        checks.append({'name': short + '-shared', 'charged_bytes': charged, 'increase': 576,
                       'scope': 'current compiler selections; native two-consumer outputs; full backing accounting'})

        # Small protocol exercises actual private vector entropy, a vector message,
        # selected transcript challenge, scalar response, and terminal equation.
        bindings = [[k, c, [field] if c != 'control.require' else [], ''] for k, c in
                    [('mask', 'random.vector'), ('at', 'vector.at'), ('draw', 'random.draw'),
                     ('mul', 'field.mul'), ('eq', 'field.equal'), ('require', 'control.require')]]
        functions = [
            function('Mask', [['rng', rng]], [vector, rng], [op('mask', 'mask', ['3'], ['rng'], ['v', 'next']), ['return', ['v', 'next']]]),
            function('Head', [['v', vector]], [scalar], [op('head', 'at', ['0'], ['v'], ['x']), ['return', ['x']]]),
            function('Draw', [['rng', rng]], [scalar, rng], [op('draw', 'draw', [], ['rng'], ['c', 'next']), ['return', ['c', 'next']]]),
            function('Response', [['x', scalar], ['c', scalar]], [scalar], [op('mul', 'mul', [], ['x', 'c'], ['z']), ['return', ['z']]]),
            function('Check', [['x', scalar], ['c', scalar], ['z', scalar]], ['bool'],
                     [op('mul', 'mul', [], ['x', 'c'], ['expected']), op('eq', 'eq', [], ['expected', 'z'], ['ok']),
                      op('require', 'require', [], ['ok'], []), ['return', ['ok']]])]
        body = [['local', 'mask', 'P', 'Mask', ['rng'], ['m', 'next']],
                ['message', 'mask_message', 'mask', 'P', 'V', 'm', 'received'],
                ['local', 'p_head', 'P', 'Head', ['m'], ['p']],
                ['local', 'v_head', 'V', 'Head', ['received'], ['q']],
                ['local', 'challenge', 'V', 'Draw', ['coins'], ['c', 'after']],
                ['message', 'challenge_message', 'challenge', 'V', 'P', 'c', 'r'],
                ['local', 'response', 'P', 'Response', ['p', 'r'], ['z']],
                ['message', 'response_message', 'response', 'P', 'V', 'z', 'received_z'],
                ['local', 'check', 'V', 'Check', ['q', 'c', 'received_z'], ['ok']],
                ['return', ['ok', 'after', 'next']]]
        src = journal.write(short + '.source.json', module(bindings, functions, [['rng', 'P', rng], ['coins', 'V', rng]],
                   [['V', 'bool'], ['V', rng], ['P', rng]], body, ('P', 'V')))
        suite = 'merlin3.ristretto255.scalar64le/1' if short == 'ristretto' else 'merlin3.bls12-381.fr64be/1'
        for policy in ('exact', 'normalized'):
            prefix = short + '-descriptor-' + policy
            desc = journal.write(prefix + '.descriptor.json', ['zkc.construction/1', 'main', 'P', 'V', [], ['coins', [['Draw', 'draw']]], '0', suite, policy])
            paths = constructed_plan(journal, a.compiler, src, desc, prefix + '.')
            base_input = ['zkc.artifact-inputs/1', '', [], [], ['zkc.public-configuration/1', [], [], []]]
            vi = journal.write(prefix + '.validator.json', base_input)
            base_input[3] = [['rng', 'rng', '3']]
            pi = journal.write(prefix + '.producer.json', base_input)
            proof = journal.directory / (prefix + '.proof')
            producer = call(prefix + '.produce', [a.zkc, 'produce-artifact', *paths, pi, a.compiler, a.lean, proof, '1000'])
            assert producer['status'] == 'produced', producer
            assert any([r['generation'], r['transitions'], r['budget'], r['stage']] == [1, 3, 0, 'rng'] for r in producer['resources']), producer
            original = proof.read_bytes()
            modulus = 7237005577332262213973186563042994240857116359379907606001950938285454250989 if short == 'ristretto' else 52435875175126190479447740508185965837690552500527637822603658699938581184513
            wrong_scalar = (int.from_bytes(original[-32:], 'little') + 1) % modulus
            wrong_equation = original[:-32] + wrong_scalar.to_bytes(32, 'little')
            for label, candidate in [('honest', original), ('trailing', original + b'\0'), ('bad-equation', wrong_equation)]:
                path = journal.directory / (prefix + '-' + label + '.proof')
                path.write_bytes(candidate)
                native = call(prefix + '.' + label, [a.zkc, 'validate-artifact', *paths, vi, a.compiler, a.lean, path, '1000'], success=label == 'honest')
                refdir = journal.directory / (prefix + '-' + label + '-reference')
                ref = run_reference(a.reference, a.primitive, src, desc, vi, path, refdir)
                assert ref[0] == 'zkc.artifact-observation/1', ref
                assert (native['status'] == 'accepted') == (ref[1][0] == 'accepted') == (label == 'honest'), (native, ref)
                assert native['events'] == ref[2], (short, label, 'events')
                assert native['proof_bytes'] == int(ref[4]), (native, ref)
                requests = json.loads((refdir / 'replies.json').read_text())[1]
                transcripts = [r[0] for r in requests if r[0][0] == 'zkc.transcript-request/3']
                assert transcripts and all(r[1] == suite for r in transcripts), requests
                assert not any(r[0][0] == 'zkc.transcript-request/1' for r in requests)
                checks.append({'name': prefix + '-' + label, 'events': len(native['events']), 'scope': 'full artifact validator/reference observation'})

    for name, pin in pins.items():
        assert hashlib.sha256(getattr(a, name).read_bytes()).hexdigest() == pin['sha256'], (name, 'binary changed during checks')
    journal.write('checks.json', checks)
    print(json.dumps({'status': 'passed', 'checks': len(checks), 'binaries': pins}))



def test_composable_domains():
    main()


if __name__ == "__main__":
    main()
