"""A captured external AIR proved by the ordinary STARK/FRI source libraries.

The AIR fixture comes from direct upstream execution. Tests exercise the full
proof path and adversarial obligations, without asserting a soundness bound.
"""
import json
import re
from pathlib import Path

import pytest

from logical_tree import decode_tree

ROOT = Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / 'examples/projects/air-stark/main.zkc'
TABLE = ROOT / 'libraries/air/table.zkc'
STARK = ROOT / 'libraries/air/stark.zkc'
FIXTURE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence'
P = 2130706433


def scalar(value):
    return (b'ZKCV\x00\x13' + value.to_bytes(4, 'little')).hex()


def vector(values):
    return (b'ZKCV\x00\x14' + len(values).to_bytes(4, 'little')
            + b''.join(v.to_bytes(4, 'little') for v in values)).hex()


def unpack(value):
    raw = bytes.fromhex(value)
    assert raw[:6] == b'ZKCV\x00\x14'
    size = int.from_bytes(raw[6:10], 'little')
    assert len(raw) == 10 + 4 * size
    return [int.from_bytes(raw[i:i + 4], 'little') for i in range(10, len(raw), 4)]


def inputs():
    original = json.loads((FIXTURE / 'source-trace-honest.json').read_text())
    data = original['roles']['Evaluator']['inputs']
    x0, y0, final = unpack(data['public_data'])
    return ({'configuration': data['configuration'], 'x0': scalar(x0),
             'y0': scalar(y0), 'final_acc': scalar(final), 'shift': scalar(3),
             'round_count': 3, 'query_count': 8, 'attempt_count': 8},
            {'trace': data['trace']})


def test_documented_air_stark_requests(journal, directory):
    import sys
    journal.run([sys.executable, EXAMPLE.with_name('prepare.py'), directory])
    public, private = inputs()
    assert json.loads((directory / 'prover.json').read_text()) == {
        'format': 'zkc.entry-proof/0', 'public': public, 'inputs': private}
    assert json.loads((directory / 'verifier.json').read_text()) == {
        'format': 'zkc.entry-proof/0', 'public': public, 'inputs': {}}


def compile_entry(toolchain, journal, directory, *, log_size=5, queries=8,
                  flags=(), entry='Proof', source=None, table=TABLE, stark=STARK):
    source = EXAMPLE.read_text() if source is None else source
    source = source.replace('TableArgument<0,Recurrence,3,5,8,8>',
                            f'TableArgument<0,Recurrence,3,{log_size},{queries},8>')
    path = directory / 'main.zkc'
    path.write_text(source)
    package = directory / f'{entry}.entry'
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
               f'--module=air_stark_example={path}',
               f'--module=air_stark={stark}',
               f'--module=air_table={table}',
               f'--module=air_polynomial={ROOT}/libraries/air/polynomial.zkc',
               f'--module=fri={ROOT}/libraries/fri/lib.zkc',
               f'--asset=recurrence=relation-bundle-json={FIXTURE}/bundle.json',
               f'--entry=air_stark_example::{entry}', f'--output={package}', *flags]
    report = journal.json(command)
    return package, report['package_sha256']


def request(journal, name, public, private=None):
    return journal.write(name + '.json', {'format': 'zkc.entry-proof/0',
                                        'public': public, 'inputs': private or {}})


def frames(proof):
    offset, result = 40, []
    while offset < len(proof):
        count = int.from_bytes(proof[offset:offset + 8], 'little')
        result.append(proof[offset + 8:offset + 8 + count])
        offset += count + 8
    assert offset == len(proof)
    return result


def replace_frame(proof, position, value):
    messages = frames(proof)
    messages[position] = value
    return proof[:40] + b''.join(len(m).to_bytes(8, 'little') + m for m in messages)


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('profile', [(4, 8), (5, 8), (6, 12)])
def test_external_air_stark_produces_and_verifies(toolchain, journal, directory, flags, profile):
    log_size, queries = profile
    package, pin = compile_entry(toolchain, journal, directory, log_size=log_size,
                                queries=queries, flags=flags)
    public, private = inputs()
    public['query_count'] = queries
    producer = request(journal, 'producer', public, private)
    verifier = request(journal, 'verifier', public)
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, 'prove', package, pin, producer, proof])
    checked = journal.json([toolchain.runtime, 'verify', package, pin, verifier, proof])
    assert produced['status'] == 'produced' and checked['status'] == 'accepted'
    # Trace root, quotient root, two OOD claims, 3 FRI roots and terminal,
    # then four FRI messages per round/query and four table-opening messages.
    assert len(frames(proof.read_bytes())) == 8 + 16 * queries
    captured = json.loads(package.read_text())
    assert any('zkc.relation-bundle/0' in text for _, text in captured['assets'])


def test_stark_checks_statement_trace_schedule_and_shape(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory)
    public, private = inputs()
    honest_proof = directory / 'honest.bin'
    producer = request(journal, 'honest', public, private)
    journal.run([toolchain.runtime, 'prove', package, pin, producer, honest_proof])
    trace, configuration = unpack(private['trace']), unpack(public['configuration'])
    changed_trace = trace.copy()
    changed_trace[4 * 3 + 1] = (changed_trace[4 * 3 + 1] + 1) % P
    changed_config = configuration.copy()
    changed_config[2] += 1
    changes = [
        ('trace', {}, {'trace': vector(changed_trace)}),
        ('short-trace', {}, {'trace': vector(trace[:-1])}),
        ('configuration', {'configuration': vector(changed_config)}, {}),
        ('short-configuration', {'configuration': vector(configuration[:-1])}, {}),
        ('first-boundary', {'x0': scalar(17)}, {}),
        ('last-boundary', {'final_acc': scalar(17)}, {}),
        ('zero-shift', {'shift': scalar(0)}, {}),
        ('intersecting-coset', {'shift': scalar(1)}, {}),
        ('zero-rounds', {'round_count': 0}, {}),
        ('wrong-rounds', {'round_count': 2}, {}),
        ('zero-queries', {'query_count': 0}, {}),
        ('wrong-queries', {'query_count': 7}, {}),
        ('zero-attempts', {'attempt_count': 0}, {}),
        ('wrong-attempts', {'attempt_count': 7}, {}),
    ]
    for name, public_change, private_change in changes:
        changed_public = public | public_change
        changed_private = private | private_change
        candidate = directory / f'{name}.bin'
        p = request(journal, name + '-producer', changed_public, changed_private)
        v = request(journal, name + '-verifier', changed_public)
        made = journal.attempt([toolchain.runtime, 'prove', package, pin, p, candidate])
        if made.returncode == 0:
            journal.run([toolchain.runtime, 'verify', package, pin, v, candidate],
                        refuses='artifact-stopped')
        else:
            assert made.returncode > 0
            code = json.loads(made.stdout)['code']
            if name == 'short-trace':
                assert code == 'refused:vector-shape'
            else:
                assert code.startswith('artifact-stopped:')
            assert not candidate.exists()
        if public_change:
            # Statement binding also rejects an honest proof replayed against
            # changed public data, even before any AIR equation is checked.
            replay = journal.attempt([toolchain.runtime, 'verify', package, pin, v, honest_proof])
            assert replay.returncode > 0
            assert json.loads(replay.stdout)['status'] == 'refused'


def test_stark_authenticates_claims_roots_and_late_openings(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory)
    public, private = inputs()
    producer = request(journal, 'producer', public, private)
    verifier = request(journal, 'verifier', public)
    proof = directory / 'honest.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    original = proof.read_bytes()
    messages = frames(original)
    # Every table/FRI root, both OOD vectors, terminal, and all four final
    # trace/quotient opening components. Mutation retains the outer framing.
    for position in [*range(8), *range(len(messages) - 4, len(messages))]:
        payload = bytearray(messages[position])
        if payload[:6] in (b'ZKCV\x00\x14', b'ZKCV\x00\x1b'):
            old = int.from_bytes(payload[10:14], 'little')
            payload[10:14] = ((old + 1) % P).to_bytes(4, 'little')
        else:
            payload[-1] ^= 1
        candidate = directory / f'message-{position}.bin'
        candidate.write_bytes(replace_frame(original, position, payload))
        journal.run([toolchain.runtime, 'verify', package, pin, verifier, candidate],
                    refuses='artifact-stopped')
    for name, value, code in [('truncated', original[:-1], 'proof-truncated'),
                              ('trailing', original + b'\x00', 'proof-trailing')]:
        candidate = directory / f'{name}.bin'
        candidate.write_bytes(value)
        journal.run([toolchain.runtime, 'verify', package, pin, verifier, candidate], refuses=code)


def test_stark_transcript_orders_commitments_claims_and_queries(toolchain, journal):
    bundle = journal.json([toolchain.compiler, 'language-bundle', '--source-format=zkc',
        '--entry=air_stark_example::Proof', f'--module=air_stark_example={EXAMPLE}',
        f'--module=air_stark={STARK}', f'--module=air_table={TABLE}',
        f'--module=air_polynomial={ROOT}/libraries/air/polynomial.zkc',
        f'--module=fri={ROOT}/libraries/fri/lib.zkc',
        f'--asset=recurrence=relation-bundle-json={FIXTURE}/bundle.json'])
    descriptor = bundle[2]
    assert descriptor[0] == 'zkc.native-proof-descriptor/0'
    policy = descriptor[1]
    assert policy[2:4] == ['P', 'V'] and policy[7] == [str(i) for i in range(1, 9)]
    events = []
    for kind, encoded, *bound in descriptor[3]:
        template = decode_tree(bytes.fromhex(encoded))
        assert template[0] == 'zkc.native-origin-template/0' and template[3] == []
        steps, event = template[2], template[4]
        assert all(step[0] in ('apply', 'repeat') for step in steps)
        loops = tuple(tuple(step) for step in steps if step[0] == 'repeat')
        events.append((kind, loops, event, bound))
    # Trace root -> alpha -> quotient root -> bounded OOD sampling -> both
    # claims -> rho/eta -> FRI roots/folds/terminal -> positions -> FRI paths
    # -> original trace/quotient paths at those same positions.
    assert [(kind, len(loops)) for kind, loops, _, _ in events] == [
        ('message', 0), ('query', 0), ('message', 0), ('message', 0),
        ('query', 1), ('message', 1), ('message', 0), ('message', 0),
        ('query', 0), ('message', 0), ('query', 0), ('message', 0),
        ('message', 1), ('query', 1), ('message', 1), ('message', 0),
        ('index', 1), ('message', 1)] + [('message', 2)] * 4 + [('message', 1)] * 4
    draws = [1, 4, 8, 10, 13, 16]
    assert len(policy[8]) == len(draws)
    for (query, delivery), i in zip(policy[8], draws, strict=True):
        assert query.endswith('_' + events[i][2][2])
        assert delivery.endswith('_' + events[i + 1][2][2])
        assert events[i][2][5:7] == ['index' if i == 16 else 'draw', 'V']
    assert events[16][3] == ['32']
    for i, (kind, _, event, bound) in enumerate(events):
        if kind == 'message':
            assert event[4:6] == (['V', 'P'] if i - 1 in draws else ['P', 'V'])
            assert bound == []
    # One OOD loop, one fold loop, a separate query draw loop and opening
    # loops. Neither retries nor openings are interleaved with new queries.
    assert events[4][1] == events[5][1]
    assert events[12][1] == events[13][1] == events[14][1]
    assert events[16][1] == events[17][1]
    assert len({events[i][1] for i in [4, 12, 16, 18, 22]}) == 5
    assert all(events[i][1] == events[18][1] for i in range(18, 22))
    assert all(events[i][1] == events[22][1] for i in range(22, 26))


@pytest.mark.parametrize('dishonest', ['quotient', 'deep'])
def test_stark_rejects_consistent_dishonest_prover_words(toolchain, journal, directory, dishonest):
    # Change only P. The resulting proof has its own consistent commitments,
    # FRI folds and transcript, so rejection must come from the outer equation.
    source = STARK.read_text()
    if dishonest == 'quotient':
        old = '  let quotient @P = quotient_values'
        new = '  let wrong_alpha @P = alter(alphaP);\n' + old
        source = source.replace('dataP, heightP, shiftP, sizeP, alphaP);',
                                'dataP, heightP, shiftP, sizeP, wrong_alpha);')
        source += '\nfn alter(value: Extension) -> Extension { return value + 1; }\n'
        guard, loops = 2, []
    else:
        old = '  let (fri_ok, positionsP, positionsV, valuesV) ='
        new = '  let reduced @P = alter_word(honest_reduced);\n' + old
        source = source.replace('let reduced @P = deep_word', 'let honest_reduced @P = deep_word')
        source += '\nfn alter_word(word: Vector<Extension>) -> Vector<Extension> {\n'
        source += '  let two: Extension = 2; return kernel<Extension>("vector.scale", word, two);\n}\n'
        guard, loops = 6, ['0']
    assert source.count(old) == 1
    source = source.replace(old, new)
    library = directory / 'stark.zkc'
    library.write_text(source)
    package, pin = compile_entry(toolchain, journal, directory, stark=library)
    # Guard sites are derived from the actual variant. They need not retain
    # the honest source's generated identifiers after inserting P operations.
    emitted = journal.run([toolchain.compiler, 'language-emit', '--source-format=zkc',
        '--entry=air_stark_example::Proof', f'--module=air_stark_example={directory}/main.zkc',
        f'--module=air_stark={library}', f'--module=air_table={TABLE}',
        f'--module=air_polynomial={ROOT}/libraries/air/polynomial.zkc',
        f'--module=fri={ROOT}/libraries/fri/lib.zkc',
        f'--asset=recurrence=relation-bundle-json={FIXTURE}/bundle.json'])
    sites = re.findall(r'"protocol\.guard"\(%\d+(?:#\d+)?\) <\{owner = "(\w+)", site = "(s\d+)"\}>', emitted)
    assert [owner for owner, _ in sites[:7]] == ['V', 'P', 'V', 'V', 'V', 'V', 'V']
    expected = sites[guard][1]
    public, private = inputs()
    producer = request(journal, 'producer', public, private)
    verifier = request(journal, 'verifier', public)
    proof = directory / 'dishonest.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, producer, proof])
    report = journal.json([toolchain.runtime, 'verify', package, pin, verifier, proof],
                          refuses='artifact-stopped')
    stop = report['execution']['stop']
    assert stop['role'] == 'V' and stop['kind'] == 'Explicit("reject")'
    assert stop['site'].endswith('_' + expected), stop
    assert [frame[2] for frame in stop['origin'][4] if frame[0] == 'loop'] == loops


SAMPLER = '''module air_stark_example;
use air_stark::{Extension, consider, finish};
use air_polynomial::{Vector};
fn choose(values: Vector<Extension>, shift: Extension) -> Extension {
  let mut chosen: Extension = 0;
  let mut found = false;
  for i in 0..kernel<Extension>("vector.length", values) {
    let candidate = kernel<Extension>("vector.get", values, i);
    let next = consider(8, 32, shift, chosen, found, candidate);
    chosen = next.0;
    found = next.1;
  }
  return finish(chosen, found);
}
protocol Sample roles(V)(values:Vector<Extension>@V, shift:Extension@V)
 -> (selected:Extension@V) {
 let selected@V=choose(values,shift);
 return (selected=selected);
}
entry Run=Sample;
'''


def extension_wire(values, scalar_value=False):
    return (b'ZKCV\x00' + bytes([26 if scalar_value else 27])
            + (b'' if scalar_value else len(values).to_bytes(4, 'little'))
            + b''.join(x.to_bytes(4, 'little') for v in values for x in v)).hex()


def test_outside_sampler_excludes_domains_selects_first_and_exhausts(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory, source=SAMPLER, entry='Run')
    def base(n):
        return [n] + [0] * 7
    root = pow(1791270792, (1 << 24) // 32, P)
    invalid = [base(0), base(1), base(pow(root, 4, P)), base(3), base(3 * root % P)]
    first = [11, 1, 0, 0, 0, 0, 0, 0]
    second = [13, 0, 1, 0, 0, 0, 0, 0]
    for name, candidates, succeeds in [
            ('first', invalid + [first, second], True),
            ('retained', [first] + invalid + [second], True),
            ('exhausted', invalid, False), ('empty', [], False)]:
        r = journal.write(name + '.json', {'format': 'zkc.entry-run/0', 'session': name,
            'roles': {'V': {'inputs': {'values': extension_wire(candidates),
                                      'shift': extension_wire([base(3)], True)}}}})
        output = directory / f'{name}.output.json'
        report = journal.json([toolchain.runtime, 'run', package, pin, r, f'--results={output}'],
                              refuses=None if succeeds else 'entry-run-incomplete')
        if succeeds:
            actual = json.loads(output.read_text())['roles']['V']['selected']
            assert actual == extension_wire([first], True)
        else:
            assert not output.exists()
            (role,) = report['execution']['roles']
            assert role['after'][0] == 'stopped'
            cause = role['after'][1]['cause']
            assert cause[0] == 'explicit' and cause[1]['text'] == 'exhausted'


POLYNOMIAL_VIEW = '''module air_stark_example;
use air_polynomial::{Vector, empty, extend_columns, split_quotient};
use air_table::{quotient_values, claims, opening_claims, identity, deep_word};
domain E=field("koala-bear.ext8-binomial3");
domain B=bundle(asset recurrence);
fn inspect(trace:Vector<E>, configuration:Vector<E>, data:Vector<E>,
 shift:E, alpha:E, zeta:E, rho:E, eta:E, size:index)
 -> (Vector<E>,Vector<E>,Vector<E>,Vector<E>,bool,Vector<E>) {
 let w=extend_columns(trace,4,8,shift,size);
 let c=extend_columns(configuration,1,8,shift,size);
 let none=empty<E>();
 let quotient=quotient_values<E,0,B>(w,c,none,data,8,shift,size,alpha);
 let chunks=split_quotient(quotient,shift,size,8,2);
 let opened=claims<E,0,B>(trace,configuration,none,data,8,zeta);
 let quotient_opened=opening_claims(chunks,2,shift,size,zeta);
 let valid=identity<E,0,B>(opened,quotient_opened,configuration,none,data,8,zeta,alpha);
 let reduced=deep_word<E,0,B>(w,chunks,opened,quotient_opened,8,shift,size,zeta,rho,eta);
 return (quotient,chunks,opened,quotient_opened,valid,reduced);
}
protocol Inspect roles(P)(trace:Vector<E>@P, configuration:Vector<E>@P,
 data:Vector<E>@P, shift:E@P, alpha:E@P, zeta:E@P, rho:E@P, eta:E@P,
 size:index@P) -> (quotient:Vector<E>@P, chunks:Vector<E>@P,
 opened:Vector<E>@P, quotient_opened:Vector<E>@P, valid:bool@P, reduced:Vector<E>@P) {
 let result@P=inspect(trace,configuration,data,shift,alpha,zeta,rho,eta,size);
 return (quotient=result.0,chunks=result.1,opened=result.2,
  quotient_opened=result.3,valid=result.4,reduced=result.5);
}
entry Run=Inspect;
'''


@pytest.mark.parametrize('size', [16, 32])
def test_air_quotient_openings_and_deep_word_match_independent_polynomials(
        toolchain, journal, directory, size):
    from octic_reference import ONE, ZERO, add, mul, power

    def base(n):
        return [n % P] + [0] * 7

    def neg(a):
        return [(-x) % P for x in a]

    def sub(a, b):
        return add(a, neg(b))

    def inv(a):
        assert a != ZERO
        return base(pow(a[0], P - 2, P)) if a[1:] == [0] * 7 else power(a, P**8 - 2)

    def evaluate(coefficients, x):
        value = ZERO
        for coefficient in reversed(coefficients):
            value = add(coefficient, mul(x, value))
        return value

    def interpolate(values, shift):
        n = len(values)
        g = pow(1791270792, (1 << 24) // n, P)
        coefficients = []
        for k in range(n):
            total = ZERO
            for i, value in enumerate(values):
                total = add(total, mul(value, base(pow(g, (-i * k) % n, P))))
            coefficients.append(mul(total, base(pow(n, P - 2, P) * pow(shift, -k, P))))
        return coefficients

    public, private = inputs()
    trace = unpack(private['trace'])
    trace_columns = [[base(trace[4 * row + column]) for row in range(8)] for column in range(4)]
    config = [base(v) for v in unpack(public['configuration'])]
    data = [base(int.from_bytes(bytes.fromhex(public[name])[6:], 'little'))
            for name in ['x0', 'y0', 'final_acc']]
    polynomials = [interpolate(column, 1) for column in trace_columns] + [interpolate(config, 1)]
    alpha, zeta = [2, 1, 0, 0, 0, 0, 0, 0], [11, 2, 0, 0, 0, 0, 0, 0]
    rho, eta = [3, 1, 2, 0, 0, 0, 0, 0], [7, 0, 0, 1, 0, 0, 0, 0]
    g = pow(1791270792, (1 << 24) // 8, P)
    root = pow(1791270792, (1 << 24) // size, P)
    domain = [base(3 * pow(root, i, P)) for i in range(size)]
    scopes = [(0, 8), (0, 1), (0, 1), (0, 1), (0, 7), (0, 7), (0, 7), (7, 8), (7, 8)]

    def assignments(at):
        current = [evaluate(p, at) for p in polynomials]
        following = [evaluate(polynomials[i], mul(base(g), at)) for i in [0, 1, 3]]
        return current[:4] + following + [current[4]] + data

    def constraints(at):
        # Written directly from the exported AIR's source recurrence, without
        # reading its expression arena or using a native evaluator.
        x, y, product, acc, x1, y1, acc1, k, x0, y0, last = assignments(at)
        return [sub(product, mul(x, y)), sub(x, x0), sub(y, y0), acc,
                sub(x1, y), sub(y1, add(add(product, k), base(123456789))),
                sub(acc1, add(acc, mul(mul(product, x), k))), sub(acc, last), sub(x1, x0)]

    quotient = []
    for at in domain:
        value, weight = ZERO, ONE
        for residual, (begin, end) in zip(constraints(at), scopes, strict=True):
            denominator = ONE
            for row in range(begin, end):
                denominator = mul(denominator, sub(at, base(pow(g, row, P))))
            value = add(value, mul(weight, mul(residual, inv(denominator))))
            weight = mul(weight, alpha)
        quotient.append(value)
    coefficients = interpolate(quotient, 3)
    assert all(c == ZERO for c in coefficients[15:])
    chunk_polynomials = [coefficients[:8], coefficients[8:16]]
    chunk_values = [evaluate(p, at) for p in chunk_polynomials for at in domain]
    opened, quotient_opened = assignments(zeta), [evaluate(p, zeta) for p in chunk_polynomials]
    subjects = [(column, 0) for column in range(4)] + [(column, 1) for column in [0, 1, 3]]
    reduced = []
    for at in domain:
        value, weight = ZERO, ONE
        for claim, (column, rotation) in zip(opened[:7], subjects, strict=True):
            point = mul(zeta, base(pow(g, rotation, P)))
            term = mul(sub(evaluate(polynomials[column], at), claim), inv(sub(at, point)))
            value, weight = add(value, mul(weight, term)), mul(weight, rho)
        for p, claim in zip(chunk_polynomials, quotient_opened, strict=True):
            term = mul(sub(evaluate(p, at), claim), inv(sub(at, zeta)))
            value, weight = add(value, mul(weight, term)), mul(weight, rho)
        reduced.append(mul(value, add(ONE, mul(eta, at))))
    assert all(c == ZERO for c in interpolate(reduced, 3)[8:])

    package, pin = compile_entry(toolchain, journal, directory, source=POLYNOMIAL_VIEW, entry='Run')
    values = {'trace': extension_wire([x for column in trace_columns for x in column]),
              'configuration': extension_wire(config), 'data': extension_wire(data), 'size': size}
    values.update({name: extension_wire([value], True) for name, value in
                   [('shift', base(3)), ('alpha', alpha), ('zeta', zeta), ('rho', rho), ('eta', eta)]})
    r = journal.write('inspect.json', {'format': 'zkc.entry-run/0', 'session': 'polynomial-reference',
                                     'roles': {'P': {'inputs': values}}})
    result = directory / 'inspect.output.json'
    journal.run([toolchain.runtime, 'run', package, pin, r, f'--results={result}'])
    actual = json.loads(result.read_text())['roles']['P']
    assert actual['valid'] is True
    for name, expected in [('quotient', quotient), ('chunks', chunk_values), ('opened', opened),
                           ('quotient_opened', quotient_opened), ('reduced', reduced)]:
        assert actual[name] == extension_wire(expected), name
