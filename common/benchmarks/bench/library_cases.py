"""Existing library compositions, explicitly labeled as correlated evidence."""
import json
import sys

from .io import Journal
from .programs import Program
from .stark import mutate_claim


def mutate_response(proof):
    # Monero BP+ puts the first response scalar after three 32-byte points.
    # Keep a canonical scalar and the same framing/statement.
    order = 2**252 + 27742317777372353535851937790883648493
    if len(proof) < 128 or proof[:8] == b'ZKCPRF00' or int.from_bytes(proof[96:128], 'little') >= order:
        raise ValueError('expected raw Monero proof with a canonical response')
    changed = (int.from_bytes(proof[96:128], 'little') + 1) % order
    return proof[:96] + changed.to_bytes(32, 'little') + proof[128:]


def bulletproofs(root, shape, directory):
    n, index = shape['commitments'], shape['statement']
    corpus = root/'common/tests/fixtures/bulletproofs-plus/corpus.json'
    cases = {c['name']: c for c in json.loads(corpus.read_text())['cases']}
    kinds = ('mixed', 'max', 'random', 'zero')
    if index >= 4*n:
        raise ValueError('BP+ changing-input schedule exceeds the retained fixture permutations')
    case = cases[f'{n}-{kinds[index % 4]}']
    rotate = index // 4
    def rotated(values):
        return values[rotate:] + values[:rotate]
    commitments = bytes.fromhex(case['commitments'])
    points = [commitments[i:i+32] for i in range(0, len(commitments), 32)]
    public = {'commitments': list(b''.join(rotated(points))), 'rounds': str(6+(n-1).bit_length())}
    private = {'values': list(map(str, rotated(case['values']))), 'masks': rotated(case['masks'])}
    # Negate one admitted point without choosing another scheduled statement.
    altered = list(b''.join(rotated(points)))
    altered[31] ^= 0x80
    changed = public | {'commitments': altered}
    source = root/'examples/projects/bulletproofs-plus/main.zkc'
    return Program(source.read_text(), [{'public': public, 'witness': private}], entry='example::Proof',
                   dependencies=('bulletproofs',), proof=True, changed=changed, mutate_proof=mutate_response,
                   support=(source, corpus), oracle='retained Monero conformance corpus; same-stack verification here, independent Monero comparison in the monero family')


def machine(root, shape, directory, *, timeout):
    if shape['statement']:
        raise ValueError('machine regression fixtures support fixed inputs only')
    project = root/'common/tests/fixtures/projects/accumulator-machine'
    fixture = root/'compiler/adapters/accumulator-machine/fixtures'/shape['fixture']/'run.json'
    generated = directory/'machine-inputs'
    command = [sys.executable, project/'prepare.py', fixture, generated]
    if shape['fixture'] == 'store-load':
        command += ['--memory-clocks', '16', '--memory-present']
    Journal(directory/'generator', timeout).command(command, cwd=root)
    public, witness = [json.loads((generated/f'{name}.json').read_text()) for name in ('public', 'witness')]
    bundle = root/'compiler/adapters/accumulator-machine/fixtures/bundle.json'
    return Program((project/'main.zkc').read_text(), [{'public': public, 'witness': witness}],
        entry=f'accumulator_machine::Proof{shape["reduction"]}', dependencies=('stark', 'fri'),
        assets={'machine': json.loads(bundle.read_text())}, proof=True,
        mutate_proof=mutate_claim,
        changed=public | {'final': str((int(public['final'])+1) % 2130706433)},
        support=(project/'main.zkc', project/'prepare.py', fixture, bundle,
                 root/'compiler/adapters/accumulator-machine/accumulator_machine.py', root/'compiler/adapters/ring_arena.py'),
        oracle='existing external machine adapter and same-stack verifier; correlated library regression, not an independent VM benchmark')
