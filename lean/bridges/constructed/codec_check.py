#!/usr/bin/env python3
"""Actual selected Stream codec import, decoding stops and final coverage controls."""
import argparse
import json
from pathlib import Path

from check import execute, lean
from extract import ROOT, extract
from native import Native


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--optimizer', type=Path, default=ROOT / 'build/compiler/zkc-opt')
    parser.add_argument('--output', type=Path, default=ROOT / 'build/experiments/constructed/codec')
    args = parser.parse_args()
    directory = args.output
    directory.mkdir(parents=True, exist_ok=True)
    source = ROOT / 'lean/bridges/constructed/fixtures/schnorr-codec.zkc'
    options = ['--source-format=zkc', '--entry=constructed_codec::Packed',
               f'--module=constructed_codec={source}']
    options += [f'--module=zkc::{name}={ROOT}/libraries/zkc/{name}.zkc'
                for name in ['proof', 'encoding', 'bytes']]
    original = directory / 'source.mlir'
    original.write_text(execute([args.compiler, 'language-emit', *options]))
    interface = json.loads(execute([args.compiler, 'language-interface', *options]))
    policy = ['zkc.native-proof-policy/0', interface['protocol'], 'role00000000', 'role00000001',
              '0', 'merlin3.bls12-381.fr64be/0', ['4'], ['0', '1'],
              [['label_6368616c6c656e6765', 'label_64656c6976657279_0']], 'raw.bytes/0',
              interface['job']['construction']['symbol']]
    policy_path = directory / 'policy.json'
    policy_path.write_text(json.dumps(policy))
    candidate = directory / 'candidate.mlir'
    candidate.write_text(execute([args.compiler, 'protocol-construct-proof', original, policy_path]))
    generic = execute([args.optimizer, candidate, '--mlir-print-op-generic'])
    (directory / 'generic.mlir').write_text(generic)
    output = directory / 'Snapshot.json'
    data = extract(args.compiler, original, policy_path, candidate, output, 'ConstructedSchnorrCodec')
    extract(args.compiler, original, policy_path, candidate, output, 'ConstructedSchnorrCodec', check=True)
    execute(['lake', 'env', 'lean', output.with_suffix('.lean')], cwd=ROOT / 'lean')
    assert sum(i[0] == 'guard' for i in data[10]) == 3
    base, secret, nonce, initial = 5, 7, 11, 19
    commitment = base * nonce % 97
    observed = (initial * 131 + commitment * 17 + 1) % 65521
    response = (nonce + (observed % 97) * secret) % 97
    proof = commitment.to_bytes(48, 'big') + response.to_bytes(32, 'big')
    cases = [('valid', proof, 'returned'),
             ('invalid-point', b'\xff' * 48 + proof[48:], 'reject'),
             ('invalid-scalar', proof[:48] + b'\xff' * 32, 'reject'),
             ('truncated', proof[:-1], 'refused'),
             ('trailing', proof + b'\0', 'reject')]
    requests, expected, evidence = [], [], []
    for name, payload, ending in cases:
        native = Native(generic, lambda *_: 0)
        token = native.buffer(payload)
        inputs = [base, base * secret % 97, initial, token]
        result = native.run(data[5], inputs)
        assert result[0] == ending if ending == 'returned' else result == ['stopped', ending]
        if ending == 'returned':
            assert result[1][0] == 1
        requests.append(['zkc.constructed-run/0', inputs, native.entries])
        expected.append(['zkc.constructed-result/0', result, len(native.entries),
                         [[entry[0], entry] for entry in native.entries]])
        evidence.append({'case': name, 'outcome': result, 'primitive_calls': len(native.entries)})
    runs = directory / 'runs.json'
    runs.write_text(json.dumps(['zkc.constructed-runs/0', requests]))
    assert json.loads(lean(output, runs)) == expected
    report = {'candidate': data[2], 'handlers': len(data[7]), 'instructions': len(data[10]),
              'runs': evidence, 'meaning': 'Z/97, tokenized test codec, deterministic state-sensitive transcript'}
    (directory / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
