#!/usr/bin/env python3
"""Native refusal of unmodelled control and preservation of an authored stop."""
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
    parser.add_argument('--output', type=Path, default=ROOT / 'build/experiments/constructed/boundaries')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    source = ROOT / 'lean/bridges/constructed/fixtures/bounded-control.zkc'
    options = ['--source-format=zkc', '--entry=bounded::Demo', f'--module=bounded={source}']
    original = args.output / 'bounded.mlir'
    original.write_text(execute([args.compiler, 'language-emit', *options]))
    interface = json.loads(execute([args.compiler, 'language-interface', *options]))
    policy = ['zkc.native-proof-policy/0', interface['protocol'], 'role00000000', 'role00000001',
              '0', 'merlin3.bls12-381.fr64be/0', ['2'], ['0'],
              [['label_6368616c6c656e6765', 'label_64656c6976657279_0']], 'zkc.framed/0', '']
    policy_path = args.output / 'bounded.policy.json'
    policy_path.write_text(json.dumps(policy))
    candidate = args.output / 'bounded.candidate.mlir'
    candidate.write_text(execute([args.compiler, 'protocol-construct-proof', original, policy_path]))
    refused = execute([args.compiler, 'protocol-constructed-lean', original, policy_path, candidate], success=False)
    assert 'constructed-source-control: protocol.loop' in refused

    # A selected decoder with an unconditional authored stop normalizes to an
    # actual terminal stop, including the primitive/decode prefix before it.
    source = args.output / 'stopping.zkc'
    source.write_text((ROOT / 'lean/bridges/constructed/fixtures/schnorr-codec.zkc').read_text()
                      .replace('return value;', 'stop "abort";', 1))
    options = ['--source-format=zkc', '--entry=constructed_codec::Packed',
               f'--module=constructed_codec={source}']
    options += [f'--module=zkc::{name}={ROOT}/libraries/zkc/{name}.zkc'
                for name in ['proof', 'encoding', 'bytes']]
    original = args.output / 'stopping.mlir'
    original.write_text(execute([args.compiler, 'language-emit', *options]))
    interface = json.loads(execute([args.compiler, 'language-interface', *options]))
    policy[1] = interface['protocol']
    policy[6:8] = [['4'], ['0', '1']]
    policy[9:11] = ['raw.bytes/0', interface['job']['construction']['symbol']]
    policy_path = args.output / 'stopping.policy.json'
    policy_path.write_text(json.dumps(policy))
    candidate = args.output / 'stopping.candidate.mlir'
    candidate.write_text(execute([args.compiler, 'protocol-construct-proof', original, policy_path]))
    output = args.output / 'Snapshot.json'
    data = extract(args.compiler, original, policy_path, candidate, output, 'ConstructedStoppingCodec')
    assert data[10][-1][0:2] == ['stop', 'abort'] and data[11] == []
    execute(['lake', 'env', 'lean', output.with_suffix('.lean')], cwd=ROOT / 'lean')
    native = Native(execute([args.optimizer, candidate, '--mlir-print-op-generic']), lambda *_: 0)
    inputs = [5, 35, 19, native.buffer((55).to_bytes(48, 'big') + bytes(32))]
    result = native.run(data[5], inputs)
    assert result == ['stopped', 'abort']
    run = args.output / 'run.json'
    run.write_text(json.dumps(['zkc.constructed-run/0', inputs, native.entries]))
    assert json.loads(lean(output, run)) == ['zkc.constructed-result/0', result, len(native.entries),
                                            [[entry[0], entry] for entry in native.entries]]
    report = {'unsupported_control': 'constructed-source-control: protocol.loop',
              'authored_stop': result, 'primitive_calls_before_stop': len(native.entries)}
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
