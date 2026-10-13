#!/usr/bin/env python3
"""Export/check an actual constructed verifier and its transparent Lean carrier.

The compiler rechecks the entire supplied candidate against retained source.
--check regenerates both artifacts exactly; a digest is never authentication.
"""
import argparse
import json
from pathlib import Path
import subprocess

from snapshot import render

ROOT = Path(__file__).resolve().parents[3]


def extract(compiler, source, policy, candidate, output, namespace, check=False):
    command = [str(compiler), 'protocol-constructed-lean', str(source), str(policy), str(candidate)]
    result = subprocess.run(command, text=True, capture_output=True, timeout=90, check=True)
    data = json.loads(result.stdout)
    generated = render(data, namespace)
    json_text = json.dumps(data, ensure_ascii=True, indent=2) + '\n'
    if check:
        if output.read_text() != json_text or output.with_suffix('.lean').read_text() != generated:
            raise ValueError('constructed-source-mismatch')
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json_text)
        output.with_suffix('.lean').write_text(generated)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('policy', type=Path)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--compiler', type=Path, default=ROOT / 'build/compiler/zkc-compile')
    parser.add_argument('--namespace', default='ConstructedCandidate')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    try:
        data = extract(args.compiler, args.source, args.policy, args.candidate,
                       args.output, args.namespace, args.check)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        raise SystemExit(str(error)) from error
    print(json.dumps({'status': 'checked' if args.check else 'exported',
                      'candidate': data[2], 'instructions': len(data[10])}))


if __name__ == '__main__':
    main()
