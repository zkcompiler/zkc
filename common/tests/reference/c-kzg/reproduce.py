"""Regenerate the EIP-4844 corpora from the pinned c-kzg-4844 checkout.

vectors.json holds the upstream EIP-4844 vectors. extra.json holds cases derived
from them (malformed points, changed proofs, duplicated and reordered batches)
with the outcomes computed by the pinned c-kzg-4844 reference executable.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

TAG = 'v2.1.8'
REVISION = 'e125905e5e01186e6ccb7a0ced4845bf7eddbcfe'
SETUP_SHA256 = 'd39b9f2d047cc9dca2de58f264b6a09448ccd34db967881a6713eacacf0f26b7'
FUNCTIONS = [
    'blob_to_kzg_commitment',
    'compute_kzg_proof',
    'compute_blob_kzg_proof',
    'compute_challenge',
    'verify_kzg_proof',
    'verify_blob_kzg_proof',
    'verify_blob_kzg_proof_batch',
]
# Values too large to repeat per case are stored once, keyed by SHA-256.
LARGE = {'blob', 'blobs'}


def scalar(text):
    """One YAML value of the upstream format: hex, a Boolean or null."""
    text = text.strip()
    if text in ('null', 'true', 'false'):
        return {'null': None, 'true': True, 'false': False}[text]
    if text.startswith("'") and text.endswith("'"):
        text = text[1:-1]
    if not text.startswith('0x'):
        raise ValueError(f'unexpected value {text[:20]!r}')
    return bytes.fromhex(text[2:])


def parse(path):
    """The upstream data.yaml files use a fixed two-level layout."""
    inputs, output, key, section = {}, None, None, None
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        if line == 'input:':
            section = 'input'
        elif line.startswith('output:'):
            section, rest = 'output', line[len('output:'):].strip()
            output = scalar(rest) if rest else []
        elif section == 'output':
            assert line.startswith('- '), line
            output.append(scalar(line[2:]))
        elif line.startswith('  - '):
            inputs[key].append(scalar(line[4:]))
        else:
            assert line.startswith('  ') and ':' in line, line
            key, rest = line[2:].split(':', 1)
            rest = rest.strip()
            inputs[key] = [] if rest in ('', '[]') else scalar(rest)
    return inputs, output


def text(value, blobs):
    if isinstance(value, bytes):
        return value.hex()
    if isinstance(value, list):
        return [text(v, blobs) for v in value]
    return value


def large(value, blobs):
    if isinstance(value, list):
        return [large(v, blobs) for v in value]
    digest = hashlib.sha256(value).hexdigest()
    blobs[digest] = value.hex()
    return digest


R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
P = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
INFINITY = bytes([0xc0]) + bytes(47)


def point_variants(point):
    """Encodings near a canonical compressed G1 point that every decoder refuses."""
    return {
        'compression-flag-cleared': bytes([point[0] & 0x7f]) + point[1:],
        'infinity-with-sign': bytes([0xe0]) + bytes(47),
        'infinity-with-coordinate': INFINITY[:47] + b'\x01',
        'uncompressed-infinity': bytes([0x40]) + bytes(47),
        'coordinate-equal-to-modulus': bytes([0x80 | (P >> 376)]) + P.to_bytes(48, 'big')[1:],
        # x = 1 gives x^3 + 4 = 5, a nonsquare in the base field.
        'coordinate-without-point': bytes([0x80]) + bytes(46) + b'\x01',
        # x = 0 gives y = 2: on the curve, outside the prime-order subgroup.
        'point-outside-subgroup': bytes([0x80]) + bytes(47),
        'trailing-byte': point + b'\x00',
        'missing-byte': point[:-1],
    }


def negated(point):
    """The other square root: a valid encoding of the negated point."""
    assert point[0] & 0x40 == 0
    return bytes([point[0] ^ 0x20]) + point[1:]


def derived(cases):
    """Cases derived from upstream inputs; outcomes come from the reference."""
    def find(name):
        return next(dict(c['input']) for c in cases if c['name'] == name)
    extra = []

    def add(function, name, values):
        extra.append({'function': function, 'name': name, 'input': values})
    point = {k: bytes.fromhex(v) for k, v in find('verify_kzg_proof_case_correct_proof_2_0').items()}
    for part in ('commitment', 'proof'):
        for name, value in point_variants(point[part]).items():
            add('verify_kzg_proof', f'{part}-{name}', dict(point, **{part: value}))
    add('verify_kzg_proof', 'negated-proof', dict(point, proof=negated(point['proof'])))
    add('verify_kzg_proof', 'identity-proof', dict(point, proof=INFINITY))
    shifted = ((int.from_bytes(point['y'], 'big') + 1) % R).to_bytes(32, 'big')
    add('verify_kzg_proof', 'shifted-value', dict(point, y=shifted))
    for part in ('z', 'y'):
        for name, value in [('modulus', R.to_bytes(32, 'big')), ('wide', bytes(33)), ('narrow', bytes(31))]:
            add('verify_kzg_proof', f'{part}-{name}', dict(point, **{part: value}))

    blob, other = find('verify_blob_kzg_proof_case_correct_proof_2'), find('verify_blob_kzg_proof_case_correct_proof_3')
    single = {'blob': blob['blob'], 'commitment': bytes.fromhex(blob['commitment']),
              'proof': bytes.fromhex(blob['proof'])}
    add('verify_blob_kzg_proof', 'other-proof', dict(single, proof=bytes.fromhex(other['proof'])))
    add('verify_blob_kzg_proof', 'other-commitment', dict(single, commitment=bytes.fromhex(other['commitment'])))
    add('verify_blob_kzg_proof', 'other-blob', dict(single, blob=other['blob']))
    add('verify_blob_kzg_proof', 'negated-proof', dict(single, proof=negated(single['proof'])))
    for name, value in point_variants(single['proof']).items():
        add('verify_blob_kzg_proof', f'proof-{name}', dict(single, proof=value))

    batch = find('verify_blob_kzg_proof_batch_case_4')
    openings = [(b, bytes.fromhex(c), bytes.fromhex(p))
                for b, c, p in zip(batch['blobs'], batch['commitments'], batch['proofs'], strict=True)]
    assert openings[2][2][0] & 0x40 == 0 and openings[3][2][0] & 0x40 == 0

    def add_batch(name, chosen):
        add('verify_blob_kzg_proof_batch', name, {'blobs': [o[0] for o in chosen],
                                                  'commitments': [o[1] for o in chosen],
                                                  'proofs': [o[2] for o in chosen]})
    o = openings
    add_batch('duplicated-opening', [o[0], o[1], o[2], o[3], o[2]])
    add_batch('repeated-opening', [o[3], o[3], o[3]])
    add_batch('single-opening', [o[2]])
    add_batch('reordered', [o[2], o[0], o[3], o[1]])
    add_batch('reversed', o[::-1])
    add_batch('duplicated-commitment', [o[0], o[1], o[2], (o[3][0], o[2][1], o[3][2])])
    add_batch('duplicated-blob', [o[0], o[1], o[2], (o[2][0], o[3][1], o[3][2])])
    add_batch('duplicated-statement-other-proof', [o[0], o[1], o[2], (o[2][0], o[2][1], o[3][2])])
    add_batch('swapped-proofs', [o[0], o[1], (o[2][0], o[2][1], o[3][2]), (o[3][0], o[3][1], o[2][2])])
    add_batch('changed-proof', [o[0], o[1], o[2], (o[3][0], o[3][1], o[2][2])])
    add_batch('negated-proof', [o[0], o[1], o[2], (o[3][0], o[3][1], negated(o[3][2]))])
    add_batch('identity-proof', [o[0], o[1], o[2], (o[3][0], o[3][1], INFINITY)])
    add_batch('invalid-proof', [o[0], o[1], o[2], (o[3][0], o[3][1], bytes([o[3][2][0] & 0x7f]) + o[3][2][1:])])
    add_batch('single-other-proof', [(o[2][0], o[2][1], o[3][2])])
    shorter = [o[0], o[1], o[2], o[3]]
    extra.append({'function': 'verify_blob_kzg_proof_batch', 'name': 'missing-proof',
                  'input': {'blobs': [x[0] for x in shorter], 'commitments': [x[1] for x in shorter],
                            'proofs': [x[2] for x in shorter[:-1]]}})
    extra.append({'function': 'verify_blob_kzg_proof_batch', 'name': 'extra-proof',
                  'input': {'blobs': [x[0] for x in shorter], 'commitments': [x[1] for x in shorter],
                            'proofs': [x[2] for x in shorter] + [shorter[0][2]]}})
    extra.append({'function': 'verify_blob_kzg_proof_batch', 'name': 'missing-blob',
                  'input': {'blobs': [x[0] for x in shorter[:-1]], 'commitments': [x[1] for x in shorter],
                            'proofs': [x[2] for x in shorter]}})
    return extra


def request(case, blobs):
    """One reference input line; blob arguments are corpus keys."""
    def hexed(value):
        return value.hex() if isinstance(value, bytes) else value

    def blob(key):
        return blobs[key]

    def items(values, convert):
        return ','.join(convert(v) for v in values) or '-'
    i, f = case['input'], case['function']
    if f == 'verify_kzg_proof':
        args = [hexed(i[k]) for k in ('commitment', 'z', 'y', 'proof')]
    elif f == 'verify_blob_kzg_proof':
        args = [blob(i['blob']), hexed(i['commitment']), hexed(i['proof'])]
    else:
        args = [items(i['blobs'], blob), items(i['commitments'], hexed), items(i['proofs'], hexed)]
    return ' '.join([f, *args])


def outcome(line):
    return {'true': True, 'false': False, 'error': None}[line]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    head = subprocess.check_output(['git', '-C', args.source, 'rev-parse', 'HEAD'], text=True).strip()
    if head != REVISION or subprocess.check_output(['git', '-C', args.source, 'status', '--porcelain']):
        parser.error(f'the source must be the unmodified c-kzg-4844 {TAG} checkout')
    setup = (args.source / 'src/trusted_setup.txt').read_bytes()
    if hashlib.sha256(setup).hexdigest() != SETUP_SHA256:
        parser.error('unexpected trusted setup')
    blobs, cases, files = {}, [], hashlib.sha256()
    for function in FUNCTIONS:
        for path in sorted((args.source / 'tests' / function / 'kzg-mainnet').glob('*/data.yaml')):
            raw = path.read_bytes()
            files.update(path.relative_to(args.source).as_posix().encode() + b'\0' + raw + b'\0')
            inputs, output = parse(path)
            cases.append({
                'function': function,
                'name': path.parent.name,
                'input': {key: large(value, blobs) if key in LARGE else text(value, blobs)
                          for key, value in inputs.items()},
                'output': text(output, blobs),
            })
    corpus = {
        'source': {'repository': 'https://github.com/ethereum/c-kzg-4844', 'tag': TAG,
                   'revision': REVISION, 'trusted_setup_sha256': SETUP_SHA256,
                   'vector_files_sha256': files.hexdigest()},
        'blobs': dict(sorted(blobs.items())),
        'cases': cases,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'vectors.json').write_text(json.dumps(corpus, indent=1) + '\n')

    extra = derived(cases)
    lines = [request(case, corpus['blobs']) for case in extra]
    answers = subprocess.run([args.reference.resolve(), args.source / 'src/trusted_setup.txt'],
                             input='\n'.join(lines) + '\n', capture_output=True, text=True,
                             check=True).stdout.splitlines()
    assert len(answers) == len(extra)
    for case, answer in zip(extra, answers, strict=True):
        case['input'] = {key: [v.hex() if isinstance(v, bytes) else v for v in value]
                         if isinstance(value, list) else value.hex() if isinstance(value, bytes) else value
                         for key, value in case['input'].items()}
        case['output'] = outcome(answer)
    (args.output / 'extra.json').write_text(json.dumps({
        'source': {'reference': f'c-kzg {TAG}', 'derived_from': 'vectors.json'},
        'cases': extra}, indent=1) + '\n')
    print(len(cases), 'cases,', len(blobs), 'blobs,', len(extra), 'derived cases')


if __name__ == '__main__':
    main()
