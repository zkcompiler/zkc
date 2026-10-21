"""Write sample Entry inputs from the official vectors and the library's trusted setup.

The blobs and the setup are large, so each document references pinned native
frames written beside it. The output defaults to build/inputs in this project.
"""
import argparse
import hashlib
import json
from pathlib import Path

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parents[2]
CORPUS = ROOT / 'libraries/constructions/ethereum/eip4844/example_vectors.json'
SETUP_SHA256 = 'd39b9f2d047cc9dca2de58f264b6a09448ccd34db967881a6713eacacf0f26b7'
SETUP = ROOT / 'libraries/constructions/ethereum/eip4844/trusted_setup.txt'


def frame(tag, payload, count):
    return b'ZKCV\x00' + bytes([tag]) + count.to_bytes(4, 'little') + payload


class Directory:
    def __init__(self, path):
        self.path = path
        path.mkdir(parents=True, exist_ok=True)

    def reference(self, name, data):
        (self.path / name).write_bytes(data)
        return {'file': name, 'sha256': hashlib.sha256(data).hexdigest()}

    def bytes(self, name, data):
        return self.reference(f'{name}.zkcv', frame(70, data, len(data)))

    def setup(self):
        setup_bytes = SETUP.read_bytes()
        assert hashlib.sha256(setup_bytes).hexdigest() == SETUP_SHA256
        words = setup_bytes.decode().split()
        points = b''.join(bytes.fromhex(word) for word in words[2:2 + 4096])
        return self.reference('setup.zkcv', frame(67, points, 4096))

    def arguments(self, value):
        self.write('arguments', {'inputs': {'P': value}})

    def write(self, name, value):
        (self.path / f'{name}.json').write_text(json.dumps(value, indent=1) + '\n')


def case(corpus, name):
    found = next(c for c in corpus['cases'] if c['name'] == name)
    return {key: (bytes.fromhex(corpus['blobs'][value]) if key == 'blob' else
                  [bytes.fromhex(corpus['blobs'][v]) for v in value] if key == 'blobs' else
                  [bytes.fromhex(v) for v in value] if isinstance(value, list) else bytes.fromhex(value))
            for key, value in found['input'].items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=PROJECT / 'build/inputs')
    args = parser.parse_args()
    corpus = json.loads(CORPUS.read_text())
    blob = case(corpus, 'verify_blob_kzg_proof_case_correct_proof_2')
    point = case(corpus, 'verify_kzg_proof_case_correct_proof_2_0')
    opened = case(corpus, 'compute_kzg_proof_case_valid_blob_2_0')
    batch = case(corpus, 'verify_blob_kzg_proof_batch_case_4')

    d = Directory(args.output / 'example.BlobToCommitment')
    d.arguments({'blob': d.bytes('blob', blob['blob']), 'setup': d.setup()})
    d = Directory(args.output / 'example.ComputeKzgProof')
    d.arguments({'blob': d.bytes('blob', opened['blob']), 'z': list(opened['z']), 'setup': d.setup()})
    d = Directory(args.output / 'example.ComputeChallenge')
    d.arguments({'blob': d.bytes('blob', blob['blob']), 'commitment': list(blob['commitment'])})
    d = Directory(args.output / 'example.PointEvaluationPrecompile')
    versioned = b'\x01' + hashlib.sha256(point['commitment']).digest()[1:]
    data = versioned + point['z'] + point['y'] + point['commitment'] + point['proof']
    d.arguments({'input': list(data)})
    d = Directory(args.output / 'example.KzgProof')
    d.write('public', {key: list(point[key]) for key in ('commitment', 'z', 'y')})
    # The point vectors with this commitment open the blob of the blob vector.
    assert point['commitment'] == blob['commitment']
    d.write('witness', {'blob': d.bytes('blob', blob['blob']), 'setup': d.setup()})
    d = Directory(args.output / 'example.BlobProof')
    d.write('public', {'blob': d.bytes('blob', blob['blob']), 'commitment': list(blob['commitment'])})
    d.write('witness', {'setup': d.setup()})
    d = Directory(args.output / 'example.BlobBatchProof')
    d.write('public', {'blobs': d.bytes('blobs', b''.join(batch['blobs'])),
                       'commitments': d.bytes('commitments', b''.join(batch['commitments'])),
                       'count': str(len(batch['commitments']))})
    d.write('witness', {'setup': d.setup()})


if __name__ == '__main__':
    main()
