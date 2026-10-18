"""Explicit, unweighted coverage catalog for source execution experiments."""
from dataclasses import dataclass

from . import library_cases, programs, stark


@dataclass(frozen=True)
class Case:
    identifier: str
    name: str
    shape: dict
    category: str
    mix: tuple
    limitation: str

    def generate(self, root, directory, statement=0, *, timeout=300):
        shape = self.shape | {'statement': statement}
        if self.name == 'machine':
            return library_cases.machine(root, shape, directory, timeout=timeout)
        if self.name == 'bulletproofs':
            return library_cases.bulletproofs(root, shape, directory)
        if self.name in ('fri', 'air'):
            return getattr(stark, self.name)(root, shape)
        return getattr(programs, self.name)(shape)


def cases():
    result = []
    def add(name, family, shape, category, mix, limitation):
        result.append(Case(name, family, shape, category, mix, limitation))
    for field, short in [('koala-bear', 'kb'), ('bls12-381.fr', 'fr')]:
        for n in (0, 17, 1024, 8192):
            for form in ('reduce', 'collect', 'bulk', 'total-collect-fold', 'total-fold'):
                add(f'finite-{short}-{form}-{n}', 'finite', {'field': field, 'elements': n, 'form': form},
                    'operation', ('pointwise multiply/add', 'sum'), 'Same formula across source forms; includes equality check and Host costs.')
    for n in (17, 1024, 4096):
        for form in ('scalar', 'bulk'):
            add(f'scan-{form}-{n}', 'scan', {'elements': n, 'form': form}, 'operation',
                ('ordered accumulation', 'vector construction'), 'Local program; no storage-release performance claim.')
    for rows, columns in ((7, 13), (32, 33), (128, 31)):
        add(f'control-{rows}x{columns}', 'control', {'rows': rows, 'columns': columns}, 'composition',
            ('nested loops', 'conditional', 'indexing', 'carried scalar state'), 'Independent of machine libraries; not a previously unseen statistical holdout.')
    for degree in (1, 8):
        for n in (32, 1024, 8192):
            add(f'polynomial-ext{degree}-{n}', 'polynomial', {'elements': n, 'extension_degree': degree},
                'operation', ('coset evaluation', 'interpolation', 'vector equality'), 'Full dense coefficients; extension coordinates are nontrivial. Includes validation arithmetic.')
    for n in (1, 17, 1024):
        add(f'extension-{n}', 'extension', {'elements': n}, 'operation', ('dense extension multiply',),
            'Degree-eight KoalaBear extension; does not represent other extension towers.')
    for n in (1, 32, 256):
        add(f'curve-{n}', 'curve', {'elements': n}, 'composition', ('point generation', 'vector scale', 'MSM'),
            'BLS12-381 G1 only; composed operation, not a kernel-only or constant-time comparison.')
    for rows, columns, stride in ((17, 31, 1), (128, 257, 1), (128, 257, 16)):
        add(f'matrix-{rows}x{columns}-s{stride}', 'matrix', {'rows': rows, 'columns': columns, 'stride': stride},
            'operation', ('sparse matrix-vector multiplication',), 'BLS12-381 Fr; density and rectangular shape vary, not a full R1CS proof.')
    for n in (2, 8, 32):
        add(f'pairing-{n}', 'pairing', {'pairs': n}, 'operation', ('scalar multiply', 'pairing', 'equality'),
            'BN254 bilinearity control; not a full Groth16 or KZG workload.')
    for rounds, elements in ((4, 1), (32, 1), (4, 256), (32, 256)):
        add(f'transcript-{rounds}x{elements}', 'transcript', {'rounds': rounds, 'elements': elements}, 'composition',
            ('message encoding', 'transcript absorption', 'challenge sampling', 'ordered state'),
            'Merlin proof construction; no zero-knowledge or independent security claim.')
    for size, bound, queries in ((64, 16, 8), (1024, 16, 8), (1024, 256, 8), (4096, 1024, 8), (1024, 256, 16)):
        add(f'fri-n{size}-d{bound}-q{queries}', 'fri', {'evaluation_size': size, 'degree_bound': bound, 'queries': queries},
            'protocol', ('dense extension polynomial', 'FRI', 'Merkle', 'transcript'), 'Dense polynomials of degree bound-1; not an independently implemented FRI comparison.')
    for height, width, blowup in ((8, 1, 4), (32, 1, 4), (128, 1, 4), (32, 4, 4), (32, 16, 4), (32, 4, 8)):
        add(f'air-h{height}-w{width}-b{blowup}', 'air', {'height': height, 'width': width, 'evaluation_size': height*blowup, 'queries': 8},
            'protocol', ('trace extension', 'quadratic AIR', 'quotients', 'FRI', 'Merkle', 'transcript'),
            'Independent height/width/blowup sweeps; one table with no lookup or memory argument.')
    for n in (1, 3, 8, 16):
        add(f'bulletproofs-{n}', 'bulletproofs', {'commitments': n}, 'protocol', ('vector scale', 'MSM', 'transcript'),
            'Retained fixture amounts/masks; includes non-power-of-two aggregation. Not a sampled wallet workload.')
    for reduction in ('LogUp', 'Product'):
        for fixture in ('arithmetic-only', 'store-load'):
            add(f'machine-{reduction.lower()}-{fixture}', 'machine', {'reduction': reduction, 'fixture': fixture},
                'regression', ('table composition', 'lookup/memory argument', 'FRI'),
                'Shared STARK libraries and small fixtures; not independent evidence for scaling or a production zkVM.')
    return result


# Deliberately fixed lists: adding a workload does not silently expand a smoke run.
SMOKE = ('finite-kb-reduce-17', 'finite-kb-collect-17', 'finite-fr-bulk-17',
         'scan-scalar-17', 'scan-bulk-17', 'control-7x13', 'polynomial-ext1-32',
         'polynomial-ext8-32', 'extension-17', 'curve-1', 'pairing-2',
         'transcript-4x1', 'fri-n64-d16-q8', 'air-h8-w1-b4')


def catalog():
    return [(case.identifier, case, case.shape) for case in cases()]
