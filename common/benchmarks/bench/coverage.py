"""Explicit, unweighted coverage catalog for source execution experiments."""
from dataclasses import dataclass

from . import algebra as a
from . import commitments, expressions, library_algebra, library_cases, operations, programs, stark


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
        if self.name in ('kzg', 'curve_family', 'sparse_matrix', 'opening_quotient'):
            return getattr(library_algebra, self.name)(shape, root=root)
        if self.name == 'machine':
            return library_cases.machine(root, shape, directory, timeout=timeout)
        if self.name == 'bulletproofs':
            return library_cases.bulletproofs(root, shape, directory)
        if self.name in ('fri', 'air'):
            return getattr(stark, self.name)(root, shape)
        if self.name == 'stark':
            return stark.library(root, shape)
        if self.name == 'expression':
            return expressions.expression(shape, root=root)
        if self.name == 'field_vector':
            return operations.field_vector(shape, root=root)
        if self.name == 'host_vector':
            return operations.host_vector(shape)
        if self.name in ('hash_bytes', 'poseidon', 'merkle'):
            return getattr(commitments, self.name)(shape)
        if self.name in ('transform', 'coset', 'coset_batch', 'coset_point', 'curve_operation'):
            return getattr(operations, self.name)(shape)
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
    for field, short in [('koala-bear', 'kb'), ('bls12-381.fr', 'fr'),
                         ('koala-bear.ext8-binomial3', 'ext8')]:
        # Three encoded extension columns at 8192 exceed the normal Host
        # request-byte ceiling. Keep that ceiling, and record the smaller shape.
        for n in (0, 17, 1024, 4096 if short == 'ext8' else 8192):
            for sink in ('map', 'sum', 'product'):
                for form in ('map', 'collect', 'bulk'):
                    add(f'numerical-{short}-{sink}-{form}-{n}', 'numerical',
                        {'field': field, 'elements': n, 'form': form, 'sink': sink},
                        'operation', ('two columns', 'scalar captures', 'pointwise arithmetic', sink),
                        'Identical inputs and polynomial across source forms; includes equality and Host costs. Non-base extension captures vary every coordinate.')
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
    for height, width, blowup in ((8, 1, 4), (32, 1, 4), (128, 1, 4), (1024, 1, 4),
                                  (32, 4, 4), (1024, 4, 4), (32, 16, 4), (32, 4, 8)):
        add(f'air-h{height}-w{width}-b{blowup}', 'air', {'height': height, 'width': width, 'evaluation_size': height*blowup, 'queries': 8},
            'protocol', ('trace extension', 'quadratic AIR', 'quotients', 'FRI', 'Merkle', 'transcript'),
            'Independent height/width/blowup sweeps; one table with no lookup or memory argument.')
        add(f'stark-h{height}-w{width}-b{blowup}', 'stark', {'height': height, 'width': width, 'evaluation_size': height*blowup, 'queries': 8},
            'protocol', ('trace extension', 'quadratic AIR', 'quotients', 'FRI', 'Merkle multi-opening', 'transcript'),
            'The air cases\' AIR and sizes through the parameterized library; quartic challenges, Poseidon2 Merkle trees.')
    for n in (1, 3, 8, 16):
        add(f'bulletproofs-{n}', 'bulletproofs', {'commitments': n}, 'protocol', ('vector scale', 'MSM', 'transcript'),
            'Retained fixture amounts/masks; includes non-power-of-two aggregation. Not a sampled wallet workload.')
    for reduction in ('LogUp', 'Product'):
        for fixture in ('arithmetic-only', 'store-load'):
            add(f'machine-{reduction.lower()}-{fixture}', 'machine', {'reduction': reduction, 'fixture': fixture},
                'regression', ('table composition', 'lookup/memory argument', 'FRI'),
                'Shared STARK libraries and small fixtures; not independent evidence for scaling or a production zkVM.')
    # Representative authored shapes, not a shape x field x size product. Roles
    # are fixed here, before timing; no selector uses measured performance.
    expression_panel = [(name, 'kb', 129, sink) for name in expressions.EXPRESSIONS
                        for sink in ('map', 'sum', 'product')]
    expression_panel += [('short-horner', 'kb', n, 'map') for n in (0, 1, 31, 32, 33, 127, 128, 4096)]
    expression_panel += [
        ('short-horner', 'fr', 33, 'sum'), ('wide-independent', 'fr', 128, 'map'),
        ('deep-horner', 'fr', 1024, 'product'), ('capture-heavy', 'ext4', 31, 'sum'),
        ('shared-subexpression', 'ext4', 129, 'map'), ('deep-horner', 'ext4', 1024, 'map'),
        ('shared-subexpression', 'ext8', 33, 'product'), ('wide-independent', 'ext8', 127, 'map'),
        ('capture-heavy', 'ext8', 1024, 'sum'), ('short-horner', 'binary64', 32, 'map'),
        ('input-heavy', 'binary64', 128, 'sum'), ('shared-subexpression', 'binary64', 1024, 'product'),
        ('short-horner', 'binary-ext3', 1024, 'map'), ('capture-heavy', 'binary-ext3', 127, 'sum'),
        ('shared-subexpression', 'binary-ext3', 129, 'product'), ('input-heavy', 'kb', 1024, 'map'),
        ('difference-products', 'ext4', 33, 'sum'), ('alternating-powers', 'binary64', 127, 'map'),
    ]
    fields = {'kb': 'koala-bear', 'fr': 'bls12-381.fr', 'ext4': 'koala-bear.ext4-binomial3',
              'ext8': 'koala-bear.ext8-binomial3', 'binary64': a.BINARY,
              'binary-ext3': a.BINARY_CUBIC}
    for expression, short, n, sink in expression_panel:
        definition = expressions.EXPRESSIONS[expression]
        add(f'expression-{short}-{expression}-{sink}-{n}', 'expression',
            {'field': fields[short], 'expression': expression, 'elements': n, 'sink': sink,
             'role': definition.role, 'columns': len(definition.columns), 'captures': len(definition.captures)},
            'operation', ('authored Math function', expression, sink),
            'Fixed shape panel; independent scalar formula, full result check and Host costs. Source shape is not a guarantee of lowered IR shape.')
    vector_panel = [('kb', op, 129) for op in ('add', 'subtract', 'hadamard', 'scale', 'sum', 'product', 'dot')]
    vector_panel += [('kb', 'sum', 0), ('kb', 'product', 0), ('fr', 'dot', 1024),
                     ('ext4', 'hadamard', 129), ('ext8', 'sum', 1024),
                     ('binary64', 'product', 33), ('binary-ext3', 'dot', 33)]
    for short, operation, n in vector_panel:
        add(f'field-vector-{short}-{operation}-{n}', 'field_vector',
            {'field': fields[short], 'elements': n, 'operation': operation}, 'operation', (operation,),
            'Independent scalar arithmetic; SDK/run includes validation and Host costs, not kernel-only time.')
    for degree, n in ((1, 32), (4, 32), (8, 32), (1, 1024), (8, 1024)):
        for operation in ('dft', 'interpolate'):
            add(f'transform-ext{degree}-{operation}-{n}', 'transform',
                {'extension_degree': degree, 'elements': n, 'operation': operation}, 'operation', (operation,),
                'One direction, unit shift, dense full-degree coefficients; independent Python oracle. Includes polynomial adaptation, equality and Host costs.')
    for degree in (1, 4, 8):
        # Width, transform length and conversion cost vary separately. Both
        # forms consume identical inputs and check every output coordinate.
        for height, width, layout in [(32, w, 'columns') for w in (1, 4, 16, 64)] + [
                (1024, 1, 'columns'), (256, 4, 'columns'), (32, 4, 'rows')]:
            for form in ('columns', 'library'):
                add(f'coset-batch-ext{degree}-h{height}-w{width}-{layout}-{form}', 'coset_batch',
                    {'extension_degree': degree, 'height': height, 'width': width,
                     'evaluation_size': height*2, 'layout': layout, 'form': form},
                    'operation', ('coset extension', 'batch output construction', layout+' layout', 'vector equality'),
                    'Independent integer transforms and full output comparison. Column loop and library share inputs; row layout includes both transposes. SDK/run includes validation and Host costs.')
        for n in (32, 8192):
            for operation in ('points', 'fold'):
                add(f'coset-ext{degree}-{operation}-{n}', 'coset',
                    {'extension_degree': degree, 'elements': n, 'operation': operation},
                    'operation', ('coset shift', operation, 'vector equality'),
                    'Independent integer field oracle; dense extension coordinates and arbitrary fold inputs. Includes equality and Host costs, not a low-degree test.')
    # Fixed point-evaluation panel: vary width and height separately, then
    # compare repeated interpolation with coefficient reuse for many points.
    # Keep small controls even when interpolation is the faster strategy.
    point_panel = [(32, 1, 1), (32, 4, 1), (32, 16, 1), (1024, 1, 1), (1024, 4, 1),
                   (4096, 1, 1), (4096, 4, 1), (32, 4, 8), (1024, 1, 8), (4096, 1, 8)]
    for degree in (1, 4, 8):
        domains = [(height, width, points, 'off-domain') for height, width, points in point_panel]
        for height, width, points, kind in domains + [(4, 4, 4, 'on-domain')]:
            forms = ('coefficients', 'library', 'reused-coefficients') if points > 1 else \
                    ('coefficients', 'library')
            for form in forms:
                strategy = {'coefficients': 'Interpolation repeated per point and column, then native Horner.',
                            'library': 'Library opening_claims per point on one checked batch.',
                            'reused-coefficients': 'Interpolation once per column, native Horner per point; includes output transpose.'}[form]
                add(f'coset-point-ext{degree}-h{height}-w{width}-p{points}-{kind}-{form}', 'coset_point',
                    {'extension_degree': degree, 'height': height, 'width': width,
                     'points': points, 'point_kind': kind, 'form': form},
                    'operation', ('coset point evaluation', form, kind, 'point-major vector equality'),
                    'Independent full-degree coefficients and Horner expectations; identical words, shifts and points across forms. '
                    + strategy + ' Repeated interpolation and coefficient reuse are distinct strategies. '
                    'SDK/run includes setup, output construction, equality and Host costs; default capacities.')
    for n in (1, 33, 128):
        for operation in ('vector-scale', 'scale-each', 'msm'):
            add(f'curve-operation-{operation}-{n}', 'curve_operation',
                {'elements': n, 'operation': operation}, 'operation', ('point construction', operation, 'group-law validation'),
                'BLS12-381 G1; weaker scalar/group-law oracle shares native group kernels. SDK/run includes point generation and validation, not kernel-only time.')
    for height, width, degree, blowup in ((8, 2, 2, 4), (32, 4, 2, 4), (128, 4, 2, 4),
                                          (32, 8, 2, 4), (32, 4, 3, 8)):
        for family in ('air', 'stark'):
            add(f'{family}-coupled-d{degree}-h{height}-w{width}-b{blowup}', family,
                {'height': height, 'width': width, 'evaluation_size': height*blowup,
                 'queries': 8, 'constraint': 'coupled', 'constraint_degree': degree},
                'protocol', ('coupled columns', f'degree-{degree} AIR', 'quotients', 'FRI', 'Merkle', 'transcript'),
                'Matched one-table AIR across both profiles; independent Python trace. Default capacities; not a production or multi-table scaling study.')
    for size in (0, 64, 8192):
        add(f'hash-sha256-{size}', 'hash_bytes', {'algorithm': 'sha256', 'payload_bytes': size},
            'operation', ('SHA-256', 'digest equality'),
            'Independent hashlib digest; includes byte input adaptation, equality and Host costs.')
    for count in (1, 17, 256):
        add(f'poseidon2-kb-states-{count}', 'poseidon', {'field': 'koala-bear', 'state_width': 16, 'states': count},
            'operation', ('batched Poseidon2 permutation', 'vector equality'),
            'Published Plonky3 known answer repeated per state; only one distinct state; includes result check and Host costs.')
    for height, width, opening in ((16, 1, 'single'), (256, 1, 'single'), (16, 8, 'single'),
                                    (16, 9, 'single'), (13, 9, 'single'), (256, 1, 'multi')):
        add(f'merkle-poseidon2-h{height}-w{width}-{opening}', 'merkle',
            {'field': 'koala-bear', 'height': height, 'row_width': width, 'opening': opening,
             'queries': 4 if opening == 'multi' else 1},
            'composition', ('row commitment', opening+' opening', 'positive and negative authentication', 'row equality'),
            'Python expected rows; root/path authentication shares the provider. Width and height vary separately; includes all operations and Host costs.')
    machine_panel = [(reduction, height, False, 2*height)
                     for reduction in ('LogUp', 'Product') for height in (8, 16)]
    machine_panel += [('LogUp', 8, True, memory) for memory in (16, 32)]
    for reduction, height, present, memory in machine_panel:
        add(f'machine-{reduction.lower()}-h{height}-m{memory}-'+('present' if present else 'absent'), 'machine',
            {'reduction': reduction, 'cpu_height': height, 'program_height': height,
             'memory_present': present, 'memory_height': memory, 'memory_events': 4 if present else 0,
             'max_log_height': 5, 'log_domain_size': 6, 'rounds': 5, 'queries': 8, 'attempts': 8,
             'channels': 2, 'shift': 3},
            'protocol', ('ThreeTableArgument', reduction, 'program lookup', 'optional memory', 'FRI'),
            'Existing captured Bundle and proof profile; CPU/program heights at most 16, present memory at most 32. Same-stack verification; no arbitrary arity or production zkVM scale.')
    add('machine-logup-h8-m16-present-idle', 'machine',
        {'reduction': 'LogUp', 'cpu_height': 8, 'program_height': 8,
         'memory_present': True, 'memory_accesses': False, 'memory_height': 16, 'memory_events': 0,
         'max_log_height': 5, 'log_domain_size': 6, 'rounds': 5, 'queries': 8, 'attempts': 8,
         'channels': 2, 'shift': 3},
        'protocol', ('ThreeTableArgument', 'LogUp', 'program lookup', 'present idle memory', 'FRI'),
        'Same arithmetic program, CPU witness and final value as the height-8 absent-memory control; isolates optional memory presence. Same-stack proof validation; bounded fixture profile.')
    for n in (16384, 65536):
        for operation in ('length', 'sum'):
            add(f'host-vector-kb-{operation}-{n}', 'host_vector',
                {'field': 'koala-bear', 'elements': n, 'operation': operation, 'input_path': 'json-host-run'},
                'operation', ('typed vector input', operation, 'scalar equality'),
                'Matched inputs across length/sum, linear Python expectations, default capacities. Decode and SDK/Host boundaries stay separate; no transport-only timing.')
    # Bounded public-library panels. Existing cases and SMOKE stay fixed.
    kzg_panel = [('fr', n, 'natural') for n in (1, 8, 64, 256, 1024)]
    kzg_panel += [('kb', 32, 'natural'), ('fr', 256, 'bit-reversed')]
    for short, n, order in kzg_panel:
        for kind in ('on-domain', 'off-domain'):
            for operation in ('evaluate', 'quotient'):
                suffix = '-bit-reversed' if order == 'bit-reversed' else ''
                add(f'kzg-{short}-{operation}-{kind}-{n}{suffix}', 'kzg',
                    {'field': fields[short], 'elements': n, 'operation': operation,
                     'point_kind': kind, 'order': order},
                    'composition', ('checked evaluation domain', 'generic KZG '+operation, kind),
                    'Actual commitments/kzg library; independent coefficient/Horner/quotient oracle and full result check. '
                    'SDK/run includes checked-carrier setup and validation; no commitment, pairing or KZG security claim.')
    curve_panel = [(curve, 17, form) for curve in library_algebra.CURVES
                   for form in ('fixed-base', 'shared-scalar', 'per-point', 'msm')]
    curve_panel += [(curve, n, form) for curve in ('bls-g1', 'edwards') for n in (1, 64)
                    for form in ('shared-scalar', 'msm')]
    for curve, n, form in curve_panel:
        group, field = library_algebra.CURVES[curve]
        add(f'curve-family-{curve}-{form}-{n}', 'curve_family',
            {'curve': curve, 'group': group, 'field': field, 'elements': n, 'form': form},
            'operation', ('point construction', form, 'per-result group-law validation'),
            'Shared-provider group-law self-consistency with Python scalar expectations; not independent curve coordinates. '
            'Fixed-base is authored generator multiplication. SDK/run includes setup and checking; no timing or security claim.')
    sparse_panel = [(rows, columns, nnz, distribution)
                    for rows, columns, nnz in ((17, 31, 68), (128, 257, 512), (257, 33, 512))
                    for distribution in ('uniform', 'clustered', 'empty-rows')]
    sparse_panel += [(17, 31, 0, 'uniform'), (128, 257, 1024, 'uniform')]
    for rows, columns, nnz, distribution in sparse_panel:
        for direction in ('forward', 'transpose'):
            add(f'sparse-matrix-{rows}x{columns}-nnz{nnz}-{distribution}-{direction}', 'sparse_matrix',
                {'rows': rows, 'columns': columns, 'nnz': nnz, 'distribution': distribution,
                 'direction': direction, 'field': 'bls12-381.fr'},
                'operation', ('typed sparse matrix', direction+' contraction', distribution),
                'Exact nnz and dimensions, unique nonzero entries; independent integer oracle checks all rows/columns. '
                'Matched distribution and direction controls; SDK/run includes typed admission and equality, default capacities.')
    opening_panel = [(8, 1, 1, 'repeated'), (32, 4, 4, 'repeated'), (32, 4, 4, 'distinct'),
                     (128, 4, 4, 'distinct'), (32, 8, 6, 'distinct'), (8, 4, 0, 'repeated'),
                     (1024, 4, 8, 'distinct'), (4096, 1, 8, 'distinct')]
    for degree in (1, 4, 8):
        for height, width, count, kind in opening_panel:
            for form in ('library', 'reference'):
                add(f'opening-quotient-ext{degree}-h{height}-w{width}-o{count}-{kind}-{form}',
                    'opening_quotient', {'extension_degree': degree, 'height': height, 'width': width,
                                         'openings': count, 'point_kind': kind, 'form': form},
                    'composition', ('checked coset/openings', 'weighted quotient sum', form, kind+' off-domain points'),
                    'Current deep_columns versus authored per-opening quotient+accumulate; identical inputs and nonzero initial state. '
                    'Independent coefficient/Horner/synthetic-division oracle checks every coordinate and final weight; '
                    'SDK/run includes checked setup, validation and output construction; no performance/security claim.')
    return result


# Deliberately fixed lists: adding a workload does not silently expand a smoke run.
SMOKE = ('finite-kb-reduce-17', 'finite-kb-collect-17', 'finite-fr-bulk-17',
         'scan-scalar-17', 'scan-bulk-17', 'control-7x13', 'polynomial-ext1-32',
         'polynomial-ext8-32', 'extension-17', 'curve-1', 'pairing-2',
         'transcript-4x1', 'fri-n64-d16-q8', 'air-h8-w1-b4')


def catalog():
    return [(case.identifier, case, case.shape) for case in cases()]
