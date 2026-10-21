"""Public hash/permutation and row-commitment controls, outside full proofs."""
from copy import deepcopy
import hashlib

from . import algebra as a
from .programs import Program, increment_first, local


# Plonky3 0.8.0, p3-koala-bear/src/poseidon2.rs: default width-16 KAT.
# Also exercised through source by common/tests/kernels/test_poseidon2.py.
POSEIDON_INPUT = (894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695,
                  1717947831, 120589055, 19776022, 42382981, 1831865506, 724844064,
                  171220207, 1299207443, 227047920, 1783754913)
POSEIDON_EXPECTED = (1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110,
                     1391183747, 351743874, 1238264085, 1292768839, 2023573270, 1201586780,
                     1360691759, 1230682461, 748270449, 651545025)


def hash_bytes(shape):
    payload = bytes((17*i + 23) % 256 for i in range(shape['payload_bytes']))
    inputs = {'payload': list(payload), 'expected': list(hashlib.sha256(payload).digest())}
    incorrect = deepcopy(inputs)
    incorrect['expected'][0] ^= 1
    source = '''module example;
use zkc::bytes::{Bytes};
use zkc::bytes as bytes;
protocol Work roles(P)(payload:Bytes @P, expected:Bytes @P)->(accepted:bool @P) {
  let accepted @P=bytes::equal(bytes::sha256(payload),expected);
  return (accepted=accepted);
}
entry fn Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    return Program(source, [{'P': inputs}], dependencies=('core.encoding',),
                   incorrect={'P': incorrect},
                   oracle='independent Python hashlib.sha256; every digest byte checked')


def poseidon(shape):
    count = shape['states']
    program = local('koala-bear', 'states:Vector<F>, expected:Vector<F>',
                    'return v::equal(permutation::poseidon2_16(states),expected);',
                    {'states': list(map(str, POSEIDON_INPUT))*count,
                     'expected': list(map(str, POSEIDON_EXPECTED))*count})
    program.source = program.source.replace('fn compute(', 'use zkc::permutation as permutation;\nfn compute(')
    program.dependencies = ('core.collections', 'core.primitives.cryptography')
    program.oracle = 'retained Plonky3 0.8.0 published known answer repeated per state; full batch check, one distinct state, not independent parameter generation'
    return program


def merkle(shape):
    height, width = shape['height'], shape['row_width']
    multiple = shape['opening'] == 'multi'
    positions = [height-1, 0, height//2, height//2] if multiple else [height-1]
    values = [x[0] for x in a.dense(height*width, seed=271)]
    expected = [str(x) for i in positions for x in values[i*width:(i+1)*width]]
    bad_rows = increment_first({'rows': expected}, 'rows', a.P)['rows']
    inputs = {'values': list(map(str, values)), 'width': str(width), 'height': str(height),
              'expected': expected, 'bad_rows': bad_rows}
    coordinate_type = 'Indices' if multiple else 'index'
    coordinate = 'positions' if multiple else 'position'
    inputs[coordinate] = list(map(str, positions)) if multiple else str(positions[0])
    opening, check = ('open_many', 'check_many') if multiple else ('open', 'check')
    # Evaluate all three checks, even when a previous one is false. The negative
    # row is canonical and the request shape/positions remain unchanged.
    body = f'''let tree=oracle::commit<Rows>(values,width);
      let opened=oracle::{opening}<Rows>(tree.1,{coordinate});
      let correct=v::equal(opened.0,expected);
      let valid=oracle::{check}<Rows>(tree.0,width,height,{coordinate},opened.0,opened.1);
      let invalid=oracle::{check}<Rows>(tree.0,width,height,{coordinate},bad_rows,opened.1);
      return correct && valid && !invalid;'''
    program = local('koala-bear',
        f'values:Vector<F>, width:index, height:index, {coordinate}:{coordinate_type}, expected:Vector<F>, bad_rows:Vector<F>',
        body, inputs)
    program.source = program.source.replace('fn compute(', '''use zkc::oracle as oracle;
use zkc::indices::{Indices};
domain Rows=commitment("rows.merkle-poseidon2-16.koala-bear/0");
fn compute(''')
    program.dependencies = ('core.collections', 'core.primitives.cryptography')
    program.oracle = 'independent Python row-major opened values; canonical changed-row rejection; root/path authentication is same-provider consistency, not an independent Merkle root oracle'
    return program
