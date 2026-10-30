"""Source fixtures for ordinary proof-client measurements, not security examples."""
from copy import deepcopy
from dataclasses import replace
import json
import re
from types import SimpleNamespace

from . import algebra, commitments, operations, stark
from .execution import compile_program
from .io import digest, require, write_json
from .programs import Program, local
from .runner import Capture


def proof_control(program):
    """Expose an existing checked computation through an authored proof Entry.

    The verifier repeats the public computation. A sent dummy witness keeps the
    ordinary proof path observable. This measures computation/transport, not a
    cryptographic construction or a proof of private computation.
    """
    prefix = program.source.split('protocol Work roles(P)(', 1)[0]
    match = re.search(r'fn compute\((.*?)\)\s*->\s*bool', prefix, re.S)
    require(match is not None, 'browser control needs a boolean compute function')
    parameters = [p.strip() for p in match[1].split(',')]
    names = [p.split(':')[0].strip() for p in parameters]
    source = prefix + f'''
fn checked({', '.join(parameters)}, token:index)->bool {{return compute({', '.join(names)}) && token==0;}}
protocol Work roles(P,V)({', '.join(p+'@(P,V)' for p in parameters)},token:index@P)->(accepted:bool@V) {{
 let received=send P->V(token);
 let ok @V=checked({', '.join(names)},received);
 return (accepted=ok);
}}
proof Proof=Work{{prover P;verifier V;public{{{','.join(names)}}};accept accepted;construction authored;}}
'''
    return replace(program, source=source, inputs=[{'public': deepcopy(program.inputs[0]['P']), 'witness': {'token': '0'}}],
                   proof=True, entry='example::Proof')


def poseidon_distinct(count):
    states = list(commitments.POSEIDON_INPUT) + [x[0] for x in algebra.dense((count-1)*16, seed=743)]
    program = local('koala-bear', 'states:Vector<F>, count:index, expected:Vector<F>', '''
 let all=permutation::poseidon2_16(states);
 let mut same=true;
 for i in 0..count {
   let one=permutation::poseidon2_16(v::slice(states,i*16,16));
   same=same && v::equal(one,v::slice(all,i*16,16));
 }
 return same && v::equal(v::slice(all,0,16),expected);
''', {'states': list(map(str, states)), 'count': str(count), 'expected': list(map(str, commitments.POSEIDON_EXPECTED))})
    program.source = program.source.replace('fn compute(', 'use zkc::permutation as permutation;\nfn compute(')
    program.dependencies = ('core.collections', 'core.primitives.cryptography')
    program.oracle = 'distinct dense states; every batch output compared with scalar calls; first state checked against retained Plonky3 0.8.0 KAT; correlated provider check'
    return proof_control(program)


def keccak_scalar(root, size):
    from hash_chain_reference import keccak256
    payload = bytes((17*i+23) % 256 for i in range(size))
    program = Program('''module example;
use zkc::bytes::{Bytes}; use zkc::bytes as bytes; use zkc::primitives::hash as hash;
fn compute(payload:Bytes,expected:Bytes)->bool{return bytes::equal(hash::keccak256(payload),expected);}
protocol Work roles(P)(payload:Bytes@P,expected:Bytes@P)->(accepted:bool@P){return compute(payload,expected);}
''', [{'P': {'payload': list(payload), 'expected': list(keccak256(payload))}}],
        dependencies=('core.encoding', 'core.primitives.cryptography'), support=(root/'common/tests/support/hash_chain_reference.py', root/'common/tests/support/logical_tree.py'),
        oracle='independent retained Python Keccak-f[1600] reference; every digest byte checked; scalar hash API')
    return proof_control(program)


def keccak_tree(width, height):
    values = list(map(str, (v[0] for v in algebra.dense(width*height, seed=761))))
    source = '''module example;
use zkc::vector::{Vector};use zkc::vector as v;use zkc::oracle as oracle;use zkc::oracle::{Root,Path};
domain F=field("koala-bear"); domain Rows=commitment("rows.merkle-keccak256.koala-bear/0");
fn check(root:Root<Rows>,width:index,height:index,row:Vector<F>,path:Path<Rows>,expected:Vector<F>)->bool {
 return oracle::check<Rows>(root,width,height,0,row,path) && v::equal(row,expected);
}
protocol Work roles(P,V)(values:Vector<F>@P,width:index@(P,V),height:index@(P,V),expected:Vector<F>@(P,V))
 ->(accepted:bool@V) {
 let tree @P=oracle::commit<Rows>(values,width);
 let root=send P->V(tree.0);
 let opened @P=oracle::open<Rows>(tree.1,0);
 let row=send P->V(opened.0);let path=send P->V(opened.1);
 let ok @V=check(root,width,height,row,path,expected);
 return (accepted=ok);
}
proof Proof=Work{prover P;verifier V;public{width,height,expected};accept accepted;construction authored;}
'''
    return Program(source, [{'public': {'width': str(width), 'height': str(height), 'expected': values[:width]}, 'witness': {'values': values}}],
        entry='example::Proof', proof=True, dependencies=('core.collections', 'core.primitives.cryptography'),
        oracle='independent expected opened row; portable scalar leaf hashing and SIMD two-lane batching cross-verify exact root/path proof bytes; not an independent root oracle')


def quartic_keccak():
    """Exercise the exact quartic row codec and derived challenge together."""
    values = [[str(1 + 4*i + j) for j in range(4)] for i in range(8)]
    source = '''module example;
use zkc::vector::{Vector};use zkc::vector as v;use zkc::oracle as oracle;use zkc::oracle::{Root,Path};
domain F=field("koala-bear.ext4-binomial3");
domain Rows=commitment("rows.merkle-keccak256.koala-bear.ext4-binomial3/0");
fn check(root:Root<Rows>,width:index,height:index,row:Vector<F>,path:Path<Rows>,
         expected:Vector<F>,challenge:F,response:Vector<F>)->bool {
 return oracle::check<Rows>(root,width,height,0,row,path) && v::equal(row,expected)
   && v::equal(response,v::scale(row,challenge));
}
protocol Work roles(P,V)(values:Vector<F>@P,width:index@(P,V),height:index@(P,V),
                        expected:Vector<F>@(P,V),coins:Random<F>@V)->(accepted:bool@V) {
 let tree @P=oracle::commit<Rows>(values,width);
 let root=send P->V(tree.0);
 let challenge=coins.draw();let received=send V->P(challenge);
 let opened @P=oracle::open<Rows>(tree.1,0);
 let response=send P->V(v::scale(opened.0,received));
 let row=send P->V(opened.0);let path=send P->V(opened.1);
 let ok @V=check(root,width,height,row,path,expected,challenge,response);
 return (accepted=ok);
}
proof Proof=Work{prover P;verifier V;public{width,height,expected};accept accepted;
 construction fiat_shamir("hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0",coins);}
'''
    return Program(source, [{'public': {'width': '2', 'height': '4', 'expected': values[:2]},
                             'witness': {'values': values}}], entry='example::Proof', proof=True,
                   dependencies=('core.collections', 'core.primitives.cryptography'),
                   oracle='every ascending quartic coordinate is nonzero; opened row compared with public expected coordinates; native/browser exact proof agreement; no independent root or security claim')


def blst_control(pairing):
    if pairing:
        parameters = 'count:index'
        body = '''let a=curve::generator<G1>(); let b=curve::generator<G2>();
 let mut left=curve::empty<G1>();let mut right=curve::empty<G2>();
 for i in 0..count { left=curve::append(left,a);left=curve::append(left,curve::neg(a));
   right=curve::append(right,b);right=curve::append(right,b); }
 return pairing::check<F>(left,right);'''
        values = {'count': '2'}
    else:
        parameters = 'scalar:F, expected:F, count:index'
        body = '''let base=curve::generator<G2>();let mut point=base;
 for i in 0..count {point=point*scalar;}
 return point==base*expected;'''
        values = {'scalar': '7', 'count': '17', 'expected': str(pow(7, 17, algebra.FR))}
    source = f'''module example;
use zkc::curve as curve;use zkc::pairing as pairing;
domain F=field("bls12-381.fr");domain G1=group("bls12-381.g1");domain G2=group("bls12-381.g2");
fn compute({parameters})->bool{{{body}}}
protocol Work roles(P)({parameters})->(accepted:bool@P){{return true;}}
'''
    return proof_control(Program(source, [{'P': values}], dependencies=('core.algebra',),
        oracle='nonidentity cancelling pairing product' if pairing else 'independent scalar exponent; shared-provider group law; resident G2 chain; conversions and checks included'))


def publication(size):
    payload = list(bytes((i*19+7) % 256 for i in range(size)))
    source = '''module example;
use zkc::bytes::{Bytes};use zkc::bytes as bytes;
protocol Work roles(P,V)(value:Bytes@P,expected:Bytes@(P,V))->(accepted:bool@V,value:Bytes@V){
 let received=send P->V(value);let ok @V=bytes::equal(received,expected);
 return (accepted=ok,value=received);
}
proof Proof=Work{prover P;verifier V;public{expected};accept accepted;construction authored;}
'''
    return Program(source, [{'public': {'expected': payload}, 'witness': {'value': payload}}], entry='example::Proof', proof=True,
                   dependencies=('core.encoding',), oracle='every published payload byte is compared with the public expected input')


def catalog(root, setup_material=None):
    # Yield lazily so selected source-only controls need no expensive generator.
    for field, short in [('goldilocks', 'base'), ('goldilocks.ext2-binomial7', 'ext2')]:
        for size in (0, 1, 2, 3, 17, 1025):
            yield f'goldilocks-{short}-{size}', lambda f=field, n=size: proof_control(operations.field_vector({'field': f, 'elements': n, 'operation': 'hadamard'}, root=root)), ['plonky3']
    for size in (0, 136, 8192):
        yield f'keccak-scalar-{size}', lambda n=size: keccak_scalar(root, n), ['plonky3']
    # Exact canonical header used by the existing oracle, including width/height.
    header = len(b'zkc.oracle.keccak256.leaf/0\0') + 24 + len(b'koala-bear.canonical-u32le/0')
    threshold = (32768//2-header)//4
    for width, height in [(1, 1), (1, 2), (17, 8), (threshold, 2), (threshold+1, 2)]:
        yield f'keccak-tree-{width}x{height}', lambda w=width, h=height: keccak_tree(w, h), ['plonky3']
    yield 'quartic-keccak', quartic_keccak, ['plonky3']
    for count in (1, 3, 17):
        yield f'poseidon2-distinct-{count}', lambda n=count: poseidon_distinct(n), ['plonky3']
    for n in (2, 32, 1024):
        yield f'ntt-{n}', lambda n=n: proof_control(operations.transform({'extension_degree': 1, 'elements': n, 'operation': 'dft'})), ['plonky3']
    for n, d, q in [(8, 2, 1), (1024, 256, 8)]:
        yield f'fri-{n}', lambda n=n, d=d, q=q: stark.fri(root, {'evaluation_size': n, 'degree_bound': d, 'queries': q}), ['plonky3']
    yield 'blst-resident-g2', lambda: blst_control(False), ['arkworks', 'blst']
    yield 'blst-pairing', lambda: blst_control(True), ['arkworks', 'blst']
    for size in (0, 32768):
        yield f'publication-{size}', lambda n=size: publication(n), []



def setup_key(root, material):
    source = root/'compiler/test/fixtures/language/pcs_setup.zkc'
    inputs = [{key: json.loads((material/f'{key}-{i}.json').read_text())
               for key in ('public', 'witness')} for i in range(2)]
    support = (source, *(p for p in material.iterdir() if p.is_file()))
    return Program(source.read_text(), inputs, entry='sample::Prove', dependencies=(), proof=True,
                   support=support, oracle='existing two-slot source PCS proof fixture; actual development KZG keys, pinned PK bytes, independent VK authority, two distinct public points and commitments; no setup security claim')

def prepare(args):
    root, output = args.source.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    capture = Capture(output/'capture')
    cases, manifest = [], {'files': capture.files}
    if args.compiler:
        capture.add(args.compiler)
    selected = list(catalog(root))
    if args.setup_material:
        selected.append(('setup-key-proof', lambda: setup_key(root, args.setup_material.resolve()), ['arkworks', 'blst']))
    require(not args.case or set(args.case) <= {c[0] for c in selected}, 'unknown browser fixture case')
    for name, generate, providers in selected:
        if args.case and name not in args.case:
            continue
        program = generate()
        if args.source_only:
            directory = output/'cases'/name
            directory.mkdir(parents=True)
            (directory/'main.zkc').write_text(program.source)
        else:
            args.compiler_option = []
            directory, _ = compile_program(args, output, capture, manifest, SimpleNamespace(identifier=name), program)
            (directory/'pin.txt').write_text(digest(directory/'entry.zkpkg')+'\n')
        statements = []
        for i, inputs in enumerate(program.inputs):
            statement = {}
            for key, value in inputs.items():
                filename = f'{key}.json' if len(program.inputs) == 1 else f'{key}-{i}.json'
                write_json(directory/filename, value)
                statement[key] = filename
            statements.append(statement)
        write_json(directory/'fixture.json', {'oracle': program.oracle, 'providers': providers, 'entry': program.entry})
        candidate = {'name': name, 'directory': str(directory), 'providers': providers,
                     'statements': statements, 'options': {'allow_authored': 'construction authored' in program.source}}
        if name == 'setup-key-proof':
            material = args.setup_material.resolve()
            candidate['authority'] = str(material/'authority.json')
            for kind in ('setups', 'bindings'):
                candidate[kind] = json.loads((material/f'{kind}.json').read_text())
                for binding in candidate[kind]:
                    binding['path'] = str(material/binding['path'])
        cases.append(candidate)
    require(cases, 'no browser fixture cases selected')
    write_json(output/'cases.json', {'format': 'zkc.browser-cases/0', 'cases': cases})
    write_json(output/'generation.json', manifest | {'source_only': args.source_only})
    capture.check()
    return 0
