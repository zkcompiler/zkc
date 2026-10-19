"""STARK dimensions: trace shape, evaluation size and polynomial degree are distinct."""
from functools import partial
import importlib.util

from . import algebra as a
from .programs import Program


def mutate_claim(proof, tag=b'ZKCV\x00\x1b', minimum=42):
    """Alter a canonical extension-field claim while preserving the invocation
    and framing: an Ext8 vector by default, or another vector tag and minimum
    frame size.

    Uses docs/spec/formats/proof.md and messages.md, as do the maintained STARK
    conformance controls. Provers reject invalid traces before producing proofs.
    """
    if proof[:8] != b'ZKCPRF00' or len(proof) < 40:
        raise ValueError('expected native framed proof')
    offset = 40
    while offset < len(proof):
        size = int.from_bytes(proof[offset:offset+8], 'little')
        start, end = offset+8, offset+8+size
        if end > len(proof):
            raise ValueError('truncated proof frame')
        payload = proof[start:end]
        if payload[:6] == tag and size >= minimum:
            coordinate = int.from_bytes(payload[10:14], 'little')
            changed = ((coordinate+1) % a.P).to_bytes(4, 'little')
            return proof[:start+10] + changed + proof[start+14:]
        offset = end
    raise ValueError('missing extension claim')


def fri(root, shape):
    size, bound, queries = shape['evaluation_size'], shape['degree_bound'], shape['queries']
    rounds = bound.bit_length()-1
    coefficients = a.dense(bound, 8, seed=91+shape.get('statement', 0))
    shift = (3+2*shape.get('statement', 0), 1, 0, 0, 0, 0, 0, 0)
    public = {'shift': a.encode(shift), 'round_count': str(rounds), 'query_count': str(queries)}
    source = '''module example;
use zkc::vector::{Vector};
use fri::{LowDegree};
domain E=field("koala-bear.ext8-binomial3");
domain Rows=commitment("rows.merkle-keccak256.koala-bear.ext8-binomial3/0");
protocol Fri roles(P,V)(word:Vector<E>@P,shift:E@(P,V),round_count:index@(P,V),
 query_count:index@(P,V),coins:Random<E>@V)->(accepted:bool@V){
 let (accepted,_,_,_)=LowDegree<Rows,SIZE,0,ROUNDS,QUERIES>(word,shift,shift,round_count,query_count,coins);
 return accepted;
}
proof Proof=Fri {prover P;verifier V;public {shift,round_count,query_count};accept accepted;
 construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0",coins);}
'''.replace('SIZE', str(size.bit_length()-1)).replace('ROUNDS', str(rounds)).replace('QUERIES', str(queries))
    witness = {'word': list(map(a.encode, a.coset(coefficients, shift, size)))}
    return Program(source, [{'public': public, 'witness': witness}], invalid_witness={'word': list(map(a.encode, a.coset([*coefficients, (1, 0, 0, 0, 0, 0, 0, 0)], shift, size)))},
                   entry='example::Proof', dependencies=('protocols.polynomial.fri',), proof=True,
                   changed=public | {'shift': a.encode((2, 1, 0, 0, 0, 0, 0, 0))},
                   oracle='independent Python polynomial evaluation; same-stack FRI verification and refusal controls')


def recurrence(root, shape):
    """The quadratic recurrence AIR shared by both STARK profiles: its Bundle,
    boundary values and row-major trace."""
    height, width = shape['height'], shape['width']
    spec = importlib.util.spec_from_file_location('benchmark_ring_arena', root/'compiler/adapters/ring_arena.py')
    arena_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(arena_module)
    arena = arena_module.Arena()
    outputs, assertions = [], []
    for col in range(width):
        current = arena.input('koala-bear', ['read', 0, '0', col])
        following = arena.input('koala-bear', ['read', 0, '1', col])
        initial = arena.input('koala-bear', ['public', col])
        final = arena.input('koala-bear', ['public', width+col])
        for value, selector in ((current-initial, ['first']), (current-final, ['last']),
                                (following-current*current-(col+1), ['interior', 0, 1])):
            assertions.append([len(outputs), selector])
            outputs.append(value)
    ring, bindings = arena.finish(outputs)
    bundle = ['zkc.relation-bundle/0', [[f'public-{i}', 'koala-bear'] for i in range(2*width)], [],
              [['trace', 'required', ['fixed', height], 'cyclic', [['trace', 'witness', 'koala-bear', width]],
                ring, bindings, assertions, []]]]
    initial = [x[0] for x in a.dense(width, seed=101+shape.get('statement', 0))]
    current, trace = initial, []
    for _ in range(height):
        trace.extend(current)
        final = current
        current = [(x*x+i+1) % a.P for i, x in enumerate(current)]
    return bundle, initial, final, trace


def air(root, shape):
    height, size = shape['height'], shape['evaluation_size']
    bundle, initial, final, trace = recurrence(root, shape)
    public = {'public_data': list(map(str, initial+final)), 'shift': '3',
              'round_count': str(height.bit_length()-1), 'query_count': str(shape['queries']), 'attempt_count': '8'}
    source = '''module example;
use stark::configurations::koala_bear_octic::{Base,Extension};
use stark::octic_table::{Statement,TableArgument};
use zkc::vector::{Vector}; use zkc::vector as v;
domain Trace=bundle(asset trace);
fn statement(public_data:Vector<Base>,shift:Base)->Statement {
 return Statement {configuration:v::empty<Base>(),public_columns:v::empty<Base>(),public_data,shift};
}
protocol Air roles(P,V)(trace:Vector<Base>@P,public_data:Vector<Base>@(P,V),shift:Base@(P,V),
 round_count:index@(P,V),query_count:index@(P,V),attempt_count:index@(P,V),coins:Random<Extension>@V)->(accepted:bool@V){
 let prover@P=statement(public_data,shift);let verifier@V=statement(public_data,shift);
 let accepted=TableArgument<0,Trace,HEIGHT,SIZE,QUERIES,8>(trace,prover,verifier,round_count,query_count,attempt_count,coins);
 return accepted;
}
proof Proof=Air {prover P;verifier V;public {public_data,shift,round_count,query_count,attempt_count};accept accepted;
 construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0",coins);}
'''.replace('HEIGHT', str(height.bit_length()-1)).replace('SIZE', str(size.bit_length()-1)).replace('QUERIES', str(shape['queries']))
    changed = public | {'public_data': [str((initial[0]+1) % a.P), *public['public_data'][1:]]}
    witness = {'trace': list(map(str, trace))}
    return Program(source, [{'public': public, 'witness': witness}], mutate_proof=mutate_claim,
                   entry='example::Proof', dependencies=('arguments.stark.single_table.koala_bear_octic',), assets={'trace': bundle}, proof=True,
                   changed=changed, support=(root/'compiler/adapters/ring_arena.py',), oracle='Python quadratic trace recurrence; generated relation with first/last/transition constraints; same-stack proof verification')


def library(root, shape):
    """The same AIR through the parameterized library at its KoalaBear quartic
    Poseidon2 configuration, with the final polynomial a constant."""
    height, size = shape['height'], shape['evaluation_size']
    bundle, initial, final, trace = recurrence(root, shape)
    public = {'public_data': list(map(str, initial+final))}
    source = '''module example;
use stark::configurations::koala_bear_octic::{Base,Extension};
use stark::configurations::koala_bear_quartic::{Poseidon2};
use stark::single_table::{Statement,TableArgument};
use zkc::vector::{Vector}; use zkc::vector as v;
domain Trace=bundle(asset trace);
fn statement(public_data:Vector<Base>)->Statement<Base> {
 return Statement<Base> {configuration:v::empty<Base>(),public_columns:v::empty<Base>(),public_data};
}
protocol Air roles(P,V)(trace:Vector<Base>@P,public_data:Vector<Base>@(P,V),coins:Random<Extension>@V)->(accepted:bool@V){
 let prover@P=statement(public_data);let verifier@V=statement(public_data);
 let accepted=TableArgument<Poseidon2,0,Trace,0,ROUNDS,BLOWUP,QUERIES>(trace,prover,verifier,coins);
 return accepted;
}
proof Proof=Air {prover P;verifier V;public {public_data};accept accepted;
 construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0",coins);}
'''.replace('ROUNDS', str(height.bit_length()-1)).replace('BLOWUP', str((size//height).bit_length()-1)).replace('QUERIES', str(shape['queries']))
    changed = public | {'public_data': [str((initial[0]+1) % a.P), *public['public_data'][1:]]}
    witness = {'trace': list(map(str, trace))}
    return Program(source, [{'public': public, 'witness': witness}],
                   mutate_proof=partial(mutate_claim, tag=b'ZKCV\x00\x16', minimum=26),
                   entry='example::Proof', dependencies=('arguments.stark.single_table', 'arguments.stark.configurations.koala_bear_octic',
                                                        'arguments.stark.configurations.koala_bear_quartic'), assets={'trace': bundle}, proof=True,
                   changed=changed, support=(root/'compiler/adapters/ring_arena.py',), oracle='Python quadratic trace recurrence; generated relation with first/last/transition constraints; same-stack proof verification')
