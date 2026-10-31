"""STARK dimensions: trace shape, evaluation size and polynomial degree are distinct."""
from dataclasses import dataclass
from functools import partial
import importlib.util

from . import algebra as a
from .programs import Program


@dataclass(frozen=True)
class LibraryProfile:
    configuration: str
    modulus: int
    extension: str
    degree: int
    challenge_configuration: str
    transcript: str
    poseidon_width: int
    shift: int
    vector_tag: int
    coordinate_bytes: int


# Exact authored configurations, selected before compilation and measurement.
# KoalaBear's quartic FRI retains the original octic transcript draws.
LIBRARY_PROFILES = {
    'koala-bear': LibraryProfile(
        'koala_bear_quartic', a.P, 'koala-bear.ext4-binomial3', 4, 'koala_bear_octic',
        'merlin3.koala-bear.ext8-binomial3.rejection31le/0', 16, 3, 22, 4),
    'baby-bear': LibraryProfile(
        'baby_bear_quartic', 2013265921, 'baby-bear.ext4-binomial11', 4, 'baby_bear_quartic',
        'merlin3.baby-bear.ext4-binomial11.rejection31le/0', 16, 31, 94, 4),
    'goldilocks': LibraryProfile(
        'goldilocks_quadratic', 18446744069414584321, 'goldilocks.ext2-binomial7', 2, 'goldilocks_quadratic',
        'merlin3.goldilocks.ext2-binomial7.rejection64le/0', 8, 7, 100, 8),
}


def library_profile(shape):
    field = shape.get('field', 'koala-bear')
    if field not in LIBRARY_PROFILES:
        raise ValueError('unsupported STARK field family')
    profile = LIBRARY_PROFILES[field]
    if shape.get('profile', profile.configuration) != profile.configuration:
        raise ValueError('STARK field and configuration must match')
    return field, profile


def mutate_claim(proof, tag=b'ZKCV\x00\x1b', minimum=42, *, modulus=a.P, coordinate_bytes=4):
    """Alter a canonical extension-field claim while preserving the invocation
    and framing: a KoalaBear Ext8 vector by default, or another explicit vector
    tag, minimum frame size, prime characteristic and coordinate byte width.

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
            coordinate = int.from_bytes(payload[10:10+coordinate_bytes], 'little')
            changed = ((coordinate+1) % modulus).to_bytes(coordinate_bytes, 'little')
            return proof[:start+10] + changed + proof[start+10+coordinate_bytes:]
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
use fri::{Direct, LowDegree};
domain E=field("koala-bear.ext8-binomial3");
protocol Fri roles(P,V)(word:Vector<E>@P,shift:E@(P,V),round_count:index@(P,V),
 query_count:index@(P,V),coins:Random<E>@V)->(accepted:bool@V){
 let (accepted,_,_,_)=LowDegree<Direct<E>,SIZE,0,ROUNDS,QUERIES>(word,shift,shift,round_count,query_count,coins);
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
    """Shared AIR Bundle and independently computed row-major trace.

    The original independent quadratic recurrence stays the default. Coupled
    columns read their cyclic neighbors in the same row; updates are simultaneous.
    """
    height, width = shape['height'], shape['width']
    field, profile = library_profile(shape)
    modulus = profile.modulus
    coupled = shape.get('constraint') == 'coupled'
    degree = shape.get('constraint_degree', 2)
    if coupled and (width < 2 or degree not in (2, 3)):
        raise ValueError('coupled AIR requires at least two columns and degree two or three')
    spec = importlib.util.spec_from_file_location('benchmark_ring_arena', root/'compiler/adapters/ring_arena.py')
    arena_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(arena_module)
    arena = arena_module.Arena()
    outputs, assertions = [], []
    for col in range(width):
        current = arena.input(field, ['read', 0, '0', col])
        following = arena.input(field, ['read', 0, '1', col])
        initial = arena.input(field, ['public', col])
        final = arena.input(field, ['public', width+col])
        first_boundary, last_boundary = current-initial, current-final
        if coupled:
            neighbor = arena.input(field, ['read', 0, '0', (col+1) % width])
            previous = arena.input(field, ['read', 0, '0', (col-1) % width])
            product = current*neighbor
            if degree == 3:
                product = current*product
            transition = following-product-previous-(col+1)
        else:
            transition = following-current*current-(col+1)
        for value, selector in ((first_boundary, ['first']), (last_boundary, ['last']),
                                (transition, ['interior', 0, 1])):
            assertions.append([len(outputs), selector])
            outputs.append(value)
    ring, bindings = arena.finish(outputs)
    bundle = ['zkc.relation-bundle/0', [[f'public-{i}', field] for i in range(2*width)], [],
              [['trace', 'required', ['fixed', height], 'cyclic', [['trace', 'witness', field, width]],
                ring, bindings, assertions, []]]]
    initial = [x[0] for x in a.dense(width, seed=101+shape.get('statement', 0), modulus=modulus)]
    current, trace = initial, []
    for _ in range(height):
        trace.extend(current)
        final = current
        if coupled:
            current = [(pow(x, degree-1, modulus)*current[(i+1) % width]+current[(i-1) % width]+i+1) % modulus
                       for i, x in enumerate(current)]
        else:
            current = [(x*x+i+1) % modulus for i, x in enumerate(current)]
    return bundle, initial, final, trace


def trace_oracle(shape):
    kind = f"coupled degree-{shape['constraint_degree']}" if shape.get('constraint') == 'coupled' else 'quadratic'
    return f'Python {kind} trace recurrence; generated relation with first/last/transition constraints; same-stack proof verification'


def air(root, shape):
    if shape.get('field', 'koala-bear') != 'koala-bear':
        raise ValueError('octic AIR control requires KoalaBear')
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
                   changed=changed, support=(root/'compiler/adapters/ring_arena.py',), oracle=trace_oracle(shape))


def library(root, shape):
    """The same AIR through an explicit library configuration and transcript,
    with the final polynomial a constant. KoalaBear remains the default."""
    _, profile = library_profile(shape)
    height, size = shape['height'], shape['evaluation_size']
    bundle, initial, final, trace = recurrence(root, shape)
    public = {'public_data': list(map(str, initial+final))}
    source = '''module example;
use stark::configurations::CHALLENGE_MODULE::{Base,Extension};
use stark::configurations::CONFIGURATION_MODULE::{Poseidon2};
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
 construction fiat_shamir("TRANSCRIPT_SUITE",coins);}
'''.replace('CHALLENGE_MODULE', profile.challenge_configuration).replace('CONFIGURATION_MODULE', profile.configuration).replace('TRANSCRIPT_SUITE', profile.transcript).replace('ROUNDS', str(height.bit_length()-1)).replace('BLOWUP', str((size//height).bit_length()-1)).replace('QUERIES', str(shape['queries']))
    changed = public | {'public_data': [str((initial[0]+1) % profile.modulus), *public['public_data'][1:]]}
    witness = {'trace': list(map(str, trace))}
    configurations = dict.fromkeys((profile.challenge_configuration, profile.configuration))
    dependencies = ('arguments.stark.single_table', *(f'arguments.stark.configurations.{name}' for name in configurations))
    return Program(source, [{'public': public, 'witness': witness}],
                   mutate_proof=partial(mutate_claim, tag=b'ZKCV\x00'+bytes([profile.vector_tag]),
                                        minimum=10+profile.degree*profile.coordinate_bytes,
                                        modulus=profile.modulus, coordinate_bytes=profile.coordinate_bytes),
                   entry='example::Proof', dependencies=dependencies, assets={'trace': bundle}, proof=True,
                   changed=changed, support=(root/'compiler/adapters/ring_arena.py',), oracle=trace_oracle(shape))
