"""Independent contract matrix through typed source, dialect IR and physical plans."""
import copy
import json

from cases import case
from commands import Commands
from tools import records

commands = Commands(records())
run = commands.source


verify = commands.verified


# F/V/T/P/U/G/B/R are exact nominal field/vector/table/point/polynomial/group/
# group-vector/rng types. This table is authored independently of C++ metadata.
contracts = [
    ('matrix.mul_vector', 'MV', 'V', [], 'algebra.matrix_mul_vector'),
    ('matrix.transpose_mul_vector', 'MV', 'V', [], 'algebra.matrix_transpose_mul_vector'),
    ('matrix.bilinear', 'MVV', 'F', [], 'algebra.matrix_bilinear'),
    ('matrix.shape_check', 'M', 'b', ['2', '3'], 'algebra.matrix_shape_check'),
    ('field.sub', 'FF', 'F', [], 'algebra.subtract'),
    ('field.neg', 'F', 'F', [], 'algebra.negate'),
    ('field.inverse', 'F', 'F', [], 'algebra.inverse'),
    ('vector.constant', '', 'V', [], 'algebra.vector_constant'),
    ('vector.constant', '', 'V', ['0', '7', '0'], 'algebra.vector_constant'),
    ('vector.scatter_sum', 'V', 'V', ['0'], 'algebra.vector_scatter_sum'),
    ('vector.scatter_sum', 'V', 'V', ['3', '2', '0', '2'], 'algebra.vector_scatter_sum'),
    ('vector.empty', '', 'V', [], 'algebra.vector_empty'),
    ('vector.append', 'VF', 'V', [], 'algebra.vector_append'),
    ('vector.splat', 'F', 'V', ['0'], 'algebra.vector_splat'),
    ('vector.powers', 'F', 'V', ['8'], 'algebra.vector_powers'),
    ('vector.add', 'VV', 'V', [], 'algebra.vector_add'),
    ('vector.sub', 'VV', 'V', [], 'algebra.vector_sub'),
    ('vector.mul', 'VV', 'V', [], 'algebra.vector_mul'),
    ('vector.scale', 'VF', 'V', [], 'algebra.vector_scale'),
    ('vector.sum', 'V', 'F', [], 'algebra.vector_sum'),
    ('vector.dot', 'VV', 'F', [], 'algebra.vector_dot'),
    ('vector.split', 'V', 'VV', [], 'algebra.vector_split'),
    ('vector.concat', 'VV', 'V', [], 'algebra.vector_concat'),
    ('vector.at', 'V', 'F', ['3'], 'algebra.vector_at'),
    ('vector.length_check', 'V', 'b', ['0'], 'algebra.vector_length_check'),
    ('vector.gather', 'V', 'V', [], 'algebra.vector_gather'),
    ('vector.gather', 'V', 'V', ['3', '0', '3'], 'algebra.vector_gather'),
    ('vector.kronecker', 'VV', 'V', [], 'algebra.vector_kronecker'),
    ('vector.matvec', 'VV', 'V', ['2', '3', '0'], 'algebra.vector_matvec'),
    ('vector.matvec', 'VV', 'V', ['2', '3', '1'], 'algebra.vector_matvec'),
    ('vector.from_point', 'P', 'V', [], 'poly.point_to_vector'),
    ('vector.to_point', 'V', 'P', [], 'poly.point_from_vector'),
    ('vector.from_table', 'T', 'V', [], 'poly.table_to_vector'),
    ('vector.to_table', 'V', 'T', [], 'poly.table_from_vector'),
    ('poly.equality_weights', 'P', 'V', [], 'poly.equality_weights'),
    ('poly.from_coefficients', 'V', 'U', [], 'poly.from_coefficients'),
    ('poly.coefficients', 'U', 'V', [], 'poly.coefficients'),
    ('poly.degree_check', 'U', 'b', ['3'], 'poly.degree_check'),
    ('poly.univariate_evaluate', 'UF', 'F', [], 'poly.univariate_evaluate'),
    ('poly.univariate_boundary', 'U', 'F', [], 'poly.univariate_boundary'),
    ('random.vector', 'R', 'VR', ['8'], 'pir.random_vector'),
    ('curve.neg', 'G', 'G', [], 'algebra.curve_negate'),
    ('curve.nonidentity', 'G', 'b', [], 'algebra.curve_nonidentity'),
    ('curve.msm', 'VB', 'G', [], 'algebra.curve_msm'),
    ('curve.scale_each', 'VB', 'B', [], 'algebra.curve_scale_each'),
    ('curve.vector_add', 'BB', 'B', [], 'algebra.curve_vector_add'),
    ('curve.vector_scale', 'BF', 'B', [], 'algebra.curve_vector_scale'),
    ('curve.split', 'B', 'BB', [], 'algebra.curve_split'),
    ('curve.concat', 'BB', 'B', [], 'algebra.curve_concat'),
    # Existing scalar, vector-of-group, RNG and nonce operations in both domains.
    ('poly.boundary', 'Q', 'F', [], 'poly.boundary'),
    ('poly.round_evaluate', 'QF', 'F', [], 'poly.round_evaluate'),
    ('field.constant', '', 'F', ['5'], 'algebra.constant'),
    ('field.add', 'FF', 'F', [], 'algebra.sum'),
    ('field.mul', 'FF', 'F', [], 'algebra.product'),
    ('field.equal', 'FF', 'b', [], 'algebra.compare'),
    ('curve.generator', '', 'G', [], 'algebra.curve_generator'),
    ('curve.add', 'GG', 'G', [], 'algebra.curve_add'),
    ('curve.scale', 'GF', 'G', [], 'algebra.curve_scale'),
    ('curve.equal', 'GG', 'b', [], 'algebra.curve_equal'),
    ('curve.empty', '', 'B', [], 'algebra.curve_empty'),
    ('curve.append', 'BG', 'B', [], 'algebra.curve_append'),
    ('curve.at', 'B', 'G', ['0'], 'algebra.curve_at'),
    ('curve.get', 'BI', 'G', [], 'algebra.curve_get'),
    ('curve.length', 'B', 'I', [], 'algebra.curve_length'),
    ('random.draw', 'R', 'FR', [], 'pir.random_draw'),
    ('curve.commit', 'BN', 'BN', [], 'algebra.curve_commit'),
    ('curve.response', 'FFN', 'F', [], 'algebra.curve_response'),
]
fields = [('bls12-381.fr', 'bls12-381.g1', 'arkworks'),
          ('ristretto255.scalar', 'ristretto255.group', 'dalek'),
          ('koala-bear', '', 'plonky3'),
          ('bn254.fr', 'bn254.g1', 'arkworks'),
          ('bn254.fr', 'bn254.g2', 'arkworks')]


def generic_source(contract, ins, outs, attrs, domain):
    f, g, backend = domain
    group = contract.startswith('curve.') and contract != 'curve.response'
    parameter, sort, actual = ('G', 'Group', g) if group else ('F', 'Field', f)
    def types(field, group):
        return dict(F=field+'::Element', V='Vector<'+field+'::Element>',
                    M='Matrix<'+field+'::Element>',
                    T='Table<'+field+'>', P='Point<'+field+'>', U='Polynomial<'+field+'>',
                    G=group+'::Element', B='Vector<'+group+'::Element>',
                    R='Rng<'+field+'>', N='Nonce<'+field+'>', Q='Round<'+field+'>', b='bool', I='index')
    abstract = types('G::Scalar' if group else 'F', 'G')
    concrete = types(json.dumps(f), json.dumps(g))
    in_names = [f'a{i}' for i in range(len(ins))]
    out_names = [f'o{i}' for i in range(len(outs))]
    def join(xs):
        return ', '.join(xs)
    return f'''module {{
  fn Work<{parameter}: domain {sort}>({join(n+': '+abstract[k] for n,k in zip(in_names,ins))})
      -> ({join(abstract[k] for k in outs)}) requires ({'ScalarAction(G)' if group else 'Field(F)'}) {{
    [site] let ({join(out_names)}) = {contract.replace('.', '::')}::<{parameter}>({join(in_names)})
      attributes ({join(json.dumps(a) for a in attrs)});
    return ({join(out_names)});
  }}
  configure Concrete = Work({parameter} = {actual});
  protocol Main {{
    roles (P);
    inputs ({join('P '+n+': '+concrete[k] for n,k in zip(in_names,ins))});
    outputs ({join('P '+concrete[k] for k in outs)});
    local [call] P: let ({join(out_names)}) = Concrete({join(in_names)});
    return ({join(out_names)});
  }}
  instance concrete: Main {{ roles (P = P); }}
  entry main = concrete;
}}'''


for domain in fields:
    for contract, ins, outs, attrs, op in contracts:
        # A numerical field does not install a group or a scalar action.
        if domain[2] == 'plonky3' and contract.startswith('curve.'):
            continue
        source = generic_source(contract, ins, outs, attrs, domain)
        unavailable = ('TPRN' if domain[2] == 'plonky3'
                       else 'TPN' if domain[0] == 'bn254.fr'
                       else 'TP' if domain[2] == 'dalek' else '')
        if any(k in ins+outs for k in unavailable):
            run('protocol-compile', source, refuses='binding-representation')
            continue
        ir = run('protocol-import', source)
        assert '"'+op+'"' in ir
        if 'V' in ins+outs or 'B' in ins+outs:
            assert 'tensor<?x!algebra.' in ir and '!algebra.groups' not in ir
        if 'U' in ins+outs:
            assert '!poly.univariate<' in ir
        physical = json.loads(run('protocol-compile', source))
        assert physical[1][0][1] == contract
        assert physical[1][0][3] == domain[2]+'/'+contract
        pir = run('protocol-physical-ir', source)
        verify(pir)
        assert json.loads(run('protocol-export', pir)) == physical

# Natural attrs are neither signed literals nor field reductions. Every arity is
# checked, including empty gather and transpose selection. Quoting exercises the
# semantic checker rather than a lexer refusal.
for contract, ins, outs, attrs, code in [
    ('vector.splat', 'F', 'V', [], 'interactive-kernel-parameters'),
    ('vector.splat', 'F', 'V', ['1', '2'], 'interactive-kernel-parameters'),
    ('vector.at', 'V', 'F', ['-1'], 'expected-natural'),
    ('vector.powers', 'F', 'V', ['01'], 'noncanonical-natural'),
    ('vector.length_check', 'V', 'b', ['+1'], 'expected-natural'),
    ('vector.gather', 'V', 'V', ['0', '01'], 'noncanonical-natural'),
    ('vector.gather', 'V', 'V', ['18446744073709551616'], 'interactive-kernel-parameters'),
    ('vector.matvec', 'VV', 'V', ['2', '3'], 'interactive-kernel-parameters'),
    ('vector.matvec', 'VV', 'V', ['2', '3', '2'], 'interactive-kernel-parameters'),
    ('vector.matvec', 'VV', 'V', ['2', '3', '0', '1'], 'interactive-kernel-parameters'),
    ('poly.degree_check', 'U', 'b', [''], 'expected-natural'),
    ('random.vector', 'R', 'VR', ['1.0'], 'expected-natural'),
    ('field.sub', 'FF', 'F', ['0'], 'interactive-kernel-parameters'),
]:
    with case(f"{contract} with attributes {attrs}"):
        run('protocol-import', generic_source(contract, ins, outs, attrs, fields[0]),
            refuses=code)

# Constant specialization casts by the selected nominal modulus. Closed physical
# constants must already be canonical; values in [Ristretto order, BLS order)
# must not be silently admitted for Ristretto.
moduli = [52435875175126190479447740508185965837690552500527637822603658699938581184513,
          2**252 + 27742317777372353535851937790883648493,
          2130706433,
          21888242871839275222246405745257275088548364400416034343698204186575808495617,
          21888242871839275222246405745257275088548364400416034343698204186575808495617]
for domain, modulus in zip(fields, moduli):
    source = generic_source('field.constant', '', 'F', [str(modulus+7)], domain)
    plan = json.loads(run('protocol-compile', source))
    assert plan[3][0][4][0][3] == ['7']
    damaged = copy.deepcopy(plan)
    damaged[3][0][4][0][3] = [str(modulus)]
    run('protocol-import', json.dumps(damaged), refuses='interactive-constant')
    ir = run('protocol-physical-ir', source)
    verify(ir.replace('parameters = ["7"]', 'parameters = ["'+str(modulus)+'"]'),
           'interactive-constant')

# Nominal scalar-action signature and rank constraints are checked from actual
# SSA types. Dynamic shape is not a proof of equal runtime lengths.
source = generic_source('curve.msm', 'VB', 'G', [], fields[1])
ir = run('protocol-import', source)
verify(ir.replace('tensor<?x!algebra.field<"ristretto255.scalar">>',
                  'tensor<?x!algebra.field<"bls12-381.fr">>'),
       'binding-operation-signature')
for replacement in ['tensor<4x!algebra.field<"ristretto255.scalar">>',
                    'tensor<?x?x!algebra.field<"ristretto255.scalar">>',
                    'tensor<?xi64>']:
    verify(ir.replace('tensor<?x!algebra.field<"ristretto255.scalar">>', replacement),
           'binding-operation-signature')

# A polynomial is not an MLE table or the stronger quadratic round carrier.
ir = run('protocol-import', generic_source('poly.degree_check', 'U', 'b', ['2'], fields[0]))
verify(ir.replace('!poly.univariate<', '!poly.quadratic<'), 'binding-operation-signature')

# Unknown operation contracts / actual dialect operations / physical kernels
# cannot acquire support from an installed representation.
source = generic_source('vector.sum', 'V', 'F', [], fields[0])
run('protocol-import', source.replace('vector::sum::<F>', 'vector::unknown::<F>'), refuses='source-name-unresolved')
pir = run('protocol-physical-ir', source)
verify(pir.replace('kernel = "arkworks/vector.sum"', 'kernel = "arkworks/unknown"'),
       'binding-implementation')
# New serializable carriers are observed through exact nominal codec bindings.
for field, group, backend in fields[:2]:
    transcript = ('merlin3.bls12-381.fr64be/1' if backend == 'arkworks'
                  else 'merlin3.ristretto255.scalar64le/1')
    for kind in ['field', 'vector', 'polynomial', 'round', 'group', 'groups', 'bool']:
        nominal = group if kind in ('group', 'groups') else field
        parameter = 'G' if kind in ('group', 'groups') else 'F'
        sort = 'Group' if parameter == 'G' else 'Field'
        roots = 'T: domain Transcript, '+(parameter+': domain '+sort+', ' if kind != 'bool' else '')+'E: domain Codec'
        arguments = 'T, '+(parameter+', ' if kind != 'bool' else '')+'E'
        surface = {'field': lambda d: d+'::Element', 'group': lambda d: d+'::Element',
                   'vector': lambda d: 'Vector<'+d+'::Element>', 'groups': lambda d: 'Vector<'+d+'::Element>',
                   'polynomial': lambda d: 'Polynomial<'+d+'>', 'round': lambda d: 'Round<'+d+'>', 'bool': lambda d: 'bool'}
        payload = surface[kind](parameter)
        concrete = surface[kind](json.dumps(nominal))
        codec = 'zkcv.'+kind+('.'+nominal if kind != 'bool' else '')+'/1'
        encoded = 'E, '+parameter if kind != 'bool' else 'E'
        config = ('T = "'+transcript+'", '+
                  (parameter+' = '+nominal+', ' if kind != 'bool' else '')+
                  'E = "'+codec+'"')
        text = f'''module {{
          fn Observe<{roots}>(state: Transcript<T>, value: {payload}) -> (Transcript<T>)
              requires (Transcript(T), Encodes.{kind}({encoded})) {{
            [observe] let next = transcript::observe::{kind}::<{arguments}>(state, value)
                attributes (Main, message, schema, P, V);
            return (next);
          }}
          configure Concrete = Observe({config});
          protocol Main {{
            roles (P);
            inputs (P state: Transcript<"{transcript}">, P value: {concrete});
            outputs (P Transcript<"{transcript}">);
            local [observe] P: let next = Concrete(state, value);
            return (next);
          }}
          instance concrete: Main {{ roles (P = P); }}
          entry main = concrete;
        }}'''
        plan = json.loads(run('protocol-compile', text))
        assert plan[1][0][3] == backend+'/transcript.observe.'+kind
        verify(run('protocol-physical-ir', text))
        if kind != 'bool':
            bad = text.replace('E = "'+codec+'"', 'E = "zkcv.bool/1"')
            run('protocol-import', bad, refuses='source-protocol-requirement')

for contract, ins, outs, attrs in [('vector.constant', '', 'V', ['1']),
                                    ('vector.scatter_sum', 'V', 'V', ['1', '0']),
                                    ('vector.mul', 'VV', 'V', []),
                                    ('poly.coefficients', 'U', 'V', []),
                                    ('poly.degree_check', 'U', 'b', ['3']),
                                    ('curve.scale_each', 'VB', 'B', [])]:
    text = generic_source(contract, ins, outs, attrs, fields[0])
    begin = text.index('    [site]')
    end = text.index(';', begin)+1
    unused = text[begin:end].replace('[site]', '[unused]').replace('let (o0)', 'let (unused)')
    text = text[:begin]+unused+'\n'+text[begin:]
    ir = run('protocol-import', text)
    transformed = verify(ir, None, '--canonicalize', '--cse')
    dialect = next(op for key, _, _, _, op in contracts if key == contract)
    assert transformed.count('"'+dialect+'"(') == 2, (contract, transformed)

print(f'vector/polynomial contracts: {commands.save()} pipeline checks')
