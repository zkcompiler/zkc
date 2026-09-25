"""Exact local signatures and eager batch predicates: what the source admits.

What the native runtime and the independent Lean consumer compute from the same
source is a separate test, tests/execution/test_local_vocabulary_reference.py,
because it needs two further builds.
"""
import copy
import json
import re
from cases import case
from commands import Commands
from tools import compiler, corpus, optimizer, records



commands = Commands(records())


def run(args, text=None, refuses=None):
    return commands.run(args, stdin=text, refuses=refuses)


def compile(mode, source, refuses=None, *flags):
    return run([compiler, mode, '-', *flags], source, refuses)


base = corpus.joinpath('local-vocabulary.pir').read_text()
for group in ('bls12-381.g1', 'ristretto255.group'):
    with case(f"{group} local vocabulary"):
        source = base.replace('bls12-381.g1', group)
        logical = compile('protocol-import', source)
        for name in ('algebra.curve_get', 'algebra.curve_length', 'pir.not', 'pir.or'):
            assert '"'+name+'"' in logical, name
        run([optimizer, '--verify-each'], logical)
        physical = compile('protocol-physical-ir', source)
        run([optimizer, '--verify-each'], physical)
        candidate = json.loads(compile('protocol-compile', source))
        assert json.loads(compile('protocol-export', physical)) == candidate
        providers = {b[1]: b[3] for b in candidate[1]}
        for contract in ('curve.get', 'curve.length'):
            assert providers[contract] == ('dalek/' if 'ristretto' in group else 'arkworks/')+contract
        for contract in ('bool.not', 'bool.or'):
            assert providers[contract] == 'arkworks/'+contract
        # Even duplicate unused operations retain their failure/charge positions.
        for contract, dialect in (('curve.get', 'algebra.curve_get'),
                                  ('curve.length', 'algebra.curve_length'),
                                  ('bool.not', 'pir.not'), ('bool.or', 'pir.or')):
            line = next(line for line in source.splitlines() if '= '+contract.replace('.', '::') in line)
            unused = re.sub(r'\[\w+\] let \w+', '[unused] let unused', line)
            dead = compile('protocol-import', source.replace(line, unused+'\n'+line))
            optimized = run([optimizer, '--canonicalize', '--cse'], dead)
            assert optimized.count('"'+dialect+'"(') == 2
        # Test actual bound /2 admission independently of generic preparation.
        for contract in ('bool.not', 'bool.or', 'curve.get', 'curve.length'):
            bad = copy.deepcopy(candidate)
            binding = next(b for b in bad[1] if b[1] == contract)
            binding[3] = 'invented/'+contract
            compile('protocol-import', json.dumps(bad), 'binding-implementation')
            bad = copy.deepcopy(candidate)
            name = next(b[0] for b in bad[1] if b[1] == contract)
            op = next(op for fn in bad[3] for op in fn[4] if op[0] == 'op' and op[2] == name)
            op[3] = ['0']
            compile('protocol-import', json.dumps(bad), 'interactive-kernel-parameters')
        compile('protocol-source', source.replace('bool::not(enabled)', 'bool::not(query)'), 'source-type-mismatch')
        compile('protocol-source', source.replace('curve::get::<G>(batch, query)', 'curve::get::<G>(batch, enabled)'), 'source-type-mismatch')
        compile('protocol-source', source.replace('bool::or(disabled, equation)', 'bool::or(disabled)'), 'source-call-arity')
        # Mutated real MLIR cannot substitute another registered operation at a binding.
        run([optimizer, '--verify-each'], logical.replace('"pir.not"', '"pir.or"'), 'binding-operation')
        other = 'ristretto255.group' if group == 'bls12-381.g1' else 'bls12-381.g1'
        bad = copy.deepcopy(candidate)
        next(b for b in bad[1] if b[1] == 'curve.get')[2] = [other]
        compile('protocol-import', json.dumps(bad), 'binding-implementation')
        # A valid foreign binding still cannot consume the original nominal SSA type.
        selected = next(b for b in bad[1] if b[1] == 'curve.get')
        selected[3] = ('dalek/' if 'ristretto' in other else 'arkworks/')+'curve.get'
        compile('protocol-import', json.dumps(bad), 'binding-operation-signature')
print(f"local vocabulary: {commands.save()} checks passed")
