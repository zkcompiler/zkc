"""Generic algorithm formation, retained SSA calls and independent expansion."""
import copy
import json
from pathlib import Path

from journal import Journal
from toolchain import Toolchain, records

# The Lean reference these generic sources are checked against.
def main():
    CHECKER = "interactive-protocol"

    tools = Toolchain()
    compiler, optimizer = tools.compiler, tools.optimizer
    checker = tools.checker(CHECKER)
    repository = Path(__file__).resolve().parents[2]

    root = Path(repository)
    journal = Journal(records())

    def native(mode, value, error=None):
        output = journal.run([compiler, mode, '-'], value if isinstance(value, str) else json.dumps(value), error)
        return json.loads(output) if not error and output.startswith('[') else output


    text = (root / 'tests/fixtures/generic-composition.pir').read_text()
    source = native('protocol-source', text)
    assert native('protocol-source', native('protocol-format', source)) == source
    assert source[1][1][6][0] == ['apply', 'first', 'Chosen', ['F'], ['x'], ['a']]
    common = native('protocol-import', source)
    assert common.count('call @') == 5
    closed = native('protocol-export', common)
    assert len([f for f in closed[2] if f[5][0] == 'Twice']) == 2
    assert all(not i[3] for f in closed[2] for i in f[4] if i[0] == 'apply')
    expanded = journal.run([optimizer, '--zkc-expand-algorithms'], common)
    assert 'call @' not in expanded
    assert native('protocol-export', expanded) == native('protocol-expand', source)
    assert journal.run([optimizer, '--zkc-expand-algorithms'], expanded) == expanded
    candidate = native('protocol-compile', source)
    assert not any(i[0] == 'apply' for f in candidate[3] for i in f[4])

    directory = journal.directory
    sp, cp = Path(directory) / 'source.json', Path(directory) / 'candidate.json'

    def lean(value, plan=candidate, error=None):
        sp.write_text(json.dumps(value)); cp.write_text(json.dumps(plan))
        return json.loads(journal.run([checker, '--check-generic', sp, cp], refuses=error))

    def positive(value):
        value = native('protocol-source', value)
        lean(value, native('protocol-compile', value))
        return value

    def negative(change, native_error, lean_error=True, mode='protocol-source'):
        value = copy.deepcopy(source)
        change(value)
        native(mode, value, native_error)
        lean(value, error=lean_error)

    lean(source)
    reordered = copy.deepcopy(source)
    reordered[1].reverse(); reordered[2].reverse()
    positive(reordered)
    # The superseded five-field apply is refused rather than interpreted compatibly.
    negative(lambda s: s[1][1][6][0].pop(3), 'algorithm-call-shape', 'generic-instruction')
    # Each checked callee promise becomes an obligation in the caller.
    negative(lambda s: s[1][1].__setitem__(3, []), 'generic-public-requirement', 'generic-requirement-not-provided')
    negative(lambda s: s[1][1][6][0].__setitem__(3, []), 'generic-static-arity', 'generic-static-arity')
    negative(lambda s: s[1][1][6][0].__setitem__(3, ['F', 'F']), 'generic-static-arity', 'generic-static-arity')
    negative(lambda s: s[1][1][6][0].__setitem__(3, ['Missing']), 'generic-term-reference')
    negative(lambda s: s[1][1][6][0].__setitem__(2, 'Absent'), 'generic-configuration-reference')
    negative(lambda s: s[3][2][0][4][0].__setitem__(3, ['koala-bear']), 'generic-static-arity', 'generic-static-arity')
    negative(lambda s: s[2][2][3][0].__setitem__(1, 'bls12-381.fr'), 'algorithm-call-signature')
    negative(lambda s: s[1][1][6][0].__setitem__(1, 'a' * 125), 'algorithm-origin-limit', 'algorithm-origin-limit', 'protocol-compile')
    # Unused affine declarations are still checked.
    affine = ['generic_function', 'Pass', [['F', 'Field']], [], [['r', 'rng:F']], ['rng:F'], [['return', ['r']]]]
    bad = ['generic_function', 'Reuse', [['F', 'Field']], [], [['r', 'rng:F']], ['rng:F'], [
        ['apply', 'one', 'Pass', ['F'], ['r'], ['r1']],
        ['apply', 'two', 'Pass', ['F'], ['r'], ['r2']], ['return', ['r2']]]]
    negative(lambda s: s[1].extend([affine, bad]), 'generic-resource-reuse', 'generic-affine-reuse')
    bad_return = copy.deepcopy(affine)
    bad_return[1] = 'RepeatedReturn'; bad_return[5] *= 2; bad_return[6][0][1] *= 2
    negative(lambda s: s[1].append(bad_return), 'generic-resource-reuse', 'generic-affine-reuse')
    # Different static domains cannot be substituted without a promised equality.
    cross = ['generic_function', 'Cross', [['F', 'Field'], ['H', 'Field']], [['Field', ['H']]],
             [['x', 'field:F']], ['field:H'], [['apply', 'call', 'Twice', ['H'], ['x'], ['y']], ['return', ['y']]]]
    negative(lambda s: s[1].append(cross), 'generic-public-requirement', 'generic-requirement-not-provided')
    equal = copy.deepcopy(cross); equal[3].append(['=', ['F', 'H']])
    supplied = copy.deepcopy(source); supplied[1].append(equal)
    positive(supplied)
    wrong_sort = copy.deepcopy(cross); wrong_sort[2][1][1] = 'Group'; wrong_sort[3] = []
    wrong_sort[5] = ['field:F']
    negative(lambda s: s[1].append(wrong_sort), 'generic-static-sort', 'generic-static-sort')
    negative(lambda s: s[1][1][6][0].__setitem__(2, 'Four'), 'algorithm-call-cycle', 'algorithm-call-cycle')
    negative(lambda s: s[1][1][6][0].__setitem__(2, 'Left'), 'algorithm-call-cycle', 'algorithm-call-cycle')
    # An implementation choice is attached to a primitive site, never an apply.
    negative(lambda s: s[2][1][4].append(['first', 'arkworks/field.add']), 'generic-implementation-site', 'binding-implementation')
    # Fixed configuration arguments are nominal constants, with residual arguments positional.
    extra = '''
      fn Pair<A: domain Field, B: domain Field>(x: B::Element) -> (bool) requires (Field(A), Field(B)) {
        [constant] let a = field::constant::<A>() attributes (2130706434);
        [same] let ok = field::equal::<A>(a, a);
        return (ok);
      }
      configure Fixed = Pair(A = koala-bear);
      fn Wrapper<F: domain Field>(x: F::Element) -> (bool) requires (Field(F)) {
        [partial] let ok = Fixed::<F>(x);
        return (ok);
      }
      configure Wrapped = Wrapper(F = bls12-381.fr);
      fn Use(x: "bls12-381.fr"::Element) -> (bool) {
        [closed] let ok = Wrapped(x);
        return (ok);
      }
    '''
    positive(text.replace('module {', 'module {' + extra))
    # A ground false requirement must never become an assumed fact.
    impossible = text.replace('module {', 'module {' + extra.replace('Field(A), Field(B)', 'ExtensionField(A), Field(B)'))
    native('protocol-source', impossible, 'binding-requirement')
    # Native emits no JSON for rejected source; build the corresponding raw mutation.
    bad_fixed = native('protocol-source', text.replace('module {', 'module {' + extra))
    bad_fixed[1][0][3][0][0] = 'ExtensionField'
    lean(bad_fixed, error='binding-requirement')
    # A closed helper may directly apply a generic definition to nominal arguments.
    positive(text.replace('Right(x)', 'Four::<koala-bear>(x)'))
    associated = """
      fn Associated<G: domain Group>(x: G::Scalar::Element) -> (G::Scalar::Element)
          requires (Field(G::Scalar)) {
        [associated] let y = Twice::<G::Scalar>(x);
        return (y);
      }
      configure AssociatedBls = Associated(G = bls12-381.g1);
      fn UseAssociated(x: "bls12-381.fr"::Element) -> ("bls12-381.fr"::Element) {
        [selected] let y = AssociatedBls(x);
        return (y);
      }
    """
    positive(text.replace('module {', 'module {' + associated))
    selected_layout = """
      fn Fold<F: domain Field>(t: Table<F>, r: F::Element) -> (Table<F>) requires (CommRing(F)) {
        [fold] let u = poly::fold::<F>(t, r);
        return (u);
      }
      configure Layout = Fold() using (fold = "arkworks-msb/poly.fold");
      configure Preferred = Layout();
      fn NestedFold<F: domain Field>(t: Table<F>, r: F::Element) -> (Table<F>) requires (Field(F)) {
        [fold] let u = Preferred::<F>(t, r);
        return (u);
      }
      configure FoldBls = NestedFold(F = bls12-381.fr);
      fn UseFold(t: Table<"bls12-381.fr">, r: "bls12-381.fr"::Element) -> (Table<"bls12-381.fr">) {
        [selected] let u = FoldBls(t, r);
        return (u);
      }
    """
    positive(text.replace('module {', 'module {' + selected_layout))


    # Whole declaration DAG depth is checked even when never instantiated.
    def chain(s, count, branching=False):
        for n in range(count):
            body = [['return', []]] if n == 0 else [
                ['apply', 'a', f'E{n-1}', ['F'], [], []],
                *([['apply', 'b', f'E{n-1}', ['F'], [], []]] if branching else []), ['return', []]]
            s[1].append(['generic_function', f'E{n}', [['F', 'Field']], [], [], [], body])
    negative(lambda s: chain(s, 67), 'algorithm-call-depth', 'algorithm-call-depth')
    large = copy.deepcopy(source); chain(large, 17, True)
    large[2].append(['configure', 'Huge', 'E16', [['F', 'koala-bear']], []])
    large[3][2].append(['function', 'Force', [], [], [['apply', 'force', 'Huge', [], [], []], ['return', []]], ['Force', []]])
    native('protocol-source', large)
    native('protocol-compile', large, 'algorithm-expansion-limit')
    lean(large, error='algorithm-expansion-limit')
    # Monomorphization itself has a global bound, even for primitive-free bodies.
    import itertools
    many = copy.deepcopy(source)
    many[1].append(['generic_function', 'Empty', [], [], [], [], [['return', []]]])
    many[1].append(['generic_function', 'Many', [['A', 'Field'], ['B', 'Field'], ['C', 'Field']], [], [], [],
        [['apply', f'c{i}', 'Empty', [], [], []] for i in range(1250)] + [['return', []]]])
    for i, values in enumerate(itertools.product(['bls12-381.fr', 'koala-bear', 'ristretto255.scalar'], repeat=3)):
        name = f'Choice{i}'
        many[2].append(['configure', name, 'Many', [list(p) for p in zip(['A', 'B', 'C'], values)], []])
        many[3][3][0][7].insert(0, ['local', name, 'P', name, [], []])
    native('protocol-source', many, 'generic-specialization-limit')
    lean(many, error='generic-specialization-limit')
    alternate = copy.deepcopy(source)
    alternate[1].append(['generic_function', 'Identity', [['F', 'Field']], [], [['x', 'field:F']],
                         ['field:F'], [['return', ['x']]]])
    substituted = copy.deepcopy(alternate)
    substituted[1][1][6][0][2] = 'Identity'
    lean(alternate, native('protocol-compile', substituted), error='source-local-unmatched')
    # Independent checking rejects primitive changes after actual MLIR expansion.
    tampered = copy.deepcopy(candidate)
    f = next(f for f in tampered[3] if f[5][0] == 'Four')
    f[4].pop(0)
    lean(source, tampered, error=True)
    print(f'{journal.save()} generic composition checks passed')



def test_generic_composition():
    main()


if __name__ == "__main__":
    main()
