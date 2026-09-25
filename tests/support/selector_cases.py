"""Small independent selector subjects with deliberately different site orders."""


def source(*, offset=True, calls=False):
    field, rng = 'field:bls12-381.fr', 'rng:bls12-381.fr'
    functions = []
    for name in ('F', 'A'):
        body = ([['op', 'padding', 'constant', ['1'], [], ['pad']]]
                if name == 'A' and offset else [])
        body += [['op', 'sample', 'draw', [], ['r'], ['x', 'next']],
                 ['return', ['x', 'next']]]
        functions.append(['function', name, [['r', rng]], [field, rng], body,
                          ['Sampling', []]])
    functions.append(['function', 'Check', [['x', field]], ['bool'], [
        ['op', 'equal', 'equal', [], ['x', 'x'], ['ok']],
        ['op', 'guard', 'guard', [], ['ok'], []], ['return', ['ok']]], ['Check', []]])
    if calls:
        # A wholly unrelated call forces the expansion path for the module.
        functions += [
            ['function', 'Identity', [['b', 'bool']], ['bool'], [['return', ['b']]], ['Identity', []]],
            ['function', 'Caller', [['b', 'bool']], ['bool'], [
                ['apply', 'call', 'Identity', [], ['b'], ['out']], ['return', ['out']]], ['Caller', []]]]
    return ['zkc.protocol/1', [
        ['draw', 'random.draw', ['bls12-381.fr'], ''],
        ['constant', 'index.constant', [], ''],
        ['equal', 'field.equal', ['bls12-381.fr'], ''],
        ['guard', 'control.require', [], '']], functions,
        [['protocol', 'Main', ['P', 'V'], [], [['coins', 'V', rng]],
          [['V', 'bool'], ['V', rng]], [], [
              ['local', 'first', 'V', 'F', ['coins'], ['x', 'r1']],
              ['local', 'second', 'V', 'A', ['r1'], ['y', 'r2']],
              ['local', 'check', 'V', 'Check', ['y'], ['ok']],
              ['return', ['ok', 'r2']]]]],
        [['instance', 'root', 'Main', [], [], [['P', 'P'], ['V', 'V']]]],
        [['entry', 'main', 'root']]]


def descriptor(identity, owners):
    return ['zkc.construction/1', 'main', 'P', 'V', [],
            ['coins', [[owner, 'sample'] for owner in owners]], '0',
            'merlin3.bls12-381.fr64be/1', identity]


def family_source(*, nested=False, tail=False, padding=None):
    """An ordinary function plus a concrete helper copy sharing its origin."""
    value = source(offset=False)
    value[2][0][5][0] = value[2][1][5][0] = 'F'
    if padding is not None:
        assert padding in ('F', 'A')
        function = next(f for f in value[2] if f[1] == padding)
        function[4].insert(0, ['op', 'padding', 'constant', ['1'], [], ['pad']])
    if tail:
        value[2][1][4].insert(-1, ['op', 'tail', 'constant', ['1'], [], ['pad']])
    if nested:
        field, rng = 'field:bls12-381.fr', 'rng:bls12-381.fr'
        value[2].append(['function', 'Wrapper', [['r', rng]], [field, rng], [
            ['apply', 'first', 'F', [], ['r'], ['x', 'r1']],
            ['apply', 'second', 'A', [], ['r1'], ['y', 'r2']],
            ['return', ['y', 'r2']]], ['Wrapper', []]])
        value[3][0][7][:2] = [['local', 'wrapped', 'V', 'Wrapper', ['coins'], ['y', 'r2']]]
    return value


def library_family_source(*, owner='D', padding=None):
    """A configured generic draw and an ordinary carrier member of its alias.

    C is configured directly; Alias follows a configuration edge. The common
    member deliberately need not be a compiler-generated generic instance.
    """
    assert owner in ('D', 'C', 'Alias')
    assert padding in (None, 'definition', 'member')
    common = source(offset=padding == 'member')
    common[2].pop(0)
    common[2][0][5][0] = owner
    common[3][0][7][0][3] = 'Alias' if owner == 'Alias' else 'C'
    body = [['op', 'sample', 'random.draw', ['T'], [], ['r'], ['x', 'next']],
            ['return', ['x', 'next']]]
    if padding == 'definition':
        body.insert(0, ['op', 'padding', 'index.constant', [], ['1'], [], ['pad']])
    return ['zkc.library/1', [
        ['generic_function', 'D', [['T', 'Field']], [['Field', ['T']]],
         [['r', 'rng:T']], ['field:T', 'rng:T'], body]], [
        ['configure', 'C', 'D', [['T', 'bls12-381.fr']], []],
        ['configure', 'Alias', 'C', [], []]], common]


def nonprimitive_owner_source(*, conflict=False):
    """The owner provides a coordinate; a sibling provides its selected draw."""
    value = family_source(padding='A' if conflict else None)
    leaf = source(offset=False)[2][0]
    leaf[1] = leaf[5][0] = 'Leaf'
    value[2].append(leaf)
    value[2][0][4][0] = ['apply', 'sample', 'Leaf', [], ['r'], ['x', 'next']]
    return value


def authored_helper_source():
    """Real checked-library helper adaptation, with no authored carrier origins."""
    return '''module {
      library(namespace="example", name="selectors", version="1", resolution="capture-1");
      fn Draw(r: rng<"bls12-381.fr">) -> (field<"bls12-381.fr">, rng<"bls12-381.fr">) effects (local) {
        let (x, next) = random::draw::<"bls12-381.fr">(r); return (x, next);
      }
      fn Client<>(r: rng<"bls12-381.fr">) -> (field<"bls12-381.fr">, rng<"bls12-381.fr">) effects (local) {
        return Draw(r);
      }
      link Closed = Client<>;
      fn Check(x: "bls12-381.fr"::Element) -> bool {
        let ok = field::equal::<bls12-381.fr>(x, x); control::require(ok); return ok;
      }
      protocol Main {
        roles (P, V);
        inputs (V coins: Rng<"bls12-381.fr">);
        outputs (V bool, V Rng<"bls12-381.fr">);
        local [first] V: let (x, r1) = Draw(coins);
        local [second] V: let (y, r2) = Closed(r1);
        local [check] V: let ok = Check(y);
        return (ok, r2);
      }
      instance root: Main { roles (P = P, V = V); }
      entry main = root;
    }'''
