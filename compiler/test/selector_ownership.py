"""Direct functions, origin groups, definitions and configurations stay distinct."""

import json

from cases import case
from commands import Commands
from selector_cases import descriptor, family_source, source
from tools import compiler, construction_test, records


directory = records()
commands = Commands(directory)


def write(name, value):
    path = directory / name
    path.write_text(value if isinstance(value, str) else json.dumps(value))
    return path


def run(mode, *paths, refuses=None):
    return commands.run([compiler, mode, *paths], refuses=refuses)


for identity in ('exact', 'normalized'):
    for calls in (False, True):
        for offset in (False, True):
            with case(f'group-{identity}-calls-{calls}-offset-{offset}'):
                carrier = source(offset=offset, calls=calls)
                raw = write('source.json', carrier)
                printed = run('protocol-format', raw)
                text = write('source.pir', printed)
                assert json.loads(run('protocol-source', text)) == carrier
                # A closed representation change cannot alter selector scope,
                # successful constructions or the reason a request refuses.
                for name, owners in (('direct', ['F']), ('both', ['F', 'A']),
                                     ('group', ['Sampling']), ('overlap', ['F', 'Sampling'])):
                    draw = write('carrier-draw.json', descriptor(identity, owners))
                    reason = ('construction-unselected-draw' if name == 'direct' else
                              'source-site-selection' if identity == 'normalized' and
                              name in ('group', 'overlap') else None)
                    original = run('protocol-construct', raw, draw, refuses=reason)
                    formatted = run('protocol-construct', text, draw, refuses=reason)
                    if reason is None:
                        assert json.loads(formatted) == json.loads(original)
                # Authoring has project selectors. Carrier text retains the
                # closed selector contract, checked separately below.
                spelling = printed.replace('carrier module', 'module', 1)
                text = write('source.pir', spelling)
                direct = write('direct.json', descriptor(identity, ['F']))
                # F must not silently select A's draw through Sampling.
                run('protocol-construct', text, direct, refuses='construction-unselected-draw')
                both = write('both.json', descriptor(identity, ['F', 'A']))
                selected = json.loads(run('protocol-construct', text, both))
                assert selected[1][5][1] == [['F', 'sample'], ['A', 'sample']]
                group = write('group.json', descriptor(identity, ['Sampling']))
                grouped = json.loads(run('protocol-construct', text, group))
                # Binding normalized groups must use each member's own map.
                assert grouped[2:] == selected[2:]
                overlap = write('overlap.json', descriptor(identity, ['F', 'Sampling']))
                assert json.loads(run('protocol-construct', text, overlap))[2:] == selected[2:]
                missing = write('missing.json', descriptor(identity, ['Sampling']))
                value = descriptor(identity, ['Sampling']); value[5][1][0][1] = 'absent'
                missing.write_text(json.dumps(value))
                run('protocol-construct', text, missing,
                    refuses='source-site-selection' if identity == 'normalized' else 'construction-draw-selector')

# Shared origins may equal concrete names. Admission and formatting preserve
# these valid carriers; only an unsafe normalized construction is refused.
for reverse in (False, True):
    for offset in (False, True):
        with case(f'origin-family-{reverse}-{offset}'):
            carrier = source(offset=offset)
            carrier[2][0][5][0] = 'F'
            carrier[2][1][5][0] = 'F'
            if reverse:
                carrier[2].reverse()
            raw = write('family.json', carrier)
            run('protocol-admit', raw)
            text = write('family.pir', run('protocol-format', raw))
            assert json.loads(run('protocol-source', text)) == carrier
            run('protocol-prepare', raw)
            for identity in ('exact', 'normalized'):
                draw = write('family-draw.json', descriptor(identity, ['F']))
                if identity == 'normalized' and offset:
                    run('protocol-construct', raw, draw, refuses='construction-selector-coordinates')
                else:
                    selected = json.loads(run('protocol-construct', raw, draw))
                    overlap = write('family-overlap.json', descriptor(identity, ['F', 'A']))
                    assert json.loads(run('protocol-construct', raw, overlap))[2:] == selected[2:]

with case('raw-origin-alias-must-not-select-an-unrelated-numbered-draw'):
    carrier = source(offset=False)
    carrier[2][0][5][0] = carrier[2][1][5][0] = 'F'
    body = carrier[2][1][4]
    body[0][4] = ['r1']
    body.insert(0, ['op', 'other', 'draw', [], ['r'], ['ignored', 'r1']])
    raw = write('unrelated.json', carrier)
    run('protocol-admit', raw)
    run('protocol-format', raw)
    for identity in ('exact', 'normalized'):
        draw = write('unrelated-draw.json', descriptor(identity, ['F', 'A']))
        run('protocol-construct', raw, draw, refuses=(
            'construction-unselected-draw' if identity == 'exact'
            else 'construction-selector-coordinates'))

with case('reclaimed-origin-is-valid-but-direct-authoring-selector-is-ambiguous'):
    carrier = source(offset=False)
    carrier[2][0][5][0] = 'Different'
    carrier[2][1][5][0] = 'F'
    raw = write('reclaimed.json', carrier)
    printed = run('protocol-format', raw)
    app = write('reclaimed.pir', printed.replace('carrier module', 'module', 1))
    run('protocol-admit', app)
    for identity in ('exact', 'normalized'):
        draw = write('reclaimed-draw.json', descriptor(identity, ['F', 'A']))
        run('protocol-construct', app, draw, refuses='construction-source-selector-ambiguous')
        # The closed carrier selector intentionally denotes the alias union.
        selected = run('protocol-construct', raw, draw)
        closed = write('reclaimed-carrier.pir', printed)
        assert json.loads(run('protocol-construct', closed, draw)) == json.loads(selected)

# Imported ordinary functions bind to the origin their declaration was
# allocated, which their emitted entries and linked copies share; aliases
# preserve that target. Generic definitions keep their origin names,
# configurations their own.
for generic in (False, True):
    with case(f'imported-generic-{generic}'):
        body = '''
          pub fn Draw<F: domain Field>(r: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
            [sample] let (x, next) = random::draw::<F>(r); return (x, next);
          }
          pub configure First = Draw(F = bls12-381.fr);
          pub configure Second = Draw(F = bls12-381.fr);
        ''' if generic else '''
          pub fn First(r: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
            [sample] let (x, next) = random::draw::<bls12-381.fr>(r); return (x, next);
          }
          pub fn Second(r: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
            [padding] let pad = index::constant() attributes ("1");
            [sample] let (x, next) = random::draw::<bls12-381.fr>(r); return (x, next);
          }
        '''
        write('helpers.pir', 'module {' + body + '}')
        # Format a complete admitted source first, then substitute declarations.
        raw = write('import-base.json', source())
        formatted = run('protocol-format', raw)
        check_start = formatted.index('fn Check')
        rest = formatted[check_start:]
        rest = rest.replace('equal(x, x)', 'field::equal::<bls12-381.fr>(x, x)')
        rest = rest.replace('guard(ok)', 'control::require(ok)')
        rest = rest.replace('F(coins)', 'First(coins)').replace('A(r1)', 'Second(r1)')
        app = write('import.pir', 'module { mod helpers; use helpers::{First, Second}; use helpers::First as Alias;\n' + rest)
        lowered = json.loads(run('protocol-source', app))
        common = lowered[3] if generic else lowered
        if generic:
            names = [row[1] for row in lowered[2]]
        else:
            names = [row[1] for row in common[2] if row[5][0] in ('helpers.First', 'helpers.Second')]
        assert len(names) == 2, names
        for identity in ('exact', 'normalized'):
            direct = write('import-direct.json', descriptor(identity, ['Alias']))
            run('protocol-construct', app, direct, refuses='construction-unselected-draw')
            both = write('import-both.json', descriptor(identity, ['Alias', 'helpers.Second']))
            selected = json.loads(run('protocol-construct', app, both))
            # Exact identity keeps the origins; normalized identity writes each
            # out as the functions carrying the site.
            assert {s[0] for s in selected[1][5][1]} == (
                set(names) if generic or identity == 'normalized'
                else {'helpers.First', 'helpers.Second'})
            if generic:
                all_copies = write('definition.json', descriptor(identity, ['helpers.Draw']))
                defined = json.loads(run('protocol-construct', app, all_copies))
                assert defined[1][5][1] == [['helpers.Draw', 'sample']]
                assert defined[2:] == selected[2:]
                # Materialized function origins name the generic definition;
                # the common carrier must still admit and format losslessly.
                prepared = json.loads(run('protocol-prepare', app))
                prepared_path = write('prepared.json', prepared)
                printed_path = write('prepared.pir', run('protocol-format', prepared_path))
                assert json.loads(run('protocol-source', printed_path)) == prepared

with case('a-function-named-as-its-shared-group-is-ambiguous'):
    # F and A both claim the origin F. The selector F names F alone and the
    # group, whose closed carrier selector would also reach A.
    raw = write('namesake.json', family_source())
    lines = run('protocol-format', raw).replace('carrier module', 'module', 1).splitlines()
    index = next(i for i, line in enumerate(lines) if line.lstrip().startswith('fn F('))
    # The printer leaves a self-origin implicit; authored source states F's claim.
    assert lines[index].endswith(' {') and 'origin' not in lines[index]
    lines[index] = lines[index][:-2] + ' origin F() {'
    app = write('namesake.pir', '\n'.join(lines) + '\n')
    run('protocol-admit', app)
    for identity in ('exact', 'normalized'):
        for owners in (['F'], ['F', 'A']):
            draw = write('namesake-draw.json', descriptor(identity, owners))
            run('protocol-construct', app, draw, refuses='construction-source-selector-ambiguous')
        alone = write('namesake-alone.json', descriptor(identity, ['A']))
        run('protocol-construct', app, alone, refuses='construction-unselected-draw')
        # The closed carrier selector denotes the family, as a helper's copies share it.
        draw = write('namesake-draw.json', descriptor(identity, ['F']))
        run('protocol-construct', raw, draw)

LIBRARY = """module {
  library(namespace="test", name="sel", version="1", resolution="r1");
  pub fn Sample(coins: rng<"bls12-381.fr">) -> (field<"bls12-381.fr">, rng<"bls12-381.fr">) effects (local) {
    let (x, after) = random::draw::<"bls12-381.fr">(coins);
    return (x, after);
  }
  pub interface Source {
    local draw(coins: rng<"bls12-381.fr">) -> (field<"bls12-381.fr">, rng<"bls12-381.fr">) effects (local);
  }
  pub component Plain: Source {
    local draw(coins: rng<"bls12-381.fr">) -> (field<"bls12-381.fr">, rng<"bls12-381.fr">) effects (local) {
      return Sample(coins);
    }
  }
  pub fn Forward<C: Source>(coins: rng<"bls12-381.fr">) -> (field<"bls12-381.fr">, rng<"bls12-381.fr">) effects (local) {
    return C::draw(coins);
  }
}
"""
LINKING = """module {
  dependency sel = library(namespace="test", name="sel", version="1", resolution="r1");
  use sel::{Sample, Plain, Forward};
  link Linked = Forward<Plain>;
  fn Same(a: "bls12-381.fr"::Element) -> bool { let s = field::equal::<bls12-381.fr>(a, a); return s; }
  protocol Pair {
    roles (P, V);
    inputs (V coins: Rng<"bls12-381.fr">);
    outputs (V bool);
    local [first] V: let (a, r1) = Sample(coins);
    local [second] V: let (b, r2) = Linked(r1);
    local [check] V: let same = Same(a);
    return same;
  }
  instance run: Pair { roles (P = P, V = V); }
  entry main = run;
}
"""

with case('an-imported-library-function-reaches-its-copies'):
    # The imported entry applies a copy of the library body, and linking makes
    # another inside the linked client. Both carry the draw; naming the
    # function selects both.
    library = write('sel-lib.pir', LIBRARY)
    app = write('linking.pir', LINKING)
    lowered = json.loads(run('protocol-source', app, f'--library={library}'))
    copies = {row[1] for row in lowered[2]
              if row[5][0] == 'Sample' and any(i[0] == 'op' for i in row[4])}
    assert len(copies) == 2, copies
    for identity in ('exact', 'normalized'):
        for spelling in ('Sample', 'sel::Sample'):
            descriptor_text = (f'construction main identity {identity} {{ producer P; validator V; '
                               f'random coins at ({spelling} call_1); accept 0; '
                               'suite "merlin3.bls12-381.fr64be/1"; }')
            chosen = write('linking.construction.pir', descriptor_text)
            printed = run('protocol-construct', app, chosen, f'--library={library}')
            assert commands.run([construction_test, app, chosen, library]) == printed
            constructed = json.loads(printed)
            selected = {selector[0] for selector in constructed[1][5][1]}
            assert selected == ({'Sample'} if identity == 'exact' else copies), selected

# Force the SSA-expansion branch with an unrelated identity call. It must choose
# exactly the same reached primitive occurrences as the call-free fast path.
# The construction identity prefix changes with source, so compare occurrence
# provenance and the actual substituted challenge operations, not proof bytes.
for identity in ("exact", "normalized"):
    for offset in (False, True):
        with case(f"expansion-occurrence-parity-{identity}-{offset}"):
            results = []
            for calls in (False, True):
                raw = write("parity.json", source(offset=offset, calls=calls))
                draw = write("parity-descriptor.json", descriptor(identity, ["F", "A"]))
                results.append(json.loads(run("protocol-construct", raw, draw)))
            # Generated helper symbols contain the source identity prefix.
            provenance = [[row[1:] for row in result[4]] for result in results]
            assert provenance[0] == provenance[1], "expansion changed primitive provenance"
            selected = [row for row in provenance[0] if row[-1] == "construction"]
            assert len(selected) == 4, "both selected draws must be substituted for both roles"

print(f'{commands.save()} selector ownership checks passed')
