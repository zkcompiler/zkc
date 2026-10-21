"""Exercise migration records with kernel-checked Lean modules and the real emitter.

Run in an existing Lake environment, without building shared outputs:
python3 lean/checks/check_migration_exporter.py --package /absolute/lean/package \
    --output /tmp/migration-exporter-controls
All generated sources, oleans and records stay in the output directory.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.migration import capture_records, compare, name_key, read_records  # noqa: E402


def run(package, *args):
    subprocess.run(['lake', 'env', 'lean', *map(str, args)], cwd=package,
                   stdin=subprocess.DEVNULL, check=True)


def controls(package, output):
    package, output = package.resolve(), output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    scratch = output / 'modules'
    scratch.mkdir(exist_ok=True)
    # Lake retains the caller's LEAN_PATH after its own package paths.
    original = os.environ.get('LEAN_PATH')
    os.environ['LEAN_PATH'] = str(scratch) + (os.pathsep + original if original else '')
    results = []

    def check(label, condition):
        if not condition: raise AssertionError(label)
        results.append(label)

    def build(module, source):
        path = scratch / f'{module}.lean'
        path.write_text(source)
        run(package, '-R', scratch, '-o', scratch / f'{module}.olean', path)

    def capture(label, modules):
        path = output / f'{label}.jsonl'
        capture_records(package, modules, path)
        return read_records([path])

    def key(*components):
        return name_key([['num' if type(value) is int else 'str', value] for value in components])

    try:
        for module, proof in [('ProvenancePure', 'True.intro'),
                              ('ProvenanceChoice', 'Classical.choice (show Nonempty True from ⟨True.intro⟩)')]:
            build(module, f'''import Lean
theorem Shared.claim : True := {proof}
theorem Shared.helper : True := {proof}
theorem Shared.indirect : True := Shared.helper
''')
        both = capture('provenance-combined', ['ProvenancePure', 'ProvenanceChoice'])
        for declaration in ('claim', 'helper', 'indirect'):
            identity = key('Shared', declaration)
            check(f'pure stored {declaration} has no axioms',
                  both.declarations[('ProvenancePure', identity)]['axioms'] == [])
            check(f'choice stored {declaration} retains choice',
                  both.declarations[('ProvenanceChoice', identity)]['axioms'] == [key('Classical', 'choice')])
        pure = capture('provenance-pure', ['ProvenancePure'])
        choice = capture('provenance-choice', ['ProvenanceChoice'])
        result = compare(pure, choice, {'ProvenancePure': ['ProvenanceChoice']})
        check('same-name theorem proof changes are detected solely through axioms',
              result['status'] == 'review-required' and len(result['changes']) == 3 and
              all(row['fields'] == ['axioms'] for row in result['changes']))

        build('NameOwners', '''import Lean
open Lean Elab Command
run_cmd do
  for (name, value) in [
      (Name.str .anonymous "A.b»", 0),
      (Name.str (Name.str .anonymous "A") "b»", 1),
      (Name.num (Name.str .anonymous "N") 7, 2),
      (Name.str (Name.str .anonymous "N") "7", 3),
      (Name.str .anonymous (String.ofList (([9,8,12,10,13,34,92,955] : List Nat).map Char.ofNat)), 4)] do
    liftCoreM <| addDecl <| .defnDecl {
      name := name
      levelParams := []
      type := mkConst ``Nat
      value := mkNatLit value
      hints := .abbrev
      safety := .safe }
  for name in [Name.str .anonymous "Assumption.proof»",
               Name.str (Name.str .anonymous "Assumption") "proof»"] do
    liftCoreM <| addDecl <| .axiomDecl {
      name := name
      levelParams := []
      type := mkConst ``True
      isUnsafe := false }
''')
        for module, reference in [
            ('ReferenceOne', 'Name.str .anonymous "A.b»"'),
            ('ReferenceTwo', 'Name.str (Name.str .anonymous "A") "b»"'),
        ]:
            build(module, f'''import NameOwners
open Lean Elab Command
run_cmd do
  liftCoreM <| addDecl <| .defnDecl {{
    name := `Collision.target
    levelParams := []
    type := mkConst ``Nat
    value := mkConst ({reference})
    hints := .abbrev
    safety := .safe }}
''')
        owners = capture('colliding-identities', ['NameOwners'])
        flat, nested = key('A.b»'), key('A', 'b»')
        check('colliding diagnostic declaration names preserve separate identities',
              ('NameOwners', flat) in owners.declarations and ('NameOwners', nested) in owners.declarations and
              owners.declarations[('NameOwners', flat)]['display_name'] ==
              owners.declarations[('NameOwners', nested)]['display_name'])
        check('numeric and string kernel components preserve separate identities',
              ('NameOwners', key('N', 7)) in owners.declarations and
              ('NameOwners', key('N', '7')) in owners.declarations)
        check('control characters and Unicode have identical Lean/Python key encodings',
              ('NameOwners', key('\t\b\f\n\r"\\λ')) in owners.declarations)
        one = capture('reference-one', ['ReferenceOne'])
        two = capture('reference-two', ['ReferenceTwo'])
        result = compare(one, two, {'ReferenceOne': ['ReferenceTwo']})
        check('switching an unselected upstream reference with colliding display is rejected',
              result['status'] == 'review-required' and len(result['changes']) == 1 and
              result['changes'][0]['fields'] == ['body'])
        target = key('Collision', 'target')
        check('upstream body references carry injective identities',
              one.declarations[('ReferenceOne', target)]['body'] == ['constant', flat, []] and
              two.declarations[('ReferenceTwo', target)]['body'] == ['constant', nested, []])
        try:
            compare(one, two, {'ReferenceOne': ['ReferenceTwo']}, {flat: nested})
        except ValueError:
            results.append('unselected upstream names cannot be silently renamed')
        else:
            raise AssertionError('unselected rename accepted')

        for module, reference in [
            ('AxiomOne', 'Name.str .anonymous "Assumption.proof»"'),
            ('AxiomTwo', 'Name.str (Name.str .anonymous "Assumption") "proof»"'),
        ]:
            build(module, f'''import NameOwners
open Lean Elab Command
run_cmd do
  liftCoreM <| addDecl <| .thmDecl {{
    name := `Collision.claim
    levelParams := []
    type := mkConst ``True
    value := mkConst ({reference}) }}
''')
        axiom_one = capture('axiom-one', ['AxiomOne'])
        axiom_two = capture('axiom-two', ['AxiomTwo'])
        result = compare(axiom_one, axiom_two, {'AxiomOne': ['AxiomTwo']})
        check('colliding upstream axiom names remain a semantic axiom change',
              result['status'] == 'review-required' and len(result['changes']) == 1 and
              result['changes'][0]['fields'] == ['axioms'])
        for components in [('Assumption.proof»',), ('Assumption', 'proof»')]:
            identity = key(*components)
            check(f'owned axiom includes its own encoded identity {components}',
                  owners.declarations[('NameOwners', identity)]['axioms'] == [identity])

        for module in ('PrivateOriginal', 'PrivateRelocated'):
            build(module, '''import Lean
private def helper : Nat := 37
def PrivateClient.target : Nat := helper
''')
        old = capture('private-original', ['PrivateOriginal'])
        new = capture('private-relocated', ['PrivateRelocated'])
        moves = {'PrivateOriginal': ['PrivateRelocated']}
        check('private relocation requires an explicit mapping', compare(old, new, moves)['status'] == 'review-required')
        old_helpers = [name for (_, name), row in old.declarations.items() if row['display_name'].startswith('_private.')]
        new_helpers = [name for (_, name), row in new.declarations.items() if row['display_name'].startswith('_private.')]
        check('private relocation fixture owns exactly one helper per module', len(old_helpers) == len(new_helpers) == 1)
        renames = {old_helpers[0]: new_helpers[0]}
        (output / 'private-renames.json').write_text(json.dumps(renames, indent=2) + '\n')
        check('explicit injective private-name relocation preserves actual records',
              compare(old, new, moves, renames)['status'] == 'preserved')
        build('EmptyOwner', 'import Lean\n')
        try:
            capture_records(package, ['EmptyOwner'], output / 'empty-must-not-exist.jsonl')
        except ValueError:
            check('an empty selected inventory cannot pass preservation',
                  not (output / 'empty-must-not-exist.jsonl').exists())
        else:
            raise AssertionError('empty capture accepted')
        with_empty = capture('explicit-empty-owner', ['PrivateOriginal', 'EmptyOwner'])
        check('an existing empty module stays explicitly covered alongside owned declarations',
              with_empty.modules == {'PrivateOriginal', 'EmptyOwner'})
    finally:
        if original is None: os.environ.pop('LEAN_PATH', None)
        else: os.environ['LEAN_PATH'] = original
    emitter = Path(__file__).with_name('MigrationRecords.lean')
    receipt = {'status': 'pass', 'checks': results, 'count': len(results),
               'package': str(package), 'scratch': str(output), 'shared_builds': 0}
    receipt['emitter_sha256'] = hashlib.sha256(emitter.read_bytes()).hexdigest()
    (output / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    receipt = controls(args.package, args.output)
    print(f"migration exporter: {receipt['count']} actual-emitter controls passed")


if __name__ == '__main__':
    main()
