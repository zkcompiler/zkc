"""Semantic-preservation controls that statement-only checks would miss."""

from copy import deepcopy
import json

import pytest
from harness import load


def audit():
    return load('lean_migration', 'lean/support/migration.py')


def key(name):
    # These fixture names deliberately contain only ordinary string components.
    return audit().name_key([['str', part] for part in name.split('.')])


def fixture(module='Old'):
    row = {'name': key('Family.target'), 'display_name': 'Family.target', 'module': module, 'kind': 'definition',
           'universes': [], 'type': ['sort', ['zero']],
           'body': ['constant', key('True'), []], 'shape': {'safety': 'Lean.DefinitionSafety.safe', 'hints': ['abbreviation']}, 'axioms': [],
           'type_dependencies': [], 'body_dependencies': [key('True')]}
    theorem = row | {'name': key('Family.claim'), 'kind': 'theorem',
                     'type': ['forall', 'explicit', ['constant', key('Family.target'), []],
                              ['constant', key('Family.target'), []]],
                     'body': None, 'shape': None, 'body_dependencies': []}
    return audit().Records({module}, {(module, row['name']): row, (module, theorem['name']): theorem})


def test_explicit_module_move_preserves_declarations():
    result = audit().compare(fixture(), fixture('New'), {'Old': ['New']})
    assert result['status'] == 'preserved'
    assert result['preserved_declarations'] == 2
    assert not result['changes']


def test_definition_change_is_found_when_claim_type_is_unchanged():
    before, after = fixture(), fixture()
    after.declarations[('Old', key('Family.target'))]['body'] = ['constant', key('False'), []]
    result = audit().compare(before, after)
    assert result['status'] == 'review-required'
    assert result['preserved_declarations'] == 1
    assert result['changes'][0]['name'] == key('Family.target')
    assert result['changes'][0]['fields'] == ['body']


def test_new_permitted_axiom_is_still_a_preservation_change():
    before, after = fixture(), fixture()
    after.declarations[('Old', key('Family.claim'))]['axioms'] = [key('Classical.choice')]
    result = audit().compare(before, after)
    assert result['changes'][0]['fields'] == ['axioms']


def test_unselected_package_cannot_silently_skip_old_claims():
    result = audit().compare(fixture(), fixture('Other'))
    assert result['missing_modules'] == ['Old']
    assert len(result['changes']) == 2
    assert all(row['status'] == 'missing' for row in result['changes'])


def test_implicit_binder_changes_are_retained():
    before, after = fixture(), fixture()
    after.declarations[('Old', key('Family.claim'))]['type'][1] = 'implicit'
    assert audit().compare(before, after)['changes'][0]['fields'] == ['type']


def test_split_requires_every_declared_destination_to_be_emitted():
    result = audit().compare(fixture(), fixture(), {'Old': ['Old', 'Security']})
    assert result['missing_modules'] == ['Security']
    assert result['status'] == 'review-required'


@pytest.mark.parametrize('change', ['empty', 'count', 'duplicate', 'unselected'])
def test_record_reader_rejects_incomplete_or_ambiguous_coverage(tmp_path, change):
    rows = list(fixture().declarations.values())
    header = {'format': audit().FORMAT, 'name_encoding': audit().NAME_ENCODING,
              'axiom_provenance': audit().AXIOM_PROVENANCE, 'modules': ['Old'], 'declarations': 2}
    if change == 'empty':
        header['declarations'] = 0
        rows = []
    elif change == 'count':
        rows.pop()
    elif change == 'duplicate':
        rows[1] = deepcopy(rows[0])
    else:
        rows[0]['module'] = 'Outside'
    path = tmp_path / 'records.jsonl'
    path.write_text('\n'.join(json.dumps(row) for row in [header, *rows]) + '\n')
    with pytest.raises(ValueError):
        audit().read_records([path])


def test_universe_alpha_renaming_preserves_indices_and_usage():
    before, after = fixture(), fixture()
    old = before.declarations[('Old', key('Family.target'))]
    new = after.declarations[('Old', key('Family.target'))]
    old.update(universes=[key('u'), key('v')], type=['sort', ['parameter', key('u')]])
    new.update(universes=[key('alpha'), key('beta')], type=['sort', ['parameter', key('alpha')]])
    assert audit().compare(before, after)['status'] == 'preserved'
    new['type'] = ['sort', ['parameter', key('beta')]]
    assert audit().compare(before, after)['changes'][0]['fields'] == ['type']


def test_explicit_private_rename_checks_references_and_definitions():
    before, after = fixture(), fixture('New')
    row = after.declarations.pop(('New', key('Family.target')))
    row['name'] = key('Moved.target')
    after.declarations[('New', key('Moved.target'))] = row
    claim = after.declarations[('New', key('Family.claim'))]
    claim['type'] = ['forall', 'explicit', ['constant', key('Moved.target'), []],
                     ['constant', key('Moved.target'), []]]
    moves, renames = {'Old': ['New']}, {key('Family.target'): key('Moved.target')}
    assert audit().compare(before, after, moves)['status'] == 'review-required'
    assert audit().compare(before, after, moves, renames)['status'] == 'preserved'
    row['body'] = ['constant', key('False'), []]
    assert audit().compare(before, after, moves, renames)['changes'][0]['fields'] == ['body']


def test_renaming_never_rewrites_string_literals():
    before, after = fixture(), fixture()
    before.declarations[('Old', key('Family.target'))]['body'] = ['string', 'Family.target']
    after.declarations[('Old', key('Family.target'))]['body'] = ['string', 'Moved.target']
    assert audit().compare(before, after)['status'] == 'review-required'
    assert audit().canonical(before.declarations[('Old', key('Family.target'))],
                             {key('Family.target'): key('Moved.target')})['body'] == ['string', 'Family.target']


@pytest.mark.parametrize('renames', [
    {key('Missing'): key('Family.target')}, {key('Family.target'): key('Missing')},
    {key('Family.target'): key('Family.claim')},
])
def test_rename_map_cannot_hide_missing_or_duplicate_declarations(renames):
    with pytest.raises(ValueError):
        audit().compare(fixture(), fixture(), renames=renames)


def write_records(path, rows, modules=None, header=None):
    header = audit().record_header(modules or ['Old'], len(rows)) if header is None else header
    path.write_text('\n'.join(json.dumps(row) for row in [header, *rows]) + '\n')


def test_structural_name_keys_are_injective_and_display_names_are_diagnostics(tmp_path):
    encoder = audit().name_key
    names = [encoder([]), encoder([['str', '']]), encoder([['str', 'A.b»']]),
             encoder([['str', 'A'], ['str', 'b»']]), encoder([['str', 'A'], ['num', 3]]),
             encoder([['str', 'A'], ['str', '3']])]
    assert len(set(names)) == len(names)
    rows = []
    for name in names:
        row = deepcopy(next(iter(fixture().declarations.values())))
        row.update(name=name, display_name='same diagnostic spelling')
        rows.append(row)
    path = tmp_path / 'records.jsonl'
    write_records(path, rows)
    assert len(audit().read_records([path]).declarations) == len(names)


@pytest.mark.parametrize('components', [None, ['A'], [['str', 0]], [['num', '0']],
                                       [['num', -1]], [['num', True]], [['other', 'A']]])
def test_invalid_kernel_name_components_are_refused(components):
    with pytest.raises(ValueError): audit().name_key(components)


def test_kernel_name_encoding_matches_lean_control_character_escaping():
    components = [['str', '\t\b\f\n\r"\\λ']]
    encoded = audit().name_key(components)
    assert json.loads(encoded) == components
    assert '\\u0009' in encoded and '\\u0008' in encoded and '\\u000c' in encoded
    audit().validate_name(encoded)
    with pytest.raises(ValueError): audit().name_key([['str', '\ud800']])


@pytest.mark.parametrize('field', ['name', 'universes', 'axioms', 'type_dependencies',
                                  'body_dependencies', 'constant', 'projection', 'parameter',
                                  'free', 'metavariable', 'inductive', 'constructors', 'rule'])
def test_reader_requires_encoded_names_in_every_semantic_position(tmp_path, field):
    row = deepcopy(next(iter(fixture().declarations.values())))
    if field == 'name': row[field] = 'Unencoded'
    elif field in ('universes', 'axioms', 'type_dependencies', 'body_dependencies'):
        row[field] = ['Unencoded']
    elif field == 'constant': row['body'] = ['constant', 'Unencoded', []]
    elif field == 'projection': row['body'] = ['projection', 'Unencoded', 0, ['bound', 0]]
    elif field in ('parameter', 'free', 'metavariable'): row['body'] = [field, 'Unencoded']
    elif field == 'inductive':
        row.update(kind='constructor', shape={'inductive': 'Unencoded', 'index': 0,
                                             'parameters': 0, 'fields': 0, 'unsafe': False})
    elif field == 'constructors':
        row.update(kind='inductive', shape={'parameters': 0, 'indices': 0, 'mutual': [],
                                           'constructors': ['Unencoded'], 'nested': 0,
                                           'recursive': False, 'unsafe': False, 'reflexive': False})
    else:
        row.update(kind='recursor', shape={'mutual': [], 'parameters': 0, 'indices': 0,
                                          'motives': 0, 'minors': 0, 'k': False, 'unsafe': False,
                                          'rules': [{'constructor': 'Unencoded', 'fields': 0,
                                                     'rhs': ['bound', 0]}]})
    path = tmp_path / 'records.jsonl'
    write_records(path, [row])
    with pytest.raises(ValueError): audit().read_records([path])


@pytest.mark.parametrize('change', ['old-header', 'noncanonical-name', 'unknown-expression',
                                   'unknown-shape-field', 'unknown-row-field', 'duplicate-universe',
                                   'name-encoding', 'axiom-provenance', 'missing-expression-name',
                                   'safety', 'shape-count', 'shape-flag'])
def test_reader_refuses_legacy_or_malformed_semantics(tmp_path, change):
    row = deepcopy(next(iter(fixture().declarations.values())))
    header = audit().record_header(['Old'], 1)
    if change == 'old-header':
        header.pop('name_encoding'); header.pop('axiom_provenance')
    elif change == 'noncanonical-name': row['name'] = '[["str", "Family"]]'
    elif change == 'unknown-expression': row['body'] = ['unrecognized', key('Family.target')]
    elif change == 'unknown-shape-field': row['shape']['unrecognized'] = key('Family.target')
    elif change == 'unknown-row-field': row['unrecognized'] = 0
    elif change == 'duplicate-universe': row['universes'] = [key('u'), key('u')]
    elif change == 'name-encoding': header['name_encoding'] = 'display-names'
    elif change == 'axiom-provenance': header['axiom_provenance'] = 'merged-environment'
    elif change == 'missing-expression-name': row['body'] = ['constant']
    elif change == 'safety': row['shape']['safety'] = 'unknown'
    else:
        row.update(kind='constructor', shape={'inductive': key('Family.target'), 'index': 0,
                                             'parameters': 0, 'fields': 0, 'unsafe': False})
        if change == 'shape-count': row['shape']['fields'] = True
        else: row['shape']['unsafe'] = 0
    path = tmp_path / 'records.jsonl'
    write_records(path, [row], header=header)
    with pytest.raises(ValueError): audit().read_records([path])


def test_explicit_renaming_covers_projection_shape_rules_and_axioms():
    old = deepcopy(next(iter(fixture().declarations.values())))
    source, destination = key('Family.target'), key('Moved.target')
    old.update(kind='recursor', body=['projection', source, 0, ['constant', source, []]],
               axioms=[source], shape={'mutual': [source], 'rules': [
                   {'constructor': source, 'fields': 0, 'rhs': ['constant', source, []]}]})
    new = deepcopy(old)
    new.update(body=['projection', destination, 0, ['constant', destination, []]],
               axioms=[destination], shape={'mutual': [destination], 'rules': [
                   {'constructor': destination, 'fields': 0, 'rhs': ['constant', destination, []]}]})
    assert audit().canonical(old, {source: destination}) == audit().canonical(new)


def test_capture_runs_modules_independently_and_keeps_an_existing_result_on_failure(tmp_path, monkeypatch):
    module = audit()
    calls = []
    fail = False

    def exporter(command, **kwargs):
        calls.append((command, kwargs))
        owner = command[-1]
        if fail and owner == 'Old': raise module.subprocess.CalledProcessError(1, command)
        write_records(module.Path(command[-2]), list(fixture(owner).declarations.values()), modules=[owner])

    monkeypatch.setattr(module.subprocess, 'run', exporter)
    output = tmp_path / 'capture.jsonl'
    assert module.capture_records(tmp_path, ['Old', 'New'], output) == 4
    assert module.read_records([output]).modules == {'Old', 'New'}
    assert [command[-1] for command, _ in calls] == ['New', 'Old']
    assert all(command[:4] == ['lake', 'env', 'lean', '--run'] for command, _ in calls)
    previous = output.read_bytes()
    fail = True
    with pytest.raises(module.subprocess.CalledProcessError):
        module.capture_records(tmp_path, ['Old', 'New'], output)
    assert output.read_bytes() == previous
    assert sorted(path.name for path in tmp_path.iterdir()) == ['capture.jsonl']
