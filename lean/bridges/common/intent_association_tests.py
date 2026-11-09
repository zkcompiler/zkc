#!/usr/bin/env python3
"""Focused Python association controls; no compiler, Lean process or builds.

Scalar interfaces below are reader fixtures over actual maintained snapshots,
not fresh native/source correspondence evidence. Recursive interface fixtures
are the exact compiler-produced files and retain their documented scope.
"""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[1]
ROOT = LEAN.parent
sys.path.insert(0, str(LEAN))
sys.path.insert(0, str(HERE))

import intent  # noqa: E402
from bridges.common.intent_association import LogicalInterface, SourceAssociation  # noqa: E402
from request_support import Obligation  # noqa: E402
from verify import validate  # noqa: E402


def read(path):
    return json.loads(path.read_text())


def schema(kind, identity, leaf):
    return {'kind': kind, 'identity': identity, 'type': 'diagnostic spelling', 'generated': None,
            'custody': 0, 'sealed': False, 'constructible': True, 'permissions': ['Copy', 'Drop'],
            'roles': [], 'element': None, 'leaves': [leaf] if leaf else [], 'fields': [], 'alternatives': []}


def port(name, index, native, shape, roles):
    return {'name': name, 'index': index, 'native': [native], 'type': shape['type'],
            'schema': copy.deepcopy(shape), 'placement': {'kind': 'data', 'roles': roles},
            'components': [{'path': [], 'leaf': 0, 'role': role, 'facet': 'data', 'native': native}
                           for role in roles]}


def scalar_fixture(form='schnorr'):
    data = read(LEAN / 'applications/Zkc/Applications/IR/NativePrograms/fixtures' / (form + '.json'))
    root = next(row for row in data[7] if row[1] == data[3])
    declaration = data[5][0] if data[5] else None
    group = schema('group', '1' * 64, 'group:bls12-381.g1')
    field = schema('field', '2' * 64, 'field:bls12-381.fr')
    boolean = schema('boolean', '3' * 64, 'bool')
    shapes = [group, group, field]
    roles = ['P', 'V']
    inputs = [port(name, index, index, shape, [0, 1] if index < 2 else [0])
              for index, (name, shape) in enumerate(zip(('base', 'point', 'scalar'), shapes))]
    def selector(value):
        direction, index, role = value
        return {'direction': direction, 'port': index, 'role': roles[root[6][1].index(role)], 'path': []}
    clauses = []
    for retained in data[8][0][1]:
        clauses.append({'name': retained[1], 'kind': retained[0], 'subject': {
            'relation': retained[2][0], 'operands': list(map(selector, retained[2][1]))},
            'residual': None, 'decision': selector(retained[4])})
    protocol = {'symbol': data[3], 'roles': roles, 'inputs': inputs,
                'outputs': [port('accepted', 0, 0, boolean, [1])],
                'services': [{'name': name, 'native': index, 'owner': roles[index - 3],
                              'contract': root[4][index][1]}
                             for index, name in ((3, 'nonces'), (4, 'challenges'))],
                'clauses': clauses, 'common_input_requirements': []}
    relation = None if declaration is None else {
                'symbol': declaration[1], 'static_arguments': copy.deepcopy(declaration[6]),
                'inputs': [{'name': name, 'purpose': purpose, 'native': [index], 'schema': copy.deepcopy(shape)}
                           for index, (name, purpose, shape) in enumerate(zip(
                               ('base', 'point', 'scalar'), declaration[9], shapes))],
                'definition': {'kind': 'formula', 'function': declaration[10]}}
    interface = {'format': 'zkc.language-interface/0', 'original': data[2].removeprefix('sha256:'),
                 'capture': '4' * 64, 'toolchain': '5' * 64, 'entry': 'fixture::Run',
                 'protocol': data[3], 'protocols': [protocol], 'relations': [relation] if relation else [],
                 'job': {'kind': 'run'}, 'setups': []}
    return data, interface, read(HERE / 'requests/schnorr-dsl.json')


def nested_fixture():
    data, interface, spec = scalar_fixture()
    protocol = interface['protocols'][0]
    base, point = protocol['inputs'][:2]
    empty = schema('unit', '6' * 64, None)
    inner = schema('record', '7' * 64, None)
    inner['leaves'] = base['schema']['leaves'] + point['schema']['leaves']
    inner['fields'] = [{'name': name, 'offset': index, 'public': public, 'placement': None, 'schema': shape}
                       for index, (name, public, shape) in enumerate([
                           ('base', True, base['schema']), ('point', False, point['schema']),
                           ('empty', False, empty)])]
    outer = schema('record', '8' * 64, None)
    outer['leaves'] = inner['leaves']
    outer['fields'] = [{'name': 'public_data', 'offset': 0, 'public': True,
                        'placement': None, 'schema': inner}]
    combined = {'name': 'statement', 'index': 0, 'native': [0, 1], 'type': 'record display',
                'schema': outer, 'placement': {'kind': 'data', 'roles': [0, 1]},
                'components': [{**item, 'path': [0, index]} for index, old in enumerate((base, point))
                               for item in old['components']]}
    protocol['inputs'] = [combined, protocol['inputs'][2]]
    protocol['inputs'][1]['index'] = 1
    for index, operand in enumerate(protocol['clauses'][0]['subject']['operands']):
        operand['port'] = 0 if index < 2 else 1
        operand['path'] = [0, index] if index < 2 else []
    spec['inputs']['base'] = spec['inputs']['key'] = 'statement'
    return data, interface, spec


class AssociationTests(unittest.TestCase):
    def setUp(self):
        self.data, self.interface, self.spec = scalar_fixture()

    def resolve(self, data=None, interface=None, spec=None):
        with tempfile.TemporaryDirectory() as directory:
            result = intent.resolve(spec if spec is not None else self.spec,
                                    data if data is not None else self.data,
                                    interface if interface is not None else self.interface,
                                    None, Path(directory))
            self.assertEqual(read(Path(directory) / 'relation.json'), result[1])
            return result

    def refuses(self, code, action=None):
        with self.assertRaises(Obligation) as raised:
            (action or self.resolve)()
        self.assertEqual(raised.exception.code, code)

    def test_actual_supported_requests_and_source_forms(self):
        for form in ('schnorr', 'schnorr-helpers', 'schnorr-reordered'):
            for simulation in (False, True):
                with self.subTest(form=form, simulation=simulation):
                    data, interface, spec = scalar_fixture(form)
                    validate(data, read(HERE / 'requests' / ('schnorr-simulation.json' if simulation else 'schnorr.json')))
                    if simulation:
                        spec['properties'] = ['honest-verifier-zero-knowledge']
                        spec['experiment'] = 'interactive.honest-verifier-view/0'
                    if not data[5]:
                        self.refuses('intent-clause', lambda: self.resolve(data, interface, spec))
                        continue
                    request, relation, metadata = self.resolve(data, interface, spec)
                    self.assertEqual(request['inputs'], ['base', 'key', None, None, 'service'])
                    self.assertEqual(relation['snapshot'], data)
                    self.assertEqual(metadata['relation'], data[5][0][1])

    def test_nested_operands_can_share_one_logical_port(self):
        data, interface, spec = nested_fixture()
        request, relation, _ = self.resolve(data, interface, spec)
        self.assertEqual(request['inputs'], ['base', 'key', None, None, 'service'])
        self.assertEqual(relation['snapshot'], data)
        selected = SourceAssociation(data, interface).select(
            interface['protocols'][0]['clauses'][0]['subject']['operands'][1])
        self.assertEqual(len(selected.ancestors), 2)
        self.assertFalse(selected.ancestors[-1][0]['fields'][1]['public'])
        self.assertEqual(selected.ancestors[-1][0]['fields'][2]['schema']['kind'], 'unit')

    def test_private_nested_path_is_not_external_ingress(self):
        data, interface, _ = nested_fixture()
        association = SourceAssociation(data, interface)
        selector = interface['protocols'][0]['clauses'][0]['subject']['operands'][1]
        self.assertEqual(association.select(selector).native, (1,))
        self.refuses('intent-selector-access', lambda: association.select(selector, external=True))

    def test_zero_storage_ordinary_field_remains_a_selection(self):
        data, interface, _ = nested_fixture()
        association = SourceAssociation(data, interface)
        selector = {'direction': 'input', 'port': 0, 'role': 'V', 'path': [0, 2]}
        selected = association.select(selector)
        self.assertEqual(selected.native, ())
        self.refuses('intent-layout', selected.scalar)
        self.refuses('intent-selector-empty', lambda: association.native_selectors(selector))

    def test_display_spellings_are_not_type_authority(self):
        self.interface['relations'][0]['inputs'][0]['schema']['type'] = 'different display'
        self.resolve()

    def test_schema_authority_is_complete(self):
        for field, value in (('identity', '0' * 64), ('generated', '0' * 64), ('sealed', True),
                             ('constructible', False), ('permissions', ['Drop'])):
            with self.subTest(field=field):
                interface = copy.deepcopy(self.interface)
                interface['relations'][0]['inputs'][0]['schema'][field] = value
                self.refuses('intent-relation-bindings', lambda: self.resolve(interface=interface))

    def test_wrong_source_identity(self):
        self.interface['original'] = '0' * 64
        self.refuses('intent-identity')

    def test_equal_but_noncanonical_source_hash_is_not_an_identity(self):
        self.interface['original'] = 'same text'
        self.data[2] = 'sha256:same text'
        self.refuses('intent-identity')

    def test_duplicate_logical_roles(self):
        self.interface['protocols'][0]['roles'] = ['P', 'P']
        self.refuses('intent-role')

    def test_exact_typed_static_arguments(self):
        self.interface['relations'][0]['static_arguments'] = [['group', 'other.group']]
        self.refuses('intent-relation-statics')

    def test_static_arguments_keep_type_and_order(self):
        statics = [['group', 'bls12-381.g1'], ['field', 'bls12-381.fr']]
        self.data[5][0][6] = copy.deepcopy(statics)
        self.interface['relations'][0]['static_arguments'] = copy.deepcopy(statics)
        self.resolve()
        self.interface['relations'][0]['static_arguments'].reverse()
        self.refuses('intent-relation-statics')

    def test_purpose_and_native_order_are_fixed(self):
        for edit in ('purpose', 'native'):
            with self.subTest(edit=edit):
                interface = copy.deepcopy(self.interface)
                formal = interface['relations'][0]['inputs'][0]
                formal[edit] = 'statement' if edit == 'purpose' else [1]
                self.refuses('intent-relation-formals' if edit == 'purpose' else 'intent-relation-layout',
                             lambda: self.resolve(interface=interface))

    def test_formula_symbol_is_the_actual_relation_link(self):
        self.interface['relations'][0]['definition']['function'] = self.data[3]
        self.refuses('intent-relation-body')

    def test_formula_helper_signature_is_exact(self):
        helper = next(row for row in self.data[7] if row[1] == self.data[5][0][10])
        helper[4][0] = copy.deepcopy(helper[4][2])
        self.refuses('intent-relation-body')

    def test_missing_retained_relation(self):
        self.data[5].clear()
        self.refuses('intent-relation-declaration')

    def test_duplicate_retained_relation(self):
        self.data[5].append(copy.deepcopy(self.data[5][0]))
        self.refuses('intent-relation-declaration')

    def test_opaque_relation_has_no_invented_meaning(self):
        self.interface['relations'][0]['definition'] = {'kind': 'opaque'}
        self.refuses('intent-relation-body')

    def test_reordered_source_selectors_cannot_match_by_type(self):
        selectors = self.data[8][0][1][0][2][1]
        selectors[:2] = selectors[1::-1]
        self.refuses('intent-clause-association')

    def test_consistently_swapped_target_still_disagrees_with_named_request(self):
        selectors = self.data[8][0][1][0][2][1]
        selectors[:2] = selectors[1::-1]
        operands = self.interface['protocols'][0]['clauses'][0]['subject']['operands']
        operands[:2] = operands[1::-1]
        self.refuses('intent-relation-bindings')

    def test_wrong_participant_copy(self):
        self.interface['protocols'][0]['clauses'][0]['subject']['operands'][0]['role'] = 'P'
        self.refuses('intent-clause-association')

    def test_nested_decision_uses_components_instead_of_logical_position(self):
        protocol = self.interface['protocols'][0]
        output = protocol['outputs'][0]
        ordinary = schema('record', '9' * 64, None)
        ordinary['leaves'] = ['bool']
        ordinary['fields'] = [
            {'name': 'empty', 'offset': 0, 'public': True, 'placement': None,
             'schema': schema('unit', '6' * 64, None)},
            {'name': 'accepted', 'offset': 0, 'public': True, 'placement': None, 'schema': output['schema']}]
        output['schema'] = ordinary
        for component in output['components']:
            component['path'] = [1]
        protocol['clauses'][0]['decision']['path'] = [1]
        self.resolve()

    def test_missing_clause_cannot_hide_behind_successful_selected_target(self):
        extra = copy.deepcopy(self.data[8][0][1][0])
        extra[1] = 'omitted'
        self.data[8][0][1].append(extra)
        self.refuses('intent-clause-coverage')

    def test_additional_input_clause_requires_its_own_fixed_goal(self):
        extra = copy.deepcopy(self.data[8][0][1][0])
        extra[0:2] = ['input', 'premise']
        extra[4] = None
        self.data[8][0][1].append(extra)
        logical = copy.deepcopy(self.interface['protocols'][0]['clauses'][0])
        logical.update(name='premise', kind='input', decision=None)
        self.interface['protocols'][0]['clauses'].append(logical)
        self.refuses('intent-clause-coverage')

    def test_independent_registered_input_coverage(self):
        for binding in ('base', 'key', 'service'):
            with self.subTest(binding=binding):
                spec = copy.deepcopy(self.spec)
                del spec['inputs'][binding]
                self.refuses('intent-inputs', lambda: self.resolve(spec=spec))

    def test_unregistered_meaning_and_property_are_refused(self):
        self.spec['target']['relation'] = 'arbitrary-relation/0'
        self.refuses('intent-relation-adapter')
        self.spec = scalar_fixture()[2]
        self.spec['properties'] = ['arbitrary-property/0']
        self.refuses('property-unregistered')

    def test_duplicate_binding_retains_existing_diagnostic(self):
        self.spec['inputs']['key'] = 'base'
        self.refuses('intent-inputs')

    def test_wrong_native_component_or_service_owner(self):
        self.interface['protocols'][0]['inputs'][2]['components'][0]['role'] = 1
        self.refuses('intent-placement')
        self.interface = scalar_fixture()[1]
        self.interface['protocols'][0]['services'][1]['owner'] = 'P'
        self.refuses('intent-service')

    def test_component_overlap_and_missing_coverage(self):
        for mutation in ('overlap', 'missing', 'duplicate'):
            with self.subTest(mutation=mutation):
                interface = copy.deepcopy(self.interface)
                ports = interface['protocols'][0]['inputs']
                if mutation == 'overlap':
                    ports[1]['native'] = [0]
                elif mutation == 'missing':
                    ports[1]['components'].clear()
                else:
                    ports[1]['components'].append(copy.deepcopy(ports[1]['components'][0]))
                self.refuses('intent-layout', lambda: self.resolve(interface=interface))

    def test_invalid_paths_and_product_identity_refuse(self):
        association = SourceAssociation(self.data, self.interface)
        for selector in ({'direction': 'input', 'port': 999, 'role': 'V', 'path': []},
                         {'direction': 'input', 'port': 0, 'role': 'V', 'path': [0]}):
            with self.subTest(selector=selector):
                self.refuses('intent-selector', lambda: association.select(selector))
        data, interface, _ = nested_fixture()
        combined = interface['protocols'][0]['inputs'][0]
        combined['placement'] = {'kind': 'product', 'instance': 'wrong', 'arguments': [0, 1],
                                 'fields': [{'kind': 'data', 'roles': [0, 1]}]}
        association = SourceAssociation(data, interface)
        self.refuses('intent-placement', lambda: association.select(
            interface['protocols'][0]['clauses'][0]['subject']['operands'][0]))

    def test_nested_execution_requires_ancestry_and_capture_contract(self):
        for fixture in ('application', 'repeat', 'repeat-nested', 'repeat-service-wrapper'):
            with self.subTest(fixture=fixture):
                nested = read(LEAN / 'bridges/structured/fixtures' / (fixture + '.json'))
                association = SourceAssociation(self.data, self.interface)
                association.root = next(row for row in nested[7] if row[1] == nested[3])
                self.refuses('intent-occurrence-context', lambda: association.require_scalar_root(
                    self.interface['protocols'][0]['clauses'][0]))

    def test_changed_formula_is_retained_for_independent_lean_checking(self):
        helper = next(row for row in self.data[7] if row[1] == self.data[5][0][10])
        helper[9] = ['block', [[['bool.constant', True], [], [['apply', 'bool', []]], [], '']], ['return', [0]]]
        _, relation, _ = self.resolve()
        self.assertEqual(relation['snapshot'], self.data)
        self.assertEqual(set(relation), {'snapshot', 'helper'})

    def test_association_does_not_reuse_mutated_caller_objects(self):
        association = SourceAssociation(self.data, self.interface)
        self.data[7][0][8][0] = 'mutated::Owner'
        self.interface['capture'] = '0' * 64
        self.assertEqual(association.root[8][0], 'schnorr::Schnorr')
        self.assertEqual(association.interface['capture'], '4' * 64)


class StructuralSelectionTests(unittest.TestCase):
    """Ordinary structural products use the owning interface's intersection rule."""

    def fixture(self, kind='tuple', empty_role=1):
        _, interface, _ = scalar_fixture()
        port = interface['protocols'][0]['inputs'][0]
        group = copy.deepcopy(port['schema'])
        empty = schema('unit', '6' * 64, None)
        shape = schema(kind, '7' * 64, None)
        if kind == 'array':
            shape['element'] = empty
            children = [empty]
            placements = [{'kind': 'data', 'roles': [empty_role]}]
            components = []
        else:
            children = [group, empty]
            shape['leaves'] = group['leaves']
            shape['fields'] = [
                {'name': str(i), 'offset': i, 'public': True, 'placement': None, 'schema': child}
                for i, child in enumerate(children)]
            placements = [{'kind': 'data', 'roles': [1]},
                          {'kind': 'data', 'roles': [empty_role]}]
            components = [{'path': [0], 'leaf': 0, 'role': 1, 'facet': 'data', 'native': 0}]
        port.update(schema=shape, native=[0] if components else [], components=components,
                    placement={'kind': 'product', 'instance': shape['identity'],
                               'arguments': sorted({1, empty_role}), 'fields': placements})
        selector = {'direction': 'input', 'port': 0, 'role': 'V', 'path': []}
        return interface, selector

    def test_structural_tuple_available_internally_and_externally(self):
        interface, selector = self.fixture()
        for external in (False, True):
            with self.subTest(external=external):
                selected = LogicalInterface(interface).select(selector, external=external)
                self.assertEqual(selected.native, (0,))
                # Neutral association does not enlarge the registered scalar ABI.
                with self.assertRaises(Obligation) as raised:
                    selected.scalar()
                self.assertEqual(raised.exception.code, 'intent-layout')

    def test_empty_child_participates_in_intersection(self):
        interface, selector = self.fixture(empty_role=0)
        with self.assertRaises(Obligation) as raised:
            LogicalInterface(interface).select(selector)
        self.assertEqual(raised.exception.code, 'intent-selector-role')

    def test_zero_array_uses_element_template(self):
        interface, selector = self.fixture(kind='array')
        selected = LogicalInterface(interface).select(selector, external=True)
        self.assertEqual(selected.native, ())
        with self.assertRaises(Obligation):
            selected.scalar()
        interface, selector = self.fixture(kind='array', empty_role=0)
        with self.assertRaises(Obligation) as raised:
            LogicalInterface(interface).select(selector)
        self.assertEqual(raised.exception.code, 'intent-selector-role')

    def test_zero_array_cannot_hide_logical_element(self):
        interface, selector = self.fixture(kind='array')
        port = interface['protocols'][0]['inputs'][0]
        element = port['schema']['element']
        element['kind'] = 'logical_record'
        port['placement']['fields'][0] = {
            'kind': 'product', 'instance': element['identity'], 'arguments': [1], 'fields': []}
        with self.assertRaises(Obligation) as raised:
            LogicalInterface(interface).select(selector)
        self.assertEqual(raised.exception.code, 'intent-selector-role')

    def test_structural_product_cannot_claim_nominal_logical_access(self):
        interface, selector = self.fixture()
        interface['protocols'][0]['inputs'][0]['schema']['kind'] = 'logical_record'
        with self.assertRaises(Obligation) as raised:
            LogicalInterface(interface).select(selector)
        self.assertEqual(raised.exception.code, 'intent-selector-role')


class RecursiveInterfaceTests(unittest.TestCase):
    def setUp(self):
        self.interface = read(ROOT / 'compiler/test/fixtures/language-interface/recursive-records.json')
        self.association = LogicalInterface(self.interface)

    def test_complete_nested_logical_metadata_is_retained(self):
        retained = self.association.protocol['inputs'][0]
        self.assertEqual(retained, self.interface['protocols'][0]['inputs'][0])
        empty = retained['schema']['fields'][2]
        self.assertFalse(empty['public'])
        self.assertEqual(empty['schema']['fields'], [])
        self.assertEqual(empty['schema']['element']['kind'], 'logical_record')
        self.assertEqual(len(retained['placement']['fields'][2]['fields']), 1)

    def test_ordinary_child_uses_its_own_role(self):
        selector = {'direction': 'input', 'port': 0, 'role': self.association.roles[0], 'path': [1]}
        self.assertEqual(self.association.select(selector, external=True).scalar(), 4)
        selector['role'] = self.association.roles[1]
        with self.assertRaises(Obligation) as raised:
            self.association.select(selector)
        self.assertEqual(raised.exception.code, 'intent-selector-role')

    def test_anchor_uses_exact_path_and_preserves_receiver_copies(self):
        selector = {'direction': 'input', 'port': 0, 'role': None, 'path': [0, 0]}
        selected = self.association.select(selector)
        self.assertEqual(selected.native, (1,))
        self.assertEqual([component['role'] for component in selected.components], [0, 1])
        with self.assertRaises(Obligation):
            self.association.select(selector, external=True)

    def test_whole_logical_product_is_not_ordinary_data(self):
        selector = {'direction': 'input', 'port': 0, 'role': self.association.roles[0], 'path': []}
        with self.assertRaises(Obligation) as raised:
            self.association.select(selector)
        self.assertEqual(raised.exception.code, 'intent-selector-role')

    def test_private_zero_array_is_not_an_invented_element(self):
        selector = {'direction': 'input', 'port': 0, 'role': self.association.roles[0], 'path': [2, 0]}
        with self.assertRaises(Obligation) as raised:
            self.association.select(selector)
        self.assertEqual(raised.exception.code, 'intent-selector')

    def test_nested_custody_is_preserved_and_external_projection_refuses(self):
        fixture = read(ROOT / 'compiler/test/fixtures/language-interface/custody-records.json')
        association = LogicalInterface(fixture)
        retained = association.protocol['inputs'][0]
        self.assertEqual(retained['schema']['custody'], 2)
        self.assertEqual(retained['schema']['fields'][0]['schema']['custody'], 1)
        selector = {'direction': 'input', 'port': 0, 'role': association.roles[1], 'path': [0]}
        with self.assertRaises(Obligation) as raised:
            association.select(selector, external=True)
        self.assertEqual(raised.exception.code, 'intent-selector-access')


if __name__ == '__main__':
    unittest.main()
