"""Associate retained logical selectors with the same Structured source unit.

This is tested boundary tooling, not source elaboration or proof admission. The
native source/interface comparison still owns schema/component authenticity and
lexical access. Keep whole ports (including private and empty children) intact;
only project an ABI when an existing retained selector actually requests it.
No mathematical interpretation, companion lookup key or assurance state is
inferred here. The scalar caller supplies its registered meaning separately.
"""
import copy
from dataclasses import dataclass
import re

from bridges.common import interface as language_interface
from bridges.common.schema import interpreted_type
from request_support import require
from structured import entry


def schema_identity(value):
    """Compare complete authority metadata, excluding only display spellings."""
    if isinstance(value, dict):
        return {key: schema_identity(child) for key, child in value.items() if key != 'type'}
    if isinstance(value, list):
        return [schema_identity(child) for child in value]
    return value


def ordinary_at(schema, placement, role):
    """Structural availability is an intersection, including empty children.

    Product arguments record participants, not whole-value access. A zero
    array keeps its element template even though it has no stored components.
    Nominal logical products and oracle facets are not ordinary selections.
    """
    if 'Copy' not in schema['permissions']:
        return False
    if placement['kind'] == 'data':
        return role in placement['roles']
    if placement['kind'] != 'product' or schema['kind'] not in ('tuple', 'array'):
        return False
    children = ([schema['element']] if schema['kind'] == 'array' else
                [field['schema'] for field in schema['fields']])
    return (placement['instance'] == schema['identity'] and bool(children) and
            len(children) == len(placement['fields']) and
            all(child is not None and ordinary_at(child, where, role)
                for child, where in zip(children, placement['fields'])))


@dataclass(frozen=True)
class Selection:
    selector: dict
    port: dict
    schema: dict
    placement: dict
    ancestors: tuple
    components: tuple

    @property
    def native(self):
        """ABI order comes from components, never offsets or a role union."""
        return tuple(dict.fromkeys(component['native'] for component in self.components))

    def scalar(self):
        require(self.placement['kind'] == 'data' and self.schema['custody'] == 0 and
                len(self.native) == 1 and len(self.components) == 1 and
                self.components[0]['facet'] == 'data',
                'intent-layout', 'The registered scalar meaning requires one ordinary data component')
        return self.native[0]


class LogicalInterface:
    """Read existing paths without converting a logical product into data.

    Internal selection preserves private/custody ancestors: an authenticated
    source clause can observe Copy payloads without granting external ingress.
    `external=True` additionally enforces public, unsealed, custody-free paths;
    it does not admit bytes, construct a handle or authorize resource use.
    """

    def __init__(self, interface):
        self.interface = copy.deepcopy(language_interface.decode(interface))
        self.protocol = language_interface.selected_protocol(self.interface)
        self.roles = self.protocol['roles']
        require(len(self.roles) == len(set(self.roles)), 'intent-role', 'Ambiguous protocol role names')

    def select(self, selector, *, external=False):
        language_interface.selector(selector, 'intent.selector')
        direction = selector['direction']
        ports = self.protocol['inputs' if direction == 'input' else 'outputs']
        require(selector['port'] < len(ports), 'intent-selector', 'Selector names no logical port')
        port = copy.deepcopy(ports[selector['port']])
        schema, placement, ancestors = port['schema'], port['placement'], []
        for ordinal in selector['path']:
            require(schema['kind'] in ('tuple', 'array', 'record', 'logical_record') and
                    ordinal < len(schema['fields']),
                    'intent-selector', 'Selector path names no transparent declared field')
            field = schema['fields'][ordinal]
            if external:
                require(schema['custody'] == 0 and not schema['sealed'] and field['public'],
                        'intent-selector-access', 'External projection crosses custody, sealing or privacy')
            ancestors.append((copy.deepcopy(schema), copy.deepcopy(placement), ordinal))
            if placement['kind'] == 'product':
                position = 0 if schema['kind'] == 'array' else ordinal
                require(placement['instance'] == schema['identity'] and
                        position < len(placement['fields']),
                        'intent-placement', 'Product placement does not describe the selected schema')
                placement = placement['fields'][position]
            else:
                require(placement['kind'] == 'data', 'intent-placement', 'A handle has no field projection')
            schema = field['schema']
        if external:
            require(schema['custody'] == 0 and not schema['sealed'],
                    'intent-selector-access', 'External selection requires an ordinary accessible value')
        path, role = selector['path'], selector['role']
        if role is None:
            require(not external and schema['kind'] == 'oracle' and placement['kind'] == 'oracle',
                    'intent-selector-role', 'Only a singleton oracle has an implicit anchor selector')
            facets = ('oracle_anchor',)
            selected_role = None
        else:
            require(role in self.roles, 'intent-selector-role', 'Selector names no declared participant')
            selected_role = self.roles.index(role)
            require(ordinary_at(schema, placement, selected_role),
                    'intent-selector-role', 'Selection is not ordinary data at that exact participant')
            facets = ('data',)
        components = tuple(copy.deepcopy(component) for component in port['components']
                           if component['path'][:len(path)] == path and component['facet'] in facets and
                           (selected_role is None or component['role'] == selected_role))
        # Empty ordinary values remain selections; no fabricated scalar is made.
        return Selection(copy.deepcopy(selector), port, copy.deepcopy(schema),
                         copy.deepcopy(placement), tuple(ancestors), components)


class SourceAssociation(LogicalInterface):
    """Join logical metadata to one exact retained root, clause and declaration.

    Structured admission remains Lean-owned. This layer deliberately accepts no
    user-supplied occurrence/capture summary. The scalar client below supports
    the root environment only; source-instance/call/repeat association requires
    the owning source-correspondence contract and checked placement laws.
    """

    def __init__(self, data, interface):
        super().__init__(interface)
        self.snapshot = copy.deepcopy(data)
        self.root = entry(self.snapshot)
        require(re.fullmatch(r'sha256:[0-9a-f]{64}', self.snapshot[2]) is not None and
                self.snapshot[2] == 'sha256:' + self.interface['original'] and
                self.snapshot[3] == self.interface['protocol'],
                'intent-identity', 'Interface and snapshot must select the same original and protocol')
        self.native_roles, self.input_scopes, self.output_scopes = self.root[6][1:]
        require(len(self.roles) == len(self.native_roles) and
                len(set(self.native_roles)) == len(self.native_roles) and
                len(self.input_scopes) == len(self.root[4]) and
                len(self.output_scopes) == len(self.root[5]),
                'intent-role', 'Source and native rosters disagree')
        self._check_ports()

    def _check_ports(self):
        for direction, types, scopes in (('inputs', self.root[4], self.input_scopes),
                                         ('outputs', self.root[5], self.output_scopes)):
            occupied = set()
            for port in self.protocol[direction]:
                require(len(set(port['native'])) == len(port['native']) and
                        not occupied.intersection(port['native']),
                        'intent-layout', 'Logical ports overlap in the native signature')
                occupied.update(port['native'])
                require(all(index < len(types) for index in port['native']),
                        'intent-layout', 'Port references a missing native coordinate')
                require(set(port['native']) == {item['native'] for item in port['components']},
                        'intent-layout', 'Port native coordinates differ from its component inventory')
                keys = set()
                for component in port['components']:
                    key = (tuple(component['path']), component['leaf'], component['role'], component['facet'])
                    require(key not in keys, 'intent-layout', 'Duplicate logical component')
                    keys.add(key)
                    require(component['role'] < len(self.roles) and
                            self.native_roles[component['role']] in scopes[component['native']],
                            'intent-placement', 'Component is absent at its claimed native participant')
            if direction == 'inputs':
                for service in self.protocol['services']:
                    index = service['native']
                    require(index < len(types) and index not in occupied and service['owner'] in self.roles,
                            'intent-service', 'Service does not select a distinct native input')
                    require(types[index] == ['service', service['contract']] and
                            self.native_roles[self.roles.index(service['owner'])] in scopes[index],
                            'intent-service', 'Service contract or owner differs from the native input')
                    occupied.add(index)
            require(occupied == set(range(len(types))), 'intent-layout',
                    'Logical ports and services must cover the complete native signature')

    def native_selectors(self, selector):
        selected = self.select(selector)
        require(selected.native, 'intent-selector-empty',
                'Structured contract selectors cannot encode a zero-storage logical argument')
        if selector['role'] is None:
            require(len(selected.native) == 1, 'intent-selector-role', 'Anchor coordinates disagree')
            return [['anchor', selector['direction'], selected.native[0]]]
        role = self.native_roles[self.roles.index(selector['role'])]
        return [[selector['direction'], index, role] for index in selected.native]

    def application(self, application):
        declarations = [row for row in self.snapshot[5] if row[1] == application['relation']]
        logical = [row for row in self.interface['relations'] if row['symbol'] == application['relation']]
        require(len(declarations) == len(logical) == 1, 'intent-relation-declaration',
                'Relation must resolve uniquely in the same retained declaration table')
        declaration, relation = declarations[0], logical[0]
        formals = relation['inputs']
        require(relation['static_arguments'] == declaration[6], 'intent-relation-statics',
                'Ordered typed static arguments differ from the retained relation declaration')
        require(len(formals) == len(application['operands']), 'intent-relation-formals',
                'Every logical relation formal requires one ordered authored operand')
        layout = [index for formal in formals for index in formal['native']]
        require(layout == list(range(len(declaration[7]))), 'intent-relation-layout',
                'Relation formals must cover the exact declaration ABI in order')
        purposes = [formal['purpose'] for formal in formals for _ in formal['native']]
        require(purposes == declaration[9], 'intent-relation-formals',
                'Relation purposes differ from the retained declaration')
        selectors = []
        for formal, operand in zip(formals, application['operands']):
            selected = self.select(operand)
            require(schema_identity(selected.schema) == schema_identity(formal['schema']),
                    'intent-relation-bindings', 'Selected schema differs from the exact logical relation formal')
            types = self.root[4 if operand['direction'] == 'input' else 5]
            require([types[index] for index in selected.native] ==
                    [declaration[7][index] for index in formal['native']],
                    'intent-relation-bindings', 'Selected components differ from the ordered relation ABI')
            selectors.extend(self.native_selectors(operand))
        definition = relation['definition']
        if definition['kind'] == 'formula':
            require(declaration[3] == 'zkc.language.formula/0' and
                    declaration[10] == definition['function'],
                    'intent-relation-body', 'Formula link differs from the retained relation declaration')
            helpers = [row for row in self.snapshot[7] if row[0] == 'function' and
                       row[1] == definition['function']]
            require(len(helpers) == 1 and helpers[0][2] == 'math' and
                    helpers[0][4:6] == declaration[7:9],
                    'intent-relation-body', 'Linked formula helper must have the exact relation ABI')
        else:
            require(False, 'intent-relation-body',
                    'This connector has no registered meaning adapter for an opaque or asset relation')
        return [relation['symbol'], selectors], copy.deepcopy(relation)

    def clause(self, name):
        """Check all retained clause coverage before selecting one by label."""
        contracts = [row for row in self.snapshot[8] if row[0] == self.snapshot[3]]
        require(len(contracts) == 1, 'intent-clause-coverage', 'Root contract is missing or ambiguous')
        clauses = self.protocol['clauses']
        require(len(clauses) == len(contracts[0][1]) and
                len({clause['name'] for clause in clauses}) == len(clauses),
                'intent-clause-coverage', 'Interface clauses must cover the complete retained root contract')
        associations = []
        for clause, retained in zip(clauses, contracts[0][1]):
            subject, relation = self.application(clause['subject'])
            residual = self.application(clause['residual'])[0] if clause['residual'] is not None else None
            decision = None
            if clause['decision'] is not None:
                decisions = self.native_selectors(clause['decision'])
                require(len(decisions) == 1, 'intent-decision', 'Decision must select exactly one native value')
                decision = decisions[0]
            require([clause['kind'], clause['name'], subject, residual, decision] == retained,
                    'intent-clause-association', 'Ordered clause, operands or decision differ from the retained source')
            associations.append((clause, relation))
        matches = [item for item in associations if item[0]['name'] == name]
        require(len(matches) == 1, 'intent-clause', 'Select one authored clause by its exact label')
        return copy.deepcopy(matches[0])

    def require_scalar_root(self, clause):
        require(len(self.protocol['clauses']) == 1 and clause['kind'] == 'target' and
                clause['residual'] is None,
                'intent-clause-coverage', 'The scalar adapter covers one target; additional clauses need fixed goals')

        def inspect(value):
            if not isinstance(value, list):
                return
            if value and isinstance(value[0], str):
                require(value[0] not in ('protocol_apply', 'protocol_repeat', 'local_call'),
                        'intent-occurrence-context',
                        'Nested calls/repeats need checked ordered ancestry and capture/environment association')
            for child in value:
                inspect(child)
        inspect(self.root[9])

    def scalar_type(self, selected):
        index = selected.scalar()
        types = self.root[4 if selected.selector['direction'] == 'input' else 5]
        return interpreted_type(types[index], payload=True)
