"""Associate named DSL intent and propose a checked registered relation adapter.

The native interface is a tested name/selector boundary, not a proof. The relation
body is exported and admitted independently; a matching name never proves it.
Port types are compared by schema kind and identity and by the typed native
leaf of the structured export; display `type` strings are never compared.
"""
import copy
import hashlib
import json

from structured import entry, profile
from bridges.structured.snapshot import render, text
from bridges.common.intent_association import SourceAssociation
from bridges.common.schema import interpreted_type
from request_support import require
from verify import validate, VERSION


def resolve(spec, data, interface, compiler, output):
    require(isinstance(spec, dict) and set(spec) == {
        'format', 'contract', 'properties', 'experiment', 'role', 'inputs', 'wiring', 'target'},
        'spec-shape', 'Expected the named verification-spec fields')
    require(spec['format'] == 'zkc.verification-spec/0', 'spec-version', 'Unsupported verification specification')
    association = SourceAssociation(data, interface)
    interface, protocol = association.interface, association.protocol
    roles = protocol['roles']
    require(isinstance(spec['role'], str) and spec['role'] in roles,
            'intent-role', 'Select a declared verifier role by name')
    target = spec['target']
    require(isinstance(target, dict) and set(target) == {'clause', 'relation'} and
            target['relation'] == 'discrete-log/0' and spec['contract'] == 'schnorr.verifier/0',
            'intent-relation-adapter', 'No registered meaning adapter for this relation and contract')
    clause, relation_declaration = association.clause(target['clause'])
    association.require_scalar_root(clause)
    operands = clause['subject']['operands']
    require(len(operands) == 3 and [formal['purpose'] for formal in relation_declaration['inputs']] ==
            ['parameter', 'statement', 'witness'],
            'intent-relation-formals', 'Discrete-log expects ordered parameter, statement and witness formals')
    request = {k: copy.deepcopy(spec[k]) for k in ('contract', 'properties', 'experiment', 'wiring')}
    request.update(format=VERSION, role=roles.index(spec['role']), inputs=[None] * len(entry(data)[4]))
    require(isinstance(request['wiring'], dict) and request['wiring'].get('prover') in roles,
            'intent-prover', 'Select a declared prover role by name')
    request['wiring']['prover'] = roles.index(request['wiring']['prover'])
    require(isinstance(spec['inputs'], dict) and all(isinstance(v, str) for v in spec['inputs'].values()),
            'intent-inputs', 'Map contract inputs to named logical ports or services')
    from registry import CONTRACTS
    require(set(spec['inputs']) == set(CONTRACTS[spec['contract']].inputs),
            'intent-inputs', 'Bindings must cover the independently registered semantic inputs exactly')
    semantic_selectors = dict(zip(('base', 'key'), operands[:2]))
    ports = {}
    for port in protocol['inputs']:
        require(port['name'] not in ports, 'intent-inputs', 'Ambiguous input name')
        ports[port['name']] = (port, False)
    for service in protocol['services']:
        require(service['name'] not in ports, 'intent-inputs', 'Ambiguous input/service name')
        ports[service['name']] = (service, True)
    for binding, name in spec['inputs'].items():
        require(name in ports, 'intent-inputs', f'Unknown input or service: {name}')
        port, service = ports[name]
        if service:
            native = port['native']
        else:
            selector = semantic_selectors.get(binding)
            if selector is None or selector['direction'] != 'input' or selector['port'] != port['index']:
                selector = {'direction': 'input', 'port': port['index'], 'role': spec['role'], 'path': []}
            native = association.select(selector).scalar()
        require(request['inputs'][native] is None, 'intent-inputs', 'Two bindings select the same native leaf')
        request['inputs'][native] = binding
    validate(data, request)
    require(clause['decision'] is not None, 'intent-decision', 'The target needs an actual decision selector')
    decision = association.select(clause['decision'])
    require(clause['decision']['direction'] == 'output' and clause['decision']['role'] == spec['role'] and
            decision.scalar() == 0 and decision.schema['kind'] == 'boolean' and
            association.scalar_type(decision) == ['bool'],
            'intent-decision', 'The target must use the actual Boolean verifier output')
    for binding, selector in zip(('base', 'key'), operands[:2]):
        selected = association.select(selector)
        require(selector['direction'] == 'input' and selector['role'] == spec['role'] and
                request['inputs'][selected.scalar()] == binding,
                'intent-relation-bindings', f'Target {binding} must select the verified role-local input')
    witness = association.select(operands[2])
    require(operands[2]['direction'] == 'input' and operands[2]['role'] == roles[request['wiring']['prover']] and
            witness.schema['kind'] == 'field' and
            association.scalar_type(witness) == ['field', request['wiring']['fieldDomain']],
            'intent-relation-bindings', 'Witness field differs from the requested scalar field')
    definition = relation_declaration['definition']
    require(definition.get('kind') == 'formula', 'intent-relation-body', 'An opaque target needs its own proved adapter')
    # Select the retained named formula from this same Structured unit. There is
    # no relation-only Common export or second reader.
    relation = {'snapshot': copy.deepcopy(data), 'helper': definition['function']}
    validate_relation(relation, request)
    (output / 'relation.json').write_text(json.dumps(relation, indent=2) + '\n')
    return request, relation, {'clause': target['clause'], 'relation': clause['subject']['relation'],
        'interface_sha256': hashlib.sha256(json.dumps(interface, sort_keys=True).encode()).hexdigest(),
        'binding_scope': 'tested root logical selectors and exact retained declaration/ABI association'}


def validate_relation(data, request):
    require(isinstance(data, dict) and set(data) == {'snapshot', 'helper'},
            'intent-relation-profile', 'Select a named formula in the same Structured unit')
    render(data['snapshot'], 'RelationShape')
    w = request['wiring']
    profile(data['snapshot'], w['fieldDomain'], w['groupDomain'])
    matches = [d for d in data['snapshot'][7] if d[0] == 'function' and d[1] == data['helper']]
    require(len(matches) == 1, 'intent-relation-profile', 'Formula helper is missing or ambiguous')
    helper = matches[0]
    require(helper[2] == 'math' and [interpreted_type(value) for value in helper[4]] == [['group', w['groupDomain']],
            ['group', w['groupDomain']], ['field', w['fieldDomain']]] and [interpreted_type(value) for value in helper[5]] == [['bool']],
            'intent-relation-profile', 'Expected the actual scalar group predicate signature')
    return helper


def relation_candidate(data, request):
    validate_relation(data, request)
    return data


def helper_term(data, request):
    from bridges.structured.snapshot import seq, ty
    helper = validate_relation(data, request)
    return '⟨' + ', '.join([text(helper[1]), '.math', seq(helper[4], ty), seq(helper[5], ty)]) + '⟩'


def render_relation(data, request, proposal):
    from verify import audit
    validate_relation(data, request)
    helper = helper_term(proposal, request)
    return f'''
namespace GeneratedRelation
open Zkc.Source Zkc.Source.Structured
noncomputable section

def helper : Helper := {helper}
theorem helper_present : helper ∈ RelationCandidateInputs.program.payload.definitions.map (·.helper) := by
  decide +kernel
variable {{F G : Type}} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def inputs (base key : G) (secret : F) : Values (assignment F G) helper.inputs :=
  .cons base (.cons key (.cons secret .nil))

/-- The named helper runs in the actual admitted Structured table. -/
theorem corresponds (base key : G) (secret : F) :
    invoke (RelationCandidateInputs.program.payload.tables F G).closed helper (inputs base key secret) =
      PIR.Process.done (.cons (decide (key = secret • base)) .nil) := by
  rfl
end
end GeneratedRelation
''' + audit('GeneratedRelation', ['helper_present', 'corresponds'], 'RELATION-KERNEL-PASS')


def relation_subject(data, request):
    from verify import audit
    helper = helper_term(data, request)
    return f'''
namespace ExpectedRelation
open Zkc.Source Zkc.Source.Structured
noncomputable section

theorem snapshot_eq : RelationExpectedData.snapshot = RelationCandidateData.snapshot := by kernel_rfl
/-- The request's authored relation and verifier have the same source unit. -/
theorem same_source : RelationExpectedData.snapshot = ExpectedData.snapshot := by kernel_rfl

def helper : Helper := {helper}
theorem helper_present : helper ∈ RelationExpectedInputs.program.payload.definitions.map (·.helper) := by
  decide +kernel
variable {{F G : Type}} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

theorem approvedRelation (base key : G) (secret : F) :
    invoke (RelationExpectedInputs.program.payload.tables F G).closed helper
      (.cons base (.cons key (.cons secret .nil))) =
        PIR.Process.done (.cons (decide (key = secret • base)) .nil) :=
  GeneratedRelation.corresponds base key secret

/-- Two accepting actual verifier executions yield a witness for the actual
retained authored formula. Native selector resolution remains a tested edge. -/
theorem target_special_soundness (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : (Zkc.Protocols.Schnorr.Common.run ExpectedRequest.expectedVerifier
      base key service prover first).outcome = .returned (some true))
    (acceptSecond : (Zkc.Protocols.Schnorr.Common.run ExpectedRequest.expectedVerifier
      base key service prover second).outcome = .returned (some true)) :
    invoke (RelationExpectedInputs.program.payload.tables F G).closed helper
      (.cons base (.cons key (.cons
        ((prover.response first - prover.response second) / (first - second)) .nil))) =
      PIR.Process.done (.cons true .nil) := by
  rw [approvedRelation]
  have opening := ExpectedRequest.approvedContract.special_soundness
    base key service prover first second distinct acceptFirst acceptSecond
  simp only [opening, decide_true]
end
end ExpectedRelation
''' + audit('ExpectedRelation', ['snapshot_eq', 'same_source', 'helper_present', 'approvedRelation',
                                'target_special_soundness'], 'RELATION-BOUNDARY-PASS')
