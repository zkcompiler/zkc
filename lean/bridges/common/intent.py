"""Resolve named DSL intent and propose a checked scalar relation adapter.

The native interface is a tested name/selector boundary, not a proof. The relation
body is exported and admitted independently; a matching name never proves it.
"""
import copy
import hashlib
import json

from structured import entry, profile
from bridges.structured.snapshot import render, text
from request_support import require
from verify import validate, VERSION


def resolve(spec, data, interface, compiler, output):
    require(isinstance(spec, dict) and set(spec) == {
        'format', 'contract', 'properties', 'experiment', 'role', 'inputs', 'wiring', 'target'},
        'spec-shape', 'Expected the named verification-spec fields')
    require(spec['format'] == 'zkc.verification-spec/0', 'spec-version', 'Unsupported verification specification')
    require(interface.get('format') == 'zkc.language-interface/0' and
            data[2] == 'sha256:' + interface['original'] and data[3] == interface['protocol'],
            'intent-identity', 'Interface and program export must describe the same source and selected protocol')
    protocols = [p for p in interface['protocols'] if p['symbol'] == data[3]]
    require(len(protocols) == 1, 'intent-protocol', 'The selected protocol must occur exactly once')
    protocol = protocols[0]
    roles = protocol['roles']
    require(isinstance(spec['role'], str) and spec['role'] in roles,
            'intent-role', 'Select a declared verifier role by name')
    request = {k: copy.deepcopy(spec[k]) for k in ('contract', 'properties', 'experiment', 'wiring')}
    request.update(format=VERSION, role=roles.index(spec['role']), inputs=[None] * len(entry(data)[4]))
    require(isinstance(request['wiring'], dict) and request['wiring'].get('prover') in roles,
            'intent-prover', 'Select a declared prover role by name')
    request['wiring']['prover'] = roles.index(request['wiring']['prover'])
    require(isinstance(spec['inputs'], dict) and all(isinstance(v, str) for v in spec['inputs'].values()),
            'intent-inputs', 'Map contract inputs to named scalar ports or services')
    ports = {}
    for port in protocol['inputs']:
        require(port['name'] not in ports, 'intent-inputs', 'Ambiguous input name')
        ports[port['name']] = (port, port['native'])
    for service in protocol['services']:
        require(service['name'] not in ports, 'intent-inputs', 'Ambiguous input/service name')
        ports[service['name']] = (service, [service['native']])
    for binding, name in spec['inputs'].items():
        require(name in ports, 'intent-inputs', f'Unknown input or service: {name}')
        _, native = ports[name]
        require(len(native) == 1 and type(native[0]) is int and 0 <= native[0] < len(entry(data)[4]),
                'intent-layout', 'This profile requires one scalar native leaf per binding')
        require(request['inputs'][native[0]] is None, 'intent-inputs', 'Two bindings select the same native leaf')
        request['inputs'][native[0]] = binding
    validate(data, request)
    target = spec['target']
    require(isinstance(target, dict) and set(target) == {'clause', 'relation'} and
            target['relation'] == 'discrete-log/0' and request['contract'] == 'schnorr.verifier/0',
            'intent-relation-adapter', 'This relation adapter connects a discrete-log target to Schnorr')
    clauses = [c for c in protocol['clauses'] if c['name'] == target['clause']]
    require(len(clauses) == 1 and clauses[0]['kind'] == 'target' and clauses[0]['residual'] is None,
            'intent-clause', 'Select one authored target clause')
    clause = clauses[0]
    outputs = protocol['outputs']
    decision = clause['decision']
    require(decision == {'direction': 'output', 'port': 0, 'role': spec['role'], 'path': []}
            and len(outputs) == 1 and outputs[0]['native'] == [0] and outputs[0]['type'] == 'bool',
            'intent-decision', 'The target must use the actual Boolean verifier output')
    operands = clause['subject']['operands']
    require(len(operands) == 3, 'intent-relation-bindings', 'Discrete-log expects base, key and witness')
    for binding, selector in zip(('base', 'key'), operands[:2]):
        port, _ = ports[spec['inputs'][binding]]
        require(selector == {'direction': 'input', 'port': port['index'], 'role': spec['role'], 'path': []},
                'intent-relation-bindings', f'Target {binding} must select the verified role-local input')
    witness = operands[2]
    require(witness.get('direction') == 'input' and witness.get('path') == [] and
            witness.get('role') == roles[request['wiring']['prover']] and
            type(witness.get('port')) is int and 0 <= witness['port'] < len(protocol['inputs']),
            'intent-relation-bindings', 'Select a scalar prover witness input')
    witness_port = protocol['inputs'][witness['port']]
    require(witness_port['type'] == 'field<' + request['wiring']['fieldDomain'] + '>',
            'intent-relation-bindings', 'Witness field differs from the requested scalar field')
    relations = [r for r in interface['relations'] if r['symbol'] == clause['subject']['relation']]
    require(len(relations) == 1 and [x['purpose'] for x in relations[0]['inputs']] ==
            ['parameter', 'statement', 'witness'], 'intent-relation-formals', 'Wrong relation purposes')
    definition = relations[0]['definition']
    require(definition.get('kind') == 'formula', 'intent-relation-body', 'An opaque target needs its own proved adapter')
    # Select the retained named formula from this same Structured unit. There is
    # no relation-only Common export or second reader.
    relation = {'snapshot': copy.deepcopy(data), 'helper': definition['function']}
    validate_relation(relation, request)
    (output / 'relation.json').write_text(json.dumps(relation, indent=2) + '\n')
    return request, relation, {'clause': target['clause'], 'relation': clause['subject']['relation'],
        'interface_sha256': hashlib.sha256(json.dumps(interface, sort_keys=True).encode()).hexdigest(),
        'binding_scope': 'tested native interface name and selector resolution'}


def validate_relation(data, request):
    require(isinstance(data, dict) and set(data) == {'snapshot', 'helper'},
            'intent-relation-profile', 'Select a named formula in the same Structured unit')
    render(data['snapshot'], 'RelationShape')
    w = request['wiring']
    profile(data['snapshot'], w['fieldDomain'], w['groupDomain'])
    matches = [d for d in data['snapshot'][7] if d[0] == 'function' and d[1] == data['helper']]
    require(len(matches) == 1, 'intent-relation-profile', 'Formula helper is missing or ambiguous')
    helper = matches[0]
    require(helper[2] == 'math' and helper[4] == [['group', w['groupDomain']],
            ['group', w['groupDomain']], ['field', w['fieldDomain']]] and helper[5] == [['bool']],
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
