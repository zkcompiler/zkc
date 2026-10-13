"""Resolve named DSL intent and propose a checked scalar relation adapter.

The native interface is a tested name/selector boundary, not a proof. The relation
body is exported and admitted independently; a matching name never proves it.
"""
import copy
import hashlib
import json
import subprocess

from snapshot import render
from symbolic import program, indent
from request_support import require
from verify import validate, VERSION


def resolve(spec, data, interface, compiler, output):
    require(isinstance(spec, dict) and set(spec) == {
        'format', 'contract', 'properties', 'experiment', 'role', 'inputs', 'wiring', 'target'},
        'spec-shape', 'Expected the named verification-spec fields')
    require(spec['format'] == 'zkc.verification-spec/0', 'spec-version', 'Unsupported verification specification')
    require(interface.get('format') == 'zkc.language-interface/0' and
            data[1] == 'sha256:' + interface['original'] and data[2] == interface['protocol'],
            'intent-identity', 'Interface and program export must describe the same source and selected protocol')
    protocols = [p for p in interface['protocols'] if p['symbol'] == data[2]]
    require(len(protocols) == 1, 'intent-protocol', 'The selected protocol must occur exactly once')
    protocol = protocols[0]
    roles = protocol['roles']
    require(isinstance(spec['role'], str) and spec['role'] in roles,
            'intent-role', 'Select a declared verifier role by name')
    request = {k: copy.deepcopy(spec[k]) for k in ('contract', 'properties', 'experiment', 'wiring')}
    request.update(format=VERSION, role=roles.index(spec['role']), inputs=[None] * len(data[4]))
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
        require(len(native) == 1 and type(native[0]) is int and 0 <= native[0] < len(data[4]),
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
    raw = subprocess.check_output([str(compiler), 'protocol-lean', str(output / 'native.mlir'),
                                  '--symbol=' + definition['function']], text=True, timeout=30)
    relation = json.loads(raw)
    require(relation[1] == data[1] and relation[2] == definition['function'],
            'intent-identity', 'Relation body and protocol must come from the same retained native source')
    (output / 'relation.json').write_text(json.dumps(relation, indent=2) + '\n')
    return request, relation, {'clause': target['clause'], 'relation': clause['subject']['relation'],
        'interface_sha256': hashlib.sha256(json.dumps(interface, sort_keys=True).encode()).hexdigest(),
        'binding_scope': 'tested native interface name and selector resolution'}


def validate_relation(data, request):
    render(data, 'RelationShape')
    w = request['wiring']
    require(data[4] == [['group', w['groupDomain']], ['group', w['groupDomain']], ['field', w['fieldDomain']]]
            and data[5] == [[0], [0], [0]] and data[6] == ['bool'] and data[7] == [0]
            and all(i[0] == 'pure' for i in data[8]),
            'intent-relation-profile', 'The relation must be a pure scalar group predicate')
    for instruction in data[8]:
        op = instruction[1]
        if op[0].startswith('group.'):
            require(op[1] == w['groupDomain'], 'intent-relation-domain', 'Unassigned relation group')
        if op[0].startswith('field.'):
            require(op[1] == w['fieldDomain'], 'intent-relation-domain', 'Unassigned relation field')
        if op[0] == 'group.scale':
            require(op[2] == w['fieldDomain'], 'intent-relation-domain', 'Unassigned relation scalar action')


def relation_candidate(data, request):
    """Propose pure syntax; admission, relation and audit commands are reviewed."""
    validate_relation(data, request)
    return program(data)


def render_relation(data, request, proposal):
    from candidate import program_expression
    validate_relation(data, request)
    source_program = program_expression(proposal)
    rendered = render(data, 'GeneratedRelation.Data').split('namespace ', 1)[1]
    return f'''
namespace {rendered}
namespace GeneratedRelation
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native

def sourceProgram : Program Nat language services Data.snapshot.inputs Data.snapshot.result :=
{indent(source_program)}
def sourceScopes : Values (fun _ => Nat → Bool) Data.snapshot.inputs :=
  (inputScopes Data.snapshot.inputs Data.snapshot.inputRoles).get (by decide +kernel)
def imported : Imported := ⟨Data.snapshot, sourceProgram, sourceScopes⟩
theorem admitted : Data.snapshot.check = .ok imported := by
  apply Data.snapshot.check_parts sourceProgram sourceScopes
  · decide +kernel
  · exact inputScopes_get Data.snapshot _
  · rfl
  · decide +kernel
  · decide +kernel
variable {{F G : Type}} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
def inputs (base key : G) (secret : F) :
    Values (fun ty => Option (ScalarValue F G ty)) Data.snapshot.inputs :=
  .cons (some base) (.cons (some key) (.cons (some secret) .nil))
theorem corresponds (base key : G) (secret : F) :
    imported.denote (scalarMeaning F G) id 0 (inputs base key secret) =
      PIR.Proc.done (some (decide (key = secret • base))) := by
  change (imported.program.denote (scalarMeaning F G) id 0
    (inputs base key secret).get).bind PIR.Proc.done = _
  rw [PIR.Proc.bind_done]
  rfl
end GeneratedRelation
'''


def relation_subject(data, request):
    validate_relation(data, request)
    rendered = render(data, 'ExpectedRelation.Data').split('namespace ', 1)[1]
    return f'''
namespace {rendered}
namespace ExpectedRelation
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
theorem admitted_subject : Data.snapshot.check = .ok GeneratedRelation.imported :=
  GeneratedRelation.admitted
variable {{F G : Type}} [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
theorem approvedRelation (base key : G) (secret : F) :
    GeneratedRelation.imported.denote (scalarMeaning F G) id 0
      (.cons (some base) (.cons (some key) (.cons (some secret) .nil))) =
      PIR.Proc.done (some (decide (key = secret • base))) :=
  GeneratedRelation.corresponds base key secret

/-- Two accepting executions of the actual imported verifier yield a witness
accepted by the actual imported authored relation. -/
theorem target_special_soundness (base key : G) (service : Nat)
    (prover : Zkc.Protocols.Schnorr.Common.Strategy F G) (first second : F)
    (distinct : first ≠ second)
    (acceptFirst : (Zkc.Protocols.Schnorr.Common.run ExpectedRequest.expectedVerifier
      base key service prover first).outcome = .returned (some true))
    (acceptSecond : (Zkc.Protocols.Schnorr.Common.run ExpectedRequest.expectedVerifier
      base key service prover second).outcome = .returned (some true)) :
    GeneratedRelation.imported.denote (scalarMeaning F G) id 0
      (.cons (some base) (.cons (some key) (.cons
        (some ((prover.response first - prover.response second) / (first - second))) .nil))) =
      PIR.Proc.done (some true) := by
  rw [approvedRelation]
  have opening := ExpectedRequest.approvedContract.special_soundness
    base key service prover first second distinct acceptFirst acceptSecond
  simp only [opening, decide_true]
  rfl
end ExpectedRelation
run_cmd do
  for name in [`ExpectedRelation.admitted_subject, `ExpectedRelation.approvedRelation,
      `ExpectedRelation.target_special_soundness] do
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "relation uses unexpected axiom: {{axiomName}}"
  Lean.logInfo "RELATION-BOUNDARY-PASS"
'''
