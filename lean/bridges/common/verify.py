#!/usr/bin/env python3
"""Check an explicit proof request against an actual Structured export.

Candidate expressions are untrusted. Reviewed code owns their validation and
the Lean command stream. Success requires kernel checking, a separate requested-
subject check and a transitive axiom audit. Python execution, the selected toolchain,
request interpretation and native export/rendering remain trusted or tested
boundaries. Receipt status always describes the selected mathematical model.
"""
import argparse
import copy
import hashlib
import json
import os
import re
import signal
import time
from pathlib import Path
import subprocess
import sys

from native_entry import native_subject
from registry import CONTRACTS
from request_support import Obligation, require
from structured import entry, profile, views, compile_modules, lean_environment
from bridges.structured.snapshot import render, text, nat
from bridges.common.schema import interpreted_type

ROOT = Path(__file__).resolve().parents[2]
VERSION = 'zkc.proof-request/0'
RECEIPT = 'zkc.proof-receipt/0'




def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON member {key}')
        result[key] = value
    return result


def read_json(path):
    with path.open('rb') as stream:
        raw = stream.read(2_000_001)
    if len(raw) > 2_000_000:
        raise ValueError('JSON input exceeds the bounded profile')
    decoded = raw.decode('utf-8')
    # Bound nesting before recursive decoding, independently of utilities that
    # raise Python's process-wide recursion limit. JSON validates the structure;
    # this scan only counts delimiters outside quoted strings.
    depth, quoted, escaped = 0, False, False
    for byte in raw:
        if quoted:
            if escaped:
                escaped = False
            elif byte == 92:
                escaped = True
            elif byte == 34:
                quoted = False
        elif byte == 34:
            quoted = True
        elif byte in (91, 123):
            depth += 1
            if depth > 128:
                raise ValueError('JSON nesting exceeds the parser profile')
        elif byte in (93, 125):
            depth -= 1
    try:
        return json.loads(decoded, object_pairs_hook=unique_object)
    except RecursionError as exc:
        raise ValueError('JSON nesting exceeds the parser profile') from exc


def validate(data, request):
    require(isinstance(request, dict) and set(request) ==
            {'format', 'contract', 'properties', 'experiment', 'role', 'inputs', 'wiring'},
            'request-shape', 'Expected exactly the versioned proof-request fields')
    require(request['format'] == VERSION, 'request-version', 'Unsupported proof-request version')
    require(isinstance(request['contract'], str) and request['contract'] in CONTRACTS,
            'contract-unregistered', 'Select a maintained semantic contract or implement an adapter')
    contract = CONTRACTS[request['contract']]
    properties = request['properties']
    require(isinstance(properties, list) and 0 < len(properties) <= 16 and
            all(isinstance(p, str) for p in properties) and len(set(properties)) == len(properties),
            'property-list', 'Properties must be a nonempty list of distinct registered identifiers')
    for prop in properties:
        require(prop in contract.properties, 'property-unregistered',
                f'{prop}: no consumer registered for {request["contract"]}; a new security theorem or adapter is required')
        require(request['experiment'] == contract.properties[prop].experiment,
                'experiment-mismatch', f'{prop} requires {contract.properties[prop].experiment}')
    # The sole serializer validates the complete Structured grammar.
    selected = entry(data)
    roles, input_scopes, output_scopes = selected[6][1:]
    input_scopes = [[roles.index(r) for r in scope] for scope in input_scopes]
    output_scopes = [[roles.index(r) for r in scope] for scope in output_scopes]
    role = request['role']
    require(type(role) is int and 0 <= role < len(roles) and role in output_scopes[0],
            'role-selection', 'The selected participant must have the Boolean output')
    require([interpreted_type(value) for value in selected[5]] == [['bool']], 'output-type', 'This contract requires a Boolean verifier result')
    bindings = request['inputs']
    require(isinstance(bindings, list) and len(bindings) == len(selected[4]),
            'input-bindings', 'Bind every declared input in declaration order')
    require(all(binding is None or isinstance(binding, str) for binding in bindings),
            'input-bindings', 'Input bindings must be registered names or null for foreign inputs')
    require(set(binding for binding in bindings if binding is not None) == set(contract.inputs),
            'input-bindings', 'Bindings must cover exactly the semantic inputs of the selected contract')
    wiring = request['wiring']
    rounds = {'prover', 'fieldDomain', 'firstSites', 'secondSites', 'firstChallenge',
              'secondChallenge', 'firstDelivery', 'secondDelivery'}
    keys = ({'prover', 'fieldDomain', 'groupDomain', 'commitmentSite', 'challengeSite',
             'deliverySite', 'responseSite'} if contract.group else
            rounds | ({'leftSite', 'rightSite'} if contract.composed else set()))
    require(isinstance(wiring, dict) and set(wiring) == keys,
            'wiring-shape', 'Bind all and only the effect sites, domains and prover role of this contract')
    require(type(wiring['prover']) is int and 0 <= wiring['prover'] < len(roles) and
            wiring['prover'] != role, 'prover-role', 'Prover and verifier must be distinct declared participants')
    for key, value in wiring.items():
        if key == 'prover':
            nat(value)
        elif key in ('firstSites', 'secondSites'):
            require(isinstance(value, list) and len(value) == 3,
                    'wiring-shape', f'{key} must bind three coefficient sites')
            for site in value:
                text(site)
        else:
            text(value)
    for binding, dtype, scopes in zip(bindings, selected[4], input_scopes):
        if binding is None:
            require(role not in scopes, 'input-availability', 'A verifier-visible input cannot be silently discarded')
        else:
            kind = contract.inputs[binding][1]
            domain = wiring['groupDomain'] if kind == 'group' else wiring['fieldDomain']
            if kind == 'service':
                domain = 'random.' + domain + '/0'
            require(interpreted_type(dtype) == [kind, domain] and role in scopes,
                    'input-domain', f'{binding}: type, nominal domain or availability disagrees with the request')
    profile(data, wiring['fieldDomain'], wiring.get('groupDomain'))
    require(len(json.dumps(data)) < 500_000, 'source-size', 'Source exceeds this request profile')
    return contract


def wiring_term(contract, wiring):
    def q(key):
        return text(wiring[key])
    if contract.group:
        return '⟨' + ', '.join([nat(wiring['prover']), q('groupDomain'), q('fieldDomain'),
            q('commitmentSite'), q('challengeSite'), q('deliverySite'), q('responseSite')]) + '⟩'
    def triple(key):
        return '(' + ', '.join(map(text, wiring[key])) + ')'
    rounds = '⟨' + ', '.join([nat(wiring['prover']), q('fieldDomain'), triple('firstSites'),
        triple('secondSites'), q('firstChallenge'), q('secondChallenge'), q('firstDelivery'), q('secondDelivery')]) + '⟩'
    return '⟨' + rounds + ', ' + q('leftSite') + ', ' + q('rightSite') + '⟩' if contract.composed else rounds


def generate(data, request):
    '''An untrusted proposal is data only, serialized by the strict reader edge.'''
    validate(data, request)
    return {'snapshot': data}


def property_source(contract, request, certificate, parameters):
    result = ''
    names = []
    for prop in request['properties']:
        item = contract.properties[prop]
        name = 'property_' + prop.replace('-', '_')
        names.append(name)
        context = item.context or ('[Fintype F] ' if item.experiment.endswith('uniform-field/0') else '')
        application = (f'{item.consumer} ({certificate} {parameters})' if item.consumer
                       else f'({certificate} {parameters}).{item.theorem}')
        result += f'\n/-- Premises: {"; ".join(item.premises)}. -/\n'
        result += f'theorem {name} {context}: type_of% ({application}) := {application}\n'
    return result, names


def audit(namespace, names, marker):
    return ('\nrun_cmd do\n  for name in [' + ', '.join('`' + namespace + '.' + n for n in names) + '''] do
    let _ ← Lean.getConstInfo name
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected certificate axiom: {axiomName}"
  Lean.logInfo "''' + marker + '"\n')


def client_source(request, prefix, namespace, *, positive=True, properties=True):
    contract = CONTRACTS[request['contract']]
    generic = 'G' if contract.group else 'F'
    parameters = '(F := F)' + (' (G := G)' if contract.group else '')
    scalar_parameters = f'(F := F) (G := {generic})'
    context = ('\n  [AddCommGroup G] [Module F G] [DecidableEq G]' if contract.group else '')
    values = '.nil'
    for binding in reversed(request['inputs']):
        value = 'none' if binding is None else '(some ' + contract.inputs[binding][0] + ')'
        values = f'.cons {value} ({values})'
    arguments = ' '.join('(' + contract.inputs[b][0] + ')' for b in request['inputs'] if b is not None)
    actual_type = f'PIR.Process (CommonAdapter.commonInterface F {generic}) (Option Bool)'
    cert_args = 'wiring ' + ('publicChecks ' if contract.composed else '') + f'(verifier {parameters})'
    unfolds = ['processView', 'wiring'] + [n if '.' in n else contract.namespace + '.' + n for n in contract.unfold]
    imports = {contract.module, prefix + 'View', 'Zkc.Source.Structured.CommonAdapter',
               'ZkcTools.ProcessView', 'Mathlib.Tactic.Ring', 'Mathlib.Tactic.Abel',
               'Mathlib.Tactic.FailIfNoProgress', 'Lean', 'Aesop'}
    if properties:
        imports.update(contract.properties[prop].module for prop in request['properties'] if contract.properties[prop].module)
    result = ''.join('import ' + m + '\n' for m in sorted(imports)) + f'''
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
noncomputable section
namespace {namespace}
open Zkc.Source Zkc.Source.Structured
open {contract.namespace}

abbrev program := {prefix}Inputs.program
abbrev imported := {prefix}Inputs.imported

def wiring : Wiring := {wiring_term(contract, request['wiring'])}
variable {{F{(' G' if contract.group else '')} : Type}} [Field F] [DecidableEq F]{context}

def inputs {contract.binders} : Values (Component (assignment F {generic})) program.payload.entry.inputs :=
  {values}

/-- The derived scalar observation of the actual typed Structured participant. -/
def verifier {contract.binders} : {actual_type} :=
  ((program.participant F {generic} {request['role']} (inputs {parameters} {contract.arguments})).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

noncomputable def processView {contract.binders} : {actual_type} :=
  process_view% (({prefix}View.view {scalar_parameters} {arguments}).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

theorem process_view_eq {contract.binders} :
    verifier {parameters} {contract.arguments} = processView {parameters} {contract.arguments} := by
  unfold verifier
  change ((program.participant F {generic} {request['role']}
    ({prefix}View.inputs {scalar_parameters} {arguments})).bind _).interpret _ = _
  rw [{prefix}View.source_equation]
  rfl
'''
    if positive:
        result += f'''
theorem correspondence {contract.binders} :
    processView {parameters} {contract.arguments} = experiment {parameters} wiring {contract.arguments} := by
  aesop (rule_sets := [-builtin, -default]) (config := {{ enableSimp := false }})
    (add norm tactic (by fail_if_no_progress dsimp +instances [{', '.join(unfolds)}, PIR.Process.bind]))
    (add norm tactic (by rw [PIR.Process.bind_ite]))
    (add norm tactic (by fail_if_no_progress simp only [apply_ite]))
    (add norm tactic (by fail_if_no_progress ring_nf))
    (add norm tactic (by fail_if_no_progress simp_all only [ite_true, ite_false, decide_true, decide_false, Bool.false_eq_true, not_false_eq_true, not_true_eq_false]))
    (add safe tactic (by split_ifs))
    (add safe tactic (by apply PIR.Process.call_congr; intro reply))
    (add safe tactic (by rfl))
    (add safe tactic (by apply funext; intro reply))
    (add safe tactic (by ring1))
{('    (add safe tactic (by abel1))' if contract.group else '')}
    (add 50% tactic (by fail_if_no_progress congr 1))

theorem contract : VerifierContract {cert_args} :=
  ⟨fun {contract.arguments} => ⟨(process_view_eq {parameters} {contract.arguments}).trans
    (correspondence {parameters} {contract.arguments})⟩⟩
'''
    names = ['process_view_eq'] + (['correspondence', 'contract'] if positive else [])
    if positive and properties:
        extra, props = property_source(contract, request, 'contract', parameters)
        result += extra
        names += props
    result += '\nend ' + namespace + '\nend\n'
    return result, names


def render_certificate(data, request, proposal):
    validate(data, request)
    require(type(proposal) is dict and set(proposal) == {'snapshot'},
            'candidate-shape', 'Expected only a Structured snapshot proposal')
    # No Lean expressions are accepted from a proposal.
    render(proposal['snapshot'], 'CandidateData')
    result, names = client_source(request, 'Candidate', 'GeneratedCertificate')
    return result + audit('GeneratedCertificate', names, 'PROOF-REQUEST-KERNEL-PASS')


def check_subject(data, request):
    '''Fresh request-fixed constructors and admission, never candidate aliases.'''
    contract = validate(data, request)
    generic = 'G' if contract.group else 'F'
    parameters = '(F := F)' + (' (G := G)' if contract.group else '')
    context = ('\n  [AddCommGroup G] [Module F G] [DecidableEq G]' if contract.group else '')
    values = '.nil'
    for binding in reversed(request['inputs']):
        value = 'none' if binding is None else '(some ' + contract.inputs[binding][0] + ')'
        values = f'.cons {value} ({values})'
    result = f'''
namespace ExpectedRequest
open Zkc.Source Zkc.Source.Structured
open {contract.namespace}
noncomputable section

theorem snapshot_eq : ExpectedData.snapshot = CandidateData.snapshot := requested_subject

theorem admitted_subject : check ExpectedData.snapshot = .ok CandidateInputs.program := by
  rw [snapshot_eq]
  exact CandidateInputs.kernel_admission

theorem program_eq : ExpectedInputs.program = CandidateInputs.program :=
  Except.ok.inj (ExpectedInputs.kernel_admission.symm.trans admitted_subject)

def wiring : Wiring := {wiring_term(contract, request['wiring'])}
variable {{F{(' G' if contract.group else '')} : Type}} [Field F] [DecidableEq F]{context}

def expectedInputs {contract.binders} :
    Values (Component (assignment F {generic})) ExpectedInputs.program.payload.entry.inputs :=
  {values}

def expectedVerifier {contract.binders} :
    PIR.Process (CommonAdapter.commonInterface F {generic}) (Option Bool) :=
  ((ExpectedInputs.program.participant F {generic} {request['role']} (expectedInputs {parameters} {contract.arguments})).bind
    fun values => PIR.Process.done (values.get .here)).interpret CommonAdapter.project

theorem approvedContract : VerifierContract wiring {('publicChecks ' if contract.composed else '')}(expectedVerifier {parameters}) := by
  have same : expectedVerifier {parameters} = GeneratedCertificate.verifier {parameters} := by
    funext {contract.arguments}
    unfold expectedVerifier GeneratedCertificate.verifier
    rfl
  rw [same]
  exact GeneratedCertificate.contract
'''
    extra, props = property_source(contract, request, 'approvedContract', parameters)
    return result + extra + '\nend\nend ExpectedRequest\n' + audit('ExpectedRequest', ['admitted_subject', 'approvedContract'] + props, 'PROOF-REQUEST-BOUNDARY-PASS')


def render_client(data, request, name, *, positive=True):
    """Fixture wrapper around the same request template; no source-name theorem lookup."""
    validate(data, request)
    prefix = 'ZkcExamples.NativePrograms.Variants.' + name
    source, _ = client_source(request, prefix, 'ZkcExamples.NativePrograms.' + name,
                             positive=positive, properties=False)
    source = re.sub(r'^import ', 'public import ', source, flags=re.M)
    end = list(re.finditer(r'^public import [^\n]+\n', source, re.M))[-1].end()
    return 'module\n\n' + source[:end] + '\n@[expose] public section\n' + source[end:]


def verify(data, request, output, lake='lake', timeout=180, relation=None):
    # Each generator sees its own disposable inputs. The requested subject and
    # receipt retain independent snapshots even if a generator mutates its copy.
    data, request, relation = copy.deepcopy((data, request, relation))
    deadline = time.monotonic() + timeout
    def remaining():
        return max(0.001, deadline - time.monotonic())
    output.mkdir(parents=True, exist_ok=True)
    receipt = {'format': RECEIPT, 'status': 'unresolved', 'claim_scope': 'formal-model',
               'contract': request.get('contract') if isinstance(request, dict) else None,
               'source_export_sha256': hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest(),
               'request_sha256': hashlib.sha256(json.dumps(request, sort_keys=True).encode()).hexdigest(),
               'verified_properties': [], 'obligations': [],
               'external_boundaries': ['native-source-to-export (check separately)', 'export-to-constructor-rendering (check separately)',
                   'request-parser and registry interpretation (reviewed and tested)',
                   'strict Structured serialization and Lean-owned view printing (tested)',
                   'Python execution and selected Lean toolchain (trusted)'],
               'not_established': ['native-runtime arithmetic and sampling conformance',
                   'DSL compiler correctness', 'Fiat-Shamir security', 'PCS binding or extractability',
                   'malicious-verifier or concurrent zero knowledge', 'whole native prover correctness']}
    (output / 'request.json').write_text(json.dumps(request, indent=2) + '\n')
    (output / 'source.json').write_text(json.dumps(data, indent=2) + '\n')
    try:
        proposal = generate(copy.deepcopy(data), copy.deepcopy(request))
        candidate = render_certificate(data, request, proposal) + check_subject(data, request)
        modules = views(proposal['snapshot'], output, 'Candidate', request['role'], timeout=remaining())
        modules += views(data, output, 'Expected', request['role'], timeout=remaining())
        # Check literal subject identity in its own kernel module before Lean
        # attempts any dependent process transport. A different candidate must
        # fail at this boundary, rather than spend the budget comparing bodies.
        (output / 'SubjectIdentity.lean').write_text('''import CandidateData
import ExpectedData
import Zkc.Source.KernelRfl

theorem requested_subject : ExpectedData.snapshot = CandidateData.snapshot := by
  kernel_rfl
''')
        modules = ['CandidateData', 'ExpectedData', 'SubjectIdentity'] + [
            module for module in modules if module not in ('CandidateData', 'ExpectedData')]
        candidate = 'import SubjectIdentity\nimport ExpectedInputs\n' + candidate
        if relation is not None:
            from intent import relation_candidate, render_relation, relation_subject
            relation_proposal = relation_candidate(copy.deepcopy(relation), copy.deepcopy(request))
            modules += views(relation_proposal['snapshot'], output, 'RelationCandidate', request['role'], timeout=remaining())[:2]
            modules += views(relation['snapshot'], output, 'RelationExpected', request['role'], timeout=remaining())[:2]
            candidate = 'import RelationCandidateInputs\nimport RelationExpectedInputs\n' + candidate
            candidate += render_relation(relation, request, relation_proposal) + relation_subject(relation, request)
        path = output / 'Certificate.lean'
        path.write_text(candidate)
        receipt['certificate_sha256'] = hashlib.sha256(candidate.encode()).hexdigest()
        contract = CONTRACTS[request['contract']]
        property_modules = [contract.properties[prop].module or contract.module for prop in request['properties']]
        environment = (ROOT / 'integrations/arklib' if any(m.startswith('ZkcArkLib.') for m in property_modules)
                       else ROOT / 'security' if any(m.startswith('ZkcSecurity.') for m in property_modules) else ROOT)
        compile_modules(output, modules, environment, lake, remaining())
        receipt['toolchain'] = (environment / 'lean-toolchain').read_text().strip()
        receipt['dependency_manifest_sha256'] = hashlib.sha256(
            (environment / 'lake-manifest.json').read_bytes()).hexdigest()
        with subprocess.Popen(['lean', '-j2', '-M16384', '--root=' + str(output.resolve()), str(path.resolve())], cwd=output,
                              env=lean_environment(environment, output, lake),
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              start_new_session=True) as child:
            try:
                stdout, _ = child.communicate(timeout=remaining())
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                stdout, _ = child.communicate()
                (output / 'lean.log').write_text(stdout)
                raise Obligation('proof-budget', 'Lean exceeded the bounded proof-generation timeout')
            result = subprocess.CompletedProcess(child.args, child.returncode, stdout)
        (output / 'lean.log').write_text(result.stdout)
        require(result.returncode == 0 and 'PROOF-REQUEST-KERNEL-PASS' in result.stdout and 'PROOF-REQUEST-BOUNDARY-PASS' in result.stdout,
                'correspondence-unproved', 'Lean did not certify this source/contract/property combination; inspect Certificate.lean and lean.log')
        require(relation is None or 'RELATION-BOUNDARY-PASS' in result.stdout,
                'relation-unproved', 'Lean did not certify the authored target relation')
        receipt['status'] = 'verified-in-model'
        if relation is not None:
            receipt['target_relation'] = {'model': 'discrete-log/0',
                'export_sha256': hashlib.sha256(json.dumps(relation, sort_keys=True).encode()).hexdigest(),
                'certificate': 'ExpectedRelation.approvedRelation'}
        contract = CONTRACTS[request['contract']]
        receipt['verified_properties'] = [{'property': prop, 'experiment': contract.properties[prop].experiment,
            'consumer': contract.properties[prop].consumer or
                contract.namespace + '.VerifierContract.' + contract.properties[prop].theorem,
            'premises': list(contract.properties[prop].premises),
            'certificate': 'ExpectedRequest.property_' + prop.replace('-', '_')}
            for prop in request['properties']]
    except Obligation as exc:
        receipt['obligations'].append({'code': exc.code, 'detail': exc.detail})
    except subprocess.TimeoutExpired as exc:
        partial = exc.stdout or b''
        (output / 'lean.log').write_text(partial.decode(errors='replace') if isinstance(partial, bytes) else partial)
        receipt['obligations'].append({'code': 'proof-budget', 'detail': 'Lean exceeded the bounded proof-generation timeout'})
    except (ValueError, TypeError, KeyError, IndexError) as exc:
        receipt['obligations'].append({'code': 'unsupported-input', 'detail': str(exc)})
    except OSError as exc:
        receipt['obligations'].append({'code': 'tool-unavailable', 'detail': str(exc)})
    (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt


def export_native(modules, subject, compiler, output):
    output.mkdir(parents=True, exist_ok=True)
    flags = ['--source-format=zkc', *['--module=' + item for item in modules], '--subject=' + subject]
    def execute(command):
        return subprocess.check_output(list(map(str, command)), text=True, stderr=subprocess.PIPE, timeout=30)
    text, interface_text, interface = native_subject(execute, compiler, flags)
    (output / 'interface.json').write_text(interface_text)
    digest = hashlib.sha256(text.encode()).hexdigest()
    require(interface['original'] == digest, 'native-identity', 'Native interface and retained source disagree')
    source = output / 'native.mlir'
    source.write_text(text)
    data = json.loads(execute([compiler, 'protocol-structured', source, '--symbol=' + interface['protocol']]))
    require(data[2] == 'sha256:' + digest and data[3] == interface['protocol'],
            'native-identity', 'Exported source identity disagrees with retained bytes or selected symbol')
    return data, {'source_sha256': digest, 'symbol': interface['protocol'],
                  'compiler_sha256': hashlib.sha256(compiler.read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', type=Path)
    parser.add_argument('--module', action='append', default=[], help='Native module binding NAME=PATH; repeatable')
    parser.add_argument('--subject', help='Closed native protocol specialization')
    parser.add_argument('--compiler', type=Path, default=ROOT.parent / 'build/compiler/zkc-compile')
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument('--request', type=Path)
    selection.add_argument('--spec', type=Path, help='Named DSL verification specification')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    if bool(args.snapshot) == bool(args.module) or bool(args.module) != bool(args.subject):
        parser.error('choose --snapshot or --module NAME=PATH with --subject MODULE::PROTOCOL')
    if args.spec and args.snapshot:
        parser.error('--spec requires a native protocol subject to resolve names and the target relation')
    native = None
    try:
        request = read_json(args.request or args.spec)
        if args.snapshot:
            data = read_json(args.snapshot)
        else:
            data, native = export_native(args.module, args.subject, args.compiler.resolve(), args.output.resolve())
        relation = None
        if args.spec:
            from intent import resolve
            request, relation, target = resolve(request, data,
                read_json(args.output / 'interface.json'), args.compiler.resolve(), args.output.resolve())
        result = verify(data, request, args.output, args.lake, relation=relation)
        if args.spec:
            result['authored_target'] = target
        if native is not None:
            result['native_export'] = native
            (args.output / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    except (ValueError, OSError, subprocess.SubprocessError) as exc:
        args.output.mkdir(parents=True, exist_ok=True)
        code = exc.code if isinstance(exc, Obligation) else 'input-or-export-failed'
        result = {'format': RECEIPT, 'status': 'unresolved', 'claim_scope': 'formal-model',
                  'verified_properties': [], 'obligations': [{'code': code, 'detail': str(exc)}]}
        (args.output / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return 0 if result['status'] == 'verified-in-model' else 1


if __name__ == '__main__':
    sys.exit(main())
