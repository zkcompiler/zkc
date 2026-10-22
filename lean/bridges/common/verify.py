#!/usr/bin/env python3
"""Check an explicit proof request against an actual common-source export.

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
from pathlib import Path
import subprocess
import sys

from native_entry import native_subject
from registry import CONTRACTS
from request_support import Obligation, require
from snapshot import render, string, natural
from symbolic import process, program, indent, Unsupported
from candidate import expression, program_expression

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
    # Rendering validates all constructors, even instructions dormant at this role.
    render(data, 'GeneratedCertificate.Data')
    role = request['role']
    require(type(role) is int and 0 <= role < len(data[3]) and role in data[7],
            'role-selection', 'The selected participant must have the Boolean output')
    require(data[6] == ['bool'], 'output-type', 'This contract requires a Boolean verifier result')
    bindings = request['inputs']
    require(isinstance(bindings, list) and len(bindings) == len(data[4]),
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
    require(type(wiring['prover']) is int and 0 <= wiring['prover'] < len(data[3]) and
            wiring['prover'] != role, 'prover-role', 'Prover and verifier must be distinct declared participants')
    for key, value in wiring.items():
        if key == 'prover':
            natural(value)
        elif key in ('firstSites', 'secondSites'):
            require(isinstance(value, list) and len(value) == 3,
                    'wiring-shape', f'{key} must bind three coefficient sites')
            for site in value:
                string(site)
        else:
            string(value)
    for binding, dtype, scopes in zip(bindings, data[4], data[5]):
        if binding is None:
            require(role not in scopes, 'input-availability', 'A verifier-visible input cannot be silently discarded')
        else:
            kind = contract.inputs[binding][1]
            domain = wiring['groupDomain'] if kind == 'group' else wiring['fieldDomain']
            if kind == 'service':
                domain = 'random.' + domain + '/0'
            require(dtype == [kind, domain] and role in scopes,
                    'input-domain', f'{binding}: type, nominal domain or availability disagrees with the request')
    # ScalarValue interprets all tags uniformly. Restrict this profile to exactly
    # the explicitly selected domains, rather than collapsing distinct fields.
    encoded = json.dumps(data)
    types = list(data[4]) + [data[6]]
    for instr in data[8]:
        if instr[0] == 'pure':
            op = instr[1]
            if op[0].startswith('field.'):
                require(op[1] == wiring['fieldDomain'], 'domain-assignment', 'An operation uses another field')
            if op[0].startswith('group.'):
                require(contract.group and op[1] == wiring['groupDomain'], 'domain-assignment', 'An operation uses another group')
                if op[0] == 'group.scale':
                    require(op[2] == wiring['fieldDomain'], 'domain-assignment', 'Scalar domain differs')
            if op[0] == 'select':
                types.append(op[1])
        elif instr[0] == 'exchange':
            types.append(instr[4])
        elif instr[0] == 'restrict':
            types.append(instr[2])
        elif instr[0] == 'draw':
            require(instr[3] == wiring['fieldDomain'], 'domain-assignment', 'A query uses another field')
        elif instr[0] == 'statement':
            types.extend(instr[2])
    for dtype in types:
        if dtype[0] in ('field', 'service'):
            expected = wiring['fieldDomain'] if dtype[0] == 'field' else 'random.' + wiring['fieldDomain'] + '/0'
            require(dtype[1] == expected, 'domain-assignment', 'Another field/service domain is present')
        elif dtype[0] == 'group':
            require(contract.group and dtype[1] == wiring['groupDomain'], 'domain-assignment', 'Another group domain is present')
    require(len(encoded) < 500_000, 'source-size', 'Source exceeds this proof-generation profile')
    return contract


def wiring_term(contract, wiring):
    def q(key):
        return string(wiring[key])
    if contract.group:
        return '⟨' + ', '.join([natural(wiring['prover']), q('groupDomain'), q('fieldDomain'),
            q('commitmentSite'), q('challengeSite'), q('deliverySite'), q('responseSite')]) + '⟩'
    def triple(key):
        return '(' + ', '.join(map(string, wiring[key])) + ')'
    rounds = '⟨' + ', '.join([natural(wiring['prover']), q('fieldDomain'), triple('firstSites'),
        triple('secondSites'), q('firstChallenge'), q('secondChallenge'), q('firstDelivery'), q('secondDelivery')]) + '⟩'
    return '⟨' + rounds + ', ' + q('leftSite') + ', ' + q('rightSite') + '⟩' if contract.composed else rounds


def generate(data, request):
    """Propose pure expressions only; the reviewed renderer owns all commands."""
    contract = validate(data, request)
    initial = [None if binding is None else contract.inputs[binding][0] for binding in request['inputs']]
    return {'program': program(data), 'process': process(data, request['role'], initial)}


def render_certificate(data, request, proposal):
    contract = validate(data, request)
    require(type(proposal) is dict and set(proposal) == {'program', 'process'},
            'candidate-shape', 'Expected only program and process expression proposals')
    source_program = program_expression(proposal['program'])
    source_process = expression(proposal['process'], 'process',
                                [item[0] for item in contract.inputs.values()])
    namespace = contract.namespace
    initial = [None if binding is None else contract.inputs[binding][0] for binding in request['inputs']]
    values = '.nil'
    for value in reversed(initial):
        values = f'.cons {"none" if value is None else "(some " + value + ")"} ({values})'
    generic = 'G' if contract.group else 'F'
    context = ('\n    [AddCommGroup G] [Module F G] [DecidableEq G]' if contract.group else '')
    parameters = '(F := F)' + (' (G := G)' if contract.group else '')
    actual_type = f'PIR.Process (Participant.interface Nat Ty services (ScalarValue F {generic})) (Option Bool)'
    cert_args = 'wiring ' + ('publicChecks ' if contract.composed else '') + f'(verifier {parameters})'
    unfolds = ['sourceProcess', 'wiring'] + [name if '.' in name else namespace + '.' + name for name in contract.unfold]

    source_data = render(data, 'GeneratedCertificate.Data').split('namespace ', 1)[1]
    external_imports = ''.join('import ' + module + '\n' for module in sorted({
        contract.properties[prop].module for prop in request['properties']
        if contract.properties[prop].module}))
    result = external_imports + f'''import Zkc.Source.Common.Import
import {contract.module}
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FailIfNoProgress
import Lean

/-! Generated candidate: source identity alone proves no semantic property. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.defProp false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace {source_data}
namespace GeneratedCertificate
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open {namespace}

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

def wiring : Wiring := {wiring_term(contract, request['wiring'])}

variable {{F{(' G' if contract.group else '')} : Type}} [Field F] [DecidableEq F]{context}

def inputs {contract.binders} :
    Values (fun ty => Option (ScalarValue F {generic} ty)) Data.snapshot.inputs :=
  {values}

def verifier {contract.binders} : {actual_type} :=
  imported.denote (scalarMeaning F {generic}) id {request['role']} (inputs {parameters} {contract.arguments})

def sourceProcess {contract.binders} : {actual_type} :=
{indent(source_process)}

theorem source_expansion {contract.binders} :
    verifier {parameters} {contract.arguments} = sourceProcess {parameters} {contract.arguments} := by
  change (imported.program.denote (scalarMeaning F {generic}) id {request['role']}
    (inputs {parameters} {contract.arguments}).get).bind PIR.Process.done = _
  rw [PIR.Process.bind_done]
  repeat' first
    | (apply PIR.Process.call_congr; intro reply)
    | (change (if _ then _ else _ : PIR.Process _ _).bind _ = _
       rw [PIR.Process.bind_ite]
       simp only [↓reduceIte])
    | rfl
    | fail_if_no_progress congr 1

{('omit [DecidableEq F] in' if contract.group else '')}
theorem correspondence {contract.binders} :
    sourceProcess {parameters} {contract.arguments} = experiment {parameters} wiring {contract.arguments} := by
  dsimp +instances [{', '.join(unfolds)}]
  {('simp only [PIR.Process.bind_ite, PIR.Process.bind]'+chr(10)+'  dsimp +instances [terminal, publicChecks, value]' if contract.composed else 'skip')}
  all_goals repeat' first
    | rfl
    | (apply PIR.Process.call_congr; intro reply)
    | (solve | ring1)
    | (solve | abel1)
    | fail_if_no_progress congr 1

theorem contract : VerifierContract {cert_args} :=
  ⟨fun {contract.arguments} => ⟨(source_expansion {parameters} {contract.arguments}).trans
    (correspondence {parameters} {contract.arguments})⟩⟩
'''
    names = ['admitted', 'source_expansion', 'correspondence', 'contract']
    for prop in request['properties']:
        registered = contract.properties[prop]
        name = 'property_' + prop.replace('-', '_')
        names.append(name)
        context = registered.context or ('[Fintype F] ' if registered.experiment.endswith('uniform-field/0') else '')
        result += f'\n/-- Premises: {"; ".join(registered.premises)}. -/\n'
        application = (f'{registered.consumer} (contract {parameters})' if registered.consumer
                       else f'(contract {parameters}).{registered.theorem}')
        result += f'noncomputable def {name} {context}:= {application}\n'
    result += '\nend GeneratedCertificate\n\n'
    result += 'run_cmd do\n'
    result += '  for name in [' + ', '.join('`GeneratedCertificate.' + name for name in names) + '] do\n'
    result += '''    let _ ← Lean.getConstInfo name
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "certificate uses unexpected axiom: {axiomName}"
  Lean.logInfo "PROOF-REQUEST-KERNEL-PASS"
'''
    return result


def check_subject(data, request):
    """Small reviewed request interpreter, separate from candidate generation.

The importer result is tied to fresh input constructors; the expected contract
mentions its actual denotation and request-selected bindings, never the
candidate's verifier or input aliases. Properties are re-derived from this
checked subject. Parsing/rendering/registry interpretation are tested boundaries.
"""
    contract = validate(data, request)
    generic = 'G' if contract.group else 'F'
    parameters = '(F := F)' + (' (G := G)' if contract.group else '')
    context = ('\n    [AddCommGroup G] [Module F G] [DecidableEq G]' if contract.group else '')
    values = '.nil'
    for binding in reversed(request['inputs']):
        value = 'none' if binding is None else '(some ' + contract.inputs[binding][0] + ')'
        values = f'.cons {value} ({values})'
    source = render(data, 'ExpectedRequest.Data').split('namespace ', 1)[1]
    result = f"""\nnamespace {source}
namespace ExpectedRequest
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open {contract.namespace}

theorem admitted_subject : Data.snapshot.check = .ok GeneratedCertificate.imported :=
  GeneratedCertificate.admitted

def wiring : Wiring := {wiring_term(contract, request['wiring'])}
variable {{F{(' G' if contract.group else '')} : Type}} [Field F] [DecidableEq F]{context}

def expectedInputs {contract.binders} :
    Values (fun ty => Option (ScalarValue F {generic} ty)) GeneratedCertificate.imported.snapshot.inputs :=
  {values}

def expectedVerifier {contract.binders} :
    PIR.Process (Participant.interface Nat Ty services (ScalarValue F {generic})) (Option Bool) :=
  GeneratedCertificate.imported.denote (scalarMeaning F {generic}) id {request['role']}
    (expectedInputs {parameters} {contract.arguments})

theorem approvedContract : VerifierContract wiring {('publicChecks ' if contract.composed else '')}(expectedVerifier {parameters}) :=
  GeneratedCertificate.contract
"""
    names = ['admitted_subject', 'approvedContract']
    for prop in request['properties']:
        item = contract.properties[prop]
        name = 'property_' + prop.replace('-', '_')
        names.append(name)
        finite = item.context or ('[Fintype F] ' if item.experiment.endswith('uniform-field/0') else '')
        application = (f'{item.consumer} (approvedContract {parameters})' if item.consumer
                       else f'(approvedContract {parameters}).{item.theorem}')
        result += f'\nnoncomputable def {name} {finite}:= {application}\n'
    result += '\nend ExpectedRequest\n\nrun_cmd do\n'
    result += '  for name in [' + ', '.join('`ExpectedRequest.' + name for name in names) + '] do\n'
    result += '''    let _ ← Lean.getConstInfo name
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "request boundary uses unexpected axiom: {axiomName}"
  Lean.logInfo "PROOF-REQUEST-BOUNDARY-PASS"
'''
    return result


def render_client(data, request, name):
    """Maintained example modules reuse the same untrusted candidate generator."""
    allowed = {'FactorExpanded', 'FactorHorner', 'FactorWrongPoint', 'FactorWrongResidual'}
    if name not in allowed:
        raise ValueError('unsupported maintained client')
    candidate = render_certificate(data, request, generate(copy.deepcopy(data), copy.deepcopy(request)))
    start = candidate.index('namespace GeneratedCertificate.Data')
    finish = candidate.index('end GeneratedCertificate.Data') + len('end GeneratedCertificate.Data')
    candidate = candidate[:start] + candidate[finish:]
    candidate = candidate[:candidate.index('run_cmd do')]
    if name in {'FactorWrongPoint', 'FactorWrongResidual'}:
        candidate = candidate[:candidate.index('theorem correspondence')] + 'end GeneratedCertificate\n'
    module = 'ZkcExamples.NativePrograms.Variants.' + name + 'Data'
    candidate = 'import ' + module + '\n' + candidate
    candidate = candidate.replace('Data.snapshot', module + '.snapshot')
    candidate = candidate.replace('GeneratedCertificate', 'ZkcExamples.NativePrograms.' + name)
    candidate = re.sub(r'^import ', 'public import ', candidate, flags=re.M)
    imports = list(re.finditer(r'^public import [^\n]+\n', candidate, re.M))
    end = imports[-1].end()
    candidate = candidate[:end] + '\n@[expose] public section\n' + candidate[end:]
    return 'module\n\n' + candidate.rstrip() + '\n'


def verify(data, request, output, lake='lake', timeout=180, relation=None):
    # Each generator sees its own disposable inputs. The requested subject and
    # receipt retain independent snapshots even if a generator mutates its copy.
    data, request, relation = copy.deepcopy((data, request, relation))
    output.mkdir(parents=True, exist_ok=True)
    receipt = {'format': RECEIPT, 'status': 'unresolved', 'claim_scope': 'formal-model',
               'contract': request.get('contract') if isinstance(request, dict) else None,
               'source_export_sha256': hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest(),
               'request_sha256': hashlib.sha256(json.dumps(request, sort_keys=True).encode()).hexdigest(),
               'verified_properties': [], 'obligations': [],
               'external_boundaries': ['native-source-to-export (check separately)', 'export-to-constructor-rendering (check separately)',
                   'request-parser and registry interpretation (reviewed and tested)',
                   'candidate expression validation and command rendering (reviewed and tested)',
                   'Python execution and selected Lean toolchain (trusted)'],
               'not_established': ['native-runtime arithmetic and sampling conformance',
                   'DSL compiler correctness', 'Fiat-Shamir security', 'PCS binding or extractability',
                   'malicious-verifier or concurrent zero knowledge', 'whole native prover correctness']}
    (output / 'request.json').write_text(json.dumps(request, indent=2) + '\n')
    (output / 'source.json').write_text(json.dumps(data, indent=2) + '\n')
    try:
        proposal = generate(copy.deepcopy(data), copy.deepcopy(request))
        candidate = render_certificate(data, request, proposal) + check_subject(data, request)
        if relation is not None:
            from intent import relation_candidate, render_relation, relation_subject
            relation_proposal = relation_candidate(copy.deepcopy(relation), copy.deepcopy(request))
            candidate += render_relation(relation, request, relation_proposal) + relation_subject(relation, request)
        path = output / 'Certificate.lean'
        path.write_text(candidate)
        receipt['certificate_sha256'] = hashlib.sha256(candidate.encode()).hexdigest()
        contract = CONTRACTS[request['contract']]
        modules = [contract.properties[prop].module or contract.module for prop in request['properties']]
        environment = (ROOT / 'integrations/arklib' if any(m.startswith('ZkcArkLib.') for m in modules)
                       else ROOT / 'security' if any(m.startswith('ZkcSecurity.') for m in modules) else ROOT)
        receipt['toolchain'] = (environment / 'lean-toolchain').read_text().strip()
        receipt['dependency_manifest_sha256'] = hashlib.sha256(
            (environment / 'lake-manifest.json').read_bytes()).hexdigest()
        with subprocess.Popen([lake, 'lean', str(path.resolve())], cwd=environment,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              start_new_session=True) as child:
            try:
                stdout, _ = child.communicate(timeout=timeout)
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
    except (Unsupported, ValueError, TypeError, KeyError, IndexError) as exc:
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
    data = json.loads(execute([compiler, 'protocol-lean', source, '--symbol=' + interface['protocol']]))
    require(data[1] == 'sha256:' + digest and data[2] == interface['protocol'],
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
