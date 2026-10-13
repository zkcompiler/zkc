#!/usr/bin/env python3
"""Verify an actual native constructed participant in a reviewed ideal FS model.

The request selects data, never proof code. Native re-export, source contracts,
actual denotation, selected consumer and independent subject checks must all
succeed before any property is recorded as verified in the mathematical model.
"""
import argparse
from contextlib import contextmanager, ExitStack
import copy
import fcntl
import hashlib
import importlib
import json
import math
import re
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import tempfile
import time

from security_request import Unresolved, decode_json, read_json, require, validate

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
RECEIPT = 'zkc.fs-verification-receipt/0'
SUITE = 'merlin3.bls12-381.fr64be/0'


class ModuleFamily:
    """Isolate legacy sibling imports; common and constructed both own snapshot.

Every lookup is a maintained module name in a fixed directory, not request data.
Aliases and sys.path are restored even on failure. Calls that can import siblings
lazily stay within this context. This synchronous CLI does not share it with threads.
"""
    def __init__(self, directory):
        self.directory = directory
        self.names = {p.stem for p in directory.glob('*.py')}
        self.modules = {}

    @contextmanager
    def load(self, name):
        require(name in self.names, 'implementation-unavailable', f'Missing maintained module: {name}')
        previous = {key: sys.modules.get(key) for key in self.names}
        path = sys.path[:]
        try:
            for key in self.names:
                if key in self.modules:
                    sys.modules[key] = self.modules[key]
                else:
                    sys.modules.pop(key, None)
            sys.path.insert(0, str(self.directory))
            yield importlib.import_module(name)
        finally:
            for key in self.names:
                module = sys.modules.get(key)
                if module is not None and Path(getattr(module, '__file__', '')).parent == self.directory:
                    self.modules[key] = module
                if previous[key] is None:
                    sys.modules.pop(key, None)
                else:
                    sys.modules[key] = previous[key]
            sys.path[:] = path


COMMON = ModuleFamily(ROOT / 'bridges/common')
CONSTRUCTED = ModuleFamily(HERE)


def digest(value):
    if isinstance(value, str):
        value = value.encode('utf-8')
    return hashlib.sha256(value).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def save_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=True) + '\n')
    temporary.replace(path)


def stop_tool(child):
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def lean_error(line):
    try:
        diagnostic = json.loads(line)
    except (ValueError, UnicodeDecodeError):
        return False
    return isinstance(diagnostic, dict) and diagnostic.get('severity') == 'error'


def lean_output(child, timeout):
    """Retain structured diagnostics and stop after Lean has reported an error."""
    deadline = time.monotonic() + timeout
    chunks, pending = [], b''
    with selectors.DefaultSelector() as selector:
        selector.register(child.stdout, selectors.EVENT_READ)
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not selector.select(remaining):
                raise subprocess.TimeoutExpired(child.args, timeout, output=b''.join(chunks))
            chunk = os.read(child.stdout.fileno(), 65536)
            if not chunk:
                try:
                    child.wait(timeout=max(0, deadline - time.monotonic()))
                except subprocess.TimeoutExpired:
                    raise subprocess.TimeoutExpired(child.args, timeout, output=b''.join(chunks)) from None
                return b''.join(chunks), lean_error(pending)
            chunks.append(chunk)
            pending += chunk
            while b'\n' in pending:
                line, pending = pending.split(b'\n', 1)
                if lean_error(line):
                    stop_tool(child)
                    tail, _ = child.communicate()
                    return b''.join(chunks) + tail, True


def execute(command, directory, label, timeout, cwd=None):
    """Kill the complete proof/tool process group on bounded execution failure."""
    require(math.isfinite(timeout) and 0 < timeout <= 1200, 'tool-budget', 'Timeout must be positive')
    save_json(directory / (label + '.command.json'),
              {'argv': list(map(str, command)), 'cwd': str(cwd or Path.cwd()), 'timeout_seconds': timeout})
    reported_error = False
    with subprocess.Popen(list(map(str, command)), cwd=cwd,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          start_new_session=True) as child:
        try:
            if label == 'lean':
                stdout, reported_error = lean_output(child, timeout)
            else:
                stdout, _ = child.communicate(timeout=timeout)
        except subprocess.TimeoutExpired as error:
            stop_tool(child)
            tail, _ = child.communicate()
            stdout = ((error.output or b'') if label == 'lean' else b'') + tail
            (directory / (label + '.log')).write_text(stdout.decode())
            raise Unresolved('tool-timeout', f'{label} exceeded its execution budget') from None
    stdout = stdout.decode()
    (directory / (label + '.log')).write_text(stdout)
    require(child.returncode == 0 and not reported_error, 'tool-failed', f'{label} failed; inspect {label}.log')
    return stdout


def derived_policy(data, request):
    """Bind only explicit source selectors; the native checker validates their wiring."""
    wiring = request['wiring']
    verifier, prover = request['role'], wiring['prover']
    service = [i for i, value in enumerate(request['inputs']) if value == 'service']
    public = [i for i, value in enumerate(request['inputs']) if value not in (None, 'service')]
    require(len(service) == 1 and all(prover in data[5][i] and verifier in data[5][i] for i in public),
            'public-binding', 'Every semantic statement input must be public to both participants')
    require(wiring['fieldDomain'] == 'bls12-381.fr' and
            wiring.get('groupDomain', 'bls12-381.g1') == 'bls12-381.g1',
            'native-domain', 'The fixed native primitive profile requires the selected BLS nominal domains')
    if request['contract'] == 'schnorr.verifier/0':
        draws = [[wiring['challengeSite'], wiring['deliverySite']]]
    else:
        draws = [[wiring['firstChallenge'], wiring['firstDelivery']],
                 [wiring['secondChallenge'], wiring['secondDelivery']]]
    return ['zkc.native-proof-policy/0', data[2], data[3][prover], data[3][verifier],
            '0', SUITE, list(map(str, service)), list(map(str, public)), draws, 'zkc.framed/0', '']


def prepare_native(args, specification, output):
    source_request = specification['source']
    compiler = args.compiler.resolve()
    require(bool(args.module) != bool(args.source) and bool(args.module) == bool(args.entry),
            'native-selection', 'Choose modules with an Entry or retained source with an explicit policy')
    require(args.source is None or args.policy is not None,
            'native-policy', 'Retained source requires its explicit construction policy')
    timeout = min(args.timeout, 120)
    supplied_policy = read_json(args.policy) if args.policy else None
    interface = None
    if args.module:
        flags = ['--source-format=zkc', *['--module=' + item for item in args.module], '--entry=' + args.entry]
        source = execute([compiler, 'language-emit', *flags], output, 'language-emit', timeout)
        interface = decode_json(execute([compiler, 'language-interface', *flags], output,
                                       'language-interface', timeout))
        require(type(interface) is dict and interface.get('format') == 'zkc.language-interface/0' and
                interface.get('original') == digest(source) and interface.get('entry') == args.entry,
                'native-identity', 'DSL interface and fresh retained source/Entry disagree')
        symbol = interface['protocol']
        save_json(output / 'interface.json', interface)
    else:
        source = args.source.read_bytes().decode('utf-8')
        require(type(supplied_policy) is list and len(supplied_policy) == 11 and
                type(supplied_policy[1]) is str, 'native-policy', 'Expected the exact native policy carrier')
        symbol = supplied_policy[1]
    require(len(source.encode()) <= 16 * 1024 * 1024, 'native-size', 'Retained source exceeds the profile')
    source_path = output / 'source.mlir'
    source_path.write_text(source)
    common = decode_json(execute([compiler, 'protocol-lean', source_path, '--symbol=' + symbol],
                                 output, 'source-export', timeout))
    with COMMON.load('verify') as common_verify:
        common_verify.validate(common, source_request)
    require(common[1] == 'sha256:' + digest(source) and common[2] == symbol,
            'source-export-identity', 'Fresh source export is detached from the selected retained bytes')
    expected_policy = derived_policy(common, source_request)
    require(supplied_policy is None or supplied_policy == expected_policy, 'policy-selection',
            'Explicit policy differs from exact source role, statement, service or challenge selectors')
    policy = expected_policy
    policy_path = output / 'policy.json'
    save_json(policy_path, policy)
    # A supplied candidate is never trusted merely because its metadata matches.
    if args.candidate:
        candidate = args.candidate.read_bytes().decode('utf-8')
    else:
        candidate = execute([compiler, 'protocol-construct-proof', source_path, policy_path],
                            output, 'construction', timeout)
    require(len(candidate.encode()) <= 16 * 1024 * 1024, 'candidate-size', 'Candidate exceeds the profile')
    candidate_path = output / 'candidate.mlir'
    candidate_path.write_text(candidate)
    constructed = decode_json(execute([compiler, 'protocol-constructed-lean', source_path,
        policy_path, candidate_path], output, 'constructed-export', timeout), maximum=16 * 1024 * 1024)
    with CONSTRUCTED.load('snapshot') as snapshot:
        snapshot.render(constructed, 'CheckedCarrier')
    require(constructed[1] == 'sha256:' + digest(source) and constructed[3] == symbol and
            re.fullmatch(r'sha256:[0-9a-f]{64}', constructed[2]) is not None and
            constructed[4] == common[3][source_request['role']] and
            decode_json(constructed[6]) == policy, 'constructed-export-identity',
            'Checked constructed export is detached from the actual source, candidate, role or policy')
    for name, identity, body in constructed[7]:
        require(identity == 'sha256:' + digest(body), 'handler-identity',
                f'Handler closure identity differs from its retained body: {name}')
    save_json(output / 'common.json', common)
    save_json(output / 'constructed.json', constructed)
    identities = {'source_sha256': digest(source), 'candidate_sha256': digest(candidate),
        'canonical_candidate_identity': constructed[2],
        'candidate_identity_rule': 'native checked generic Operation print; candidate_sha256 hashes retained bytes',
        'source_export_sha256': digest(canonical(common)),
        'constructed_export_sha256': digest(canonical(constructed)),
        'policy_sha256': digest(canonical(policy)), 'policy_file_sha256': digest(policy_path.read_bytes()),
        'handler_closure_sha256': digest(canonical(constructed[7])),
        'handlers': [{'symbol': h[0], 'sha256': h[1]} for h in constructed[7]],
        'native_primitive_closure_sha256': digest(canonical([i[1] for i in constructed[10] if i[0] == 'apply'])),
        'compiler_sha256': digest(compiler.read_bytes()), 'symbol': symbol,
        'participant': constructed[5], 'role': constructed[4]}
    if interface is not None:
        identities['interface_sha256'] = digest(canonical(interface))
    return common, constructed, identities


def receive_sites(specification):
    wiring = specification['source']['wiring']
    return ([wiring['commitmentSite'], wiring['responseSite']]
            if specification['source']['contract'] == 'schnorr.verifier/0'
            else wiring['firstSites'] + wiring['secondSites'])


def combine_modules(parts):
    """Hoist only maintained imports, preserving the order of all proof commands."""
    imports, bodies = [], []
    for part in parts:
        body = []
        for line in part.splitlines():
            if line.startswith(('import ', 'public import ')):
                name = line.removeprefix('public ').removeprefix('import ')
                if name not in imports:
                    imports.append(name)
            elif line not in ('module', '@[expose] public section'):
                body.append(line)
        bodies.append('\n'.join(body))
    return ('module\n\n' + '\n'.join('public import ' + name for name in imports) +
            '\n\n@[expose] public section\n' + '\n'.join(bodies) + '\n')


def schnorr_subject(namespace, expected=False):
    """Independent types use fixed meanings, complete replies and the source contract."""
    result = '''
open Zkc.Protocols.Schnorr
open Construction NativeConstruction
open Zkc.Source Zkc.Source.Constructed
variable {Context F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
'''
    if expected:
        # Compare the retained subject before reusing admission; reducing the
        # whole checker on a mismatched snapshot is needlessly expensive.
        result += '''
set_option backward.isDefEq.respectTransparency true
theorem snapshot_subject : snapshot = GeneratedFS.snapshot := by rfl
theorem admitted_subject :
    snapshot.check = .ok (snapshot_subject.symm ▸ GeneratedFS.imported) := by
  have transport {left right : Snapshot} (same : left = right)
      {value : Imported right} (checked : right.check = .ok value) :
      left.check = .ok (same.symm ▸ value) := by
    cases same
    exact checked
  exact transport snapshot_subject GeneratedFS.admitted

theorem full_denotation (bound : Binding Context G) (proof : G × F) :
    imported.denote (meaning proof) (inputs bound) =
      .call (bound, proof.1) (fun (challenge : F) =>
        .done (.cons (decide (proof.2 • bound.base = proof.1 + challenge • bound.key))
          (.cons (⟨bound, some proof.1, some challenge, true, some proof.2⟩ :
            Transcript Context F G) .nil))) := GeneratedFS.full_denotation bound proof
'''
    result += '''
def actual : Construction.Verifier (OccurrenceContext Context) F G :=
  NativeConstruction.verifier imported rfl rfl

theorem realizes : Realizes (actual (Context := Context) (F := F) (G := G))
    (ExpectedRequest.expectedVerifier (F := F) (G := G)) 0 := '''
    result += ('GeneratedFS.realizes\n' if expected else '''by
  intro bound proof
  constructor
  change (imported.denote (meaning proof) (inputs bound)).bind
    (fun reply => .done (result reply)) = _
  rw [full_denotation, construct_eq ExpectedRequest.approvedContract]
  rfl
''')
    result += '''
open OracleComp OracleSpec
open ZkcSecurity.VCVio.Schnorr.FiatShamir
variable [Fintype F] [Inhabited F] [SampleableType F] [DecidableEq Context]

theorem security (context : Context) (base key : G)
    (prover : Prover (OccurrenceContext Context) F G) (Q : Nat)
    (queryBound : _root_.FiatShamir.nmaHashQueryBound (Binding (OccurrenceContext Context) G)
      (prover key (binding context base key)) Q) :
    let bound := binding context base key
    let acc := acceptance actual prover bound
    acc * (acc / (Q + 1 : ENNReal) - _root_.FiatShamir.challengeSpaceInv F) ≤
      Pr{let witness ← extractor prover bound Q}[witness • base = key] := '''
    result += ('GeneratedFS.security context base key prover Q queryBound\n' if expected else '''by
  exact extraction ExpectedRequest.approvedContract realizes prover
    (binding context base key) Q queryBound
''')
    return result + f'\nend {namespace}\n'


def sumcheck_subject(namespace, expected=False):
    result = '''
open Zkc.Protocols.Sumcheck Zkc.Protocols.Sumcheck.NativeConstruction
open Zkc.Protocols.Sumcheck.Common
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Source Zkc.Source.Constructed
open OracleComp OracleSpec
open ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Native
variable {Context F : Type} [Field F] [DecidableEq F]
'''
    if expected:
        result += '''
set_option backward.isDefEq.respectTransparency true
theorem snapshot_subject : snapshot = GeneratedFS.snapshot := by rfl
theorem admitted_subject :
    snapshot.check = .ok (snapshot_subject.symm ▸ GeneratedFS.imported) := by
  have transport {left right : Snapshot} (same : left = right)
      {value : Imported right} (checked : right.check = .ok value) :
      left.check = .ok (same.symm ▸ value) := by
    cases same
    exact checked
  exact transport snapshot_subject GeneratedFS.admitted

theorem full_denotation (context : Context) (coefficients : Coefficients F)
    (claim : F) (proof : Message F × Message F) :
    imported.denote (meaning schedule proof) (inputs (binding context coefficients claim)) =
      experiment (binding context coefficients claim) proof :=
  GeneratedFS.full_denotation context coefficients claim proof
'''
    result += '''
def subject : Subject Context F := fun choice =>
  imported.denote (meaning schedule (choice.first, choice.second))
    (inputs (binding choice.context choice.coefficients choice.claim))

theorem denotation (choice : Selection Context F) :
    subject choice = reference snapshot.source snapshot.candidate schedule choice := '''
    result += ('GeneratedFS.denotation choice\n' if expected else '''by
  exact full_denotation choice.context choice.coefficients choice.claim (choice.first, choice.second)
''')
    result += '''
variable [Fintype F] [SampleableType F]
theorem query_cost (adversary : Adversary Context F) (Q : Nat)
    (queryBound : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (game snapshot.source snapshot.candidate schedule subject adversary) (Q + 2) := '''
    result += ('GeneratedFS.query_cost adversary Q queryBound\n' if expected else '''
  game_queryBound snapshot.source snapshot.candidate schedule subject denotation adversary Q queryBound
''')
    result += '''
variable [DecidableEq Context]
theorem security (adversary : Adversary Context F) (Q : Nat)
    (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let output ← (simulateQ randomOracle
      (game snapshot.source snapshot.candidate schedule subject adversary)).run' ∅}[
      acceptedRecord output.2 = true ∧
        output.1.claim ≠ (polynomial output.1.coefficients).booleanSum] ≤
          (Q + 3 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := '''
    result += ('GeneratedFS.security adversary Q queryBound\n' if expected else '''
  soundness snapshot.source snapshot.candidate schedule subject denotation adversary Q queryBound
''')
    return result + f'\nend {namespace}\n'


def sumcheck_subjects(realization, constructed, specification, expected):
    profile = realization.validate(constructed, 'sumcheck', receive_sites(specification))
    expected += '\nopen Zkc.Protocols.Sumcheck Zkc.Protocols.Sumcheck.NativeConstruction\ndef schedule : Schedule where\n'
    for name in ('receives', 'observations', 'challenges'):
        expected += f'  {name} := ' + realization.seq(profile[name], realization.primitive) + '\n'
    expected += '''
def binding {Context F : Type} (context : Context) (coefficients : Common.Coefficients F)
    (claim : F) : Binding Context F :=
  ⟨snapshot.source, snapshot.candidate, context, schedule, coefficients, claim⟩
'''
    extra = ('import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Native\nnamespace GeneratedFS\n' +
             sumcheck_subject('GeneratedFS'))
    expected += sumcheck_subject('ExpectedFS', expected=True)
    return extra, expected


def audit_actual(protocol):
    roots = ['ExpectedRequest.admitted_subject', 'ExpectedRequest.approvedContract',
             'ExpectedFS.admitted', 'ExpectedFS.snapshot_subject',
             'ExpectedFS.admitted_subject', 'ExpectedFS.full_denotation',
             'ExpectedFS.realizes' if protocol == 'schnorr' else 'ExpectedFS.denotation',
             'ExpectedFS.security']
    if protocol == 'sumcheck':
        roots.append('ExpectedFS.query_cost')
    else:
        roots.append('ZkcSecurity.VCVio.Schnorr.FiatShamir.extractor_challenge_bound')
    return '''
run_cmd do
  Lean.logInfo "FS-ACTUAL-SUBJECT-PASS"
  Lean.logInfo "FS-SECURITY-CONSUMER-PASS"
  for name in [''' + ', '.join('`' + name for name in roots) + '''] do
    let _ ← Lean.getConstInfo name
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "FS certificate uses unexpected transitive axiom: {axiomName}"
  Lean.logInfo "FS-TRANSITIVE-AXIOMS-PASS"
'''


def render_actual(realization, common, constructed, specification, protocol):
    # Each proposal gets disposable data. The expected carrier is rendered afresh
    # from the retained export; no generator-selected alias defines that subject.
    proposal = realization.render(copy.deepcopy(constructed), protocol, 'GeneratedFS',
                                  receive_sites(specification))
    expected = realization.prelude(constructed, protocol, 'ExpectedFS')
    if protocol == 'schnorr':
        profile = realization.validate(constructed, protocol, receive_sites(specification))
        expected += ('def occurrences : List Primitive := ' +
                     realization.seq(profile['operations'], realization.primitive) + '\n')
        expected += '''
def binding {Context G : Type} (context : Context) (base key : G) :
    Zkc.Protocols.Schnorr.Construction.Binding (OccurrenceContext Context) G :=
  ⟨snapshot.source, snapshot.candidate, ⟨context, snapshot.policy, occurrences⟩, base, key⟩
'''
        extra = ('import ZkcSecurity.VCVio.Schnorr.FiatShamir\nnamespace GeneratedFS\n' +
                 schnorr_subject('GeneratedFS'))
        expected += schnorr_subject('ExpectedFS', expected=True)
    else:
        extra, expected = sumcheck_subjects(realization, constructed, specification, expected)
    return combine_modules([proposal, extra, expected, audit_actual(protocol)])


def build_certificate(common, constructed, specification):
    """Reviewed assembly; generators see disposable data, independent checkers do not."""
    with COMMON.load('verify') as common_verify:
        source = specification['source']
        proposal = common_verify.generate(copy.deepcopy(common), copy.deepcopy(source))
        certificate = common_verify.render_certificate(common, source, proposal)
        certificate += common_verify.check_subject(common, source)
    protocol = 'schnorr' if source['contract'] == 'schnorr.verifier/0' else 'sumcheck'
    with CONSTRUCTED.load('realization') as realization:
        realization.validate(constructed, protocol, receive_sites(specification))
        certificate += render_actual(realization, common, constructed, specification, protocol)
    return combine_modules([certificate])


def formal_source_closure(imports):
    """Record maintained import closure; pinned external packages have manifests."""
    seen, hashes, pending = set(), {}, list(imports)
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        base = ROOT / 'integrations/arklib' if module.startswith('ZkcSecurity.') else ROOT
        path = base / (module.replace('.', '/') + '.lean')
        require(path.is_file(), 'formal-import', f'Missing maintained source: {module}')
        source = path.read_text()
        hashes[str(path.relative_to(ROOT))] = digest(path.read_bytes())
        pending.extend(re.findall(r'^(?:public )?import (Zkc[^\s]*)$', source, flags=re.MULTILINE))
    return hashes


def initial_receipt():
    return {'format': RECEIPT, 'status': 'unresolved', 'claim_scope': 'formal-model',
        'verified_properties': [], 'discharged_layers': [], 'obligations': [],
        'external_boundaries': [
            'native source export and checked construction/export implementation',
            'JSON parsing, constructor rendering and reviewed request/consumer selection',
            'host initializes the transcript with the full selected public binding',
            'native lowering/runtime and arithmetic conformance to selected mathematical field/group',
            'native Merlin provider and byte/codec conformance to the selected ideal transcript model',
            'Python and selected Lean toolchain'],
        'not_established': ['concrete Merlin security', 'native compiler/runtime correctness',
            'efficient proof of knowledge', 'unconditional adversary query budget',
            'authored DSL spec or Entry target-body equivalence',
            'concurrent or malicious-verifier zero knowledge']}


@contextmanager
def output_ownership(output):
    """Cooperating invocations cannot invalidate or replace each other's evidence."""
    output.mkdir(parents=True, exist_ok=True)
    with (output / '.verification.lock').open('a') as lock:
        try:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise Unresolved('output-busy', 'Another verification owns this output directory') from None
        try:
            yield
        finally:
            fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


def failure_receipt(error):
    receipt = initial_receipt()
    receipt['obligations'].append({'code': getattr(error, 'code', 'unsupported-input'), 'detail': str(error)})
    return receipt


def verify(args):
    try:
        with output_ownership(args.output.resolve()):
            return verify_owned(args)
    except (ValueError, OSError) as error:
        # A contender must not publish into the current owner's evidence directory.
        return failure_receipt(error)


def verify_owned(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    receipt = initial_receipt()
    # Invalidate any stale success before reading a new request or invoking tools.
    save_json(output / 'receipt.json', receipt)
    try:
        require(math.isfinite(args.timeout) and 0 < args.timeout <= 1200,
                'tool-budget', 'Timeout must be finite and between 0 and 1200 seconds')
        specification = read_json(args.spec)
        experiment = validate(specification)
        save_json(output / 'request.json', specification)
        receipt['request_sha256'] = digest(canonical(specification))
        receipt['model'] = specification['model']
        receipt['experiment'] = specification['experiment']
        receipt['native_descriptor'] = {'suite': SUITE, 'framing': 'zkc.framed/0',
            'relation_to_model': 'conditional ideal interpretation; concrete conformance not established'}
        common, constructed, identities = prepare_native(args, specification, output)
        receipt['subject'] = identities
        certificate = build_certificate(copy.deepcopy(common), copy.deepcopy(constructed), copy.deepcopy(specification))
        run_directory = Path(tempfile.mkdtemp(prefix='.verification-', dir=output))
        path = run_directory / 'Certificate.lean'
        path.write_text(certificate)
        path.chmod(0o444)
        receipt['invocation'] = run_directory.name
        receipt['certificate_path'] = str(path.relative_to(output))
        receipt['certificate_sha256'] = digest(certificate)
        evidence = {p: digest(p.read_bytes()) for p in [
            output / name for name in ('source.mlir', 'candidate.mlir', 'policy.json',
                                       'request.json', 'common.json', 'constructed.json')] + [path]}
        require(evidence[output / 'source.mlir'] == identities['source_sha256'] and
                evidence[output / 'candidate.mlir'] == identities['candidate_sha256'] and
                evidence[output / 'policy.json'] == identities['policy_file_sha256'],
                'evidence-changed', 'Retained native inputs changed during construction/export')
        environment = ROOT / 'integrations/arklib'
        receipt['toolchain'] = (environment / 'lean-toolchain').read_text().strip()
        receipt['dependency_manifests'] = {str(p.relative_to(ROOT)): digest(p.read_bytes())
            for p in [ROOT / 'lake-manifest.json', environment / 'lake-manifest.json']}
        imports = re.findall(r'^(?:public )?import (Zkc[^\s]*)$', certificate, flags=re.MULTILINE)
        execute([args.lake, 'build', *sorted(set(imports))], output, 'dependencies', args.timeout, environment)
        receipt['local_formal_sources'] = formal_source_closure(imports)
        receipt['bridge_implementation'] = {str(p.relative_to(ROOT)): digest(p.read_bytes())
            for directory in [HERE, ROOT / 'bridges/common'] for p in sorted(directory.glob('*.py'))}
        log = execute([args.lake, 'env', 'lean', '--json', '-DwarningAsError=true', path], output, 'lean', args.timeout, environment)
        required = ['PROOF-REQUEST-KERNEL-PASS', 'PROOF-REQUEST-BOUNDARY-PASS',
                    'FS-ACTUAL-SUBJECT-PASS', 'FS-SECURITY-CONSUMER-PASS', 'FS-TRANSITIVE-AXIOMS-PASS']
        require(all(marker in log for marker in required), 'proof-incomplete',
                'Lean did not check every actual-subject, consumer and audit layer')
        require(all(p.is_file() and digest(p.read_bytes()) == value for p, value in evidence.items()),
                'evidence-changed', 'Checked certificate or retained subject evidence changed during verification')
        # Publish a convenient copy only after checking the private proof artifact.
        public_copy = output / 'Certificate.lean.tmp'
        public_copy.write_bytes(path.read_bytes())
        public_copy.replace(output / 'Certificate.lean')
        receipt['discharged_layers'] = ['native checked source/candidate/policy construction',
            'source typed admission and independently checked source contract',
            'constructed typed admission and full actual denotation under fixed primitive meanings',
            'actual constructed observation/consumer correspondence',
            'independent exact requested source/candidate/theorem-type check',
            'transitive axiom audit of checked subject and security consumer']
        receipt['verified_properties'] = [{'property': experiment.property,
            'certificate': 'ExpectedFS.security', 'premises': list(experiment.premises),
            'query_bound': query_conclusion(specification), 'observation': experiment.observation,
            'statement': experiment.statement, 'adversary': experiment.adversary}]
        receipt['status'] = 'verified-in-model'
    except (ValueError, TypeError, KeyError, IndexError, RecursionError, OSError,
            subprocess.SubprocessError, ImportError, AttributeError) as error:
        receipt['obligations'].append({'code': getattr(error, 'code', 'unsupported-input'), 'detail': str(error)})
    save_json(output / 'receipt.json', receipt)
    return receipt


def query_conclusion(specification):
    if specification['source']['contract'] == 'schnorr.verifier/0':
        return {'quantification': 'every total prover and natural Q satisfying nmaHashQueryBound',
            'conclusion': 'a * (a / (Q + 1) - 1 / card F) <= extraction success',
            'arithmetic': 'ENNReal with truncated subtraction',
            'final_verification_queries': 1, 'extractor_fresh_challenge_bound': '2 * (Q + 1)'}
    return {'quantification': 'every adaptive full-prefix adversary and natural Q satisfying IsTotalQueryBound',
        'conclusion': 'false acceptance <= (Q + 3) * (2 / card F)',
        'arithmetic': 'ENNReal', 'reduction_queries': 1, 'verifier_completion_queries': 2}


class ReceiptArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        raise Unresolved('cli-arguments', message)


def parser():
    result = ReceiptArgumentParser(description=__doc__, allow_abbrev=False)
    result.add_argument('--spec', type=Path, required=True)
    result.add_argument('--module', action='append', default=[])
    result.add_argument('--entry')
    result.add_argument('--source', type=Path)
    result.add_argument('--policy', type=Path)
    result.add_argument('--candidate', type=Path)
    result.add_argument('--compiler', type=Path, default=ROOT.parent / 'build/compiler/zkc-compile')
    result.add_argument('--output', type=Path, required=True)
    result.add_argument('--lake', default='lake')
    result.add_argument('--timeout', type=float, default=180)
    return result


def output_locations(arguments):
    """Recognize exact output options even when another option cannot be parsed."""
    result = []
    for index, item in enumerate(arguments):
        if item == '--':
            break
        value = None
        if item.startswith('--output='):
            value = item[len('--output='):]
        elif item == '--output' and index + 1 < len(arguments):
            following = arguments[index + 1]
            if following == '-' or not following.startswith('-'):
                value = following
        if value is not None:
            path = Path(value).resolve()
            if path not in result:
                result.append(path)
    return result


def main(arguments=None):
    arguments = sys.argv[1:] if arguments is None else arguments
    if '--help' in arguments or '-h' in arguments:
        parser().print_help()
        return 0
    outputs, owned_outputs, receipt = [], [], initial_receipt()
    with ExitStack() as ownership:
        try:
            outputs = output_locations(arguments)
            for output in outputs:
                ownership.enter_context(output_ownership(output))
                owned_outputs.append(output)
            # Parse failures cannot preserve a previous success. Acquire ownership
            # first so a contender cannot invalidate an active verifier's receipt.
            for output in outputs:
                save_json(output / 'receipt.json', receipt)
            require(len(outputs) <= 1, 'cli-arguments', 'Select exactly one output destination')
            args = parser().parse_args(arguments)
        except (ValueError, OSError) as error:
            receipt = failure_receipt(error)
            if getattr(error, 'code', '') != 'output-busy':
                for output in owned_outputs:
                    try:
                        save_json(output / 'receipt.json', receipt)
                    except OSError:
                        pass  # Stdout still reports an unwritable destination.
            print(json.dumps(receipt, indent=2))
            return 2
        receipt = verify_owned(args)
        print(json.dumps(receipt, indent=2))
        return 0 if receipt['status'] == 'verified-in-model' else 1


if __name__ == '__main__':
    sys.exit(main())
