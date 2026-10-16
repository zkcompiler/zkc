#!/usr/bin/env python3
"""End-to-end positive and false-receipt controls for constructed FS verification.

Run after building the optional security imports. Evidence (retained native inputs,
certificates, process logs and receipts) stays in --output, including failures.
Test-only fault injection targets generator proposals and tool responses; no such
hooks, Lean source strings or theorem selections are accepted by the public CLI.
"""
import argparse
import copy
import json
import re
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch
import verification as driver


def options(args, protocol, variant, name):
    module = protocol + '_forms'
    return driver.parser().parse_args([
        '--spec', str(driver.HERE / 'requests' / (protocol + '.json')),
        '--module', f'{module}={driver.ROOT / "bridges/common/fixtures" / (protocol + "-forms.zkc")}',
        '--entry', f'{module}::{variant}', '--compiler', str(args.compiler),
        '--output', str(args.output / name), '--lake', args.lake, '--timeout', str(args.timeout)])


def checked(args, label, selected, positive=False):
    receipt = driver.verify(selected)
    expected = 'verified-in-model' if positive else 'unresolved'
    if receipt['status'] != expected or (not positive and receipt['verified_properties']):
        raise AssertionError(f'{label}: false/missing receipt: {receipt}')
    if positive and (len(receipt['discharged_layers']) != 6 or not receipt['verified_properties']):
        raise AssertionError(f'{label}: incomplete positive receipt')
    if positive:
        protocol = driver.read_json(selected.spec)['source']['contract']
        claim = ('ZkcSecurity.VCVio.Schnorr.FiatShamir.extractionProperty'
                 if protocol == 'schnorr.verifier/0' else
                 'ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Native.soundnessProperty')
        prop = receipt['verified_properties'][0]
        if prop.get('claim') != claim or not prop.get('initialization', '').startswith('one empty oracle cache, shared by'):
            raise AssertionError(f'{label}: missing fixed claim or initial-state scope')
    if label != 'proof-timeout' and any(
            obligation['code'] == 'tool-timeout' for obligation in receipt['obligations']):
        raise AssertionError(f'{label}: an unexpected timeout is not evidence of proof refusal')
    persisted = driver.read_json(selected.output / 'receipt.json')
    if persisted != receipt:
        raise AssertionError(f'{label}: persisted receipt differs')
    result = {'case': label, 'status': receipt['status'],
              'obligations': receipt['obligations'], 'receipt': str(selected.output / 'receipt.json')}
    args.results.append(result)
    driver.save_json(args.output / 'results.json', args.results)
    print(label + ': ' + expected, flush=True)
    return selected


def mutate_request(args, label, change, protocol='schnorr', code=None):
    selected = options(args, protocol, 'Helpers', label)
    request = driver.read_json(selected.spec)
    change(request)
    path = args.output / (label + '.json')
    driver.save_json(path, request)
    selected.spec = path
    checked(args, label, selected)
    if code is not None:
        codes = [item['code'] for item in driver.read_json(selected.output / 'receipt.json')['obligations']]
        if codes != [code]:
            raise AssertionError(f'{label}: expected {code}, received {codes}')


def claim_controls(args):
    """Generated proofs cannot weaken either family's independently fixed claim."""
    for protocol, method in [('schnorr', 'schnorr_subject'), ('sumcheck', 'sumcheck_subject')]:
        original = getattr(driver, method)
        def wrong_property(namespace, expected=False):
            text = original(namespace, expected)
            if expected:
                return text
            start = text.index('    (_root_.ZkcSecurity.', text.index('theorem security '))
            end = text.index('\nend ', start)
            weakened = text[:start] + '    True := by\n  have _ := queryBound\n  trivial\n' + text[end:]
            # The weaker theorem must elaborate so the independent expected
            # type rejects it. An unused-variable warning is not that evidence.
            return weakened.replace('theorem security ',
                'set_option linter.unusedSectionVars false in\ntheorem security ', 1)
        label = protocol + '-wrong-proved-property'
        with patch.object(driver, method, wrong_property):
            proof_refused(args, label, options(args, protocol, 'Helpers', label),
                          expected_fragment='GeneratedFS.security')
    original = driver.sumcheck_subject
    def wrong_budget(namespace, expected=False):
        text = original(namespace, expected)
        if expected:
            return text
        text = text.replace('(Q + 2) := ', '(Q + 3) := ', 1)
        return text.replace(
            '  game_queryBound snapshot.source snapshot.candidate schedule subject denotation adversary Q queryBound',
            '  (game_queryBound snapshot.source snapshot.candidate schedule subject denotation adversary Q queryBound).mono (by omega)', 1)
    with patch.object(driver, 'sumcheck_subject', wrong_budget):
        proof_refused(args, 'sumcheck-weaker-budget', options(args, 'sumcheck', 'Helpers', 'sumcheck-weaker-budget'),
                      expected_fragment='GeneratedFS.query_cost')
    def false_budget_alias(namespace, expected=False):
        text = original(namespace, expected)
        if expected:
            return text
        alias = '''
set_option linter.unusedSectionVars false in
def IsTotalQueryBound {ι α : Type} {spec : _root_.OracleSpec ι}
    (_ : _root_.OracleComp spec α) (_ : Nat) : Prop := False
'''
        text = text.replace('theorem query_cost ', alias + '\ntheorem query_cost ', 1)
        text = text.replace('_root_.OracleComp.IsTotalQueryBound', 'IsTotalQueryBound')
        text = text.replace(
            '  game_queryBound snapshot.source snapshot.candidate schedule subject denotation adversary Q queryBound',
            '  False.elim queryBound', 1)
        text = text.replace(
            '  soundness snapshot.source snapshot.candidate schedule subject denotation adversary Q queryBound',
            '  False.elim queryBound', 1)
        for theorem in ('query_cost', 'security'):
            text = text.replace('theorem ' + theorem + ' ',
                'set_option linter.unusedSectionVars false in\ntheorem ' + theorem + ' ', 1)
        return text + '\nnamespace ExpectedFS\n' + alias + '\nend ExpectedFS\n'
    with patch.object(driver, 'sumcheck_subject', false_budget_alias):
        proof_refused(args, 'sumcheck-false-budget-alias',
                      options(args, 'sumcheck', 'Helpers', 'sumcheck-false-budget-alias'),
                      expected_fragment='GeneratedFS.query_cost')
    mutate_request(args, 'sumcheck-wrong-experiment',
                   lambda r: r.update(experiment='fs.schnorr.fixed-statement-cached-ro/0'), 'sumcheck',
                   code='fs-property-mismatch')
    mutate_request(args, 'sumcheck-supplied-initial-state',
                   lambda r: r.update(initialization='adversarial-prepopulated-cache'), 'sumcheck',
                   code='fs-request-shape')


def proof_refused(args, label, selected, expected_fragment=None):
    """A proof mutation must reach Lean and fail checking, not exhaust the tool."""
    checked(args, label, selected)
    receipt = driver.read_json(selected.output / 'receipt.json')
    log = selected.output / 'lean.log'
    expected = [{'code': 'tool-failed', 'detail': 'lean failed; inspect lean.log'}]
    text = log.read_text() if log.exists() else ''
    resource_errors = ('(deterministic) timeout', 'maximum recursion depth',
                       'maximum memory', 'deep recursion detected')
    diagnostics = []
    for line in text.splitlines():
        try:
            diagnostics.append(json.loads(line))
        except ValueError:
            pass
    ordinary_error = any(isinstance(item, dict) and item.get('severity') == 'error'
                         for item in diagnostics)
    if (receipt['obligations'] != expected or not ordinary_error or
            any(error in text for error in resource_errors)):
        raise AssertionError(label + ': missing ordinary Lean proof refusal')
    def independent_mismatch(item):
        if not isinstance(item, dict) or item.get('severity') != 'error':
            return False
        message = str(item.get('data', item.get('message', '')))
        if expected_fragment not in message or 'type mismatch' not in message.lower():
            return False
        source = Path(item['fileName']).read_text().splitlines(keepends=True)
        prefix = ''.join(source[:item['pos']['line']])
        return prefix.rfind('namespace ExpectedFS\n') > prefix.rfind('end ExpectedFS\n')
    if expected_fragment is not None:
        first_error = next((item for item in diagnostics if isinstance(item, dict) and
                            item.get('severity') == 'error'), None)
        if not independent_mismatch(first_error):
            raise AssertionError(label + ': first error was not the independent theorem-type check')


def proposal_control(args, label, protocol, transform):
    """Only the proposal changes; independent expected subject is reconstructed intact."""
    selected = options(args, protocol, 'Helpers', label)
    with driver.CONSTRUCTED.load('realization') as realization:
        original = realization.render
        def altered(data, *rest):
            source = original(data, *rest)
            changed = transform(source)
            if changed == source:
                raise AssertionError('proposal mutation did not change the certificate: ' + label)
            return changed
        with patch.object(realization, 'render', altered):
            proof_refused(args, label, selected)


def retained(args, label, source):
    selected = options(args, 'schnorr', 'Helpers', label)
    selected.module, selected.entry = [], None
    selected.source, selected.policy = source / 'source.mlir', source / 'policy.json'
    selected.candidate = source / 'candidate.mlir'
    return selected


def state_control(args, label):
    selected = options(args, 'sumcheck', 'Helpers', label)
    with driver.CONSTRUCTED.load('realization') as realization:
        original = realization.render
        def altered(data, *rest):
            # Reuse the live state before challenge 0 at challenge 1. The operand
            # is still a well-typed transcript, but lacks the delivered predecessor.
            changed = copy.deepcopy(data)
            produced, prior_state, queries = 0, None, 0
            for instruction in changed[10]:
                if instruction[0] == 'apply' and instruction[1][0] == 'crypto.exec.indexed_transcript_challenge':
                    queries += 1
                    if queries == 1:
                        prior_state = produced - instruction[2][0]
                    else:
                        instruction[2][0] = produced - prior_state
                if instruction[0] in ('apply', 'project'):
                    produced += 1
            if queries != 2:
                raise AssertionError('predecessor state mutation did not apply')
            return original(changed, *rest)
        with patch.object(realization, 'render', altered):
            proof_refused(args, label, selected)


def cli_failures(args, base):
    """Exercise argument errors through the public process entry, with real success as seed."""
    for label, invalid in [('invalid-timeout-argument', ['--timeout', 'invalid']),
                           ('unknown-cli-option', ['--unknown-security-property'])]:
        output = args.output / label
        output.mkdir(parents=True, exist_ok=True)
        driver.save_json(output / 'receipt.json', driver.read_json(base / 'receipt.json'))
        command = [sys.executable, str(driver.HERE / 'verification.py'), '--output', str(output),
                   '--spec', str(driver.HERE / 'requests/schnorr.json'), *invalid]
        run = subprocess.run(command, text=True, capture_output=True, timeout=30)
        (output / 'invocation.log').write_text(run.stdout + run.stderr)
        driver.save_json(output / 'invocation.command.json', command)
        receipt = driver.read_json(output / 'receipt.json')
        if run.returncode != 2 or receipt['status'] != 'unresolved' or receipt['verified_properties']:
            raise AssertionError(label + ': argument error preserved success')
        if receipt['obligations'][0]['code'] != 'cli-arguments':
            raise AssertionError(label + ': missing argument diagnostic')
        args.results.append({'case': label, 'status': 'unresolved',
                             'obligations': receipt['obligations'], 'receipt': str(output / 'receipt.json')})
        driver.save_json(args.output / 'results.json', args.results)
        print(label + ': unresolved', flush=True)


def concurrency_control(args, base):
    label = 'concurrent-output-reuse'
    output = args.output / label
    with driver.output_ownership(output):
        original = driver.read_json(base / 'receipt.json')
        driver.save_json(output / 'receipt.json', original)
        command = [sys.executable, str(driver.HERE / 'verification.py'), '--output', str(output),
                   '--spec', str(driver.HERE / 'requests/schnorr.json')]
        run = subprocess.run(command, text=True, capture_output=True, timeout=30)
        reply = driver.decode_json(run.stdout)
        if run.returncode != 2 or reply['status'] != 'unresolved' or reply['verified_properties']:
            raise AssertionError('concurrent writer did not refuse')
        if reply['obligations'][0]['code'] != 'output-busy':
            raise AssertionError('missing output ownership diagnostic')
        if driver.read_json(output / 'receipt.json') != original:
            raise AssertionError('contender changed the active owner receipt')
    response = output / 'contender-response.json'
    driver.save_json(response, reply)
    driver.save_json(output / 'invocation.command.json', command)
    args.results.append({'case': label, 'status': 'unresolved',
                         'obligations': reply['obligations'], 'receipt': str(response)})
    driver.save_json(args.output / 'results.json', args.results)
    print(label + ': unresolved', flush=True)


def certificate_race_control(args, alternate):
    # Real Lean checks a different, independently successful full certificate.
    # A writer that ignores the output lock still cannot publish a mismatched receipt.
    selected = options(args, 'schnorr', 'Helpers', 'certificate-replaced-before-lean')
    original_execute = driver.execute
    def replace(command, directory, label, timeout, cwd=None):
        if label == 'lean':
            path = Path(command[-1])
            path.chmod(0o644)
            path.write_bytes((alternate / 'Certificate.lean').read_bytes())
        return original_execute(command, directory, label, timeout, cwd)
    with patch.object(driver, 'execute', replace):
        checked(args, 'certificate-replaced-before-lean', selected)
    receipt = driver.read_json(selected.output / 'receipt.json')
    if receipt['obligations'][0]['code'] != 'evidence-changed':
        raise AssertionError('race control did not reach the checked-bytes boundary')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--timeout', type=float, default=240)
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    args.results = []
    positives = {}
    for protocol, variant in [('schnorr', 'Helpers'), ('schnorr', 'Reordered'),
                              ('sumcheck', 'Helpers'), ('sumcheck', 'Horner')]:
        label = protocol + '-' + variant.lower()
        positives[label] = checked(args, label, options(args, protocol, variant, label), positive=True)
    base = positives['schnorr-helpers'].output
    cli_failures(args, base)
    concurrency_control(args, base)
    certificate_race_control(args, positives['schnorr-reordered'].output)
    positives['retained-explicit-candidate'] = checked(args, 'retained-explicit-candidate',
        retained(args, 'retained-explicit-candidate', base), positive=True)

    mutate_request(args, 'unsupported-model', lambda r: r.update(model='merlin-concrete/0'))
    mutate_request(args, 'unknown-version', lambda r: r.update(format='zkc.fs-verification-spec/1'))
    mutate_request(args, 'wrong-property', lambda r: r.update(properties=['perfect-completeness']))
    mutate_request(args, 'wrong-experiment', lambda r: r.update(experiment='fs.sumcheck.full-prefix-cached-ro/0'))
    mutate_request(args, 'request-proof-code', lambda r: r.update(theorem='True.intro'))
    mutate_request(args, 'unknown-source-field', lambda r: r['source'].update(tactic='rfl'))
    duplicate = args.output / 'duplicate.json'
    duplicate.write_text('{"format":"zkc.fs-verification-spec/0","format":"zkc.fs-verification-spec/0"}')
    selected = options(args, 'schnorr', 'Helpers', 'duplicate-json-members')
    selected.spec = duplicate
    checked(args, 'duplicate-json-members', selected)

    selected = options(args, 'schnorr', 'EarlyChallenge', 'wrong-protocol-shape')
    checked(args, 'wrong-protocol-shape', selected)
    selected = options(args, 'schnorr', 'Helpers', 'wrong-source-arithmetic')
    fixture = driver.ROOT / 'bridges/common/fixtures/schnorr-forms.zkc'
    wrong = args.output / 'wrong-arithmetic.zkc'
    original = fixture.read_text()
    changed = original.replace('base * answer == commitment + point * challenge',
                               'base * answer == commitment + base * challenge', 1)
    if changed == original:
        raise AssertionError('arithmetic mutation did not apply')
    wrong.write_text(changed)
    selected.module = ['schnorr_forms=' + str(wrong)]
    checked(args, 'wrong-source-arithmetic', selected)

    selected = retained(args, 'weak-statement-binding', base)
    policy = driver.read_json(selected.policy)
    policy[7] = ['0']
    selected.policy = args.output / 'weak-policy.json'
    driver.save_json(selected.policy, policy)
    checked(args, 'weak-statement-binding', selected)

    selected = retained(args, 'same-typed-native-candidate-substitution', base)
    selected.candidate = positives['schnorr-reordered'].output / 'candidate.mlir'
    checked(args, 'same-typed-native-candidate-substitution', selected)
    selected = retained(args, 'altered-native-handler', base)
    candidate = selected.candidate.read_text()
    changed = candidate.replace('transcript.native.indexed.challenge', 'transcript.native.indexed.observe.data', 1)
    if changed == candidate:
        raise AssertionError('native handler mutation did not apply')
    selected.candidate = args.output / 'altered-handler.mlir'
    selected.candidate.write_text(changed)
    checked(args, 'altered-native-handler', selected)

    # Tool/export authority controls use actual native outputs as detached responses.
    original_execute = driver.execute
    def detached(command, directory, label, timeout, cwd=None):
        if label == 'source-export':
            return (positives['schnorr-reordered'].output / 'source-export.log').read_text()
        return original_execute(command, directory, label, timeout, cwd)
    with patch.object(driver, 'execute', detached):
        checked(args, 'stale-source-export', options(args, 'schnorr', 'Helpers', 'stale-source-export'))

    def detached_constructed(command, directory, label, timeout, cwd=None):
        if label == 'constructed-export':
            return (positives['schnorr-reordered'].output / 'constructed-export.log').read_text()
        return original_execute(command, directory, label, timeout, cwd)
    with patch.object(driver, 'execute', detached_constructed):
        checked(args, 'stale-constructed-export', options(args, 'schnorr', 'Helpers', 'stale-constructed-export'))

    def failed_proof(command, directory, label, timeout, cwd=None):
        if label == 'lean':
            return original_execute(['/bin/false'], directory, label, timeout, cwd)
        return original_execute(command, directory, label, timeout, cwd)
    with patch.object(driver, 'execute', failed_proof):
        checked(args, 'proof-tool-failure', options(args, 'schnorr', 'Helpers', 'proof-tool-failure'))
    def timed_out(command, directory, label, timeout, cwd=None):
        if label == 'lean':
            return original_execute(['/bin/sleep', '10'], directory, label, 0.02, cwd)
        return original_execute(command, directory, label, timeout, cwd)
    with patch.object(driver, 'execute', timed_out):
        checked(args, 'proof-timeout', options(args, 'schnorr', 'Helpers', 'proof-timeout'))
    # Reuse a previously successful evidence directory; stale success must disappear.
    stale = retained(args, 'stale-success', base)
    stale.output.mkdir(parents=True, exist_ok=True)
    driver.save_json(stale.output / 'receipt.json',
                     driver.read_json(positives['retained-explicit-candidate'].output / 'receipt.json'))
    stale.spec = duplicate
    checked(args, 'stale-success', stale)

    def replace_once(old, new):
        def change(text):
            if old not in text:
                raise AssertionError('proposal mutation did not apply: ' + old)
            return text.replace(old, new, 1)
        return change
    proposal_control(args, 'candidate-forged-alias', 'schnorr',
        replace_once('def imported : Imported snapshot := ⟨program⟩',
                     'def imported : Imported snapshot := ⟨.stop .reject⟩'))
    proposal_control(args, 'missing-correspondence', 'schnorr',
        replace_once('theorem full_denotation ', 'theorem unrelated_denotation '))
    proposal_control(args, 'same-typed-constructed-substitution', 'schnorr',
        lambda text: re.sub(r'candidate := "sha256:[0-9a-f]{64}"',
                           'candidate := "sha256:' + '0' * 64 + '"', text, count=1))
    with driver.COMMON.load('verify') as common:
        original_render = common.render_certificate
        def substitute_source(data, request, proposal):
            changed = copy.deepcopy(data)
            changed[1] = 'sha256:' + '0' * 64
            return original_render(changed, request, proposal)
        with patch.object(common, 'render_certificate', substitute_source):
            proof_refused(args, 'same-typed-source-substitution',
                    options(args, 'schnorr', 'Helpers', 'same-typed-source-substitution'))
    claim_controls(args)
    proposal_control(args, 'wrong-returned-state', 'schnorr',
        replace_once('some challenge, true, some proof.2', 'some challenge, false, some proof.2'))
    state_control(args, 'dropped-predecessor-challenge')
    print(f'{len(args.results)} receipt controls passed; evidence: {args.output}', flush=True)


if __name__ == '__main__':
    main()
