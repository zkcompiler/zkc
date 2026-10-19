#!/usr/bin/env python3
"""Challenge the proof audit, Lean header parser and executable input boundary."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from support import evidence  # noqa: E402
from support.lean_headers import HeaderParser  # noqa: E402
from check_library import permitted  # noqa: E402


def main():
    rows = []
    with HeaderParser(root=ROOT, lake='lake') as headers:
        source = ('module\n/- import Wrong /- nested -/ -/\n'
                  'public import Std\nmeta import Lean\n'
                  'def text := "import Wrong"\n')
        assert headers.imports(source) == ['Std', 'Lean']
        for source in ('import\n', 'import /- unterminated', 'public import Std\n'):
            try:
                headers.imports(source)
            except ValueError:
                rows.append('malformed-header-refused')
            else:
                raise AssertionError('invalid header was accepted')
    rows.append('header-comments-and-modifiers')
    # Compile temporary modules independently. The ordinary Lean kernel accepts
    # axioms and sorry, so rejection must come from the maintained audit itself.
    with tempfile.TemporaryDirectory(prefix='zkc-audit-controls-') as temporary:
        directory = Path(temporary)
        shutil.copy2(ROOT / 'lean-toolchain', directory / 'lean-toolchain')
        audit = directory / 'ZkcTools/DeclarationAudit.lean'
        audit.parent.mkdir()
        shutil.copy2(ROOT / 'ZkcTools/DeclarationAudit.lean', audit)
        env = dict(os.environ, LEAN_PATH=str(directory))

        def compile_module(name):
            path = directory.joinpath(*name.split('.'))
            return subprocess.run(['lean', '-o', str(path.with_suffix('.olean')),
                str(path.with_suffix('.lean'))], cwd=directory, env=env,
                capture_output=True, text=True, timeout=60)

        result = compile_module('ZkcTools.DeclarationAudit')
        assert result.returncode == 0, result.stdout + result.stderr
        cases = [
            ('ordinary', 'namespace Elsewhere\ntheorem valid : True := True.intro\nend Elsewhere\n', None),
            ('unused-axiom', 'axiom Elsewhere.unused : False\n', 'unexpected owned axiom'),
            ('sorry', 'theorem Elsewhere.hole : False := by sorry\n', 'unexpected axiom'),
            ('native-evaluation', 'theorem Elsewhere.native : (1 : Nat) = 1 := by native_decide\n', 'unexpected axiom'),
            ('empty-selection', 'theorem ordinary : True := True.intro\n', 'selected no module'),
        ]
        (directory / 'Control').mkdir()
        for name, source, diagnostic in cases:
            (directory / 'Control/Subject.lean').write_text('import Lean\n' + source)
            result = compile_module('Control.Subject')
            assert result.returncode == 0, (name, result.stdout, result.stderr)
            family = 'Missing' if name == 'empty-selection' else 'Control'
            (directory / 'Audit.lean').write_text('import Control.Subject\n'
                'import ZkcTools.DeclarationAudit\n'
                f'run_cmd ZkcTools.DeclarationAudit.check [`{family}]\n')
            result = compile_module('Audit')
            if diagnostic is None:
                assert result.returncode == 0 and 'DEPENDENCY-AUDIT-PASS' in result.stdout, result
            else:
                assert result.returncode > 0 and diagnostic in result.stdout, (name, result)
                assert 'DEPENDENCY-AUDIT-PASS' not in result.stdout
            rows.append(name)
        # An audit of the current module covers every theorem written so far
        # in that module, so it can replace lists of selected theorem names.
        local_cases = [
            ('current-module-ordinary', 'theorem Local.valid : True := True.intro\n', None),
            ('current-module-sorry', 'theorem Local.valid : True := True.intro\n'
             'theorem Local.hole : False := by sorry\n', 'unexpected axiom'),
            ('current-module-native', 'theorem Local.native : (2 : Nat) = 2 := by native_decide\n',
             'unexpected axiom'),
            ('current-module-empty', 'def Local.value : Nat := 3\n', 'declares no theorem'),
        ]
        for name, source, diagnostic in local_cases:
            (directory / 'Local').mkdir(exist_ok=True)
            (directory / 'Local/Subject.lean').write_text(
                'import ZkcTools.DeclarationAudit\n' + source +
                'run_cmd ZkcTools.DeclarationAudit.checkCurrent "CURRENT-MODULE-PASS"\n')
            result = compile_module('Local.Subject')
            if diagnostic is None:
                assert result.returncode == 0 and 'CURRENT-MODULE-PASS' in result.stdout, (name, result)
            else:
                assert result.returncode > 0 and diagnostic in result.stdout, (name, result)
                assert 'CURRENT-MODULE-PASS declarations=' not in result.stdout
            rows.append(name)
        # The registry audit: every schema constant exists, a proposition schema
        # is proposition-valued, and every proposition-valued declaration of the
        # audited modules that heads a premise of one of their theorems, at any
        # binder (explicit, implicit or instance), is registered.
        (directory / 'Registry').mkdir()
        (directory / 'Registry/Subject.lean').write_text(
            'namespace Registry\n'
            'def Open (n : Nat) : Prop := n = n + 0\n'
            'class Admissible (n : Nat) : Prop where\n  holds : n = n\n'
            'def value : Nat := 3\n'
            'theorem explicit (n : Nat) (h : ∀ m, m ≤ n → Open m) : n = n := rfl\n'
            'theorem instancePremise (n : Nat) [Admissible n] : n = n := rfl\n'
            'theorem unrelated (n : Nat) (h : n = 3) : n = n := rfl\n'
            'end Registry\n')
        result = compile_module('Registry.Subject')
        assert result.returncode == 0, (result.stdout, result.stderr)
        complete = ('("registry.open", some `Registry.Open, true), '
                    '("registry.admissible", some `Registry.Admissible, true), '
                    '("registry.link", none, false)')
        registry_cases = [
            ('registry-accepted', complete, None),
            ('registry-missing-constant', complete + ', ("registry.absent", some `Registry.Absent, true)',
             'names a missing constant: Registry.Absent'),
            ('registry-unregistered-premise', '("registry.admissible", some `Registry.Admissible, true)',
             'unregistered named hypotheses'),
            ('registry-unregistered-instance-premise', '("registry.open", some `Registry.Open, true)',
             'Registry.Admissible (a premise of Registry.instancePremise)'),
            ('registry-not-proposition', complete + ', ("registry.value", some `Registry.value, true)',
             'not proposition-valued'),
            ('registry-duplicate-identifier', complete + ', ("registry.open", none, false)',
             'duplicate registry identifier'),
        ]
        for name, entries, diagnostic in registry_cases:
            (directory / 'Audit.lean').write_text('import Registry.Subject\n'
                'import ZkcTools.DeclarationAudit\n'
                f'run_cmd ZkcTools.DeclarationAudit.checkRegistry [{entries}] [`Registry] '
                '"REGISTRY-CONTROL-PASS"\n')
            result = compile_module('Audit')
            if diagnostic is None:
                assert result.returncode == 0 and 'REGISTRY-CONTROL-PASS' in result.stdout, (name, result)
                assert 'premise-heads=2 registered-premise-heads=2' in result.stdout, (name, result)
            else:
                assert result.returncode > 0 and diagnostic in result.stdout, (name, result)
                assert 'REGISTRY-CONTROL-PASS' not in result.stdout
            rows.append(name)
        # These fixtures test module ownership rather than declaration spelling.
        # Compile actual dependency bodies, then demand rejection by the auditor;
        # also keep the source-import guard in sync with the declaration policy.
        ownership_cases = [
            ('execution-protocol-body', 'ZkcSecurity.VCVio.Execution',
             'Zkc.Protocols.GuardFixture', 'body', False),
            ('execution-source-type', 'ZkcSecurity.VCVio.Execution',
             'Zkc.Source.GuardFixture', 'type', False),
            ('execution-example-body', 'ZkcSecurity.VCVio.Execution',
             'ZkcSecurity.Examples.GuardFixture', 'body', False),
            ('execution-arklib-body', 'ZkcSecurity.VCVio.Execution',
             'ZkcSecurity.ArkLib.GuardFixture', 'body', False),
            ('execution-upstream-arklib-body', 'ZkcSecurity.VCVio.Execution',
             'ArkLib.GuardFixture', 'body', False),
            ('causal-example-body', 'ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.Completion',
             'ZkcSecurity.Examples.GuardFixture', 'body', False),
            ('causal-source-type', 'ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.Phase',
             'Zkc.Source.GuardFixture', 'type', False),
            ('schnorr-protocol-allowed', 'ZkcSecurity.VCVio.Schnorr',
             'Zkc.Protocols.Schnorr.Common', 'body', True),
            ('execution-semantics-allowed', 'ZkcSecurity.VCVio.Execution',
             'Zkc.Semantics.GuardFixture', 'body', True),
            ('causal-protocol-allowed', 'ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal.Soundness',
             'Zkc.Protocols.GuardFixture', 'body', True),
        ]
        for name, owner, dependency, kind, allowed in ownership_cases:
            assert permitted(owner, dependency) == allowed, name
            path = directory.joinpath(*dependency.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('namespace GuardFixture\ndef value : Nat := 7\n'
                            'structure Token where\n  value : Nat\nend GuardFixture\n')
            result = compile_module(dependency)
            assert result.returncode == 0, (name, result.stdout, result.stderr)
            path = directory.joinpath(*owner.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            body = ('def Elsewhere.leaked : Nat := GuardFixture.value\n' if kind == 'body'
                    else 'def Elsewhere.leaked (value : GuardFixture.Token) := value\n')
            path.write_text(f'import {dependency}\n' + body)
            result = compile_module(owner)
            assert result.returncode == 0, (name, result.stdout, result.stderr)
            (directory / 'Audit.lean').write_text(f'import {owner}\n'
                'import ZkcTools.DeclarationAudit\n'
                f'run_cmd ZkcTools.DeclarationAudit.check [`{owner}] "OWNER-GUARD-PASS" true\n')
            result = compile_module('Audit')
            if allowed:
                assert result.returncode == 0 and 'OWNER-GUARD-PASS' in result.stdout, (name, result)
            else:
                assert result.returncode > 0 and f'forbidden {kind} dependency' in result.stdout, (name, result)
                assert 'OWNER-GUARD-PASS' not in result.stdout
            rows.append(name)
        executable = ROOT / '.lake/build/bin/common-source'

        def invoke(name, arguments, expected):
            result = subprocess.run([str(executable), *map(str, arguments)],
                                    capture_output=True, text=True, timeout=10)
            assert result.returncode == 1 and not result.stderr, (name, result)
            assert json.loads(result.stdout) == {'status': 'refused', 'code': expected}, (name, result)
            rows.append(name)

        invoke('arity', [], 'common-source-arguments')
        invoke('missing-file', ['check', directory / 'missing.json'], 'common-source-io')
        for name, raw, diagnostic in [
            ('invalid-utf8', b'[\xff]', 'invalid-utf8'),
            ('byte-limit', b' ' * (1024 * 1024 + 1), 'byte-limit'),
            ('large-number', b'[' + b'9' * 1025 + b']', 'number-limit'),
        ]:
            path = directory / (name + '.json')
            path.write_bytes(raw)
            invoke(name, ['check', path], diagnostic)
    output = evidence.records('enforcement', '.json')
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {'status': 'pass', 'cases': rows}
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
