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
