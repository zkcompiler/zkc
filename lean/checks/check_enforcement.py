#!/usr/bin/env python3
"""Challenge the proof audit, Lean header parser and executable input boundary."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from support.invocation import command as lean_command  # noqa: E402
from support.packages import module_package, module_path  # noqa: E402
from support import evidence  # noqa: E402
from support.lean_headers import HeaderParser  # noqa: E402
from check_library import permitted  # noqa: E402
from support.dependencies import POLICY, audit_graph, exceptions  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--policy-only', action='store_true',
                        help='check headers, stored declarations and policy parity without executable input controls')
    args = parser.parse_args()
    rows = []
    with HeaderParser(root=ROOT, lake='lake') as headers:
        source = ('module\n/- import Wrong /- nested -/ -/\n'
                  'public import Std\nmeta import Lean\n'
                  'def text := "import Wrong"\n')
        if not (headers.imports(source) == ['Std', 'Lean']):
            raise AssertionError("checks/check_enforcement.py:25: headers.imports(source) == ['Std', 'Lean']")
        if headers.details(source) != [
                {'module': 'Std', 'public': True, 'meta': False, 'all': False},
                {'module': 'Lean', 'public': False, 'meta': True, 'all': False}]:
            raise AssertionError('header visibility or phase was lost')
        for source in ('import\n', 'import /- unterminated', 'public import Std\n'):
            try:
                headers.imports(source)
            except ValueError:
                rows.append('malformed-header-refused')
            else:
                raise AssertionError('invalid header was accepted')
        # Parse a real new violating import with Lean's header parser, then run
        # the same graph audit used for maintained source packages.
        graph = {'Zkc.IR.Source.NewClient': headers.imports(
            'module\npublic import Zkc.Protocol.Library.Mathematics.Probability.UniformTape\n')}
        try:
            audit_graph(graph, ['Zkc.IR.Source'])
        except ValueError as error:
            if 'forbidden dependency (deterministic-program-probability-boundary)' not in str(error):
                raise AssertionError(error)
            rows.append('new-violating-import-refused')
        else:
            raise AssertionError('new violating import was accepted')
    rows.append('header-comments-and-modifiers')
    # Compile temporary modules independently. The ordinary Lean kernel accepts
    # axioms and sorry, so rejection must come from the maintained audit itself.
    with tempfile.TemporaryDirectory(prefix='zkc-audit-controls-') as temporary:
        directory = Path(temporary)
        shutil.copy2(ROOT / 'lean-toolchain', directory / 'lean-toolchain')
        audit = directory / 'Zkc/Tools/Program/DeclarationAudit.lean'
        audit.parent.mkdir(parents=True)
        shutil.copy2(module_path('Zkc.Tools.Program.DeclarationAudit'), audit)
        env = dict(os.environ, LEAN_PATH=str(directory))

        def compile_module(name):
            path = directory.joinpath(*name.split('.'))
            # These controls deliberately compile sorry/unused hypotheses;
            # the declaration auditor must issue the refusal being tested.
            return subprocess.run([*lean_command(module_package("Zkc.Program")),
                '-DwarningAsError=false', '-DautoImplicit=true', '-o', str(path.with_suffix('.olean')),
                str(path.with_suffix('.lean'))], cwd=directory, env=env,
                capture_output=True, text=True, timeout=60)

        result = compile_module('Zkc.Tools.Program.DeclarationAudit')
        if not (result.returncode == 0):
            raise AssertionError(result.stdout + result.stderr)
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
            if not (result.returncode == 0):
                raise AssertionError((name, result.stdout, result.stderr))
            family = 'Missing' if name == 'empty-selection' else 'Control'
            (directory / 'Audit.lean').write_text('import Control.Subject\n'
                'import Zkc.Tools.Program.DeclarationAudit\n'
                f'run_cmd ZkcTools.DeclarationAudit.check [`{family}]\n')
            result = compile_module('Audit')
            if diagnostic is None:
                if not (result.returncode == 0 and 'DEPENDENCY-AUDIT-PASS' in result.stdout):
                    raise AssertionError(result)
            else:
                if not (result.returncode > 0 and diagnostic in result.stdout):
                    raise AssertionError((name, result))
                if not ('DEPENDENCY-AUDIT-PASS' not in result.stdout):
                    raise AssertionError("checks/check_enforcement.py:84: 'DEPENDENCY-AUDIT-PASS' not in result.stdout")
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
                'import Zkc.Tools.Program.DeclarationAudit\n' + source +
                'run_cmd ZkcTools.DeclarationAudit.checkCurrent "CURRENT-MODULE-PASS"\n')
            result = compile_module('Local.Subject')
            if diagnostic is None:
                if not (result.returncode == 0 and 'CURRENT-MODULE-PASS' in result.stdout):
                    raise AssertionError((name, result))
            else:
                if not (result.returncode > 0 and diagnostic in result.stdout):
                    raise AssertionError((name, result))
                if not ('CURRENT-MODULE-PASS declarations=' not in result.stdout):
                    raise AssertionError("checks/check_enforcement.py:106: 'CURRENT-MODULE-PASS declarations=' not in result.stdout")
            rows.append(name)
        # The upstream boundary of a package: the library declarations its
        # declarations name directly, and explicitly named ones, exist and have
        # clean closures.
        (directory / 'Upstream').mkdir()
        (directory / 'Upstream/Library.lean').write_text(
            'namespace Library\n'
            'theorem clean : True := True.intro\n'
            'theorem holed : True := by sorry\n'
            'theorem unused : True := True.intro\n'
            'end Library\n')
        result = compile_module('Upstream.Library')
        if not (result.returncode == 0):
            raise AssertionError((result.stdout, result.stderr))
        boundary_cases = [
            ('boundary-accepted', 'theorem Owner.uses : True := Library.clean\n', '[`Library.unused]', None),
            ('boundary-sorry', 'theorem Owner.uses : True := Library.holed\n', '[]',
             'upstream Library.holed depends on sorryAx'),
            ('boundary-missing-named', 'theorem Owner.uses : True := Library.clean\n', '[`Library.absent]',
             'named upstream declaration is missing'),
            ('boundary-empty', 'theorem Owner.uses : True := True.intro\n', '[]',
             'name no declaration below'),
        ]
        for name, source, named, diagnostic in boundary_cases:
            (directory / 'Owner').mkdir(exist_ok=True)
            (directory / 'Owner/Subject.lean').write_text('import Upstream.Library\n' + source)
            result = compile_module('Owner.Subject')
            if not (result.returncode == 0):
                raise AssertionError((name, result.stdout, result.stderr))
            (directory / 'Audit.lean').write_text('import Owner.Subject\n'
                'import Zkc.Tools.Program.DeclarationAudit\n'
                f'run_cmd ZkcTools.DeclarationAudit.checkBoundary [`Owner] [`Upstream] {named} '
                '"BOUNDARY-CONTROL-PASS"\n')
            result = compile_module('Audit')
            if diagnostic is None:
                if not (result.returncode == 0 and 'BOUNDARY-CONTROL-PASS boundary=2' in result.stdout):
                    raise AssertionError((name, result))
            else:
                if not (result.returncode > 0 and diagnostic in result.stdout):
                    raise AssertionError((name, result))
                if not ('BOUNDARY-CONTROL-PASS boundary=' not in result.stdout):
                    raise AssertionError("checks/check_enforcement.py:143: 'BOUNDARY-CONTROL-PASS boundary=' not in result.stdout")
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
        if not (result.returncode == 0):
            raise AssertionError((result.stdout, result.stderr))
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
            ('registry-duplicate-schema', complete + ', ("registry.second-open", some `Registry.Open, true)',
             'duplicate registry schema: Registry.Open'),
        ]
        for name, entries, diagnostic in registry_cases:
            (directory / 'Audit.lean').write_text('import Registry.Subject\n'
                'import Zkc.Tools.Program.DeclarationAudit\n'
                f'run_cmd ZkcTools.DeclarationAudit.checkRegistry [{entries}] [`Registry] '
                '"REGISTRY-CONTROL-PASS"\n')
            result = compile_module('Audit')
            if diagnostic is None:
                if not (result.returncode == 0 and 'REGISTRY-CONTROL-PASS' in result.stdout):
                    raise AssertionError((name, result))
                if 'premise-heads=2 registered-premise-heads=2' not in result.stdout:
                    raise AssertionError((name, result))
            else:
                if not (result.returncode > 0 and diagnostic in result.stdout):
                    raise AssertionError((name, result))
                if not ('REGISTRY-CONTROL-PASS' not in result.stdout):
                    raise AssertionError("checks/check_enforcement.py:188: 'REGISTRY-CONTROL-PASS' not in result.stdout")
            rows.append(name)
        # These fixtures test module ownership rather than declaration spelling.
        # Compile actual dependency bodies, then demand rejection by the auditor;
        # also keep the source-import guard in sync with the declaration policy.
        ownership_cases = [
            ('client-own-helper', 'Client.GuardFixture', 'Client.Helper', 'body', True),
            ('program-client-refused', 'Zkc.Program.GuardFixture', 'Client.Helper', 'body', False),
            ('program-core-body', 'Zkc.Program.GuardFixture',
             'Zkc.IR.Source.GuardFixture', 'body', False),
            ('program-proof-type', 'Zkc.Program.GuardFixture',
             'Zkc.Protocol.Claims.GuardFixture', 'type', False),
            ('program-mathlib-body', 'Zkc.Program.Execution',
             'Mathlib.GuardFixture', 'body', False),
            ('core-proof-body', 'Zkc.IR.Source.GuardFixture',
             'Zkc.Protocol.Claims.GuardFixture', 'body', False),
            ('proof-core-type', 'Zkc.Protocol.Claims.GuardFixture',
             'Zkc.IR.Source.GuardFixture', 'type', False),
            ('proof-subject-body', 'Zkc.Protocol.Claims.GuardFixture',
             'Zkc.Applications.Security.GuardFixture', 'body', False),
            ('core-program-allowed', 'Zkc.IR.Source.GuardFixture',
             'Zkc.Program.GuardFixture', 'body', True),
            ('proof-program-allowed', 'Zkc.Protocol.Claims.GuardFixture',
             'Zkc.Program.GuardFixture', 'type', True),
            ('reusable-tools-example', 'Zkc.Tools.Verification.GuardFixture',
             'Zkc.Applications.Security.GuardFixture', 'body', False),
            ('reusable-binding-example', 'Zkc.Verification.Bindings.GuardFixture',
             'Zkc.Applications.Security.GuardFixture', 'type', False),
            ('family-binding', 'Zkc.Verification.Families.GuardFixture',
             'Zkc.Verification.Bindings.GuardFixture', 'body', False),
            ('security-upstream-arklib', 'Zkc.Verification.GuardFixture',
             'ArkLib.GuardFixture', 'body', False),
            ('security-optional-adapter', 'Zkc.Verification.GuardFixture',
             'Zkc.Adapters.ArkLib.GuardFixture', 'type', False),
            ('security-vcvio-example-provider', 'Zkc.Verification.Families.GuardFixture',
             'VCVio.Schemes.Schnorr.SigmaProtocol', 'body', True),
            ('core-probability-body', 'Zkc.IR.Source.GuardFixture',
             'Zkc.Protocol.Library.Mathematics.Probability.GuardFixture', 'body', False),
            ('probability-source-type', 'Zkc.Protocol.Library.Mathematics.Probability.GuardFixture',
             'Zkc.IR.Source.GuardFixture', 'type', False),
            ('security-example-type', 'Zkc.Verification.Bindings.Source.GuardFixture',
             'Zkc.Applications.Security.GuardFixture', 'type', False),
            ('clean-example-test-body', 'Zkc.Applications.Clean.GuardFixture',
             'Zkc.Tests.Applications.Clean.GuardFixture', 'body', False),
            ('family-probability-rejected', 'Zkc.Protocol.Library.Sumcheck.Verifier',
             'Zkc.Protocol.Library.Mathematics.Probability.UniformTape', 'body', False),
            ('execution-protocol-body', 'Zkc.Protocol.Logic.Oracle.Execution',
             'Zkc.Protocol.Library.GuardFixture', 'body', False),
            ('execution-source-type', 'Zkc.Protocol.Logic.Oracle.Execution',
             'Zkc.IR.Source.GuardFixture', 'type', False),
            ('execution-example-body', 'Zkc.Protocol.Logic.Oracle.Execution',
             'Zkc.Applications.Security.GuardFixture', 'body', False),
            ('execution-arklib-body', 'Zkc.Protocol.Logic.Oracle.Execution',
             'Zkc.Adapters.ArkLib.GuardFixture', 'body', False),
            ('execution-upstream-arklib-body', 'Zkc.Protocol.Logic.Oracle.Execution',
             'ArkLib.GuardFixture', 'body', False),
            ('causal-example-body', 'Zkc.Adapters.ArkLib.Sumcheck.Multilinear.Causal.Completion',
             'Zkc.Applications.Security.GuardFixture', 'body', False),
            ('causal-source-type', 'Zkc.Adapters.ArkLib.Sumcheck.Multilinear.Causal.Phase',
             'Zkc.IR.Source.GuardFixture', 'type', False),
            ('execution-semantics-allowed', 'Zkc.Protocol.Logic.Oracle.Execution',
             'Zkc.Program.Semantics.GuardFixture', 'body', True),
            ('causal-protocol-allowed', 'Zkc.Adapters.ArkLib.Sumcheck.Multilinear.Causal.Soundness',
             'Zkc.Protocol.Library.GuardFixture', 'body', True),
        ]
        for name, owner, dependency, kind, allowed in ownership_cases:
            if not (permitted(owner, dependency) == allowed):
                raise AssertionError(name)
            path = directory.joinpath(*dependency.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('namespace GuardFixture\ndef value : Nat := 7\n'
                            'structure Token where\n  value : Nat\nend GuardFixture\n')
            result = compile_module(dependency)
            if not (result.returncode == 0):
                raise AssertionError((name, result.stdout, result.stderr))
            path = directory.joinpath(*owner.split('.')).with_suffix('.lean')
            path.parent.mkdir(parents=True, exist_ok=True)
            body = ('def Elsewhere.leaked : Nat := GuardFixture.value\n' if kind == 'body'
                    else 'def Elsewhere.leaked (value : GuardFixture.Token) := value\n')
            path.write_text(f'import {dependency}\n' + body)
            result = compile_module(owner)
            if not (result.returncode == 0):
                raise AssertionError((name, result.stdout, result.stderr))
            (directory / 'Audit.lean').write_text(f'import {owner}\n'
                'import Zkc.Tools.Program.DeclarationAudit\n'
                f'run_cmd ZkcTools.DeclarationAudit.check [`{owner}] "OWNER-GUARD-PASS" true\n')
            result = compile_module('Audit')
            if allowed:
                if not (result.returncode == 0 and 'OWNER-GUARD-PASS' in result.stdout):
                    raise AssertionError((name, result))
            else:
                if not (result.returncode > 0 and f'forbidden {kind} dependency' in result.stdout):
                    raise AssertionError((name, result))
                if not ('OWNER-GUARD-PASS' not in result.stdout):
                    raise AssertionError("checks/check_enforcement.py:252: 'OWNER-GUARD-PASS' not in result.stdout")
            rows.append(name)
        # The data has one owner, but its two interpreters must also agree.
        # Cover every layer pair, exact guards, and every retained exception.
        representatives = [prefix + '.GuardFixture' for prefix, _ in POLICY['layers']]
        representatives += [owner for guard in POLICY['guards'] for owner in guard['owners']]
        representatives += ['Client']
        pairs = sorted({(owner, dependency) for owner in representatives
                        for dependency in representatives} | set(exceptions(POLICY)))
        # Parse the complete table as runtime data. A growing policy must not
        # turn thousands of pairs into one deeply nested elaborated literal.
        literals = json.dumps(pairs)
        (directory / 'Parity.lean').write_text(
            'import Zkc.Tools.Program.DeclarationAudit\n'
            'example : ZkcTools.DeclarationAudit.permitted `Zkc.IR.Source.GuardFixture '
            '`Zkc.Protocol.Library.Mathematics.Probability.GuardFixture = false := by decide +kernel\n'
            'example : ZkcTools.DeclarationAudit.permitted `Zkc.Protocol.Library.Sumcheck.Verifier '
            '`Zkc.Protocol.Library.Mathematics.Probability.UniformTape = false := by decide +kernel\n'
            '#eval do\n'
            f'  let pairs : Array (String × String) ← IO.ofExcept (Lean.Json.parse r##"{literals}"## >>= '
            'Lean.fromJson? (α := Array (String × String)))\n'
            '  IO.println (Lean.toJson (pairs.map fun (owner, dependency) => '
            'ZkcTools.DeclarationAudit.permitted (String.toName owner) (String.toName dependency))).compress\n')
        result = compile_module('Parity')
        if not (result.returncode == 0):
            raise AssertionError((result.stdout, result.stderr))
        if not (json.loads(result.stdout) == [permitted(*pair) for pair in pairs]):
            raise AssertionError('checks/check_enforcement.py:274: json.loads(result.stdout) == [permitted(*pair) for pair in pairs]')
        rows.append(f'shared-policy-interpreter-parity-{len(pairs)}')
        executable = module_package('Zkc.Tools.IR.StructuredSource') / '.lake/build/bin/structured-source'

        def invoke(name, arguments, expected):
            result = subprocess.run([str(executable), *map(str, arguments)],
                                    capture_output=True, text=True, timeout=10)
            if not (result.returncode == 1 and not result.stderr):
                raise AssertionError((name, result))
            if not (json.loads(result.stdout) == {'status': 'refused', 'code': expected}):
                raise AssertionError((name, result))
            rows.append(name)

        if not args.policy_only:
            invoke('arity', [], 'structured-source-arguments')
            invoke('missing-file', ['check', directory / 'missing.json'], 'structured-source-io')
            for name, raw, diagnostic in [
                ('invalid-utf8', b'[\xff]', 'invalid-utf8'),
                ('byte-limit', b' ' * (16 * 1024 * 1024 + 1), 'byte-limit'),
                ('large-number', b'[' + b'9' * 1025 + b']', 'number-limit'),
            ]:
                path = directory / (name + '.json')
                path.write_bytes(raw)
                invoke(name, ['check', path], diagnostic)
    output = evidence.records('enforcement', '.json')
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {'status': 'pass', 'cases': rows,
              'scope': 'policy' if args.policy_only else 'policy-and-executable-inputs',
              'not_run': ['structured-source-input-controls'] if args.policy_only else []}
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
