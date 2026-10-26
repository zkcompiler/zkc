"""Small real export controls; opt in with ZKC_INDEPENDENT_TOOLCHAIN=<Lean prefix>.

No project build is performed. Temporary Lean modules exercise the installed
exporter, comparator, sandbox and all bundled paranoid kernels. These tests
require Linux/bubblewrap and the exact Lean 4.35.0 release toolchain.
"""

import json
import os
from pathlib import Path

import pytest

from harness import load


PREFIX = os.environ.get("ZKC_INDEPENDENT_TOOLCHAIN")
REPLAY_TOOLSET = os.environ.get("ZKC_INDEPENDENT_REPLAY_TOOLSET")
pytestmark = pytest.mark.skipif(not PREFIX, reason="set ZKC_INDEPENDENT_TOOLCHAIN to run real checker controls")


@pytest.fixture(scope="module")
def exports(tmp_path_factory):
    root = tmp_path_factory.mktemp("independent-tools")
    audit = load('independent_tools', 'lean/checks/check_independent.py')
    prefix = Path(PREFIX)
    # Lake 4.35 cannot forward con-leche --jobs: its default reserves about
    # 1 GiB of virtual stack per hardware thread, even for a tiny fixture.
    virtual_memory_mb = max(8192, ((os.cpu_count() or 1) + 32) * 1024)
    runner = audit.Runner(root, memory_mb=virtual_memory_mb, log_mb=2, export_mb=32, timeout=60)
    bodies = {
        "base": "def statement : Prop := True\ntheorem locked : statement := True.intro\n",
        # A distinct proof term of exactly the same statement is accepted.
        "proof": "def statement : Prop := True\ntheorem locked : statement := (fun h : True => h) True.intro\n",
        "statement": "def statement : Prop := True\ntheorem locked : True ∧ True := ⟨True.intro, True.intro⟩\n",
        "dependency": "def statement : Prop := True ∧ True\ntheorem locked : statement := ⟨True.intro, True.intro⟩\n",
        "axiom": "def statement : Prop := True\naxiom bad : True\ntheorem locked : statement := bad\n",
        "strings": 'def first : String := "a"\ndef second : String := first ++ "b"\n'
                   'theorem locked : second = "ab" := rfl\n',
    }
    # Lake 4.35 compares non-target theorem bodies referenced through a
    # definition syntactically, even though their proofs are irrelevant.
    bodies["helper-base"] = "theorem helper : True := True.intro\ndef statement : Prop := helper = helper\ntheorem locked : statement := rfl\n"
    bodies["helper-proof"] = "theorem helper : True := (fun h : True => h) True.intro\ndef statement : Prop := helper = helper\ntheorem locked : statement := rfl\n"
    group = {"modules": ["Control"], "theorems": ["Independent.locked"]}
    for label, body in bodies.items():
        directory = root / label
        directory.mkdir()
        source = directory / "Control.lean"
        source.write_text("import Init\nnamespace Independent\n" + body + "end Independent\n")
        runner.run([str(prefix / "bin/lean"), "-j2", "-o", "Control.olean", "Control.lean"], directory, f"{label}-compile")
        # leanexport uses LEAN_PATH to load the temporary module, including
        # existing Init dependencies. No Lake workspace or source build needed.
        with pytest.MonkeyPatch.context() as environment:
            environment.setenv("LEAN_PATH", str(directory))
            environment.setenv("PATH", str(prefix / "bin") + os.pathsep + os.environ.get("PATH", ""))
            command = audit.export_command(str(prefix / "bin/lake"), prefix / "bin/leanexport", group)
            runner.run(command[2:], directory, f"{label}-export", export=root / f"{label}.ndjson")
    # Keep the theorem's statement and dependencies, corrupt only its proof.
    rows = [json.loads(line) for line in (root / "base.ndjson").read_text().splitlines()]
    identifiers = {0: ""}
    for row in rows:
        if "in" in row and "str" in row and row["str"]["pre"] in identifiers:
            part = row["str"]
            parent = identifiers[part["pre"]]
            identifiers[row["in"]] = (parent + "." if parent else "") + part["str"]
    theorem = next(row["thm"] for row in rows if "thm" in row and
                   identifiers.get(row["thm"]["name"]) == "Independent.locked")
    theorem["value"] = theorem["type"]
    (root / "invalid.ndjson").write_text("".join(json.dumps(row) + "\n" for row in rows))
    # Keep all expression/name references valid and alter only Quot.mk's type.
    rows = [json.loads(line) for line in (root / "base.ndjson").read_text().splitlines()]
    quotient = next(row['quot'] for row in rows if 'quot' in row and
                    identifiers.get(row['quot']['name']) == 'Quot.mk')
    quotient['type'] = theorem['type']
    tables = [r for r in rows if not {'def', 'thm', 'opaque', 'axiom', 'quot', 'inductive'} & r.keys()]
    declarations = [r for r in rows if {'def', 'thm', 'opaque', 'axiom', 'quot', 'inductive'} & r.keys()]
    (root / "corrupt-quotient.ndjson").write_text(''.join(json.dumps(r) + '\n' for r in tables + declarations))
    config = {"challenge_module": "Control", "solution_module": "Control",
              "theorem_names": group["theorems"], "definition_names": [], "permitted_axioms": audit.AXIOMS}
    audit.write_json(root / "comparator.json", config)
    return audit, runner, root, prefix


@pytest.fixture(scope="module")
def sandbox_ready(exports):
    audit, runner, root, _ = exports
    try:
        runner.run([os.environ.get("COMPARATOR_BWRAP", "bwrap"), "--ro-bind", "/", "/",
                    "--unshare-all", "--dev", "/dev", "--proc", "/proc", "--", "true"],
                   root, "sandbox-probe")
    except (OSError, audit.CheckError):
        pytest.skip(f"working bubblewrap namespaces required; see {root / 'sandbox-probe.log'}")


@pytest.mark.parametrize("label,diagnostic", [
    ("proof", None),
    ("statement", "theorem statement do not match"),
    ("dependency", "Const does not match"),
    ("axiom", "Illegal axiom"),
    ("invalid", "reject"),
])
def test_real_comparator(exports, request, label, diagnostic):
    audit, runner, root, prefix = exports
    if label in {"proof", "invalid"}:
        request.getfixturevalue("sandbox_ready")
    assert (root / "base.ndjson").read_bytes() != (root / f"{label}.ndjson").read_bytes()
    command = [str(prefix / "bin/lake"), "comparator", "--config", str(root / "comparator.json"),
               "--challenge-from-export", str(root / "base.ndjson"),
               "--solution-from-export", str(root / f"{label}.ndjson")]
    if diagnostic:
        with pytest.raises(audit.CheckError):
            runner.run(command, root, f"{label}-compare")
        assert diagnostic in (root / f"{label}-compare.log").read_text()
    else:
        runner.run(command, root, f"{label}-compare")


@pytest.mark.parametrize("label", ["proof", "axiom", "invalid"])
def test_real_paranoid_kernels(exports, sandbox_ready, label):
    audit, runner, root, prefix = exports
    command = [str(prefix / "bin/lake"), "check", "--paranoid", "--from-export", str(root / f"{label}.ndjson")]
    if label != "proof":
        with pytest.raises(audit.CheckError):
            runner.run(command, root, f"{label}-paranoid")
    else:
        runner.run(command, root, f"{label}-paranoid")
        log = (root / f"{label}-paranoid.log").read_text()
        for name in ["Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron", "Lean default"]:
            assert f"{name} kernel accepts" in log


@pytest.mark.parametrize("label", ["proof", "invalid"])
def test_direct_default_kernel_replay(exports, label):
    # This tests proof-term rejection even on hosts that forbid network namespace
    # setup. It is not an acceptance by the sandboxed Lake/paranoid command.
    audit, runner, root, prefix = exports
    command = [str(prefix / "bin/leanchecker"), "--from-export", str(root / f"{label}.ndjson")]
    if label == "invalid":
        with pytest.raises(audit.CheckError):
            runner.run(command, root, f"{label}-direct-replay")
        log = (root / f"{label}-direct-replay.log").read_text()
        assert "rejects the solution" in log and "Independent.locked" in log
    else:
        runner.run(command, root, f"{label}-direct-replay")


def test_toolchain_discovery_does_not_evaluate_lakefile(exports):
    audit, _, root, prefix = exports
    workspace = root / 'untrusted-workspace'
    workspace.mkdir()
    marker = workspace / 'lakefile-evaluated'
    (workspace / 'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\n'
        f'#eval IO.FS.writeFile {json.dumps(str(marker))} "executed"\n'
        'package untrusted\n')
    runner = audit.Runner(workspace)
    selected, _ = audit.tools_for(workspace, str(prefix / 'bin/lake'), runner, paranoid=True)
    assert selected == prefix
    assert not marker.exists()


def test_referenced_helper_proof_change_is_strictly_rejected(exports):
    audit, runner, root, prefix = exports
    command = [str(prefix / "bin/lake"), "comparator", "--config", str(root / "comparator.json"),
               "--challenge-from-export", str(root / "helper-base.ndjson"),
               "--solution-from-export", str(root / "helper-proof.ndjson")]
    with pytest.raises(audit.CheckError):
        runner.run(command, root, "helper-proof-compare")
    assert "Const does not match between challenge and target 'Independent.helper'" in (
        root / "helper-proof-compare.log").read_text()


@pytest.fixture(scope='module')
def patched_runtime(exports):
    if not REPLAY_TOOLSET:
        pytest.skip('set ZKC_INDEPENDENT_REPLAY_TOOLSET to test the explicit patched runtime')
    audit, runner, root, stock = exports
    output = root / 'patched'
    output.mkdir()
    prefix, _ = audit.select_replay_toolset(Path(REPLAY_TOOLSET), stock, {}, output, runner)
    assert runner.run([str(prefix / 'bin/lean'), '--print-prefix'], root, 'overlay-prefix').strip() == str(prefix)
    return prefix


@pytest.mark.parametrize('tool', ['leanchecker', 'leanchecker-paranoid', 'lean4lean'])
@pytest.mark.parametrize('label', ['strings', 'invalid', 'corrupt-quotient'])
def test_patched_runtime_direct_controls(exports, patched_runtime, tool, label):
    audit, runner, root, _ = exports
    command = [str(patched_runtime / 'bin' / tool), '--import' if tool == 'lean4lean' else '--from-export',
               str(root / f'{label}.ndjson')]
    if tool == 'lean4lean' and label == 'invalid':
        # Its existing error formatter panics before printing the kernel error
        # when abort-on-panic is enabled. A direct diagnostic permits its raw
        # printer fallback; production Lake/Runner still require abort-on-panic.
        command = ['env', '-u', 'LEAN_ABORT_ON_PANIC', *command]
    name = f'patched-{tool}-{label}'
    if label == 'strings':
        runner.run(command, root, name)
    else:
        with pytest.raises(audit.CheckError):
            runner.run(command, root, name)
        diagnostic = (root / f'{name}.log').read_text()
        assert any(s in diagnostic for s in ['(kernel)', 'Quotient constant mismatch', 'Quotient post-check rejects'])
        assert not any(s in diagnostic for s in ['Invalid JSON', 'Expr not found', 'Name not found'])


def test_patched_runtime_retains_all_sandboxed_kernels(exports, sandbox_ready, patched_runtime):
    _, runner, root, _ = exports
    runner.run([str(patched_runtime / 'bin/lake'), 'check', '--paranoid', '--from-export',
                str(root / 'strings.ndjson')], root, 'patched-all-kernels')
    log = (root / 'patched-all-kernels.log').read_text()
    for name in ['Lean paranoid', 'lean4lean', 'nanoda', 'con-leche', 'con-ron', 'Lean default']:
        assert f'{name} kernel accepts' in log


def test_patched_comparator_keeps_strict_dependency_comparison(exports, patched_runtime):
    audit, runner, root, _ = exports
    with pytest.raises(audit.CheckError):
        runner.run([str(patched_runtime / 'bin/lake'), 'comparator', '--config', str(root / 'comparator.json'),
                    '--challenge-from-export', str(root / 'helper-base.ndjson'),
                    '--solution-from-export', str(root / 'helper-proof.ndjson')], root, 'patched-helper-compare')
    assert "Const does not match between challenge and target 'Independent.helper'" in (
        root / 'patched-helper-compare.log').read_text()
