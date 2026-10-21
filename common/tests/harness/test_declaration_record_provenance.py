"""Actual imported ConstantInfo provenance controls; outputs stay in tmp_path."""
import json
import os
from pathlib import Path
import shutil
import subprocess

import pytest


ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean"
EMITTER = LEAN / "checks/DeclarationRecords.lean"


@pytest.fixture
def capture(tmp_path):
    if not shutil.which("lean"):
        pytest.skip("Lean is not installed")
    paths = os.environ.get("LEAN_PATH", "").split(os.pathsep)
    for package in (LEAN, LEAN / "security", LEAN / "integrations/arklib"):
        paths.append(str(package / ".lake/build/lib/lean"))
        dependencies = package / ".lake/packages"
        if dependencies.is_dir():
            paths.extend(str(path / ".lake/build/lib/lean") for path in dependencies.iterdir())
    if not any((Path(path) / "ZkcTools/DeclarationAudit.olean").is_file() for path in paths if path):
        pytest.skip("DeclarationAudit dependencies must already be built")
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(tmp_path), *dict.fromkeys(paths)]),
               ELAN_TOOLCHAIN=(LEAN / "lean-toolchain").read_text().strip(), LEAN_NUM_THREADS="2")

    def build(name, text):
        source = tmp_path / (name + ".lean")
        source.write_text(text)
        subprocess.run(["lean", "-o", str(source.with_suffix(".olean")), str(source)],
                       cwd=tmp_path, env=env, check=True, capture_output=True, text=True)

    def emit(name, success=True):
        output = tmp_path / (name + ".jsonl")
        result = subprocess.run(["lean", "--run", str(EMITTER), str(output), name + ".lean"],
                                cwd=tmp_path, env=env, capture_output=True, text=True)
        if not success:
            assert result.returncode > 0, result.stdout + result.stderr
            assert not output.exists()
            assert "ambiguous stored providers" in result.stderr
            return None
        assert result.returncode == 0, result.stdout + result.stderr
        rows = [json.loads(line) for line in output.read_text().splitlines()]
        assert rows[0]["axiom_provenance"] == "resolved-constant-info/0"
        assert rows[0]["reference_provenance"] == "checked-stored-module/0"
        return {row["name"]: row for row in rows[1:]}

    return build, emit


def test_imported_same_name_proof_conflict_refuses_capture(capture):
    build, emit = capture
    build("PureProvider", "import Lean\ntheorem Shared.claim : True := True.intro\n")
    build("ChoiceProvider", "import Lean\ntheorem Shared.claim : True := Classical.choice ⟨True.intro⟩\n")
    build("Before", "import PureProvider\ntheorem Client.claim : True := Shared.claim\n")
    assert emit("Before")["Client.claim"]["axioms"] == []
    build("After", "import PureProvider\nimport ChoiceProvider\ntheorem Client.claim : True := Shared.claim\n")
    emit("After", success=False)


def test_actual_opaque_body_contributes_imported_axioms(capture):
    build, emit = capture
    build("OpaqueProvider", "import Lean\nopaque Shared.opaque : True := Classical.choice ⟨True.intro⟩\n")
    build("OpaqueClient", "import OpaqueProvider\ntheorem Client.opaque : True := Shared.opaque\n")
    assert "Classical.choice" in emit("OpaqueClient")["Client.opaque"]["axioms"]


def test_checked_identical_reexports_are_supported(capture):
    build, emit = capture
    for name in ("IdenticalLeft", "IdenticalRight"):
        build(name, "import Lean\ntheorem Shared.identical : True := True.intro\n")
    build("IdenticalClient", "import IdenticalLeft\nimport IdenticalRight\ntheorem Client.identical : True := Shared.identical\n")
    assert emit("IdenticalClient")["Client.identical"]["axioms"] == []


def test_provider_equality_keeps_binder_annotations(capture):
    build, emit = capture
    build("ExplicitProvider", "import Lean\ntheorem Shared.visible (_n : Nat) : True := True.intro\n")
    build("ImplicitProvider", "import Lean\ntheorem Shared.visible {_n : Nat} : True := True.intro\n")
    build("VisibilityClient", "import ExplicitProvider\nimport ImplicitProvider\ntheorem Client.visible : True := @Shared.visible 0\n")
    emit("VisibilityClient", success=False)
