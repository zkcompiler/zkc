"""Normal-form requests discover names in the actual scoped-source printer output.

These are presentation names only. The generated equations still need Lean
kernel checking against the admitted source.
"""

import tomllib
from types import SimpleNamespace

import pytest

from harness import load


@pytest.fixture
def gkr():
    api = load("normal_form_names", "lean/bridges/structured/normal_forms.py")
    path = api.ROOT / "lean/bridges/structured/normal-forms/gkr-source.toml"
    request = tomllib.loads(path.read_text())
    rounds = tomllib.loads(path.with_name("gkr-rounds.toml").read_text())["bodies"]["protocol"]
    return api, path, request, SimpleNamespace(name=rounds)


def test_scoped_body_names_resolve_protocol_applications_and_helpers(gkr):
    api, path, request, rounds = gkr
    module = api.Module(request, path)
    assert module.signature_term(rounds) == "GkrSourceBodies.roundsSignature"
    assert "GkrSourceBodies.emptyHelper" in module.helpers().values()


def test_application_without_its_declared_body_module_is_refused(gkr):
    api, path, request, rounds = gkr
    request["helper_modules"] = []
    module = api.Module(request, path)
    with pytest.raises(api.GeneratorError, match="no signature declaration"):
        module.signature_term(rounds)
