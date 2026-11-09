"""Dependency exceptions shrink without opening new import paths."""

from copy import deepcopy

import pytest

from harness import lean_imports, load


@pytest.fixture(autouse=True)
def isolated_lean_workspace():
    with lean_imports():
        yield


def policy():
    return load('lean_dependencies', 'lean/support/dependencies.py')


def legacy_policy(audit):
    data = deepcopy(audit.POLICY)
    data['exceptions'] = [{
        'name': 'clean-to-applications',
        'reason': 'Synthetic legacy edge used only to test exception retirement.',
        'edges': [['Zkc.Adapters.Clean', 'Zkc.Applications.Clean.NativeClients', True]],
    }]
    return data


def legacy_graph():
    return {'Zkc.Adapters.Clean': ['Zkc.Applications.Clean.NativeClients'], 'Zkc.Applications.Clean.NativeClients': []}


def test_existing_exception_and_unselected_packages():
    audit = policy()
    result = audit.audit_graph(legacy_graph(), ['Zkc.Adapters.Clean', 'Zkc.Applications.Clean'],
                               legacy_policy(audit))
    assert audit.audit_graph({}, ['Zkc.IR'], legacy_policy(audit))['reachable_exceptions'] == 0
    assert result['reachable_exceptions'] == result['direct_exceptions'] == 1


@pytest.mark.parametrize('graph', [
    {},
    {'Zkc.Adapters.Clean': [], 'Zkc.Applications.Clean.NativeClients': []},
    {'Zkc.Adapters.Clean': ['Zkc.Adapters.Clean.Helper'],
     'Zkc.Adapters.Clean.Helper': ['Zkc.Applications.Clean.NativeClients'], 'Zkc.Applications.Clean.NativeClients': []},
])
def test_deleted_owner_removed_import_and_relocated_violation_are_refused(graph):
    with pytest.raises(ValueError, match='stale dependency exception|forbidden dependency'):
        audit = policy()
        audit.audit_graph(graph, ['Zkc.Adapters.Clean', 'Zkc.Applications.Clean'], legacy_policy(audit))


def test_transitive_exception_does_not_authorize_new_direct_import():
    audit = policy()
    data = legacy_policy(audit)
    data['exceptions'][0]['edges'][0][2] = False
    with pytest.raises(ValueError, match='new direct dependency'):
        audit.audit_graph(legacy_graph(), ['Zkc.Adapters.Clean', 'Zkc.Applications.Clean'], data)


def test_current_policy_has_no_dependency_exceptions():
    audit = policy()
    assert audit.POLICY['exceptions'] == []
    with pytest.raises(ValueError, match='forbidden dependency'):
        audit.audit_graph(legacy_graph(), ['Zkc.Adapters.Clean', 'Zkc.Applications.Clean'])


def test_new_user_of_an_existing_violation_is_refused():
    graph = legacy_graph() | {'Zkc.Adapters.Clean.NewClient': ['Zkc.Adapters.Clean']}
    with pytest.raises(ValueError, match='forbidden dependency'):
        audit = policy()
        audit.audit_graph(graph, ['Zkc.Adapters.Clean', 'Zkc.Applications.Clean'], legacy_policy(audit))


def test_hard_guard_applies_through_an_otherwise_allowed_layer():
    graph = {'Zkc.IR.Source.Client': ['Zkc.IR.Semantics.Middle'],
             'Zkc.IR.Semantics.Middle': ['Zkc.IR.Compiler.Boundary']}
    with pytest.raises(ValueError, match='source-before-compiler'):
        policy().audit_graph(graph, ['Zkc.IR'])


@pytest.mark.parametrize('uniform', ['Zkc.IR.Construction.FiatShamir',
                                   'Zkc.Verification.Transformations.FiatShamir.Soundness',
                                   'Zkc.Verification.ProgramLogic.Transcript.Composition'])
def test_generic_certificates_refuse_transitive_uniform_dependencies(uniform):
    graph = {'Zkc.Protocol.Logic.Transcript.Reduction': ['Zkc.Program.Intermediate'],
             'Zkc.Program.Intermediate': [uniform]}
    with pytest.raises(ValueError, match='generic-certificates'):
        policy().audit_graph(graph, ['Zkc.Verification'])


def test_uniform_adapter_may_consume_generic_certificates():
    graph = {'Zkc.Verification.ProgramLogic.Transcript.Composition': [
        'Zkc.Verification.Transformations.FiatShamir.Soundness', 'Zkc.Protocol.Logic.Transcript.Reduction']}
    policy().audit_graph(graph, ['Zkc.Verification'])


@pytest.mark.parametrize('defect', ['duplicate', 'shadowed', 'wrong-rule', 'unknown-target'])
def test_policy_refuses_ambiguous_or_unjustified_rows(tmp_path, defect):
    import json

    audit = policy()
    data = legacy_policy(audit)
    if defect == 'duplicate':
        data['exceptions'][0]['edges'] *= 2
    elif defect == 'shadowed':
        data['layers'].insert(0, ['Zkc', 'ir'])
    elif defect == 'wrong-rule':
        data['exceptions'][0]['name'] = 'core-to-probability'
    else:
        data['allowed'][0][1].append('unclassified')
    path = tmp_path / 'Policy.lean'
    path.write_text(audit.BEGIN + json.dumps(data) + audit.END)
    with pytest.raises(ValueError):
        audit.load_policy(path)


@pytest.mark.parametrize('owner,dependency', [
    ('Zkc.IR.Source.Client', 'Zkc.Verification.Claims.Methods.KnowledgeEndpoint'),
    ('Zkc.Verification.Transformations.FiatShamir.Client', 'ArkLib.ProofSystem.Sumcheck.Domain'),
    ('Zkc.Protocol.Library.Client', 'Zkc.Adapters.ArkLib.FiatShamir.Upstream'),
    ('Zkc.Protocol.Library.Transformations.HashChain.Client', 'Zkc.Applications.Security.Subjects.Schnorr.Evidence'),
    ('Zkc.Adapters.ArkLib.Sumcheck.Multilinear.Causal.Client', 'Zkc.IR.Source.Structure'),
])
def test_separated_boundaries_are_enforced(owner, dependency):
    with pytest.raises(ValueError, match='forbidden dependency'):
        policy().audit_graph({owner: [dependency]}, [owner])


@pytest.mark.parametrize('dependency', ['VCVio.Schemes.Schnorr.SigmaProtocol', 'VCVio.CryptoFoundations',
                                       'Zkc.Protocol.Library.Sumcheck.Verifier'])
def test_generic_security_reuses_actual_vcvio_and_core_providers(dependency):
    assert policy().permitted('Zkc.Verification.Families.Sigma.Schnorr', dependency)







def test_source_realization_owns_concrete_programs_not_family_mathematics():
    audit = policy()
    source = 'Zkc.Applications.IR.Structured.SumcheckSourceSelections'
    realization = 'Zkc.Applications.Security.Sumcheck.SourceFamilySelections'
    family = 'Zkc.Verification.Families.Sumcheck.Contract'
    audit.audit_graph({realization: [source, family]}, ['Zkc.Verification', 'Zkc.Applications.IR'])
    for dependency in [source, realization]:
        with pytest.raises(ValueError, match='verification-to-applications'):
            audit.audit_graph({family: [dependency]}, ['Zkc.Verification', 'Zkc.Applications.IR'])


@pytest.mark.parametrize("missing", ["Zkc.IR.Source.Retired", "Zkc.Tools.IR.Retired",
                                     "Zkc.Tests.IR.Retired", "Zkc.Verification.Retired"])
def test_missing_owned_import_fails_before_build(missing):
    audit = load("lean_library", "lean/checks/check_library.py")
    with pytest.raises(ValueError, match="unselected or missing owned import"):
        audit.check_owned_imports({"Zkc.Tests.IR.Client": [missing]})
    audit.check_owned_imports({"Zkc.Tests.IR.Client": [missing, "Mathlib.Data.Nat.Basic"], missing: []})


def test_external_client_can_use_its_own_helpers_without_reverse_library_edges():
    audit = policy()
    audit.audit_graph({'Client': ['Client', 'Zkc.Protocol.Claims.Assembly']}, ['Client'])
    with pytest.raises(ValueError, match='forbidden dependency'):
        audit.audit_graph({'Zkc.Protocol.Claims.Assembly': ['Client']}, ['Zkc.Protocol'])
