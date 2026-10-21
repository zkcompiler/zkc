"""Dependency exceptions shrink without opening new import paths."""

from copy import deepcopy

import pytest

from harness import load


def policy():
    return load('lean_dependencies', 'lean/support/dependencies.py')


def legacy_graph():
    return {'CleanExamples': ['TestsClean.NativeClients'], 'TestsClean.NativeClients': []}


def test_existing_exception_and_unselected_packages():
    audit = policy()
    result = audit.audit_graph(legacy_graph(), ['CleanExamples', 'TestsClean'])
    assert result['reachable_exceptions'] == result['direct_exceptions'] == 1


@pytest.mark.parametrize('graph', [
    {},
    {'CleanExamples': [], 'TestsClean.NativeClients': []},
    {'CleanExamples': ['CleanExamples.Helper'],
     'CleanExamples.Helper': ['TestsClean.NativeClients'], 'TestsClean.NativeClients': []},
])
def test_deleted_owner_removed_import_and_relocated_violation_are_refused(graph):
    with pytest.raises(ValueError, match='stale dependency exception|forbidden dependency'):
        policy().audit_graph(graph, ['CleanExamples', 'TestsClean'])


def test_transitive_exception_does_not_authorize_new_direct_import():
    graph = {'Zkc.Protocols.Sumcheck.Acceptance': ['ZkcSecurity.Probability.UniformTape']}
    with pytest.raises(ValueError, match='forbidden dependency'):
        policy().audit_graph(graph, ['Zkc.Protocols.Sumcheck.Acceptance'])


def test_new_user_of_an_existing_violation_is_refused():
    graph = legacy_graph() | {'CleanExamples.NewClient': ['CleanExamples']}
    with pytest.raises(ValueError, match='forbidden dependency'):
        policy().audit_graph(graph, ['CleanExamples', 'TestsClean'])


def test_hard_guard_applies_through_an_otherwise_allowed_layer():
    graph = {'Zkc.Source.Client': ['Zkc.Semantics.Middle'],
             'Zkc.Semantics.Middle': ['Zkc.Compiler.Boundary']}
    with pytest.raises(ValueError, match='source-before-compiler'):
        policy().audit_graph(graph, ['Zkc'])


@pytest.mark.parametrize('defect', ['duplicate', 'shadowed', 'wrong-rule', 'unknown-target'])
def test_policy_refuses_ambiguous_or_unjustified_rows(tmp_path, defect):
    import json

    audit = policy()
    data = deepcopy(audit.POLICY)
    if defect == 'duplicate':
        data['exceptions'][0]['edges'] *= 2
    elif defect == 'shadowed':
        data['layers'].insert(0, ['Zkc', 'core'])
    elif defect == 'wrong-rule':
        data['exceptions'][0]['name'] = 'core-to-probability'
    else:
        data['allowed'][0][1].append('unclassified')
    path = tmp_path / 'Policy.lean'
    path.write_text(audit.BEGIN + json.dumps(data) + audit.END)
    with pytest.raises(ValueError):
        audit.load_policy(path)


@pytest.mark.parametrize('owner,dependency', [
    ('Zkc.Source.Client', 'ZkcSecurity.Endpoint.Knowledge'),
    ('ZkcSecurity.FiatShamir.Client', 'ArkLib.ProofSystem.Sumcheck.Domain'),
    ('ZkcSecurity.Families.Client', 'ZkcArkLib.FiatShamir.Upstream'),
    ('ZkcSecurity.HashChain.Client', 'ZkcSecurity.Examples.Subjects.Schnorr.Evidence'),
    ('ZkcArkLib.Sumcheck.Multilinear.Causal.Client', 'Zkc.Source.Structure'),
])
def test_separated_boundaries_are_enforced(owner, dependency):
    with pytest.raises(ValueError, match='forbidden dependency'):
        policy().audit_graph({owner: [dependency]}, [owner])


@pytest.mark.parametrize('dependency', ['Examples.Schnorr.SigmaProtocol', 'VCVio.CryptoFoundations',
                                       'Zkc.Protocols.Sumcheck.Verifier'])
def test_generic_security_reuses_actual_vcvio_and_core_providers(dependency):
    assert policy().permitted('ZkcSecurity.Families.Schnorr', dependency)
