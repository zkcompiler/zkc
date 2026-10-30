"""Dependency exceptions shrink without opening new import paths."""

from copy import deepcopy

import pytest

from harness import load


def policy():
    return load('lean_dependencies', 'lean/support/dependencies.py')


def legacy_policy(audit):
    data = deepcopy(audit.POLICY)
    data['exceptions'] = [{
        'name': 'clean-subjects-to-tests',
        'reason': 'Synthetic legacy edge used only to test exception retirement.',
        'edges': [['CleanExamples', 'TestsClean.NativeClients', True]],
    }]
    return data


def legacy_graph():
    return {'CleanExamples': ['TestsClean.NativeClients'], 'TestsClean.NativeClients': []}


def test_existing_exception_and_unselected_packages():
    audit = policy()
    result = audit.audit_graph(legacy_graph(), ['CleanExamples', 'TestsClean'],
                               legacy_policy(audit))
    assert audit.audit_graph({}, ['Zkc'], legacy_policy(audit))['reachable_exceptions'] == 0
    assert result['reachable_exceptions'] == result['direct_exceptions'] == 1


@pytest.mark.parametrize('graph', [
    {},
    {'CleanExamples': [], 'TestsClean.NativeClients': []},
    {'CleanExamples': ['CleanExamples.Helper'],
     'CleanExamples.Helper': ['TestsClean.NativeClients'], 'TestsClean.NativeClients': []},
])
def test_deleted_owner_removed_import_and_relocated_violation_are_refused(graph):
    with pytest.raises(ValueError, match='stale dependency exception|forbidden dependency'):
        audit = policy()
        audit.audit_graph(graph, ['CleanExamples', 'TestsClean'], legacy_policy(audit))


def test_transitive_exception_does_not_authorize_new_direct_import():
    audit = policy()
    data = legacy_policy(audit)
    data['exceptions'][0]['edges'][0][2] = False
    with pytest.raises(ValueError, match='new direct dependency'):
        audit.audit_graph(legacy_graph(), ['CleanExamples', 'TestsClean'], data)


def test_current_policy_has_no_dependency_exceptions():
    audit = policy()
    assert audit.POLICY['exceptions'] == []
    with pytest.raises(ValueError, match='forbidden dependency'):
        audit.audit_graph(legacy_graph(), ['CleanExamples', 'TestsClean'])


def test_new_user_of_an_existing_violation_is_refused():
    graph = legacy_graph() | {'CleanExamples.NewClient': ['CleanExamples']}
    with pytest.raises(ValueError, match='forbidden dependency'):
        audit = policy()
        audit.audit_graph(graph, ['CleanExamples', 'TestsClean'], legacy_policy(audit))


def test_hard_guard_applies_through_an_otherwise_allowed_layer():
    graph = {'Zkc.Source.Client': ['Zkc.Semantics.Middle'],
             'Zkc.Semantics.Middle': ['Zkc.Compiler.Boundary']}
    with pytest.raises(ValueError, match='source-before-compiler'):
        policy().audit_graph(graph, ['Zkc'])


@pytest.mark.parametrize('uniform', ['Zkc.Construction.FiatShamir',
                                   'ZkcSecurity.Transformations.FiatShamir.Soundness',
                                   'ZkcSecurity.ProgramLogic.Transcript.Composition'])
def test_generic_certificates_refuse_transitive_uniform_dependencies(uniform):
    graph = {'ZkcSecurity.ProgramLogic.Transcript.Reduction': ['ZkcSecurity.ProgramLogic.Transcript.Intermediate'],
             'ZkcSecurity.ProgramLogic.Transcript.Intermediate': [uniform]}
    with pytest.raises(ValueError, match='generic-certificates'):
        policy().audit_graph(graph, ['ZkcSecurity'])


def test_uniform_adapter_may_consume_generic_certificates():
    graph = {'ZkcSecurity.ProgramLogic.Transcript.Composition': [
        'ZkcSecurity.Transformations.FiatShamir.Soundness', 'ZkcSecurity.ProgramLogic.Transcript.Reduction']}
    policy().audit_graph(graph, ['ZkcSecurity'])


@pytest.mark.parametrize('defect', ['duplicate', 'shadowed', 'wrong-rule', 'unknown-target'])
def test_policy_refuses_ambiguous_or_unjustified_rows(tmp_path, defect):
    import json

    audit = policy()
    data = legacy_policy(audit)
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
    ('Zkc.Source.Client', 'ZkcSecurity.Claims.Methods.KnowledgeEndpoint'),
    ('ZkcSecurity.Transformations.FiatShamir.Client', 'ArkLib.ProofSystem.Sumcheck.Domain'),
    ('ZkcSecurity.Families.Client', 'ZkcArkLib.FiatShamir.Upstream'),
    ('ZkcSecurity.Transformations.HashChain.Client', 'ZkcSecurityExamples.Subjects.Schnorr.Evidence'),
    ('ZkcArkLib.Sumcheck.Multilinear.Causal.Client', 'Zkc.Source.Structure'),
])
def test_separated_boundaries_are_enforced(owner, dependency):
    with pytest.raises(ValueError, match='forbidden dependency'):
        policy().audit_graph({owner: [dependency]}, [owner])


@pytest.mark.parametrize('dependency', ['VCVio.Schemes.Schnorr.SigmaProtocol', 'VCVio.CryptoFoundations',
                                       'Zkc.Protocols.Sumcheck.Verifier'])
def test_generic_security_reuses_actual_vcvio_and_core_providers(dependency):
    assert policy().permitted('ZkcSecurity.Families.Sigma.Schnorr', dependency)



def test_generic_elaborators_are_reusable_without_opening_generator_dependencies():
    audit = policy()
    subject = 'ZkcExamples.Structured.Generated.Connections.Sample'
    elaborator = 'ZkcTools.ConstructionBindings.Root'
    audit.audit_graph({subject: [elaborator], elaborator: ['Zkc.Construction.ConnectionRoot']},
                      ['ZkcExamples', 'ZkcTools', 'Zkc'])
    assert audit.POLICY['exceptions'] == []
    for forbidden in ['ZkcTools.ConstructionBindings.Generate',
                      'ZkcTools.ConstructionBindings.Analysis', 'ZkcExamples.Structured.Sample']:
        with pytest.raises(ValueError, match='forbidden dependency'):
            audit.audit_graph({subject: [elaborator], elaborator: [forbidden]},
                              ['ZkcExamples', 'ZkcTools'])
    with pytest.raises(ValueError, match='forbidden dependency'):
        audit.audit_graph({subject: ['ZkcTools.ConstructionBindings.Generate']}, ['ZkcExamples'])


@pytest.mark.parametrize('owner', [
    'ZkcSecurity.Bindings.Source.Client',
    'ZkcSecurity.Families.Sumcheck.Client',
    'ZkcArkLibExamples.Subjects.Guess.Client',
])
@pytest.mark.parametrize('elaborator', [
    'ZkcTools.StructuredSource.InferReferenceInstallation',
    'ZkcTools.StructuredSource.NormalizedRoot',
    'ZkcTools.StructuredSource.Composition',
])
def test_security_clients_share_restricted_checked_elaborators(owner, elaborator):
    audit = policy()
    graph = {owner: [elaborator], elaborator: ['Zkc.Source.Structured.NormalizedRoot']}
    audit.audit_graph(graph, ['ZkcSecurity', 'ZkcArkLib', 'ZkcTools', 'Zkc'])
    for forbidden in ['ZkcTools.StructuredSource.Bindings', 'ZkcExamples.Structured.Sample',
                      'ZkcSecurityExamples.Subjects.Sample']:
        with pytest.raises(ValueError, match='forbidden dependency'):
            audit.audit_graph({owner: [elaborator], elaborator: [forbidden]},
                              ['ZkcSecurity', 'ZkcArkLib', 'ZkcTools'])


def test_source_realization_owns_concrete_programs_not_family_mathematics():
    audit = policy()
    source = 'ZkcExamples.Structured.SumcheckSourceSelections'
    realization = 'ZkcSecurityExamples.Sumcheck.SourceFamilySelections'
    family = 'ZkcSecurity.Families.Sumcheck.Contract'
    audit.audit_graph({realization: [source, family]}, ['ZkcSecurity', 'ZkcExamples'])
    for dependency in [source, realization]:
        with pytest.raises(ValueError, match='security-families-to-'):
            audit.audit_graph({family: [dependency]}, ['ZkcSecurity', 'ZkcExamples'])


@pytest.mark.parametrize("missing", ["Zkc.Source.Retired", "ZkcTools.Retired",
                                     "Tests.Retired", "ZkcSecurity.Retired"])
def test_missing_owned_import_fails_before_build(missing):
    audit = load("lean_library", "lean/checks/check_library.py")
    with pytest.raises(AssertionError, match="unselected or missing owned import"):
        audit.check_owned_imports({"Tests.Client": [missing]})
    audit.check_owned_imports({"Tests.Client": [missing, "Mathlib.Data.Nat.Basic"], missing: []})
