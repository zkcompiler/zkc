"""One dependency policy for source imports and Lean declaration references.

The JSON literal is owned by DeclarationAudit.lean, so policy edits also
invalidate compiled audits. This reader extracts data, not Lean syntax.
"""

import json
from pathlib import Path

POLICY_SOURCE = Path(__file__).resolve().parents[1] / 'ZkcTools/DeclarationAudit.lean'
BEGIN = '-- BEGIN DEPENDENCY POLICY\nprivate def dependencyPolicyJson : String := r##"'
END = '"##\n-- END DEPENDENCY POLICY'


def below(name, root):
    return name == root or name.startswith(root + '.')


def load_policy(path=POLICY_SOURCE):
    source = path.read_text()
    if source.count(BEGIN) != 1 or source.count(END) != 1:
        raise ValueError('expected one dependency policy literal')
    policy = json.loads(source.split(BEGIN)[1].split(END)[0])
    if set(policy) != {'layers', 'allowed', 'guards', 'exceptions'}:
        raise ValueError('invalid dependency policy fields')
    layers = dict(policy['layers'])
    allowed = dict(policy['allowed'])
    if len(layers) != len(policy['layers']) or len(allowed) != len(policy['allowed']):
        raise ValueError('duplicate dependency layer')
    if not set(layers.values()) | {'upstream'} <= set(allowed):
        raise ValueError('missing allowed-edge row')
    for targets in allowed.values():
        if len(set(targets)) != len(targets) or not set(targets) <= set(allowed):
            raise ValueError('invalid allowed-edge targets')
    for i, (prefix, _) in enumerate(policy['layers']):
        if any(below(prefix, earlier) for earlier, _ in policy['layers'][:i]):
            raise ValueError(f'shadowed dependency layer: {prefix}')
    names, edges = set(), set()
    for guard in policy['guards']:
        if set(guard) != {'name', 'owners', 'exact', 'dependencies'} or type(guard['exact']) is not bool:
            raise ValueError('invalid dependency guard')
        if guard['name'] in names:
            raise ValueError('duplicate dependency rule')
        names.add(guard['name'])
    for exception in policy['exceptions']:
        if set(exception) != {'name', 'reason', 'edges'} or not exception['reason'] or not exception['edges']:
            raise ValueError('invalid dependency exception')
        if exception['name'] in names:
            raise ValueError('duplicate dependency rule')
        names.add(exception['name'])
        for owner, dependency, direct in exception['edges']:
            if type(direct) is not bool or (owner, dependency) in edges:
                raise ValueError('invalid or duplicate dependency exception edge')
            edges.add((owner, dependency))
            if rule(owner, dependency, policy) != exception['name']:
                raise ValueError(f'exception does not violate its named rule: {owner} -> {dependency}')
    return policy


def layer(name, policy):
    return next((value for prefix, value in policy['layers'] if below(name, prefix)), 'upstream')


def rule(owner, dependency, policy):
    for guard in policy['guards']:
        matches = any(owner == prefix if guard['exact'] else below(owner, prefix)
                      for prefix in guard['owners'])
        if matches and any(below(dependency, prefix) for prefix in guard['dependencies']):
            return guard['name']
    source, target = layer(owner, policy), layer(dependency, policy)
    if target not in dict(policy['allowed'])[source]:
        return f'{source}-to-{target}'
    return None


POLICY = load_policy()


def exceptions(policy):
    return {(owner, dependency): (exception['name'], direct)
            for exception in policy['exceptions']
            for owner, dependency, direct in exception['edges']}


def permitted(owner, dependency, policy=POLICY):
    broken = rule(owner, dependency, policy)
    return broken is None or exceptions(policy).get((owner, dependency), (None,))[0] == broken


def audit_graph(graph, scopes, policy=POLICY):
    """Reject new reachable pairs, new direct edges and obsolete exceptions.

    Scopes include deleted modules' prefixes, so deleting an exception's owner
    requires deleting the exception too. Optional packages outside this run are
    not declared stale. An existing transitive exception never licenses a new
    direct import of that dependency.
    """
    expected, observed = exceptions(policy), {}
    for owner, dependencies in graph.items():
        pending, seen = list(dependencies), set()
        while pending:
            dependency = pending.pop()
            if dependency in seen:
                continue
            seen.add(dependency)
            broken = rule(owner, dependency, policy)
            if broken:
                pair = owner, dependency
                if pair not in expected or expected[pair][0] != broken:
                    raise ValueError(f'forbidden dependency ({broken}): {owner} reaches {dependency}')
                direct = dependency in dependencies
                if direct and not expected[pair][1]:
                    raise ValueError(f'new direct dependency ({broken}): {owner} imports {dependency}')
                observed[pair] = broken, direct
            pending.extend(graph.get(dependency, []))
    for (owner, dependency), value in expected.items():
        if not any(below(owner, scope) for scope in scopes):
            continue
        if observed.get((owner, dependency)) != value:
            raise ValueError(f'stale dependency exception ({value[0]}): {owner} -> {dependency}')
    return {'reachable_exceptions': len(observed),
            'direct_exceptions': sum(direct for _, direct in observed.values()),
            'rules': {exception['name']: sum(name == exception['name'] for name, _ in observed.values())
                      for exception in policy['exceptions']}}
