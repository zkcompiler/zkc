"""Admitted sources: policy refusals mean missing evidence, not invalid PIR.

These probes invoke the real frontend/admission before analysis. Deliberately
malformed execution views are confined to the separate C++ API test.
"""
import json
import re
from pathlib import Path
from commands import Commands
from tools import compiler, corpus, examples, records
from journal import names

def editable_source(path):
    """Compact call arguments and omit generated sites for source mutation probes."""
    text = re.sub(r'\[__site_\d+\] ', '', path.read_text())
    text = re.sub(r'\([^()]*\)', lambda m: re.sub(r'\s+', ' ', m[0]).replace('( ', '(').replace(' )', ')').replace(', ', ','), text)
    return text


source = editable_source(corpus / 'oracle-provenance.pir')
ORDER = '--publication-before-queries'
RESPONSES = '--queries-before-responses'
SAMPLED = '--sampled-queries'
UNABSORBED = 'oracle-query-publication-unabsorbed'
NOT_SAMPLE = 'oracle-query-not-exact-sample'
BOUND = 'oracle-query-bound-unresolved'
UNGUARDED = 'oracle-check-unguarded'


commands = Commands(records())


def call(args):
    """Run the compiler and judge nothing: the call sites do that."""
    return commands.attempt([compiler, *args])


def inspect(text, *flags, command='oracle-check', entry='main'):
    directory = records()
    path = Path(directory) / 'source.pir'
    path.write_text(text)
    # Admission errors have no report. Requiring JSON makes each refusal a
    # dataflow/policy result on a valid source, never a syntax/type error.
    result = call([command, path, entry, *flags])
    assert result.returncode in (0, 1) and result.stdout, result.stderr
    report = json.loads(result.stdout)
    assert report['format'] == 'zkc.oracle-access/2'
    assert bool(result.returncode) == (command == 'oracle-check' and bool(report['findings']))
    return report


def codes(report):
    return {f['code'] for f in report['findings']}


def expect(text, flags=(), findings=()):
    report = inspect(text, *flags)
    assert codes(report) == set(findings), report
    return report


normal = expect(source, (ORDER, RESPONSES, SAMPLED))
access = normal['accesses'][0]
assert access['coordinate_sample'] in access['publication_bound_draws']
assert access['sample_bound_matches_height']
assert access['coordinate_provider_history'] and not access['coordinate_receptions']
expect(source)
assert inspect(source, command='oracle-inspect') == normal

observe = '    local V: let observed = ObserveRoot(coins,received_root);\n'
draw = '    local V: let (query,after) = DrawIndex(observed,height);\n'

# No root observation: valid source with insufficient transcript linkage.
unabsorbed = source.replace(observe, '').replace('DrawIndex(observed,height)', 'DrawIndex(coins,height)')
# Two distinct affine transcript inputs; each is consumed exactly once.
separate = source.replace('V coins: Transcript<', 'V other_coins: Transcript<"merlin3.koala-bear.ext8-binomial3.rejection31le/1">,V coins: Transcript<')
separate = separate.replace('DrawIndex(observed,height)', 'DrawIndex(other_coins,height)')
# Observation uses the actual draw successor, so the root is absorbed too late.
after = unabsorbed.replace('    message query:',
    '    local V: let observed = ObserveRoot(after,received_root);\n    message query:')
# Both the statistic and the list are computed from the real received root.
list_prefix = '    local V: let roots = RootList(received_root);\n'
statistic = source.replace(observe, list_prefix +
    '    local V: let count = RootCount(roots);\n'
    '    local V: let observed = ObserveStatistic(coins,count);\n')
whole_list = source.replace(observe, list_prefix +
    '    local V: let observed = ObserveRoots(coins,roots);\n')
# Two receptions of the same authored root are separate arbitrary peer inputs.
second = source.replace(observe,
    '    message second_root: P(root) -> V(other_root);\n' + observe)
second = second.replace('CheckRow(received_root,', 'CheckRow(other_root,')
for text in (unabsorbed, separate, after, statistic, whole_list, second):
    expect(text)
    expect(text, (SAMPLED, RESPONSES))
    refused = expect(text, (ORDER,), (UNABSORBED,))
    expect(text, (ORDER, SAMPLED, RESPONSES), (UNABSORBED,))
    assert not refused['accesses'][0]['publication_bound_draws']
    assert refused['accesses'][0]['coordinate_sample']
# Exact local selection is supported; no byte/list congruence is inferred.
selected = source.replace(observe, list_prefix +
    '    local V: let selected_root = FirstRoot(roots);\n' +
    observe.replace('coins,received_root', 'coins,selected_root'))
expect(selected, (ORDER, SAMPLED))

# A received bound remains a direct peer dependency, independently of history.
received_bound = source.replace(draw,
    '    message bound: P(width) -> V(peer_bound);\n' +
    draw.replace('observed,height', 'observed,peer_bound'))
expect(received_bound, (ORDER,), ('oracle-query-coordinate-received',))
expect(received_bound, (SAMPLED,), (BOUND,))

# Matching the received bound and height is exact identity, not independence.
received_height = received_bound.replace('expected_width,height,query',
                                       'expected_width,peer_bound,query')
expect(received_height, (SAMPLED,))
expect(received_height, (ORDER, SAMPLED), ('oracle-query-coordinate-received',))
# A peer echo never inherits the validator's sample identity or draws.
echo = source.replace('    local P: let (row,path)',
    '    message echo: P(received_query) -> V(echoed_query);\n    local P: let (row,path)')
echo = echo.replace('expected_width,height,query', 'expected_width,height,echoed_query')
report = expect(echo)
assert report['accesses'][0]['coordinate_receptions']
assert not report['accesses'][0]['coordinate_draws']
expect(echo, (ORDER,), ('oracle-query-coordinate-received',))
expect(echo, (SAMPLED,), (NOT_SAMPLE,))

# Ordering checks contributing draws; it does not require an exact sample.
mod_one = source.replace(draw, draw.replace('(query,after)', '(sample,after)') +
    '    local V: let one = OneIndex();\n    local V: let query = ModIndex(sample,one);\n')
constant = source.replace(draw, '    local V: let query = ZeroIndex();\n')
for text in (mod_one, constant):
    report = expect(text, (ORDER, RESPONSES))
    assert 'coordinate_sample' not in report['accesses'][0]
    expect(text, (SAMPLED,), (NOT_SAMPLE,))
    expect(text, (ORDER, SAMPLED, RESPONSES), (NOT_SAMPLE,))
assert expect(mod_one, (ORDER,))['accesses'][0]['coordinate_draws']
assert not expect(constant, (ORDER,))['accesses'][0]['coordinate_draws']

# Bound 1 is not known to equal the independent height input. It is an exact
# sample, but compatible height is unknown. A check of that same height 1 passes.
bound_one = source.replace(draw, '    local V: let one = OneIndex();\n' +
    draw.replace('observed,height', 'observed,one'))
report = expect(bound_one, (ORDER, RESPONSES))
assert report['accesses'][0]['coordinate_sample']
assert not report['accesses'][0]['sample_bound_matches_height']
expect(bound_one, (SAMPLED,), (BOUND,))
expect(bound_one, (ORDER, SAMPLED, RESPONSES), (BOUND,))
height_one = bound_one.replace('expected_width,height,query', 'expected_width,one,query')
expect(height_one, (ORDER, SAMPLED, RESPONSES))
# Separate equal constants do not manufacture exact local value identity.
separate_height = height_one.replace('    local V: let ok = CheckRow',
    '    local V: let also_one = OneIndex();\n    local V: let ok = CheckRow')
separate_height = separate_height.replace('expected_width,one,query', 'expected_width,also_one,query')
expect(separate_height, (SAMPLED,), (BOUND,))

# Ordinary returns are not acceptance sinks; the selected result must be bool.
returned = source.replace('    control::require(ok);', '')
unguarded = (UNGUARDED, 'oracle-response-unauthenticated')
expect(returned, (ORDER,), unguarded)
selected = expect(returned, (ORDER, '--accept-result=0', SAMPLED, RESPONSES))
assert selected['acceptance_result'] == 0 and selected['acceptance_role'] == 'V'
expect(returned, ('--accept-result=1',), (*unguarded, 'oracle-acceptance-result'))
nonbool = returned.replace('outputs (V bool);', 'outputs (V index);').replace('    return ok;\n  }\n\n  instance', '    return height;\n  }\n\n  instance')
expect(nonbool, ('--accept-result=0',), (*unguarded, 'oracle-acceptance-result'))

# Zero-based ALL entry ports: P's Boolean at 0 cannot entail V's check at 1.
mixed = returned.replace('inputs (P values:', 'inputs (P claimed:bool,P values:')
mixed = mixed.replace('outputs (V bool);', 'outputs (P bool,V bool);').replace('    return ok;\n  }\n\n  instance', '    return (claimed,ok);\n  }\n\n  instance')
p_result = expect(mixed, ('--accept-result=0',), unguarded)
v_result = expect(mixed, ('--accept-result=1',))
assert (p_result['acceptance_role'], v_result['acceptance_role']) == ('P', 'V')
received_bool = returned.replace('inputs (P values:', 'inputs (P claimed:bool,P values:')
received_bool = received_bool.replace('    return ok;\n  }\n\n  instance',
    '    message verdict: P(claimed) -> V(received_verdict);\n    return received_verdict;\n  }\n\n  instance')
peer = expect(received_bool, ('--accept-result=0',), unguarded)
assert peer['acceptance_role'] == 'V'  # Received owner is V; no V check is entailed.

# Unknown nonce transfer coverage is explicit even without oracle accesses.
nonce = (examples / 'group-exchange.pir').read_text()
expect(nonce)
for flag in (ORDER, RESPONSES, SAMPLED):
    report = expect(nonce, (flag,), ('oracle-unsupported-provenance',))
    assert len(report['findings']) == 2  # curve.commit and curve.response

# Inspect the ACTUAL constructor output, then compile it through native MLIR.
# Repeated transcript derivations at P and V remain separate sample occurrences.
# No root/state byte equality or transcript-root equality is invented to link them.
random_source = editable_source(corpus / 'oracle-provenance-random.pir')
descriptor = (corpus / 'oracle-provenance-random.construction.pir').read_text()
random_draw = '    local V: let (query,after) = DrawIndex(coins,height);\n'
early = random_source.replace(random_draw, '').replace('    local P: let (root,state)',
    random_draw + '    local P: let (root,state)')
late = random_source.replace('    local V: let ok',
    '    local V: let (later,final) = DrawIndex(after,height);\n    local V: let ok')
OPENING = 'oracle-opening-coordinate-unresolved'
EARLY = 'oracle-query-before-publication'
LATE = 'oracle-query-after-response'


def construct(text, contract=descriptor, refusal=None):
    directory = records('construction')
    folder = Path(directory)
    path = folder / 'source.pir'
    desc = folder / 'construction.pir'
    candidate = folder / 'candidate.json'
    common = folder / 'common.json'
    path.write_text(text)
    desc.write_text(contract)
    result = call(['protocol-construct', path, desc])
    if refusal:
        assert result.returncode > 0 and names(result.stderr, refusal), result
        return None
    assert result.returncode == 0, result.stderr
    constructed = json.loads(result.stdout)
    candidate.write_text(result.stdout)
    common_text = json.dumps(constructed[2])
    common.write_text(common_text)
    for args in (['protocol-check-construction', path, desc, candidate],
                 ['protocol-compile', common]):
        result = call(args)
        assert result.returncode == 0, result.stderr
    return common_text


for text, source_findings, constructed_findings in (
        (random_source, (), (OPENING,)),
        (early, (EARLY,), (OPENING, EARLY, UNABSORBED)),
        (late, (LATE,), (OPENING, LATE))):
    expect(text)
    expect(text, (SAMPLED,))
    expect(text, (ORDER, RESPONSES, SAMPLED), source_findings)
    common = construct(text)
    expect(common, findings=(OPENING,))
    report = expect(common, (ORDER, RESPONSES, SAMPLED), constructed_findings)
    access = report['accesses'][0]
    assert access['opening'] and access['publication'] and access['root_reception']
    assert not access['opening_coordinate_linked']
    assert access['coordinate_sample'] and access['sample_bound_matches_height']
    assert bool(access['publication_bound_draws']) == (text != early)
    if text == late:
        assert sum(f['code'] == LATE for f in report['findings']) == 2

# The existing collection-based constructor fixture is also analyzed unchanged.
# Its received list does not grant local root-element identity or absorption.
collection_source = (corpus / 'oracle-construction.pir').read_text()
collection_descriptor = (corpus / 'oracle-construction.construction.pir').read_text()
collection_common = construct(collection_source, collection_descriptor)
expect(collection_common, findings=(OPENING,))
collection_report = expect(collection_common, (ORDER, RESPONSES, SAMPLED),
                           (OPENING, UNABSORBED, 'oracle-publication-unresolved'))
assert 'publication' not in collection_report['accesses'][0]
assert 'root_reception' not in collection_report['accesses'][0]

# Construction indexes only V ports. The identical index 0 below selects P for
# oracle acceptance, but V for construction; descriptor index 1 is out of range.
mixed_random = random_source.replace('    control::require(ok);', '')
mixed_random = mixed_random.replace('inputs (P values:', 'inputs (P claimed:bool,P values:')
mixed_random = mixed_random.replace('outputs (V bool);', 'outputs (P bool,V bool);')
mixed_random = mixed_random.replace('    return ok;\n  }\n\n  instance', '    return (claimed,ok);\n  }\n\n  instance')
assert expect(mixed_random, ('--accept-result=0',), unguarded)['acceptance_role'] == 'P'
assert expect(mixed_random, ('--accept-result=1',))['acceptance_role'] == 'V'
constructed_mixed = construct(mixed_random)
expect(constructed_mixed, ('--accept-result=1',), (OPENING,))
construct(mixed_random, descriptor.replace('accept 0;', 'accept 1;'),
          refusal='construction-acceptance-index')

# CLI rejects duplicate, malformed, unknown, or inspection-only options.
for flags in ((SAMPLED, SAMPLED), ('--accept-result=-1',), ('--accept-result=x',),
              ('--accept-result=4294967296',), ('--accept-result=0', '--accept-result=1'),
              (ORDER, ORDER), ('--unknown-policy',)):
    result = call(['oracle-check', corpus / 'oracle-provenance.pir', 'main', *flags])
    assert result.returncode > 0 and names(result.stderr, 'unsupported-option'), result
result = call(['oracle-inspect', corpus / 'oracle-provenance.pir', 'main', SAMPLED])
assert result.returncode > 0 and names(result.stderr, 'unsupported-option')
assert '--sampled-queries' in call(['--help']).stdout

print(f'{commands.save()} admitted oracle provenance and CLI checks passed')
