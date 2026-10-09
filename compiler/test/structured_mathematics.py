"""Native structured mathematics: independent requirements and actual SSA edges."""
import copy
import hashlib
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/mathematical'
source = (FIXTURES / 'sumcheck.mlir').read_text()
requirements = json.loads((FIXTURES / 'sumcheck.requirements.json').read_text())
source_file = OUT / 'source.mlir'
source_file.write_text(source)
requirement_file = OUT / 'requirements.json'
requirement_file.write_text(json.dumps(requirements))


def changed(text, before, after):
    assert text.count(before) == 1, (before, text.count(before))
    return text.replace(before, after)


def checked(text=source, entry='reduction', requirement=requirements, flags=(), refuses=None):
    requirement_file.write_text(json.dumps(requirement))
    return commands.source('protocol-checked-bundle', text, f'--entry={entry}',
                           f'--requirements={requirement_file}', *flags, refuses=refuses)


with case('checked bundles bind original requirements and concrete connector'):
    for entry in ['reduction', 'terminal']:
        for suffix, flags in [('', ()), ('_plain', ('--no-simplify',)), ('_release', ('--release-storage',)), ('_factored', ('--fix-polynomial-factors',))]:
            text = checked(entry=entry, flags=flags)
            result = json.loads(text)
            (OUT / f'{entry}{suffix}.checked.json').write_text(text)
            (OUT / f'{entry}{suffix}.bundle').write_text(result['bundle'])
            report = result['correspondence']
            assert result['format'] == 'zkc.checked-run/0'
            assert report['source_sha256'] == hashlib.sha256(source.encode()).hexdigest()
            assert report['requirements_sha256'] == hashlib.sha256(report['requirement_source'].encode()).hexdigest()
            # The digest uses the exact compiler serialization before wrapping.
            bundle_text = commands.source('protocol-bundle', source, f'--entry={entry}', *flags).strip()
            assert json.loads(bundle_text) == json.loads(result['bundle'])
            assert report['bundle_sha256'] == hashlib.sha256(result['bundle'].encode()).hexdigest()
            [record] = report['requirements']
            assert record['connector'] == [[i, i] for i in range(5)]
            assert [r['degree'] for r in record['rounds']] == [2, 2]
            assert [r['query'] for r in record['rounds']] == ['query0', 'query1']
            assert record['original_inputs'] == [0, 1, 2] and record['original_service_inputs'] == [3]
    for name in ['array', 'univariate']:
        text = commands.source('protocol-bundle', (FIXTURES / f'{name}.mlir').read_text())
        (OUT / f'{name}.bundle').write_text(text)

with case('checked mode cannot silently become unchecked'):
    commands.source('protocol-checked-bundle', source, refuses='checked-bundle-requirement-missing')
    checked(requirement={'format': requirements['format'], 'requirements': []}, refuses='polynomial-requirement-count')
    duplicate = copy.deepcopy(requirements)
    duplicate['requirements'] *= 2
    checked(requirement=duplicate, refuses='polynomial-requirement-duplicate')
    for field, value in [('family', 'unknown'), ('arity', 2), ('claim', -1), ('subjects', [0, 0])]:
        altered = copy.deepcopy(requirements)
        altered['requirements'][0][field] = value
        checked(requirement=altered, refuses='polynomial-requirement-format')
    for field, value in [('claim', 99), ('recipe', 'missing'), ('subjects', [1, 0]),
                         ('residual_point', [3, 2]), ('terminal_subjects', [1, 0]),
                         ('terminal_scalar', 3), ('service', 2), ('verifier', 'P')]:
        altered = copy.deepcopy(requirements)
        altered['requirements'][0][field] = value
        checked(requirement=altered, refuses='polynomial-correspondence')

candidate = commands.verified(source, None, '--zkc-project-protocol=simplify=false')
requirement_file.write_text(json.dumps(requirements))
candidate_file = OUT / 'candidate.mlir'


def check_candidate(text, refuses=None):
    # Mutations below are valid admitted IR. Refusal must come from the
    # independent correspondence check, not merely parsing or type checking.
    commands.verified(text)
    candidate_file.write_text(text)
    return commands.run([compiler, 'protocol-check-reductions', str(source_file),
                         str(requirement_file), str(candidate_file)], refuses=refuses)


with case('honest independently supplied participant'):
    assert json.loads(check_candidate(candidate))['requirements'][0]['arity'] == 2

mutations = [
    ('claim substitution', '%7 = algebra.field_equal %6, %arg2', '%7 = algebra.field_equal %6, %0'),
    ('round evaluates another payload', '%13 = "poly.evaluate"(%11, %1)', '%13 = "poly.evaluate"(%3, %1)'),
    ('round endpoint repeated', '%6 = algebra.field_add %4, %5', '%6 = algebra.field_add %4, %4'),
    ('guard operands reversed', '%7 = algebra.field_equal %6, %arg2', '%7 = algebra.field_equal %arg2, %6'),
    ('wrong final evaluation point', '%17 = "poly.evaluate"(%11, %16)', '%17 = "poly.evaluate"(%11, %8)'),
    ('wrong challenge sent', '"protocol.send"(%16)', '"protocol.send"(%8)'),
    ('wrong received coefficients', '%11 = "poly.from_coefficients"(%10)', '%11 = "poly.from_coefficients"(%2)'),
    ('wrong running scalar', '%15 = algebra.field_equal %14, %9', '%15 = algebra.field_equal %14, %arg2'),
    ('subject permutation', '"protocol.finish"(%arg0, %arg1, %8, %16, %17)', '"protocol.finish"(%arg1, %arg0, %8, %16, %17)'),
    ('challenge permutation', '"protocol.finish"(%arg0, %arg1, %8, %16, %17)', '"protocol.finish"(%arg0, %arg1, %16, %8, %17)'),
    ('missing final draw', '"protocol.finish"(%arg0, %arg1, %8, %16, %17)', '"protocol.finish"(%arg0, %arg1, %8, %8, %17)'),
    ('wrong residual scalar', '"protocol.finish"(%arg0, %arg1, %8, %16, %17)', '"protocol.finish"(%arg0, %arg1, %8, %16, %9)'),
    ('terminal point permutation', '%5 = "poly.evaluate"(%4, %arg2, %arg3)', '%5 = "poly.evaluate"(%4, %arg3, %arg2)'),
    ('terminal scalar substitution', '%6 = algebra.field_equal %5, %arg4', '%6 = algebra.field_equal %5, %arg2'),
]
for name, before, after in mutations:
    with case(name):
        check_candidate(changed(candidate, before, after), refuses='polynomial-correspondence')

with case('terminal recipe mutation'):
    head, terminal = candidate.split('instance = "terminal"', 1)
    terminal = changed(terminal, '"poly.multiply"(%0, %0)', '"poly.multiply"(%0, %1)')
    check_candidate(head + 'instance = "terminal"' + terminal, refuses='polynomial-correspondence')

with case('constant terminal decision'):
    altered = changed(candidate, '      "protocol.finish"(%6) : (i1)',
                      '      %yes = arith.constant true\n      "protocol.finish"(%yes) : (i1)')
    check_candidate(altered, refuses='polynomial-correspondence')

with case('same body under another terminal recipe name'):
    start, rest = source.split('"protocol.func"()', 1)
    helper = start[start.index('func.func'):]
    altered = start + helper.replace('@recipe', '@copy') + '"protocol.func"()' + rest
    before, terminal = altered.rsplit('%f = func.call @recipe', 1)
    checked(before + '%f = func.call @copy' + terminal, refuses='polynomial-correspondence')

with case('round coefficient arrays must fit the derived degree'):
    invalid = source.replace('tensor<3x!algebra.field', 'tensor<2x!algebra.field')
    commands.source('protocol-bundle', invalid, '--entry=reduction', refuses='polynomial-formation')

with case('factorwise fixing retains two shared table leaves'):
    fixed = commands.verified(candidate, None, '--zkc-fix-polynomial-factors')
    assert fixed.count('"poly.fix_table"') == 2
    assert '"poly.fix"' not in fixed
    # Both versions preserve the closed correspondence: only prover calculation
    # changed. Recognition of verifier operations remains exact.
    check_candidate(fixed)
    plain = commands.verified(candidate, None, '--zkc-eliminate-polynomials')
    realized = commands.verified(fixed, None, '--zkc-eliminate-polynomials')
    assert '!poly.polynomial' not in plain and '!poly.polynomial' not in realized
    counts = {name: {op: text.count(op) for op in ['algebra.field_add', 'algebra.field_multiply', 'algebra.field_subtract', 'algebra.array_at']}
              for name, text in [('plain', plain), ('factorwise', realized)]}
    (OUT / 'operation-counts.json').write_text(json.dumps(counts, indent=2))


with case('shared table competitor uses the same mathematical realization'):
    comparison = {}
    for name, fixture, flags, passes in [
            ('fixing', 'fixing', ('--fix-polynomial-factors',), ('--zkc-fix-polynomial-factors',)),
            ('fixing_plain', 'fixing', ('--no-simplify',), ()),
            ('fixing_competitor', 'fixing-competitor', ('--no-simplify',), ())]:
        text = (FIXTURES / f'{fixture}.mlir').read_text()
        (OUT / f'{name}.bundle').write_text(commands.source('protocol-bundle', text, *flags))
        ir = commands.verified(text, None, '--zkc-project-protocol=simplify=false', *passes,
                               '--zkc-eliminate-polynomials', '--zkc-simplify-participant')
        comparison[name] = {op: ir.count(op) for op in ['algebra.field_add', 'algebra.field_multiply', 'algebra.field_subtract', 'algebra.array_at']}
    assert comparison['fixing'] == comparison['fixing_competitor'], comparison
    # CSE can already recover sharing. This fixture trades one multiply for
    # five additions; equal backend cost is not assumed and no speedup is asserted.
    (OUT / 'fixing-comparison.json').write_text(json.dumps({
        'pipeline': ['project(simplify=false)', 'optional factorwise fixing',
                     'eliminate-polynomials', 'simplify-participant'],
        'scope': 'scalar IR comparison; post-elimination CSE is not in the native bundle pipeline',
        'counts': comparison}, indent=2))


with case('a bad retained source cannot be rescued by an honest candidate'):
    wrong = changed(source, '%ok0 = algebra.field_equal %sum0, %claim',
                    '%ok0 = algebra.field_equal %sum0, %zero')
    try:
        source_file.write_text(wrong)
        check_candidate(candidate, refuses='polynomial-correspondence')
    finally:
        source_file.write_text(source)

with case('a coherently projected query before its guard fails correspondence'):
    lines = source.splitlines()
    guard = next(i for i, line in enumerate(lines) if 'protocol.guard %ok0' in line)
    query = next(i for i, line in enumerate(lines) if '%r0 = "protocol.query"' in line)
    assert query > guard
    lines.insert(guard, lines.pop(query))
    checked('\n'.join(lines), refuses='polynomial-correspondence')

with case('an oversized round payload does not establish the required degree'):
    # Source construction fits; the receive domain now also admits degree 3.
    checked(source.replace('tensor<3x!algebra.field', 'tensor<4x!algebra.field'),
            refuses='polynomial-correspondence')

with case('canonical distinct interpolation points are checked before simplification'):
    univariate = (FIXTURES / 'univariate.mlir').read_text()
    for point in ['3', '03', '-1', '52435875175126190479447740508185965837690552500527637822603658699938581184513']:
        invalid = univariate.replace('10395434478220956956328808592063228334810757406296085889024', point)
        commands.source('protocol-bundle', invalid, refuses='polynomial-formation')


def single_math(length, arity, body):
    field = '!algebra.field<"bls12-381.fr">'
    array = f'tensor<{length}x{field}>'
    polynomial = f'!poly.polynomial<"bls12-381.fr", {arity}>'
    return f"""module {{ "protocol.module"() ({{
      "protocol.func"() ({{
      ^entry(%T: {array}, %x: {field}):
        %p = "poly.mle"(%T) : ({array}) -> {polynomial}
        {body}
        "protocol.return"(%value) : ({field}) -> ()
      }}) {{sym_name="main", function_type=({array}, {field}) -> {field},
          roles=["Solo"], input_roles=[["Solo"],["Solo"]], output_roles=[["Solo"]]}} : () -> ()
    }}) {{profile=#protocol.profile<protocol>}} : () -> () }}"""


with case('zero arity and empty prefix remain executable mathematics'):
    field = '!algebra.field<"bls12-381.fr">'
    poly0 = '!poly.polynomial<"bls12-381.fr", 0>'
    body = f"""%fixed = "poly.fix"(%p) : ({poly0}) -> {poly0}
        %value = "poly.evaluate"(%fixed) : ({poly0}) -> {field}"""
    commands.source('protocol-bundle', single_math(1, 0, body))

with case('full prefix fixing produces a zero-arity polynomial'):
    field = '!algebra.field<"bls12-381.fr">'
    body = f"""%fixed = "poly.fix"(%p, %x, %x) : (!poly.polynomial<"bls12-381.fr", 2>, {field}, {field}) -> !poly.polynomial<"bls12-381.fr", 0>
        %value = "poly.evaluate"(%fixed) : (!poly.polynomial<"bls12-381.fr", 0>) -> {field}"""
    commands.source('protocol-bundle', single_math(4, 2, body), '--fix-polynomial-factors')

with case('bounded polynomial expansion refuses before producing an executable'):
    field = '!algebra.field<"bls12-381.fr">'
    args = ', '.join(['%x'] * 16)
    types = ', '.join([field] * 16)
    body = f'%value = "poly.evaluate"(%p, {args}) : (!poly.polynomial<"bls12-381.fr", 16>, {types}) -> {field}'
    commands.source('protocol-bundle', single_math(65536, 16, body), refuses='polynomial-lowering')


with case('all verifier outputs must belong to the residual connector'):
    # Reassign the final existing P output to V and return V's actual final draw.
    altered = changed(source, '%next1, %delivered0, %delivered1)', '%next1, %delivered0, %r1)')
    altered = changed(altered, 'output_roles=[["V"],["V"],["V"],["V"],["V"],["P"],["P"]]',
                      'output_roles=[["V"],["V"],["V"],["V"],["V"],["P"],["V"]]')
    checked(altered, refuses='polynomial-correspondence: public-sumcheck: boundary map')

with case('unused invalid coefficients refuse before default simplification'):
    marker = ' %coefficients0 = "poly.coefficients"'
    extra = ' %unused = "poly.coefficients"(%round0) : (!poly.polynomial<"bls12-381.fr", 1>) -> tensor<2x!algebra.field<"bls12-381.fr">>\n'
    commands.source('protocol-bundle', changed(source, marker, extra + marker),
                    '--entry=reduction', refuses='polynomial-formation')

with case('participant passes remove dead polynomial observations before expansion'):
    field = '!algebra.field<"bls12-381.fr">'
    constant = f'%value = "algebra.constant"() {{value="0"}} : () -> {field}'
    projected = commands.verified(single_math(65536, 16, constant), None,
                                  '--zkc-project-protocol=simplify=false')
    assert '"poly.' not in projected
    # Insert after projection: otherwise demand-based projection removes this
    # chain and neither polynomial pass ever sees it.
    args = ', '.join(['%arg1'] * 15)
    types = ', '.join([field] * 15)
    chain = f'''%dead_p = "poly.mle"(%arg0) : (tensor<65536x{field}>) -> !poly.polynomial<"bls12-381.fr", 16>
      %dead_fixed = "poly.fix"(%dead_p, %arg1) : (!poly.polynomial<"bls12-381.fr", 16>, {field}) -> !poly.polynomial<"bls12-381.fr", 15>
      %dead_value = "poly.evaluate"(%dead_fixed, {args}) : (!poly.polynomial<"bls12-381.fr", 15>, {types}) -> {field}
      '''
    participant = changed(projected, '"protocol.finish"(', chain + '"protocol.finish"(')
    commands.verified(participant)
    for option in ['--zkc-fix-polynomial-factors', '--zkc-eliminate-polynomials']:
        result = commands.verified(participant, None, option)
        assert '"poly.' not in result and 'algebra.array_at' not in result

with case('domain formation does not promise interpolation within the expansion budget'):
    field = '!algebra.field<"bls12-381.fr">'
    polynomial = '!poly.polynomial<"bls12-381.fr", 1>'
    for count in [32, 64]:
        points = json.dumps([str(i) for i in range(count)])
        body = f'''%interpolant = "poly.interpolate"(%T) {{points={points}}} : (tensor<{count}x{field}>) -> {polynomial}
          %value = "poly.evaluate"(%interpolant, %x) : ({polynomial}, {field}) -> {field}'''
        text = single_math(count, 5 if count == 32 else 6, body)
        participant = commands.verified(text, None, '--zkc-project-protocol=simplify=false')
        if count == 32:
            lowered = commands.verified(participant, None, '--zkc-eliminate-polynomials')
            assert '!poly.polynomial' not in lowered
        else:
            commands.verified(participant, 'polynomial-lowering: static expansion exceeds 100000 work units',
                              '--zkc-eliminate-polynomials')
            commands.source('protocol-bundle', text, refuses='polynomial-lowering')

with case('constant tensor packing compiles under selected simplification'):
    field = '!algebra.field<"bls12-381.fr">'
    polynomial = '!poly.polynomial<"bls12-381.fr", 1>'
    body = f'''%one = "algebra.constant"() {{value="1"}} : () -> {field}
      %two = "algebra.constant"() {{value="2"}} : () -> {field}
      %table = tensor.from_elements %one, %two : tensor<2x{field}>
      %constant_table = "poly.mle"(%table) : (tensor<2x{field}>) -> {polynomial}
      %value = "poly.evaluate"(%constant_table, %x) : ({polynomial}, {field}) -> {field}'''
    for flags in [(), ('--no-simplify',)]:
        commands.source('protocol-bundle', single_math(2, 1, body), *flags)


with case('nonidentity ports preserve original requirements and actual handoff'):
    field = '!algebra.field<"bls12-381.fr">'
    array = f'tensor<4x{field}>'
    types = {name: field for name in ['claim', 'extra', 'r0', 'r1', 'next1',
                                     'delivered0', 'delivered1']}
    types.update(T=array, U=array, random='!protocol.service_ref<"random.bls12-381.fr/0">', accept='i1')

    def reorder(body, entry, inputs, outputs, input_roles, output_roles):
        lines = body.splitlines()
        for i, line in enumerate(lines):
            if line.startswith('^entry('):
                lines[i] = '^entry(' + ', '.join(f'%{name}: {types[name]}' for name in inputs) + '):'
            elif '"protocol.return"(' in line:
                lines[i] = ' "protocol.return"(' + ', '.join('%' + name for name in outputs) + ') : (' + ', '.join(types[name] for name in outputs) + ') -> ()'
            elif line.startswith('}) {sym_name='):
                lines[i] = '}) {sym_name="' + entry + '", function_type=(' + ', '.join(types[name] for name in inputs) + ') -> (' + ', '.join(types[name] for name in outputs) + '),'
            elif line.startswith(' roles='):
                roles = ['P', 'V'] if entry == 'reduction' else ['V']
                lines[i] = f' roles={json.dumps(roles)}, input_roles={json.dumps(input_roles)}, output_roles={json.dumps(output_roles)}}} : () -> ()'
        return '\n'.join(lines)

    prefix, reduction, terminal = source.split('"protocol.func"() ({')
    reduction = reorder(reduction, 'reduction', ['random', 'claim', 'T', 'extra', 'U'],
                        ['next1', 'delivered0', 'r1', 'U', 'r0', 'T', 'delivered1'],
                        [['V'], ['P', 'V'], ['P', 'V'], ['P'], ['P', 'V']],
                        [['V'], ['P'], ['V'], ['V'], ['V'], ['V'], ['P']])
    terminal = reorder(terminal, 'terminal', ['r1', 'U', 'claim', 'T', 'r0'], ['accept'],
                       [['V']] * 5, [['V']])
    permuted = prefix + '"protocol.func"() ({' + reduction + '\n"protocol.func"() ({' + terminal
    requirement = copy.deepcopy(requirements)
    requirement['requirements'][0].update(subjects=[2, 4], claim=1, service=0,
        residual_subjects=[5, 3], residual_point=[4, 2], residual_scalar=0,
        terminal_subjects=[3, 1], terminal_point=[4, 0], terminal_scalar=2)
    (OUT / 'permuted.mlir').write_text(permuted)
    for entry in ['reduction', 'terminal']:
        text = checked(permuted, entry=entry, requirement=requirement)
        (OUT / f'{entry}_permuted.checked.json').write_text(text)
        [record] = json.loads(text)['correspondence']['requirements']
        assert record['original_inputs'] == [1, 2, 4]
        assert record['original_service_inputs'] == [0]
        assert record['original_outputs'] == [0, 2, 3, 4, 5]
        assert record['service_port'] == 'service_0'
        assert record['connector'] == [[4, 3], [2, 1], [3, 4], [1, 0], [0, 2]]
    wrong = copy.deepcopy(requirement)
    wrong['requirements'][0]['residual_subjects'] = [3, 5]
    checked(permuted, requirement=wrong, refuses='polynomial-correspondence')

counted()
