"""Settings, observational equivalence, local reuse, and consumer workflows."""
import concurrent.futures
import hashlib
import json
import shutil
import subprocess
import tomllib


def command(tools, *args):
    return [tools.runtime, '--json', *args, f'--compiler={tools.compiler}']


def project(tools, journal, directory):
    root = directory/'project'
    journal.json(command(tools, 'new', root))
    (root/'main.zkc').write_text('''module example;
fn increment(value:index)->index{return value+1;}
entry fn Main(value:index)->index{return increment(value);}
''')
    (root/'inputs/example.Main/arguments.json').write_text('{"value":"7"}')
    return root


def test_settings_reports_and_execution_are_observational(toolchain, journal, directory):
    root = project(toolchain, journal, directory)
    manifest = root/'zkc.toml'
    manifest.write_text(manifest.read_text()+'''
[build]
finite-bulk=false
[profile.native]
finite-bulk=true
release-storage=true
[profile.alternatives]
simplify=false
finite-bulk=false
release-storage=true
fuse-vector-reductions=true
fuse-collect-fold=true
calculation-batching=false
''')
    view = journal.json(command(toolchain, 'inspect', '--view=project', '--profile=native'), cwd=root)
    assert view['settings']['values']['finite-bulk'] is True
    assert view['settings']['origins']['finite-bulk'] == 'profile.native'
    plain = directory/'plain.zkpkg'
    observed = directory/'observed.zkpkg'
    report = directory/'observations'
    first = journal.json(command(toolchain, 'compile', '--profile=native', f'--output={plain}'), cwd=root)
    second = journal.json(command(toolchain, 'compile', '--profile=native', f'--output={observed}',
        f'--report={report}', '--dump=entry,protocol,participant,exec,execution,physical'), cwd=root)
    assert plain.read_bytes() == observed.read_bytes()
    assert first['package_sha256'] == second['compilation']['package_sha256']
    assert len(second['compilation']['toolchain']['binary_sha256']) == 64
    phases = second['compilation']['phases']
    assert [phase['phase'] for phase in phases] == ['entry','protocol','execution','physical']
    assert all(phase['operations'] > 0 and 'ir' not in phase for phase in phases)
    assert all((report/phase['ir_file']).is_file() for phase in phases)
    assert len(second['report']['files']) == len(phases) + 3
    assert json.loads((report/'time-trace.json').read_text())['traceEvents']
    assert second['compilation']['passes']
    assert all(phase['unit'][0] == 'example::Main' for phase in phases)
    assert len({phase['ir_file'] for phase in phases}) == len(phases)
    assert json.loads((report/'command.json').read_text()) == second
    overridden = journal.json(command(toolchain, 'compile', '--profile=native', '--no-finite-bulk',
        f'--output={directory/"override.zkpkg"}'), cwd=root)
    assert overridden['settings']['values']['finite-bulk'] is False
    assert overridden['settings']['origins']['finite-bulk'] == 'request'
    alternatives = journal.json(command(toolchain, 'compile', '--profile=alternatives',
        f'--output={directory/"alternatives.zkpkg"}'), cwd=root)
    published = json.loads((directory/'alternatives.zkpkg').read_text())['options']
    assert published == {name.replace('-', '_'): value
        for name, value in alternatives['settings']['values'].items()}
    journal.json(command(toolchain, 'compile', '--profile=absent'), cwd=root, refuses='source-profile-missing')
    journal.json(command(toolchain, 'compile', f'--report={report}'), cwd=root, refuses='report-exists')
    ordinary = journal.json(command(toolchain, 'run', '--no-results'), cwd=root)
    counted = journal.json(command(toolchain, 'run', '--no-results',
        f'--report={directory/"run-report"}'), cwd=root)
    assert ordinary['execution'] == counted['execution']
    assert set(counted['host_stages']) >= {'admission','input_decoding_and_validation','preparation',
        'sdk_execution','diagnostic_materialization'}
    capabilities = journal.json(command(toolchain, 'inspect', '--view=toolchain'), cwd=directory)
    instrument = command(toolchain, 'run', '--no-results', '--instrument=counts')
    if capabilities['toolchain']['execution_counts']:
        instrumented = journal.json(instrument, cwd=root)
        assert ordinary['execution'] == instrumented['execution']
        assert instrumented['execution_counts']['events']['charged_instructions'] > 0
        assert sum(b['calls'] for b in instrumented['binding_contexts']) == sum(
            instrumented['execution_counts']['operations'].values())
        assert all(set(b) == {'contract','arguments','implementation','calls'}
            for b in instrumented['binding_contexts'])
    else:
        rejected_report = directory/'unsupported-instrument'
        journal.json([*instrument, f'--report={rejected_report}'], cwd=root,
            refuses='instrument-unavailable')
        assert not rejected_report.exists()
    pinned = [toolchain.runtime, '--json', 'inspect', '--package='+str(plain),
        '--sha256='+first['package_sha256']]
    journal.json(pinned, cwd=directory)
    journal.json([*pinned, '--profile=native'], cwd=directory, refuses='cli-usage')


def test_cache_invalidations_corruption_quota_and_concurrency(toolchain, journal, directory):
    root = project(toolchain, journal, directory)
    cache = directory/'cache'
    def build(name, *args):
        output = directory/f'{name}.zkpkg'
        result = journal.json(command(toolchain, 'compile', f'--cache={cache}', f'--output={output}', *args), cwd=root)
        return result, output.read_bytes()
    first, package = build('first')
    hit, same = build('hit')
    assert first['cache']['status'] == 'miss' and first['cache']['retained']
    assert hit['cache']['status'] == 'hit' and same == package
    changed, other_policy = build('setting', '--no-finite-bulk')
    assert changed['cache']['status'] == 'miss' and changed['cache']['key'] != hit['cache']['key']
    bypassed, same = build('observed', f'--report={directory/"fresh-observation"}')
    assert bypassed['cache']['status'] == 'recomputed' and package == same
    entry = cache/f'{hit["cache"]["key"]}.zkcache'
    entry.write_bytes(b'corrupt')
    repaired, same = build('repaired')
    assert repaired['cache']['status'] == 'miss' and same == package
    # A self-consistent digest cannot substitute a different executable policy.
    entry.write_bytes(hashlib.sha256(other_policy).hexdigest().encode()+b'\n'+other_policy)
    repaired, same = build('policy-repaired')
    assert repaired['cache']['status'] == 'miss' and same == package
    source = root/'main.zkc'
    source.write_text(source.read_text()+'\n// New captured source identity.\n')
    changed, _ = build('source')
    assert changed['cache']['status'] == 'miss' and changed['cache']['key'] != hit['cache']['key']
    # A cold store exercises concurrent publication rather than concurrent hits.
    cache = directory/'cold-cache'
    # Writers sharing a cache can execute concurrently; publications are complete.
    def compile_concurrently(index):
        process = subprocess.run(command(toolchain, 'compile', f'--cache={cache}',
            f'--output={directory/f"parallel-{index}.zkpkg"}'), cwd=root, capture_output=True, text=True)
        assert process.returncode == 0, process.stderr+process.stdout
        return json.loads(process.stdout)
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        assert all(result['status'] == 'compiled' for result in pool.map(compile_concurrently, range(3)))
    assert sum(p.stat().st_size for p in cache.glob('*.zkcache')) <= 256*1024*1024
    main = root/'main.zkc'
    main.write_text(main.read_text()+'\nentry fn Other(value:index)->index{return increment(value); }\n')
    selected, _ = build('selected-main', 'Main')
    other, _ = build('selected-other', 'Other')
    assert selected['cache']['key'] != other['cache']['key']
    assert selected['cache']['status'] == other['cache']['status'] == 'miss'
    compiler = directory/'selected-compiler'
    shutil.copy2(toolchain.compiler, compiler)
    def selected_compiler(name):
        return journal.json([toolchain.runtime, '--json', 'compile', 'Main',
            f'--compiler={compiler}', f'--cache={cache}',
            f'--output={directory/name}'], cwd=root)
    copied = selected_compiler('copied.zkpkg')
    assert selected_compiler('copied-hit.zkpkg')['cache']['status'] == 'hit'
    # ELF permits trailing data; the executable remains usable with a new hash.
    with compiler.open('ab') as stream:
        stream.write(b'\ncompiler-identity-control\n')
    replaced = selected_compiler('replaced.zkpkg')
    assert replaced['cache']['status'] == 'miss'
    assert replaced['cache']['key'] != copied['cache']['key']


def test_generic_protocol_cache_keeps_specializations_distinct(toolchain, journal, directory):
    root = directory / 'project'
    root.mkdir()
    (root / 'zkc.toml').write_text('format="zkc.project/0"\n[modules]\nexample="main.zkc"\n')
    (root / 'main.zkc').write_text('''module example;
protocol Echo<T:Type> roles(P)(value:T@P)->(out:T@P){return value;}
''')
    cache = directory / 'cache'

    def build(name, selector):
        output = directory / f'{name}.zkpkg'
        result = journal.json(command(toolchain, 'compile', selector,
            f'--cache={cache}', f'--output={output}'), cwd=root)
        return result, output.read_bytes()

    first, original = build('first', 'Echo<bool>')
    hit, same = build('hit', 'Echo<bool>')
    assert first['cache']['status'] == 'miss'
    assert hit['cache']['status'] == 'hit' and same == original
    other, other_package = build('other', 'Echo<index>')
    assert other['cache']['status'] == 'miss'
    assert other['cache']['key'] != hit['cache']['key']
    # A valid package and matching digest cannot replace another specialization.
    entry = cache / f'{hit["cache"]["key"]}.zkcache'
    entry.write_bytes(hashlib.sha256(other_package).hexdigest().encode()+b'\n'+other_package)
    repaired, same = build('repaired', 'Echo<bool>')
    assert repaired['cache']['status'] == 'miss' and same == original


def test_test_recipes_diagnostics_and_toolchain_outside_project(toolchain, journal, directory):
    capabilities = journal.json(command(toolchain, 'inspect', '--view=toolchain'), cwd=directory)
    assert len(capabilities['toolchain']['binary_sha256']) == 64
    assert capabilities['toolchain']['phases'] == ['entry','protocol','participant','exec','execution','physical']
    root = project(toolchain, journal, directory)
    modules = tomllib.loads((root/'zkc.toml').read_text())['modules']
    low_level = [toolchain.compiler, 'language-check', '--source-format=zkc',
        *(f'--module={name}={root/path}' for name,path in modules.items())]
    failed_publication = subprocess.run([*low_level, f'--observations={root}'],
        capture_output=True, text=True, timeout=30)
    assert failed_publication.returncode > 0 and not failed_publication.stdout
    assert 'source.observation-io' in failed_publication.stderr
    api = journal.json(command(toolchain, 'inspect', '--view=api'), cwd=root)
    assert api['checked']['api']['format'] == 'zkc.source-api/0'
    placement = journal.json(command(toolchain, 'inspect', '--view=placement'), cwd=root)
    assert placement['checked']['declarations']
    manifest = root/'zkc.toml'
    manifest.write_text(manifest.read_text()+'''
[test.check]
entry="Main"
[test.run]
entry="Main"
operation="run"
args=["--input=inputs/example.Main/arguments.json", "--no-results"]
[test.refusal]
entry="Absent"
expect="source-compilation"
''')
    result = journal.json(command(toolchain, 'test'), cwd=root)
    assert result['status'] == 'tested' and all(t['passed'] for t in result['tests'])
    outside = journal.json(command(toolchain, 'test', 'run', f'--project={manifest}'), cwd=directory)
    assert outside['tests'][0]['passed']
    source = root/'main.zkc'
    source.write_text('module example;\nprotocol Broken roles(P)(')
    result = journal.json(command(toolchain, 'compile', f'--report={directory/"failure"}'),
        cwd=root, refuses='source-compilation')
    assert result['compiler_diagnostics']['completed'] is False
    assert len(result['compiler_diagnostics']['toolchain']['binary_sha256']) == 64
    assert result['compiler_diagnostics']['diagnostics']
    assert (directory/'failure/command.json').is_file()
    cached_failure = journal.json(command(toolchain, 'compile', f'--cache={directory/"failure-cache"}'),
        cwd=root, refuses='source-compilation')
    assert str(source) in cached_failure['diagnostics']
    catalog = cached_failure['compiler_diagnostics']['sources']
    assert any(item['path'] == str(source) and item['origin'] == 'captured' for item in catalog)
    assert catalog[-1]['origin'] == 'installation'
    for diagnostic in cached_failure['compiler_diagnostics']['diagnostics']:
        for span in [diagnostic, *diagnostic['related']]:
            if 'source' in span:
                assert 0 <= span['source'] < len(catalog)


def test_nested_calculations_and_deployments_share_settings_and_distinct_observations(toolchain, journal, directory):
    root = project(toolchain, journal, directory)
    (root/'main.zkc').write_text('''module example;
fn increment(value:index)->index{return value+1;}
fn twice(value:index)->index{return value*2;}
protocol Check roles(P,V)(expected:bool@(P,V),candidate:bool@P)->(accepted:bool@V){
  let received=send P->V(candidate);
  let accepted@V=received==expected;
  return(accepted=accepted);
}
proof Family=Check{prover P;verifier V;public{expected};accept accepted;construction authored;}
entry fn Main(value:index,expected:bool,candidate:bool){
  let a=increment(value);
  let b=twice(a);
  let joint=Check::run(Check::Inputs{
    P:Check::Inputs::P{expected:expected,candidate:candidate},
    V:Check::Inputs::V{expected:expected}});
  let public=Family::Public{expected:expected};
  let produced=Family::prove(public,Family::Witness{candidate:candidate});
  let verified=Family::verify(public,produced.proof);
  return(b,joint,verified);
}
''')
    (root/'inputs/example.Main/arguments.json').write_text(
        '{"value":"7","expected":true,"candidate":true}')
    plain = directory/'plain.zkpkg'
    observed = directory/'observed.zkpkg'
    journal.json(command(toolchain, 'compile', 'Main', '--no-calculation-batching',
        '--release-storage', f'--output={plain}'), cwd=root)
    report = journal.json(command(toolchain, 'compile', 'Main', '--no-calculation-batching',
        '--release-storage', f'--output={observed}', f'--report={directory/"nested-report"}',
        '--dump=entry,protocol,participant,exec,execution,physical'), cwd=root)
    assert plain.read_bytes() == observed.read_bytes()
    package = json.loads(observed.read_text())
    artifact = json.loads(package['artifact'])
    assert len(artifact['calculations']) >= 2
    assert {child['operation'] for child in artifact['deployments']} == {'run','prove','verify'}
    assert all(json.loads(child['package'])['options'] == package['options']
        for child in artifact['deployments'])
    phases = report['compilation']['phases']
    assert report['compilation']['dropped_phases'] == 0
    assert all(phase['unit'][0] == 'example::Main' for phase in phases)
    assert len({phase['ir_file'] for phase in phases}) == len(phases)
    assert sum(phase['phase'] == 'physical' for phase in phases) >= 5
    assert all(row['operation'] == 'builtin.module' for row in report['compilation']['passes'])
    assert all('builtin.module' in phase['histogram'] for phase in phases)
    assert all((directory/'nested-report'/phase['ir_file']).is_file() for phase in phases)
    executed = journal.json(command(toolchain, 'run', 'Main', '--allow-authored', '--no-results',
        f'--report={directory/"execution-report"}'), cwd=root)
    assert executed['execution']['completed']
    assert {call['operation'] for call in executed['execution']['calls']} >= {'numeric','run','prove','verify'}
