#!/usr/bin/env python3
"""Generate isolated Lean application-placement experiments; never build dependencies.

Requires the package and test modules to have been built. It uses their cached
Lean search path, writes all generated sources and outputs under --records,
and invokes Lean directly without building dependencies. Source admission/body-family checks are separate
modules from application assembly. These are finite typed application chains,
not actual-root or native compiler benchmarks. The default is a small sharing
check; request the repeated size/count matrix explicitly.
"""
import argparse
import json
import os
import shutil
from pathlib import Path
import subprocess
import tempfile
import time

HEADER = '''import Tests.SourceConnectionPilot
import Tests.ConnectionPlacementMetrics
import Zkc.Construction.ConnectionTargetPlacement
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
noncomputable section
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionLibrary ConnectionCertificate ConnectionTargetPlacement
'''


def spine(size):
    result = '.empty'
    for _ in range(size):
        result = f'.step (fun model => Domain.View.calculation model (.indexConstant 0) [] [.data .index]) ({result})'
    return result


def base_source(size):
    instructions = ',\n'.join(['.instruction (.indexConstant "0") [] [.index] [] ""'] * size)
    extent = f'.empty (layout.length + {size})'
    for offset in reversed(range(size)):
        extent = f'.sequence (.calculation (layout.length + {offset}) (.indexConstant 0) [] [.data .index]) ({extent})'
    typed_body = '.ret .nil'
    for _ in range(size):
        typed_body = f'.letOp (.mark "") .nil .nil (.letOp (.calculate (.indexConstant 0) rfl) .nil .nil ({typed_body}))'
    alignment = '\n'.join(['    apply Alignment.calculation (.indexConstant 0) rfl .nil [] rfl rfl .nil'] * size)
    result = HEADER + f'''namespace PlacementCost.Body{size}
private def protocol (name : String) (body : Structured.Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, [], [], some ⟨["P", "V"], [], []⟩,
    [], some (.protocol ⟨name, []⟩), body⟩
def snapshot : Snapshot := {{ Tests.SourceConnectionPilot.snapshot with
  definitions := [protocol "work" (.block [{instructions}] (.ret [])),
    protocol "other" (.block [{instructions}] (.ret [])), protocol "main" (.block [] (.ret []))]
  contracts := [⟨"work", []⟩, ⟨"other", []⟩, ⟨"main", []⟩] }}
def workSignature : ProtocolSignature := ⟨"work", ["P", "V"], [], [], [], []⟩
def otherSignature : ProtocolSignature := {{workSignature with name := "other"}}
def mainSignature : ProtocolSignature := {{workSignature with name := "main"}}
def workBody : Region protocolDialect [] [] := {typed_body}
def otherBody : Region protocolDialect [] [] := workBody
def mainBody : Region protocolDialect [] [] := .ret .nil
structured_views snapshot helpers [] protocols [work, other, main]
example : Structured.check snapshot = .ok program := kernel_admission
def context : Context := .plain "main" ["P", "V"] 0 1
def routing : Original.Routing := ⟨snapshot, context, .validator, 0, [], [], [], []⟩
def template : SourceTemplate program.payload [] :=
  (SourceTemplate.build program.payload [] ⟨0, by decide⟩ 1 .nil).toOption.get (by decide +kernel)
def firstLibrary : Library program.payload [template.key] := .extend .empty template
def otherTemplate : SourceTemplate program.payload [template.key] :=
  (SourceTemplate.build program.payload [template.key] ⟨1, by decide⟩ 1 .nil).toOption.get (by decide +kernel)
def library : Bundle program.payload := ⟨[otherTemplate.key, template.key], .extend firstLibrary otherTemplate⟩
def entry : Entry program.payload template.key := ⟨[], .empty, template, rfl⟩
def otherEntry : Entry program.payload otherTemplate.key := ⟨[template.key], firstLibrary, otherTemplate, rfl⟩
def bodySpine : ConnectionTargetPrefix.Prefix := {spine(size)}
'''
    for label, template, entry in [('checkedBody', 'template', 'entry'), ('checkedOther', 'otherTemplate', 'otherEntry')]:
        result += f'''
def {label}Placement {{scope : Scope}} (context : ProtocolContext) (frames : ScopedFrames scope)
    (layout : Layout scope) : Placement {template}.key where
  context := context
  scope := scope
  arguments := .nil
  frames := frames
  layout := layout
  outputs := []
  history := none
  returns := .nil
  spine := bodySpine
  extent := layout.length + {size}
measured_placement_decl {label} : ∀ {{scope : Scope}} (routing : Original.Routing)
    (selection : Selection program.payload.definitions {entry}.earlierKeys)
    (context : ProtocolContext) (frames : ScopedFrames scope) (layout : Layout scope),
    CheckedBody {entry} routing selection ({label}Placement context frames layout) := by
  intro scope routing selection context frames layout
  refine ⟨?_, ?_⟩
  ·
{alignment}
    exact .done .nil .plain
  · exact {extent}
attribute [connection_target_body] {label}
#print axioms {label}
'''
    return result + f'end PlacementCost.Body{size}\n'


def source_form(count, mixed):
    form = '.done .nil'
    for index in reversed(range(count)):
        callee = 0 if mixed and index % 2 else 1
        signature = 'otherTemplate' if callee == 0 else 'template'
        form = f'.apply ⟨{callee}, by decide⟩ {signature}.key.signature [0,1] "call{index}" .nil ({form})'
    return form


def case_source(size, count, mixed, baseline=False):
    name = f'Placements{size}x{count}' + ('Mixed' if mixed else '')
    form = source_form(count, mixed)
    source = f'''import PlacementCost.Body{size}
{HEADER}
namespace PlacementCost.{name}
open PlacementCost.Body{size}
def source : Form [] library.keys [] [] := {form}
def target : ConnectionCertificate.Block := ({spine(size * count)} : ConnectionTargetPrefix.Prefix).block
set_option zkc.connection.requireReusableBodies true in
measured_placement_decl applications : Alignment routing {{}} program.payload.definitions library.keys
    (selection := .selected program.payload rfl library.library) [] 1 [] [] none
    ([] : ScopedFrames []) [] source target := by
  derive_connection_alignment
audit_placements applications {count} [checkedBody, checkedOther]
#print axioms applications
end PlacementCost.{name}
'''
    if baseline:
        source = source.replace(name, f'PerOccurrence{size}x{count}')
        source = source.replace('set_option zkc.connection.requireReusableBodies true in',
            'attribute [-connection_target_body] checkedBody checkedOther\n'
            'set_option zkc.connection.requireReusableBodies false in')
        source = source.replace(f'audit_placements applications {count} [checkedBody, checkedOther]',
            f'audit_exact_placements applications {count} {size}')
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tree', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--records', type=Path)
    parser.add_argument('--repetitions', type=int, default=1)
    parser.add_argument('--sizes', type=int, nargs='+', default=[1])
    parser.add_argument('--counts', type=int, nargs='+', default=[1, 2])
    parser.add_argument('--baseline-control', action='store_true',
                        help='also check eight distinct per-occurrence body declarations at size 4')
    parser.add_argument('--measure-memory', action='store_true',
                        help='record each Lean process peak RSS using GNU time')
    args = parser.parse_args()
    time_binary = shutil.which('time') if args.measure_memory else None
    if args.measure_memory and time_binary is None:
        parser.error('--measure-memory requires GNU time on PATH')
    if args.repetitions < 1 or any(value < 1 for value in args.sizes + args.counts):
        parser.error('repetitions, body sizes and placement counts must be positive')
    package = args.tree.resolve() / 'lean'
    records_path = (args.records or Path(tempfile.mkdtemp(prefix='zkc-target-placement-'))).resolve()
    generated = records_path / 'generated'
    sources = generated / 'PlacementCost'
    sources.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, LEAN_NUM_THREADS='2')
    if not environment.get('LEAN_PATH'):
        environment['LEAN_PATH'] = subprocess.check_output(
            ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=package,
            env=environment, text=True).strip()
    environment['LEAN_PATH'] = str(generated) + os.pathsep + environment['LEAN_PATH']
    records = []

    def check(module, repetition, representation):
        source = generated / (module.replace('.', '/') + '.lean')
        output = source.with_suffix('.olean')
        log_path = records_path / (module + f'-{repetition}.log')
        command = ['lean', '-j2', '-M16384', '-DwarningAsError=true',
                   '-DautoImplicit=false', '--root=' + str(generated),
                   '-o', str(output), str(source)]
        memory_path = records_path / (module + f'-{repetition}.rss')
        measured_command = ([time_binary, '--format=%M', '--output=' + str(memory_path), *command]
                            if time_binary else command)
        start = time.monotonic()
        run = subprocess.run(measured_command, cwd=package, env=environment,
                             text=True, capture_output=True, timeout=600)
        log = run.stdout + run.stderr
        log_path.write_text(log)
        receipt = dict(module=module, repetition=repetition, command=command,
                       returncode=run.returncode, module_seconds=time.monotonic() - start,
                       log=str(log_path), measurement_command=measured_command,
                       generated_module_bytes=source.stat().st_size,
                       representation_sizes=representation,
                       peak_rss_kib=int(memory_path.read_text().strip())
                           if time_binary and run.returncode == 0 else None)
        records.append(receipt)
        (records_path / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
        if run.returncode or 'sorryAx' in log or 'PLACEMENT-METRIC' not in log:
            raise RuntimeError(f'placement check failed: {module}; see {log_path}')
        metrics = []
        cursor = 0
        marker = 'PLACEMENT-METRIC '
        while (cursor := log.find(marker, cursor)) != -1:
            value, end = json.JSONDecoder().raw_decode(log[cursor + len(marker):])
            metrics.append(value)
            cursor += len(marker) + end
        if '.Placements' in module:
            for metric in metrics:
                if metric['inline_alignment_calculations'] or metric['generated_exact_bodies']:
                    raise RuntimeError(f'body proof was rebuilt at a placement: {module}')
        receipt.update(olean_bytes=output.stat().st_size, metrics=metrics)
        (records_path / 'results.json').write_text(json.dumps(records, indent=2) + '\n')
        print(json.dumps(dict(module=module, repetition=repetition, status='passed',
                              seconds=round(receipt['module_seconds'], 3))), flush=True)

    for size in args.sizes:
        (sources / f'Body{size}.lean').write_text(base_source(size))
        body_sizes = dict(
            units='UTF-8 bytes of generated Lean syntax; not native-export bytes',
            source_instructions=len(',\n'.join(
                ['.instruction (.indexConstant "0") [] [.index] [] ""'] * size).encode()),
            normalized_source_form=len('.done .nil'.encode()),
            target_prefix=len(spine(size).encode()))
        check(f'PlacementCost.Body{size}', 0, body_sizes)
        for count in args.counts:
            name = f'Placements{size}x{count}'
            (sources / (name + '.lean')).write_text(case_source(size, count, False))
            for repetition in range(args.repetitions):
                check('PlacementCost.' + name, repetition, dict(
                    units='UTF-8 bytes of generated Lean syntax; not native-export bytes',
                    source_form=len(source_form(count, False).encode()),
                    target_prefix=len(spine(size * count).encode())))
        if size == 4:
            name = 'Placements4x8Mixed'
            (sources / (name + '.lean')).write_text(case_source(size, 8, True))
            for repetition in range(args.repetitions):
                check('PlacementCost.' + name, repetition, dict(
                    units='UTF-8 bytes of generated Lean syntax; not native-export bytes',
                    source_form=len(source_form(8, True).encode()),
                    target_prefix=len(spine(size * 8).encode())))
            if args.baseline_control:
                name = 'PerOccurrence4x8'
                (sources / (name + '.lean')).write_text(case_source(4, 8, False, baseline=True))
                check('PlacementCost.' + name, 0, dict(
                    units='UTF-8 bytes of generated Lean syntax; not native-export bytes',
                    source_form=len(source_form(8, False).encode()),
                    target_prefix=len(spine(4 * 8).encode())))


if __name__ == '__main__':
    main()
