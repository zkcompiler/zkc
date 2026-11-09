#!/usr/bin/env python3
"""Measure checked Region construction with cached dependencies and fresh proof modules.

Run after building Zkc.Tests.Protocol.Construction.SharingAudit. No dependency build or
cache eviction is performed. Each case gets fresh elaboration, synchronous declaration
checking and three fresh kernel rechecks. Whole-process wall time and peak RSS include
imports and Lake's no-build module setup. These are model-source measurements, not native
source admission or complete Sumcheck/FRI measurements.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support.invocation import command as lean_command  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
CASES = [*(f"flat{n}" for n in (1, 2, 4, 8)),
         *(f"nested{n}" for n in (1, 2, 4, 8)),
         *(f"count{n}" for n in (0, 1, 8, 1024))]
HEADER = '''module
import Zkc.Tests.Protocol.Construction.Sharing
import Zkc.Tests.Protocol.Construction.SharingAudit
set_option experimental.vcgen true
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open PIR Zkc.Source ProtocolProof Std.WP
open ProtocolProofExamples ProtocolProofExamples.ConstructionPilot
open ProtocolProofExamples.ConstructionSharing
'''


def source(case):
    if case.startswith("count"):
        count = int(case.removeprefix("count"))
        return HEADER + f'''
attribute [local instance] AdaptiveSource.upperLogic
measured_construction measured : ∀ (e : AdaptiveChecks.Environment)
    (env : Environment (AdaptiveSource.meaning e).Value [.accumulator]) (value : ENNReal),
    ⦃OrderDual.toDual (AdaptiveSource.potential (AdaptiveChecks.factor e.residual ^ {count} * value)
      (env .here))⦄
      (AdaptiveSource.rounds {count}).denote (AdaptiveSource.meaning e).regionMeaning env
    ⦃fun out => OrderDual.toDual (AdaptiveSource.potential value (out.get .here));
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  intro e env value
  construct_region
construction_metrics measured using ProtocolProofExamples.AdaptiveSource.rounds_upper
'''
    count = int(case.removeprefix("flat").removeprefix("nested"))
    callee = (f"ProtocolProofExamples.ConstructionSharing.nested{count // 2}_law"
              if case.startswith("nested") and count > 1
              else "ProtocolProofExamples.ConstructionPilot.helper_law")
    return HEADER + f'''
attribute [local instance] proofLogic
measured_construction measured : ∀ (env : Environment meaning.Value [(), ()])
    (post : Values meaning.Value [()] → (Potential Unit Unit)ᵒᵈ)
    (stopped : (Stop → Potential Unit Unit)ᵒᵈ),
    ⦃post (.singleton (env .here - env (.there .here)))⦄
      {case}.denote meaning.regionMeaning env ⦃post; stopped⦄ := by
  intro env post stopped
  unfold {case}
  construct_region
construction_metrics measured using {callee}
'''


def metric(log, marker):
    positions = [line.split(marker, 1)[1] for line in log.splitlines() if marker in line]
    if len(positions) != 1:
        raise ValueError(f"expected one {marker} record, got {len(positions)}")
    return json.loads(positions[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--records", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--cases", nargs="+", choices=CASES, default=CASES)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("repetitions must be positive")
    output = args.records.resolve()
    output.mkdir(parents=True, exist_ok=True)
    generated = output / "generated"
    generated.mkdir(exist_ok=True)
    package = ROOT / "lean/protocol"
    records = []
    environment = dict(os.environ, LEAN_NUM_THREADS="2")
    for case in args.cases:
        path = generated / (case.capitalize() + ".lean")
        text = source(case)
        path.write_text(text)
        for repetition in range(args.repetitions):
            artifact = path.with_suffix(".olean")
            rss = output / f"{case}-{repetition}.rss"
            log_path = output / f"{case}-{repetition}.log"
            command = lean_command(package, "-j2", "-M8192", "--root=" + str(generated),
                                   "-o", artifact, path, lake=args.lake)
            measured = ["/usr/bin/time", "-f", "%M", "-o", str(rss), *command]
            start = time.monotonic()
            try:
                result = subprocess.run(measured, cwd=package, env=environment,
                                        capture_output=True, text=True, timeout=120)
            except subprocess.TimeoutExpired as error:
                log_path.write_text(str(error))
                raise SystemExit(f"incomplete: {case} timed out; see {log_path}") from error
            log = result.stdout + result.stderr
            log_path.write_text(log)
            if result.returncode:
                raise SystemExit(f"failed: {case}; see {log_path}")
            row = dict(case=case, repetition=repetition, command=command,
                       source_sha256=hashlib.sha256(text.encode()).hexdigest(),
                       cache="fresh proof module; cached dependencies and OS cache; no cache eviction",
                       seconds=time.monotonic() - start, peak_rss_kib=int(rss.read_text()),
                       artifact_bytes=sum(item.stat().st_size for item in
                           [artifact, path.with_suffix(".olean.private"),
                            path.with_suffix(".olean.server")] if item.exists()),
                       phase=metric(log, "CONSTRUCTION-PHASE "),
                       proof=metric(log, "CONSTRUCTION-METRIC "), log=str(log_path))
            expected = int(case[4:]) if case.startswith("flat") else (
                2 if case.startswith("nested") and case != "nested1" else 1)
            if row["proof"]["references"] != expected:
                raise SystemExit(f"failed sharing assertion for {case}: {row['proof']}")
            records.append(row)
            (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
        print(json.dumps(dict(case=case, status="passed", repetitions=args.repetitions)), flush=True)


if __name__ == "__main__":
    main()
