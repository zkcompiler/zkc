#!/usr/bin/env python3
"""Measure whole direct applications and frozen native artifacts on identical inputs."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def call(command, prefix):
    command = list(map(str, command))
    start = time.perf_counter()
    result = subprocess.run(
        ["/usr/bin/time", "-v", "-o", str(prefix) + ".time", *command],
        capture_output=True,
        text=True,
        check=False,
    )
    wall = time.perf_counter() - start
    Path(str(prefix) + ".stdout").write_text(result.stdout)
    Path(str(prefix) + ".stderr").write_text(result.stderr)
    if result.returncode:
        raise RuntimeError(
            f"{command}: {result.stdout[-1000:]} {result.stderr[-1000:]}"
        )
    rss = next(
        int(line.rsplit(":", 1)[1])
        for line in Path(str(prefix) + ".time").read_text().splitlines()
        if "Maximum resident set size" in line
    )
    report = json.loads(result.stdout)
    return dict(command=command, wall_seconds=wall, max_rss_kib=rss, report=report)


def med(records, field):
    return statistics.median(r[field] for r in records)


def native_command(app, run, role, proof, inputs, tools):
    if app == "tx":
        paths = [
            run / n
            for n in (
                "source.stdout",
                "descriptor.stdout",
                "construct.stdout",
                "selected.compile.stdout",
            )
        ]
    else:
        paths = [
            run / "public" / n
            for n in (
                "source.stdout",
                "descriptor.stdout",
                "construct.stdout",
                "compile.stdout",
            )
        ]
    return [
        tools / "runtime",
        role + "-artifact",
        *paths,
        inputs,
        tools / "compiler",
        tools / "lean",
        proof,
        "1000000",
        "--trace=none",
    ]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--application", choices=["tx", "execution"], required=True)
    p.add_argument(
        "--transaction-algorithm", choices=["upstream", "matched"], default="upstream"
    )
    p.add_argument("--run", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    # The measured executables are named explicitly: a default location would
    # time whatever an earlier campaign happened to leave there.
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--tools", type=Path, help="frozen native tools; a transaction run holds its own")
    p.add_argument("--samples", type=int, default=3)
    p.add_argument("--compare-native", action="store_true")
    p.add_argument(
        "--include-claims",
        action="store_true",
        help="include retained caller requirements and actual-candidate custody",
    )
    p.add_argument(
        "--physical",
        type=Path,
        help="actual candidate for a named optimization ablation",
    )
    p.add_argument("--implementations", type=Path)
    p.add_argument("--linear-contractions", action="store_true")
    p.add_argument("--release-storage", action="store_true")
    a = p.parse_args()
    if a.transaction_algorithm == "matched" and a.application != "tx":
        p.error("--transaction-algorithm matched requires --application tx")
    if a.application == "execution" and not a.tools:
        p.error("--application execution requires --tools")
    direct_app = "tx-matched" if a.transaction_algorithm == "matched" else a.application
    assert a.samples >= 3
    if (
        a.include_claims
        or a.physical
        or a.implementations
        or a.linear_contractions
        or a.release_storage
    ) and not a.compare_native:
        p.error("native candidate and claim options require --compare-native")
    a.output.mkdir(parents=True, exist_ok=False)
    run = a.run.resolve()
    tools = a.tools.resolve() if a.tools else run / "tools"
    setup_samples = None
    export_seconds = None
    if a.application == "tx":
        public = [
            run / "parameters.json",
            run / "fixture/ledger.json",
            run / "fixture/statement.json",
        ]
        witness = run / "fixture/witness.json"
        native_inputs = dict(
            produce=run / "producer.json", validate=run / "validator.json"
        )
    else:
        start = time.perf_counter()
        subprocess.run(
            [
                "python3",
                "-B",
                HERE / "export_execution.py",
                "--run",
                run,
                "--compiler",
                tools / "compiler",
                "--output",
                a.output / "export",
            ],
            check=True,
        )
        export_seconds = time.perf_counter() - start
        public = [a.output / "export/public.json", a.output / "export/setup.json"]
        witness = run / "relation/assignment.json"
        data = json.loads(public[0].read_text())
        setup_samples = call(
            [
                a.binary,
                "execution",
                "setup-bench",
                data["columns"].bit_length() - 1,
                a.samples,
            ],
            a.output / "setup-bench",
        )["report"]
        native_inputs = dict(
            produce=run / "producer.json", validate=run / "public/validator.json"
        )
    warm = call(
        [
            a.binary,
            direct_app,
            "bench",
            *public,
            witness,
            a.output / "warm",
            a.samples,
        ],
        a.output / "warm-process",
    )["report"]
    direct = dict(prove=[], verify=[])
    native = dict(produce=[], validate=[])
    for i in range(a.samples):
        proof = a.output / f"direct-{i}.proof"
        direct["prove"].append(
            call(
                [a.binary, direct_app, "prove", *public, witness, proof],
                a.output / f"direct-prove-{i}",
            )
        )
        direct["verify"].append(
            call(
                [a.binary, direct_app, "verify", *public, proof],
                a.output / f"direct-verify-{i}",
            )
        )
        assert direct["prove"][-1]["report"]["produced"] is True
        assert direct["verify"][-1]["report"]["accepted"] is True
        if not a.compare_native:
            continue
        native_proof = a.output / f"native-{i}.proof"
        for role in ("produce", "validate"):
            admission = None
            inputs = native_inputs[role]
            # The native application wrappers have separate public admission.
            # Charge it to pipeline wall time and preserve its own record.
            if a.application == "tx":
                inputs = a.output / f"{role}-{i}-inputs.json"
                cmd = [
                    tools / "helper",
                    "prepare" if role == "produce" else "admit",
                    *public,
                ]
                if role == "produce":
                    cmd.append(witness)
                cmd.append(inputs)
                admission = call(
                    cmd, a.output / f"native-{role}-{i}-application-admission"
                )
            elif role == "validate":
                admission = call(
                    ["python3", "-B", HERE / "native_admission.py", run],
                    a.output / f"native-{role}-{i}-application-admission",
                )
            command = native_command(
                a.application, run, role, native_proof, inputs, tools
            )
            if a.physical:
                command[5] = a.physical.resolve()
            elif direct_app == "tx-matched" and not a.linear_contractions:
                # Match the source's materialized scale_each/MSM computations.
                command[5] = run / "dense.compile.stdout"
            claim_admission = None
            if a.include_claims:
                claim_dir = run / (
                    "claims" if a.application == "tx" else "public/claims"
                )
                claim_options = []
                if a.linear_contractions or (
                    a.application == "tx"
                    and not a.physical
                    and direct_app != "tx-matched"
                ):
                    claim_options.append("--linear-contractions")
                if a.release_storage:
                    claim_options.append("--release-storage")
                if a.implementations:
                    claim_options.append(
                        "--implementations=" + str(a.implementations.resolve())
                    )
                claim_admission = call(
                    [
                        "python3",
                        "-B",
                        HERE / "claim_admission.py",
                        tools / "compiler",
                        command[2],
                        claim_dir / "contract.json",
                        claim_dir / "certificate.json",
                        command[3],
                        command[4],
                        command[5],
                        *claim_options,
                    ],
                    a.output / f"native-{role}-{i}-claim-admission",
                )
            # The public artifact binding intentionally survives compatible
            # physical rewrites. Pin the actually measured candidate separately.
            artifacts = {str(path): sha(path) for path in command[2:7]}
            record = call(command, a.output / f"native-{role}-{i}")
            assert artifacts == {path: sha(path) for path in artifacts}, (
                "native benchmark inputs changed during measurement"
            )
            record["artifacts_sha256"] = artifacts
            assert record["report"]["status"] == (
                "produced" if role == "produce" else "accepted"
            )
            record["application_admission"] = admission
            record["claim_admission"] = claim_admission
            record["pipeline_wall_seconds"] = (
                record["wall_seconds"]
                + (admission["wall_seconds"] if admission else 0)
                + (claim_admission["wall_seconds"] if claim_admission else 0)
            )
            native[role].append(record)
    hashes = [sha(a.output / f"direct-{i}.proof") for i in range(a.samples)]
    if a.application == "tx":
        assert len(set(hashes)) == a.samples, "fresh proof randomness"
    direct_summary = {
        role: dict(
            process_seconds=med(records, "wall_seconds"),
            max_rss_kib=max(r["max_rss_kib"] for r in records),
            warm_seconds=med(warm["warm_samples"], role + "_seconds"),
        )
        for role, records in direct.items()
    }
    native_summary = {}
    for role, records in native.items():
        if not records:
            continue
        native_summary[role] = dict(
            process_seconds=med(records, "wall_seconds"),
            pipeline_seconds=med(records, "pipeline_wall_seconds"),
            max_rss_kib=max(r["max_rss_kib"] for r in records),
            **{
                key: statistics.median(r["report"]["timings"][key] for r in records)
                for key in ("run_seconds", "admission_seconds", "key_load_seconds")
            },
        )
    result = dict(
        application=a.application,
        direct_algorithm=a.transaction_algorithm
        if a.application == "tx"
        else "execution-source/1",
        run=str(run),
        samples=a.samples,
        machine=dict(
            platform=platform.platform(),
            cpu=next(
                (
                    v.split(":", 1)[1].strip()
                    for v in Path("/proc/cpuinfo").read_text().splitlines()
                    if v.startswith("model name")
                ),
                "",
            ),
            logical_cpus=os.cpu_count(),
        ),
        binary_sha256=sha(a.binary),
        lock_sha256=sha(HERE / "Cargo.lock"),
        harness_sha256={str(path): sha(path) for path in sorted(HERE.glob("*.py"))},
        inputs_sha256={str(f): sha(f) for f in [*public, witness]},
        native_tools_sha256={
            name: sha(tools / name)
            for name in (
                ("compiler", "runtime", "lean", "helper")
                if a.application == "tx"
                else ("compiler", "runtime", "lean")
            )
        }
        if a.compare_native
        else {},
        export_seconds=export_seconds,
        setup_samples=setup_samples,
        warm=warm,
        direct=direct,
        native=native,
        native_claim_admission_included=a.include_claims,
        direct_summary=direct_summary,
        native_summary=native_summary,
        proof_sha256=hashes,
        direct_proof_bytes=(a.output / "direct-0.proof").stat().st_size,
        native_proof_bytes=(a.output / "native-0.proof").stat().st_size
        if a.compare_native
        else None,
        scope="Same machine and original fixture; own wire/transcript. Warm direct uses cached keys/public inputs. Native run_seconds is the CLI run phase: runner execution and teardown plus proof-file read or durable publication (including sync_all), not isolated VM execution or a persistent-host benchmark. Direct warm timers exclude file I/O. Native process includes artifact admission; pipeline adds application admission and, when explicitly requested, retained actual-candidate claim checking. Export/compiler matrix staging and source compilation outside timed proof work. Shared-machine load is uncontrolled; concurrent builds must be recorded separately.",
    )
    write(a.output / "results.json", result)
    print(
        json.dumps(
            {
                k: result[k]
                for k in (
                    "application",
                    "direct_algorithm",
                    "run",
                    "direct_summary",
                    "native_summary",
                    "direct_proof_bytes",
                    "native_proof_bytes",
                )
            }
        )
    )


if __name__ == "__main__":
    main()
