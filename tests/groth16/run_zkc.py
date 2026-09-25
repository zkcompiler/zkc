#!/usr/bin/env python3
"""Exercise the separately built relation-aware zkc CLI against verified fixtures."""

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
sys.path.insert(0, str(PACKAGE / "scripts"))
from common import read_json, sha256, write_json  # noqa: E402
from prepare_reference import prepare  # noqa: E402
from record_metadata import compare  # noqa: E402
from reproduce import check_evidence, source_snapshot  # noqa: E402

SCALAR_FIELD = (
    21888242871839275222246405745257275088548364400416034343698204186575808495617
)
BASE_FIELD = (
    21888242871839275222246405745257275088696311157297823662689037894645226208583
)


class Commands:
    def __init__(self, work):
        self.work = work
        self.output = work / "zkc"
        self.output.mkdir(exist_ok=True)
        (self.output / "logs").mkdir(exist_ok=True)
        (self.output / "tmp").mkdir(exist_ok=True)
        self.records = []

    def run(self, name, arguments, *, refused=False, structured=True):
        arguments = [str(argument) for argument in arguments]
        started = time.monotonic()
        result = subprocess.run(
            arguments,
            cwd=self.work,
            env=dict(os.environ, TMPDIR=str(self.output / "tmp")),
            capture_output=True,
            text=True,
        )
        elapsed = (time.monotonic() - started) * 1000
        log = self.output / "logs" / f"{name}.log"
        log.write_text(result.stdout + result.stderr)
        if refused:
            if result.returncode == 0:
                raise ValueError(f"{name}: invalid input unexpectedly accepted")
            record = json.loads(result.stderr)
            if record.get("status") != "refused":
                raise ValueError(
                    f"{name}: failed without structured refusal; see {log}"
                )
        else:
            if result.returncode or "[ERROR]" in result.stdout + result.stderr:
                raise ValueError(f"{name}: command failed; see {log}")
            if structured:
                record = json.loads(result.stdout)
                if record.get("status") != "accepted":
                    raise ValueError(f"{name}: missing accepted result")
            else:
                record = {
                    "status": "accepted",
                    "implementation": "unmodified snarkjs CLI",
                }
        record = {"name": name, "process_ms": elapsed, **record}
        self.records.append(record)
        print(f"{name}: {record['status']} ({elapsed:.1f} ms)", flush=True)
        return record


def replace_option(arguments, option, value):
    result = list(arguments)
    result[result.index(option) + 1] = str(value)
    return result


def mutate_private_witness(source, target):
    """Change private signal 2 in a real witness, keeping its container intact."""
    data = bytearray(source.read_bytes())
    if data[:4] != b"wtns":
        raise ValueError("Expected a witness container")
    cursor = 12
    for _ in range(int.from_bytes(data[8:12], "little")):
        section = int.from_bytes(data[cursor : cursor + 4], "little")
        length = int.from_bytes(data[cursor + 4 : cursor + 12], "little")
        cursor += 12
        if section == 2:
            offset = cursor + 2 * 32
            value = (
                int.from_bytes(data[offset : offset + 32], "little") + 1
            ) % SCALAR_FIELD
            data[offset : offset + 32] = value.to_bytes(32, "little")
            target.write_bytes(data)
            return
        cursor += length
    raise ValueError("Witness has no assignment section")


def evaluate_depth(args, commands, depth):
    fixture = args.workdir / f"artifacts/depth{depth}"
    out = commands.output / f"depth{depth}"
    out.mkdir(exist_ok=True)
    base = [
        args.zkc,
        "prove",
        "--compiler",
        args.compiler,
        "--lean",
        args.lean,
        "--vk",
        fixture / "vk.json",
        "--public",
        fixture / "public.json",
        "--context",
        f"zkc.groth16.evaluation.depth{depth}.public-test-setup",
    ]
    proving = ["--zkey", fixture / "final.zkey", "--witness", fixture / "witness.wtns"]
    relation = ["--r1cs", fixture / f"depth{depth}.r1cs"]
    prefix = out / "protocol"
    first = out / "proof-r1-s2.json"
    framed = out / "proof-r1-s2.bin"
    commands.run(
        f"depth{depth}-compile-prove-r1-s2",
        base
        + relation
        + proving
        + [
            "--source",
            args.source,
            "--save-code",
            prefix,
            "--test-randomness",
            "1,2",
            "--proof",
            first,
            "--artifact",
            framed,
        ],
    )
    identity = (out / "protocol.relation-id").read_text().strip()
    cached = [
        "--common",
        out / "protocol.common.json",
        "--endpoints",
        out / "protocol.endpoints.json",
        "--relation-id",
        identity,
    ]
    verifier = [base[0], "verify", *base[2:], *cached]
    prover = base + cached + relation + proving
    snark = [
        "node",
        "--require",
        args.workdir / "scripts/limit-workers.cjs",
        args.workdir / "node_modules/snarkjs/build/cli.cjs",
    ]

    proof_hashes = {}
    for r, s in ((1, 2), (0, 0)):
        proof = out / f"proof-r{r}-s{s}.json"
        if (r, s) != (1, 2):
            commands.run(
                f"depth{depth}-prove-r{r}-s{s}",
                prover
                + [
                    "--test-randomness",
                    f"{r},{s}",
                    "--proof",
                    proof,
                ],
            )
        if read_json(proof) != read_json(fixture / proof.name):
            raise ValueError(
                f"Exact canonical proof mismatch at depth {depth}, r={r}, s={s}"
            )
        canonical = json.dumps(read_json(proof), sort_keys=True, separators=(",", ":"))
        proof_hashes[f"r{r}-s{s}"] = {
            "zkcJsonSha256": sha256(proof),
            "canonicalJsonSha256": hashlib.sha256(canonical.encode()).hexdigest(),
        }
        commands.run(
            f"depth{depth}-snarkjs-verifies-r{r}-s{s}",
            snark
            + [
                "groth16",
                "verify",
                fixture / "vk.json",
                fixture / "public.json",
                proof,
            ],
            structured=False,
        )
        commands.run(
            f"depth{depth}-zkc-verifies-upstream-r{r}-s{s}",
            verifier
            + [
                "--proof",
                fixture / proof.name,
            ],
        )

    repeat = out / "repeat.bin"
    commands.run(
        f"depth{depth}-repeat-fixed",
        prover
        + [
            "--test-randomness",
            "1,2",
            "--proof",
            out / "repeat.json",
            "--artifact",
            repeat,
        ],
    )
    if framed.read_bytes() != repeat.read_bytes():
        raise ValueError("Fixed bound artifact was not deterministic")
    for index in range(2):
        proof = out / f"fresh-{index}.json"
        commands.run(f"depth{depth}-fresh-zkc-{index}", prover + ["--proof", proof])
        commands.run(
            f"depth{depth}-snarkjs-verifies-fresh-{index}",
            snark
            + [
                "groth16",
                "verify",
                fixture / "vk.json",
                fixture / "public.json",
                proof,
            ],
            structured=False,
        )
    if read_json(out / "fresh-0.json") == read_json(out / "fresh-1.json"):
        raise ValueError("Two OS-randomized proofs unexpectedly matched")
    upstream = out / "upstream-fresh.json"
    commands.run(
        f"depth{depth}-fresh-upstream",
        snark
        + [
            "groth16",
            "prove",
            fixture / "final.zkey",
            fixture / "witness.wtns",
            upstream,
            out / "upstream-public.json",
        ],
        structured=False,
    )
    if read_json(out / "upstream-public.json") != read_json(fixture / "public.json"):
        raise ValueError(
            "Upstream public output differs from the application statement"
        )
    commands.run(
        f"depth{depth}-zkc-verifies-fresh-upstream", verifier + ["--proof", upstream]
    )

    public = read_json(fixture / "public.json")
    for name, value in (
        ("changed-root", (int(public[0]) + 1) % SCALAR_FIELD),
        ("noncanonical-root", int(public[0]) + SCALAR_FIELD),
    ):
        path = out / f"{name}.json"
        write_json(path, [str(value)])
        commands.run(
            f"depth{depth}-reject-{name}",
            replace_option(verifier, "--public", path)
            + [
                "--proof",
                first,
            ],
            refused=True,
        )
    for name in ("negated-A", "swapped-G2"):
        proof = copy.deepcopy(read_json(first))
        if name == "negated-A":
            proof["pi_a"][1] = str(BASE_FIELD - int(proof["pi_a"][1]))
        else:
            proof["pi_b"][0].reverse()
            proof["pi_b"][1].reverse()
        path = out / f"{name}.json"
        write_json(path, proof)
        commands.run(
            f"depth{depth}-reject-{name}", verifier + ["--proof", path], refused=True
        )
    commands.run(
        f"depth{depth}-reject-context",
        replace_option(verifier, "--context", "wrong-context")
        + [
            "--artifact",
            framed,
        ],
        refused=True,
    )
    wrong_vk = args.workdir / f"artifacts/depth{16 if depth == 2 else 2}/vk.json"
    commands.run(
        f"depth{depth}-reject-wrong-vk",
        replace_option(verifier, "--vk", wrong_vk)
        + [
            "--proof",
            first,
        ],
        refused=True,
    )
    truncated = out / "truncated.bin"
    truncated.write_bytes(framed.read_bytes()[:-1])
    commands.run(
        f"depth{depth}-reject-truncated-artifact",
        verifier + ["--artifact", truncated],
        refused=True,
    )
    bad_witness = out / "invalid-private.wtns"
    mutate_private_witness(fixture / "witness.wtns", bad_witness)
    forbidden_output = out / "invalid-private-proof.json"
    forbidden_output.unlink(missing_ok=True)
    commands.run(
        f"depth{depth}-reject-private-witness",
        replace_option(prover, "--witness", bad_witness)
        + [
            "--proof",
            forbidden_output,
        ],
        refused=True,
    )
    if forbidden_output.exists():
        raise ValueError("Invalid private witness produced a proof file")
    bench = [base[0], "bench", *prover[2:], "--iterations", str(args.iterations)]
    commands.run(f"depth{depth}-prepared-benchmark", bench)
    return {
        "depth": depth,
        "relationIdentity": identity,
        "fixedProofs": 2,
        "refusalControls": 8,
        "proofHashes": proof_hashes,
        "compiledSourceSha256": sha256(out / "protocol.common.json"),
        "physicalEndpointsSha256": sha256(out / "protocol.endpoints.json"),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("workdir", "zkc", "compiler", "lean", "source"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.iterations <= 1000:
        parser.error("--iterations must be in 1..1000")
    for name in ("workdir", "zkc", "compiler", "lean", "source"):
        setattr(args, name, getattr(args, name).expanduser().resolve())
    check_evidence(PACKAGE)
    if read_json(args.workdir / "RESULTS.json").get("status") != "passed":
        raise ValueError("Run reproduce.py successfully before the zkc integration")
    # Compare actual regenerated vectors and all original deterministic artifacts.
    compare(args.workdir, PACKAGE / "evidence")
    before = source_snapshot()
    external_hashes = {
        name: sha256(getattr(args, name))
        for name in ("zkc", "compiler", "lean", "source")
    }
    commands = Commands(args.workdir)
    result_path = commands.output / "RESULTS.json"
    write_json(result_path, {"status": "running"})
    try:
        prepare(args.workdir, PACKAGE / "evidence")
        results = [evaluate_depth(args, commands, depth) for depth in (2, 16)]
        prepare(args.workdir, PACKAGE / "evidence")
        for name, expected in external_hashes.items():
            if sha256(getattr(args, name)) != expected:
                raise ValueError(f"External {name} changed during integration")
        result = {
            "status": "passed",
            "scope": "Two pinned public-test-setup fixtures through the actual relation-aware compiled PIR CLI; no general conformance or secure ceremony claim",
            "depths": results,
            "fixtureControlsSeparate": 80,
            "zkcRefusalControls": 16,
            "exactFixedProofs": 4,
            "binaries": {
                name: external_hashes[name] for name in ("zkc", "compiler", "lean")
            },
            "pirSourceSha256": external_hashes["source"],
            "driverSha256": sha256(Path(__file__)),
            "verifierHasNoProvingInputs": True,
            "records": commands.records,
        }
        write_json(result_path, result)
        print(f"PASS: relation-aware zkc result in {result_path}")
    except BaseException as error:
        write_json(
            result_path,
            {"status": "failed", "error": str(error), "records": commands.records},
        )
        raise
    finally:
        if source_snapshot() != before:
            write_json(
                result_path, {"status": "failed", "error": "Maintained package changed"}
            )
            raise RuntimeError("Maintained package changed during the integration run")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"zkc integration failed: {error}", file=sys.stderr)
        sys.exit(1)
