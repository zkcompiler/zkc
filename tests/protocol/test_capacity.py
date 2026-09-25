#!/usr/bin/env python3
"""Exercise the real two-factor route at its current retained-payload boundary."""

import hashlib
import json
from pathlib import Path
import time

from journal import Journal
from toolchain import Toolchain, records


# The Lean reference this route is compared against.
CHECKER = "interactive-protocol"


def main():
    resolver = Toolchain()
    compiler, native = resolver.compiler, resolver.runtime
    checker = resolver.checker(CHECKER)
    journal = Journal(records())
    out = journal.directory
    root = Path(__file__).resolve().parents[2]
    out.mkdir(parents=True, exist_ok=True)
    tools = {"compiler": compiler, "native": native, "checker": checker}
    pins = {k: hashlib.sha256(p.read_bytes()).hexdigest() for k, p in tools.items()}
    results = []

    def run(name, command):
        """Run one step of a rank, keeping what it printed under that name."""
        proc = journal.attempt(command, text=False, timeout=900)
        (out / f"{name}.stdout").write_bytes(proc.stdout)
        (out / f"{name}.stderr").write_bytes(proc.stderr)
        journal.save()
        if proc.returncode:
            raise RuntimeError(f"{name}: tool failed; see retained output")
        return proc.stdout

    for rank in (14, 15, 16):
        source = json.loads((root / "examples/protocols/two-factor.json").read_text())
        inputs = json.loads((root / "examples/protocols/two-factor.inputs.json").read_text())
        for instance in source[4]:
            for binding in instance[3]:
                if binding[0] == "n":
                    binding[1] = str(rank)
        # Compact, varying values keep host JSON below its independent size limit.
        factors = [[(i * i + 3 * i + 1) % 97 for i in range(1 << rank)],
                   [(3 * i ** 3 + i + 4) % 89 for i in range(1 << rank)]]
        claim = str(sum(a * b for a, b in zip(*factors)))
        inputs[2] = f"capacity-{rank}-{time.time_ns()}"
        for setup in inputs[3]:
            setup[2] = str(rank)
        # A record is a role, its services, its inputs and its port constraints.
        # A constraint states the arity the backend checks the value against, and
        # one that also names a setup must agree with that setup's rank, so every
        # arity in this example moves with the rank the whole route is scaled to.
        for _, services, ports, constraints in inputs[4]:
            for service in services:
                if service[0] == "rng":
                    service[2] = str(rank)
            for port in ports:
                if port[0] in ("f", "g"):
                    port[1] = ["table", list(map(str, factors[port[0] == "g"]))]
                elif port[0] == "claim":
                    port[1] = ["field", claim]
            for constraint in constraints:
                if constraint[1] is not None:
                    constraint[1] = str(rank)
        sp = out / f"rank-{rank}.source.json"
        ip = out / f"rank-{rank}.inputs.json"
        cp = out / f"rank-{rank}.physical.json"
        for path, value in ((sp, source), (ip, inputs)):
            path.write_text(json.dumps(value, separators=(",", ":")) + "\n")
        cp.write_bytes(run(f"rank-{rank}-compile", [tools["compiler"], "protocol-compile", sp]))
        result = json.loads(run(f"rank-{rank}-run",
            [tools["native"], "run-protocol", sp, cp, ip, tools["checker"]]))
        if rank == 14:
            passed = result["outcome"][0] == "returned" and result["outcome"][1]["V"][0] == ["bool", True]
        else:
            # Preserve detailed stop/origin, usage and residual resources below.
            detail = 'Backend(BackendError { code: "exhausted:output-bytes" })' if rank == 15 else "Limit"
            passed = (result["outcome"] == ["stopped", "P", "commit_factors", detail]
                      and result["wire"]["messages"] == 0
                      and result["resources"] == [["V", "challenges", 0, 0, rank, "rng"]]
                      and all(usage["live_value_bytes"] == 0 for usage in result["usage"].values()))
        results.append({"rank": rank, "passed": passed, "result": result,
                        "inputs_bytes": ip.stat().st_size,
                        "source_sha256": hashlib.sha256(sp.read_bytes()).hexdigest(),
                        "candidate_sha256": hashlib.sha256(cp.read_bytes()).hexdigest()})
        print(f"rank {rank}: {'PASS' if passed else 'FAIL'} {result['outcome']}", flush=True)
    if pins != {k: hashlib.sha256(p.read_bytes()).hexdigest() for k, p in tools.items()}:
        raise RuntimeError("tools changed during capacity controls")
    report = {"format": "zkc.interactive-capacity/1", "tools": pins, "results": results,
              "scope": "Default limits and conservative repeated backing charges; not maximum RSS or a performance baseline."}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    return int(not all(r["passed"] for r in results))



def test_capacity():
    assert main() == 0

if __name__ == "__main__":
    raise SystemExit(main())
