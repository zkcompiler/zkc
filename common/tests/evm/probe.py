"""Compile and dynamically inspect exact, uninstrumented solc Yul artifacts."""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

from abi import keccak256
from oracle import check_trace

SOLC_SHA256 = "65c3180a336eabb6bdc4bbd49cc405aeb233976964ae6c11fba2a6c8be8f3243"
PROFILES = {
    "disabled": {"enabled": False},
    "enabled": {"enabled": True},
    "colon": {"enabled": True, "details": {"yulDetails": {"optimizerSteps": ":"}}},
}


def check_solc(solc):
    if hashlib.sha256(solc.read_bytes()).hexdigest() != SOLC_SHA256:
        raise ValueError("unexpected solc identity")
    version = subprocess.check_output([str(solc), "--version"], text=True)
    if "0.8.38+commit.1835d247" not in version:
        raise ValueError("unexpected solc version")
    return version


def compile_request(solc, request):
    process = subprocess.run([str(solc), "--standard-json"], input=json.dumps(request),
                             text=True, capture_output=True, check=True, timeout=90)
    output = json.loads(process.stdout)
    errors = [e for e in output.get("errors", []) if e["severity"] == "error"]
    if errors:
        raise RuntimeError(errors)
    contracts = [contract for source in output["contracts"].values() for contract in source.values()]
    if len(contracts) != 1:
        raise ValueError("expected one Yul contract")
    evm = contracts[0]["evm"]
    return {"request": request, "creation": evm["bytecode"]["object"],
            "runtime": evm["deployedBytecode"]["object"]}


def compile_yul(solc, body, optimizer):
    source = '''object "Probe" {
      code {
        datacopy(0, dataoffset("Runtime"), datasize("Runtime"))
        return(0, datasize("Runtime"))
      }
      object "Runtime" { code { BODY } }
    }'''.replace("BODY", body)
    request = {"language": "Yul", "sources": {"probe.yul": {"content": source}},
               "settings": {"evmVersion": "cancun", "optimizer": optimizer,
                            "outputSelection": {"*": {"*": ["evm.bytecode.object",
                                                               "evm.deployedBytecode.object"]}}}}
    return compile_request(solc, request)


def execute(runner, artifact, calldata, gas=1_000_000, *, repeat_count=1):
    request = {"creation_bytecode": artifact["creation"], "calldata": calldata.hex(),
               "expected_runtime_bytecode": artifact["runtime"], "gas_limit": gas,
               "deployment_gas_limit": 5_000_000, "fork": "Cancun", "repeat_count": repeat_count}
    process = subprocess.run([str(runner)], input=json.dumps(request), text=True,
                             capture_output=True, timeout=30)
    result = json.loads(process.stdout)
    if process.returncode:
        raise RuntimeError(result)
    return result


UNUSED = '''
    calldatacopy(0, 0, calldatasize())
    let finalState := keccak256(0, calldatasize())
    mstore(0, 1)
    return(0, 32)
'''
IDENTITY_ANCHOR = '''
    calldatacopy(0, 0, calldatasize())
    let finalState := keccak256(0, calldatasize())
    mstore(0, finalState)
    if iszero(staticcall(gas(), 4, 0, 32, 32, 32)) { revert(0, 0) }
    if iszero(eq(returndatasize(), 32)) { revert(0, 0) }
    if iszero(eq(mload(0), mload(32))) { revert(0, 0) }
    mstore(0, 1)
    return(0, 32)
'''
GAS_ANCHOR = '''
    calldatacopy(0, 0, calldatasize())
    let before := gas()
    let finalState := keccak256(0, calldatasize())
    if lt(sub(before, gas()), 30) { revert(0, 0) }
    mstore(0, 1)
    return(0, 32)
'''
VERBATIM_ANCHOR = '''
    calldatacopy(0, 0, calldatasize())
    let finalState := keccak256(0, calldatasize())
    verbatim_1i_0o(hex"50", finalState)
    mstore(0, 1)
    return(0, 32)
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solc", type=Path, required=True)
    parser.add_argument("--runner", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    version = check_solc(args.solc)
    receipt = {"solc_sha256": SOLC_SHA256, "solc_version": version, "fork": "Cancun",
               "dynamic": args.runner is not None, "cases": []}
    calldata = b"the last post-challenge observation must execute"
    expected = [{"kind": "keccak256", "input": calldata.hex(),
                 "output": keccak256(calldata).hex(), "status": "return"}]
    for name, body in [("unused", UNUSED), ("gas_anchor", GAS_ANCHOR),
                       ("identity_anchor", IDENTITY_ANCHOR),
                       ("verbatim_anchor", VERBATIM_ANCHOR)]:
        for profile, optimizer in PROFILES.items():
            artifact = compile_yul(args.solc, body, optimizer)
            case = {"name": name, "profile": profile, **artifact}
            if args.runner:
                execution = execute(args.runner, artifact, calldata)
                case["execution"] = execution
                try:
                    check_trace(execution["trace"], expected)
                    case["preserved"] = True
                except AssertionError as error:
                    case["preserved"] = False
                    case["trace_error"] = str(error)
                if name in ("identity_anchor", "verbatim_anchor"):
                    assert case["preserved"], case
                    assert execution["status"] == "return" and int(execution["output"], 16) == 1
            receipt["cases"].append(case)
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"dynamic": receipt["dynamic"], "cases": [
        {key: case[key] for key in ["name", "profile", "preserved"] if key in case}
        for case in receipt["cases"]]}, indent=2))


if __name__ == "__main__":
    main()
