"""Actual deployment controls; run with ZKC_EVM_RUNNER set to the built binary."""

import hashlib
import json
import os
import subprocess
import unittest
from pathlib import Path

from abi import encode_verify, keccak256
from oracle import check_trace
from probe import PROFILES, check_solc, compile_yul, execute
from validate import check_sdk_artifact, removed_final_hash_control


class ArtifactMetadataTests(unittest.TestCase):
    def test_sdk_fixture_binds_the_selected_execution_fork(self):
        digest = hashlib.sha256(b"\x00").hexdigest()
        for fork in ("cancun", "prague"):
            fixture = {"public": [], "context": "", "proof": "", "evm": {
                "calldata": encode_verify([], b"", b"").hex(),
                "creation": "00", "runtime": "00",
                "creation_sha256": digest, "runtime_sha256": digest,
                "manifest": {"evm_version": fork,
                             "files": {"creation.bin": digest, "runtime.bin": digest}}}}
            artifact = {"creation": "00", "runtime": "00",
                        "request": {"settings": {"evmVersion": fork}}}
            check_sdk_artifact(fixture, artifact)
            for selected in (None, "prague" if fork == "cancun" else "cancun", "latest"):
                with self.subTest(captured=fork, selected=selected):
                    artifact["request"]["settings"]["evmVersion"] = selected
                    with self.assertRaisesRegex(AssertionError, "execution fork differs"):
                        check_sdk_artifact(fixture, artifact)
            artifact["request"]["settings"]["evmVersion"] = fork
            artifact["runtime"] = "01"
            with self.assertRaisesRegex(AssertionError, "deployment differs"):
                check_sdk_artifact(fixture, artifact)


def creation_for(runtime):
    """A CODECOPY/RETURN constructor used only for adapter controls."""
    length = len(runtime).to_bytes(2, "big")
    return b"\x61" + length + b"\x61\x00\x0d\x5f\x39\x61" + length + b"\x5f\xf3" + runtime


def invoke(runtime, calldata=b"abc", gas=1_000_000, **overrides):
    request = {"creation_bytecode": creation_for(runtime).hex(),
               "expected_runtime_bytecode": runtime.hex(), "calldata": calldata.hex(),
               "gas_limit": gas, "deployment_gas_limit": 5_000_000, "fork": "cancun"}
    request.update(overrides)
    process = subprocess.run([os.environ["ZKC_EVM_RUNNER"]], input=json.dumps(request),
                             text=True, capture_output=True, timeout=30)
    return process.returncode, json.loads(process.stdout)


@unittest.skipUnless(os.getenv("ZKC_EVM_RUNNER"), "set ZKC_EVM_RUNNER for deployed controls")
class EngineTests(unittest.TestCase):
    @unittest.skipUnless(os.getenv("ZKC_SOLC"), "set ZKC_SOLC for pinned solc controls")
    def test_pinned_solc_fork_survives_actual_deployment(self):
        solc = Path(os.environ["ZKC_SOLC"])
        check_solc(solc)
        for fork in ("cancun", "prague"):
            with self.subTest(fork=fork):
                artifact = compile_yul(solc, "mstore(0, 1) return(0, 32)", PROFILES["colon"], fork=fork)
                self.assertEqual(artifact["request"]["settings"]["evmVersion"], fork)
                result = execute(os.environ["ZKC_EVM_RUNNER"], artifact, b"\xff" * 1024)
                self.assertEqual(result["fork"], fork)
                self.assertEqual(result["status"], "return")
                self.assertEqual(int(result["output"], 16), 1)
                self.assertEqual(result["runtime_bytecode"], artifact["runtime"])

    def test_selected_fork_changes_real_transaction_gas(self):
        # EIP-7623 raises Prague's floor for this calldata-heavy transaction.
        # This exercises real spec selection, even with identical deployed code.
        runtime = bytes.fromhex("60015f5260205ff3")
        executions = {}
        for fork in ("cancun", "prague"):
            code, result = invoke(runtime, calldata=b"\xff" * 1024, fork=fork)
            self.assertEqual(code, 0, result)
            self.assertEqual(result["fork"], fork)
            self.assertEqual(result["engine"], "revm/43.0.3")
            self.assertEqual(result["status"], "return")
            self.assertEqual(int(result["output"], 16), 1)
            executions[fork] = result
        self.assertGreater(executions["prague"]["runtime_gas"],
                           executions["cancun"]["runtime_gas"])

    def test_malformed_fork_refuses_before_deployment(self):
        for fork in ("Cancun", "Prague", "london", "", None, 1, {"prague": None}, ["cancun"]):
            with self.subTest(fork=fork):
                code, result = invoke(b"\x00", fork=fork)
                self.assertNotEqual(code, 0)
                self.assertTrue(result["error"].startswith("request-json:"), result)

    def test_repeat_preserves_storage_and_resets_trace(self):
        # SLOAD(slot 0), increment, SSTORE, hash the counter and return it.
        runtime = bytes.fromhex("5f54600101805f555f5260205f205060205ff3")
        code, result = invoke(runtime, repeat_count=3)
        self.assertEqual(code, 0, result)
        self.assertEqual(len(result["calls"]), 3)
        self.assertEqual(result["deployment_trace"], [])
        for nonce, call in enumerate(result["calls"], 1):
            self.assertEqual(call["nonce"], nonce)
            self.assertEqual(call["address"], result["address"])
            self.assertEqual(call["status"], "return")
            counter = nonce.to_bytes(32, "big")
            self.assertEqual(call["output"], counter.hex())
            check_trace(call["trace"], [{"kind": "keccak256", "input": counter.hex(),
                                       "output": keccak256(counter).hex(), "status": "return"}])
            self.assertEqual(call["memory_high_water"], 32)

    def test_repeat_bounds(self):
        for count in (0, 9):
            with self.subTest(count=count):
                code, result = invoke(bytes.fromhex("00"), repeat_count=count)
                self.assertNotEqual(code, 0)
                self.assertEqual(result["error"], "runner-repeat-cap")

    def test_exact_runtime_and_keccak(self):
        runtime = bytes.fromhex("365f5f37365f205060015f5260205ff3")
        code, result = invoke(runtime)
        self.assertEqual(code, 0, result)
        self.assertEqual(result["status"], "return")
        self.assertEqual(int(result["output"], 16), 1)
        self.assertEqual(result["runtime_bytecode"], runtime.hex())
        self.assertEqual(result["code_size"], len(runtime))
        expected = [{"kind": "keccak256", "input": b"abc".hex(),
                     "output": keccak256(b"abc").hex(), "status": "return"}]
        check_trace(result["trace"], expected)
        # Replace KECCAK with POP. Both original operands are consumed by the
        # two POPs; the exact same true ABI result survives without the hash.
        mutant = bytearray(runtime)
        mutant[6] = 0x50
        code, mutated = invoke(mutant)
        self.assertEqual(code, 0, mutated)
        self.assertEqual(mutated["output"], result["output"])
        with self.assertRaises(AssertionError):
            check_trace(mutated["trace"], expected)

    def test_sha256_precompile_request_and_result(self):
        runtime = bytes.fromhex("365f5f3760205f365f60025afa5060205ff3")
        code, result = invoke(runtime)
        self.assertEqual(code, 0, result)
        digest = hashlib.sha256(b"abc").hexdigest()
        self.assertEqual(result["output"], digest)
        check_trace(result["trace"], [{"kind": "sha256", "input": b"abc".hex(),
                                      "output": digest, "status": "return"}])

    def test_revert_halt_oog_and_stop_prefix(self):
        _, reverted = invoke(bytes.fromhex("365f5f37365f20505f5ffd"))
        self.assertEqual(reverted["status"], "revert")
        self.assertEqual(len(reverted["trace"]), 1)
        # A source stop before later malformed input must produce no later hash.
        _, stopped = invoke(bytes.fromhex("5f5ffd"), b"malformed future frame")
        self.assertEqual(stopped["status"], "revert")
        self.assertEqual(stopped["trace"], [])
        _, halted = invoke(bytes.fromhex("fe"))
        self.assertEqual(halted["status"], "halt")
        _, oog = invoke(bytes.fromhex("5b5f56"), b"", gas=22_000)
        self.assertEqual(oog["status"], "halt")
        self.assertIn("OutOfGas", oog["reason"])

    def test_runtime_pin(self):
        code, result = invoke(bytes.fromhex("00"), expected_runtime_bytecode="01")
        self.assertNotEqual(code, 0)
        self.assertEqual(result["error"], "installed-runtime-mismatch")

    def test_hash_memory_edges(self):
        suffix = bytes.fromhex("5060015f5260205ff3")
        for program, preimage in [
            (bytes.fromhex("5f7f") + bytes([255]) * 32 + b"\x20", b""),
            (bytes.fromhex("60405f20"), bytes(64)),
        ]:
            code, result = invoke(program + suffix)
            self.assertEqual(code, 0, result)
            check_trace(result["trace"], [{"kind": "keccak256", "input": preimage.hex(),
                                          "output": keccak256(preimage).hex(), "status": "return"}])
        _, failed = invoke(b"\x7f" + bytes([255]) * 32 + bytes.fromhex("5f20"))
        self.assertEqual(failed["status"], "halt")
        self.assertEqual(failed["trace"], [])

    def test_primitive_order_and_failed_precompile(self):
        runtime = bytes.fromhex("365f5f37365f205060205f365f60025afa5060205f205060015f5260205ff3")
        code, result = invoke(runtime)
        self.assertEqual(code, 0, result)
        sha = hashlib.sha256(b"abc").digest()
        expected = [{"kind": kind, "input": value.hex(), "output": digest.hex(), "status": "return"}
                    for kind, value, digest in [("keccak256", b"abc", keccak256(b"abc")),
                                                ("sha256", b"abc", sha),
                                                ("keccak256", sha, keccak256(sha))]]
        check_trace(result["trace"], expected)
        # Forward zero gas: the reached precompile request is recorded, but a
        # digest was never returned. The caller can still return normally.
        _, failed = invoke(bytes.fromhex("365f5f3760205f365f60025ffa5060015f5260205ff3"))
        self.assertEqual(failed["status"], "return")
        check_trace(failed["trace"], [{"kind": "sha256", "input": b"abc".hex(),
                                      "output": "", "status": "halt"}])

    def test_deployment_trace_is_separate(self):
        runtime = bytes.fromhex("00")
        constructor = (bytes.fromhex("5f5f20506100016100115f396100015ff3") + runtime)
        code, result = invoke(runtime, creation_bytecode=constructor.hex())
        self.assertEqual(code, 0, result)
        self.assertEqual(result["trace"], [])
        check_trace(result["deployment_trace"], [{"kind": "keccak256", "input": "",
                                                 "output": keccak256(b"").hex(), "status": "return"}])

    def test_final_hash_artifact_control(self):
        runtime = bytes.fromhex("365f5f37365f205060015f5260205ff3")
        code, original = invoke(runtime)
        self.assertEqual(code, 0, original)
        artifact = {"creation": creation_for(runtime).hex(), "runtime": runtime.hex(),
                    "request": {"settings": {"evmVersion": "cancun"}}}
        control = removed_final_hash_control(os.environ["ZKC_EVM_RUNNER"], artifact,
                                             b"abc", original, original["trace"], 1_000_000)
        self.assertEqual(control["execution"]["status"], "return")
        self.assertEqual(control["execution"]["output"], original["output"])
        self.assertEqual(control["execution"]["trace"], [])


if __name__ == "__main__":
    unittest.main()
