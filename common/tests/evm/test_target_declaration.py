"""The runner and harness still restate EVM target declaration facts.

`common/targets/evm.json` (`zkc.evm-target/0`) is the one authored source of
these facts. Each remaining restatement below must equal it until its reader
takes the declaration itself, so neither can change alone.
"""

import copy
import json
import unittest
from pathlib import Path

import abi
import probe
import validate
from hash_chain_reference import keccak256

HERE = Path(__file__).resolve().parent
DECLARATION = json.loads((HERE.parents[2] / "common/targets/evm.json").read_text())
FORKS = DECLARATION["forks"]
DEFAULT = DECLARATION["default_fork"]
LIMITS = {row["name"]: row["maximum"] for row in DECLARATION["limits"]}
LISTED = "(" + ", ".join(f'"{fork["name"]}"' for fork in FORKS) + ")"


class DeclarationParityTests(unittest.TestCase):
    def restates(self, name, expected, times=1):
        text = (HERE / name).read_text()
        self.assertEqual(text.count(expected), times, f"{name} restates {expected}")

    def test_selector_is_the_declared_signature_keccak(self):
        signature = DECLARATION["abi"]["signature"]
        selector = DECLARATION["abi"]["selector"]
        self.assertEqual(keccak256(signature.encode())[:4].hex(), selector)
        self.restates("abi.py", f'keccak256(b"{signature}")[:4]')
        self.assertEqual(abi.SELECTOR.hex(), selector)

    def test_fork_lists_and_default(self):
        for name, times in (("probe.py", 3), ("validate.py", 3), ("capacity.py", 1),
                            ("test_engine.py", 3)):
            self.restates(name, LISTED, times)
        for name in ("probe.py", "validate.py", "capacity.py"):
            self.restates(name, f'choices={LISTED}, default="{DEFAULT}"')
        self.restates("probe.py", f'fork="{DEFAULT}"')
        self.restates("wire_controls.py", f'"evmVersion": "{DEFAULT}"', 4)
        self.restates("test_engine.py", f'"fork": "{DEFAULT}"')
        self.restates("test_engine.py", f'"evmVersion": "{DEFAULT}"')
        # The capacity control applies the EIP-7623 calldata floor by fork name.
        floors = [fork["name"] for fork in FORKS if "EIP-7623" in fork["rules"]]
        self.assertEqual(len(floors), 1)
        self.restates("capacity.py", f'.get("evmVersion") == "{floors[0]}"')

    def test_runner_maps_each_declared_fork_to_its_engine(self):
        self.restates("src/main.rs", '" => Ok(Self::', len(FORKS))
        for fork in FORKS:
            variant = fork["name"].capitalize()
            self.restates("src/main.rs", f'"{fork["name"]}" => Ok(Self::{variant}),')
            self.restates("src/main.rs",
                          f'Self::{variant} => SpecId::{fork["hardfork"].upper()},')

    def test_solc_pin_and_optimizer(self):
        version = DECLARATION["solc"]["version"]
        self.restates("probe.py", f'"{version}" not in version')
        self.restates("wire_controls.py", f'"solc": "{version.split("+")[0]}"')
        optimizer = copy.deepcopy(DECLARATION["solc"]["optimizer"])
        # The harness omits the `yul` detail, which solc's enabled optimizer
        # already implies. Any other difference is drift.
        self.assertIs(optimizer["details"].pop("yul"), True)
        self.assertEqual(probe.PROFILES["colon"], optimizer)

    def test_code_size_ceilings(self):
        for fork in FORKS:
            self.restates("foundation_controls.py",
                          f'len(artifact["runtime"]) // 2 > {fork["runtime_code_bytes"]} or '
                          f'len(artifact["creation"]) // 2 > {fork["initcode_bytes"]}')

    def test_deployment_ceilings(self):
        self.assertEqual(abi.MAX_CALLDATA, LIMITS["calldata_bytes"])
        context, proof = LIMITS["context_bytes"], LIMITS["proof_bytes"]
        frame, elements = LIMITS["frame_bytes"], LIMITS["public_elements"]
        self.restates("capacity.py", f"len(context) > {context} or len(proof) > {proof}")
        self.restates("capacity.py", f"bytes({context + 1})")
        self.restates("capacity.py", f"bytes({proof + 1} - len(proof))")
        self.restates("capacity.py", f"bytes({proof} - len(proof))")
        self.restates("capacity.py", f"bytes({frame + 1})")
        self.restates("capacity.py", f"max(lengths) > {frame}")
        self.restates("capacity.py", f"({elements + 1}).to_bytes(4, \"little\")")
        self.restates("capacity.py", f"({LIMITS['rounds'] + 1}).to_bytes(8, \"little\")")
        self.restates("capacity.py", f"len(context) != {context}")
        self.restates("validate.py", f"len(context) < {context}")
        self.restates("native_fixtures.py", f'run("honest-1024", {LIMITS["rounds"]}, ')
        self.restates("native_fixtures.py", f"context=bytes({context})")
        self.restates("foundation_controls.py", f'("at-cap", {elements}, ')
        self.restates("foundation_controls.py", f'("over-cap", {elements + 1}, ')
        self.restates("foundation_controls.py", f'("stopping-body-at-cap", {elements + 1}, {elements}, ')
        self.restates("wire_controls.py", f'sequence([head(31)+b"\\x00"*8]*{elements})')
        self.restates("wire_controls.py", f"for ceiling in (4, {elements}):")
        # Every deployed call requests the practical validation gas ceiling.
        gas = f"{LIMITS['practical_gas']:_}"
        for name, times in (("capacity.py", 2), ("foundation_controls.py", 1), ("mutant.py", 1),
                            ("scalar_controls.py", 3), ("validate.py", 2),
                            ("wire_controls.py", 5)):
            self.restates(name, gas, times)

    def test_revert_classes(self):
        self.assertEqual(validate.REVERT_CLASSES,
                         {row["class"]: row["tag"].encode() for row in DECLARATION["reverts"]})


if __name__ == "__main__":
    unittest.main()
