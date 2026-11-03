"""The installed EVM target declaration, as the deployed-validation harness reads it.

`common/targets/evm.json` (`zkc.evm-target/0`) is the one authored source of the
verifier ABI and selector, the pinned solc version and optimizer settings, the
forks and default fork, the deployment ceilings and the revert classes. The
harness checks it with the declaration's own validator (`common/targets/
generate.py`, standard library only) and reads every target fact from it. An
artifact's restated numbers are never authority.
"""

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
_TARGETS = ROOT / "common/targets"


def _validator():
    spec = importlib.util.spec_from_file_location("zkc_evm_target_validator", _TARGETS / "generate.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_GENERATE = _validator()
DATA = (_TARGETS / "evm.json").read_bytes()
DECLARATION = _GENERATE.check(DATA)
IDENTITY = _GENERATE.identity(DATA)

SIGNATURE = DECLARATION["abi"]["signature"]
SELECTOR = bytes.fromhex(DECLARATION["abi"]["selector"])
SOLC_VERSION = DECLARATION["solc"]["version"]
SOLC_RELEASE = SOLC_VERSION.split("+")[0]
FORKS = {row["name"]: row for row in DECLARATION["forks"]}
FORK_NAMES = tuple(FORKS)
DEFAULT_FORK = DECLARATION["default_fork"]
LIMITS = {row["name"]: row["maximum"] for row in DECLARATION["limits"]}
MINIMA = {row["name"]: row["minimum"] for row in DECLARATION["limits"]}
REVERT_CLASSES = {row["class"]: row["tag"].encode() for row in DECLARATION["reverts"]}
VALIDATION_GAS = DECLARATION["validation_gas"]


def optimizer():
    """A fresh copy of the declared standard-JSON optimizer settings."""
    return _GENERATE.load(DATA)["solc"]["optimizer"]


def fork(name):
    """The declared row of the fork with exactly this name."""
    if name not in FORKS:
        raise ValueError("unsupported-fork")
    return FORKS[name]


def solc_fork(evm_version):
    """The declared fork whose solc `evmVersion` is exactly this setting."""
    for row in FORKS.values():
        if row["solc"] == evm_version:
            return row
    raise ValueError("unsupported-fork")


def transaction_gas(name):
    """Gas each validation transaction, deployment included, requests on a fork.

    A fork's declared consensus transaction cap when it has one; otherwise the
    declared validation gas, which is never a deployment ceiling. Deployment
    uses the same budget, so a runtime at the fork's code size ceiling always
    deploys.
    """
    cap = fork(name)["transaction_gas_cap"]
    return cap if cap is not None else VALIDATION_GAS
