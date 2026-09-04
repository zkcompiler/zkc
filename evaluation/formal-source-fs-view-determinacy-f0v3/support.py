"""Shared atom encodings for separately derived candidate values."""

from __future__ import annotations

import json
from typing import Any


PROFILE_DIGESTS = {
    "canonical-framed": "180a1a793a899f6a16aa17e3e02dcbcef0bf0baa54f88ec2d9f5610a02cd4809",
    "duplex-sponge": "0116b0df403b01b34fd0858745da83a4efb5d38d4b54c8946ecbf5bc4095d1a6",
}


def _wire(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def body(compiler: str, value: Any) -> dict[str, str]:
    return {"compiler": compiler, "body": _wire(value).hex()}


def raw_body(compiler: str, value: bytes) -> dict[str, str]:
    if type(value) is not bytes or not value:
        raise ValueError("raw candidate body must be nonempty bytes")
    return {"compiler": compiler, "body": value.hex()}


def law(profile: str, name: str) -> dict[str, str]:
    return {
        "profile": PROFILE_DIGESTS[profile],
        "kind": "pir.semantic-law",
        "name": name,
    }


def variant(case: int, value: Any = None) -> dict[str, Any]:
    return {"case": case, "value": value}


def record(*values: Any) -> dict[int, Any]:
    return {index: value for index, value in enumerate(values)}


def algorithm_use(algorithm: str, contract: str) -> dict[int, Any]:
    return record(
        body("algorithm-ref-body-v0", algorithm),
        body("evaluation-contract-id-body-v0", contract),
    )


def ref(compiler: str, value: Any) -> dict[str, str]:
    return body(compiler, value)
