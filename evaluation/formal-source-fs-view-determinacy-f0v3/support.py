"""Shared atom encodings for separately derived candidate values."""

from __future__ import annotations

import json
from typing import Any


PROFILE_DIGESTS = {
    "canonical-framed": "38dd578579b115e7d4b17ca4e31f255d6def4027166c831f4dba259fb597607a",
    "duplex-sponge": "15203c4745d3f4aafd1d6bb45a0e94e0e21461dbe8cc6c5d9d4949df980e761b",
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
