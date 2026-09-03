"""Shared atom encodings for separately derived candidate values."""

from __future__ import annotations

import json
from typing import Any


PROFILE_DIGESTS = {
    "canonical-framed": "fe0cfa79211bf2d8290b749b191ce311306df3321231ed09f9c1ae26269ea43c",
    "duplex-sponge": "257118b591f2040f4a1e1a243b9069825b97159b521a6640c507ded47ea79736",
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
