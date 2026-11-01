"""Compare actual primitive execution, including the unused final absorption."""

import hashlib

from abi import keccak256


def primitive_calls(trace):
    calls = []
    for event in trace:
        if event["kind"] not in ("keccak256", "sha256"):
            raise AssertionError(f"unknown primitive: {event}")
        if event.get("status") not in ("return", "halt"):
            raise AssertionError(f"unfinished primitive: {event}")
        calls.append((event["kind"], event["input"].removeprefix("0x"),
                      event["output"].removeprefix("0x"), event["status"]))
    return calls


def check_trace(actual, expected):
    """Exact equality includes count/order; never accept a matching prefix."""
    actual = primitive_calls(actual)
    expected = primitive_calls(expected)
    for i, (left, right) in enumerate(zip(actual, expected)):
        if left != right:
            raise AssertionError(f"primitive {i}: actual={left}, expected={right}")
    if len(actual) != len(expected):
        raise AssertionError(f"primitive count: actual={len(actual)}, expected={len(expected)}")
    for kind, preimage, digest, status in actual:
        if status != "return":
            continue
        hashed = (keccak256 if kind == "keccak256" else hashlib.sha256)(bytes.fromhex(preimage))
        expected_digest = hashed if isinstance(hashed, bytes) else hashed.digest()
        if expected_digest.hex() != digest:
            raise AssertionError(f"invalid {kind} output")


def chain_trace(chain):
    return [{"kind": "keccak256", "input": preimage.hex(), "output": digest.hex(),
             "status": "return"} for preimage, digest in chain.calls]
