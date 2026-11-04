"""Source-derived physical calls for the bounded BLS G1 Schnorr replay."""

from copy import deepcopy

from curve_controls import P, add, affine, scale
from validate import check_return


def record(events, address, data, output, frontier, *, failed=False):
    if events is not None:
        # Match revm's address display, including the checksum on address 12.
        suffix, kind = {5: ("05", "modexp"), 11: ("0b", "bls12_g1add"),
                        12: ("0C", "bls12_g1msm")}[address]
        events.append({"kind": kind, "address": "0x" + "0" * 38 + suffix,
                       "input": data.hex(), "output": output.hex(),
                       "status": "halt" if failed else "return",
                       "reason": "PrecompileError" if failed else "Return",
                       "precompile_called": True, "hash_event_frontier": frontier})


def modexp(events, base, exponent, frontier):
    data = (48).to_bytes(32, "big") * 3
    data += b"".join(v.to_bytes(48, "big") for v in (base, exponent, P))
    result = pow(base, exponent, P)
    record(events, 5, data, result.to_bytes(48, "big"), frontier)
    return result


def msm(events, point, scalar, frontier, *, subgroup_valid=True):
    data = affine(point) + scalar.to_bytes(32, "big")
    # EIP-2537 rejects a finite point outside the subgroup. Its return is
    # empty, not the affine encoding of an identity or a mathematical product.
    result = scale(point, scalar) if subgroup_valid else None
    record(events, 12, data, affine(result) if subgroup_valid else b"", frontier,
           failed=not subgroup_valid)
    return result


def group_add(events, left, right, frontier):
    result = add(left, right)
    record(events, 11, affine(left) + affine(right), affine(result), frontier)
    return result


def check_precompile_trace(actual, expected):
    """Compare every field and the entire sequence, including failed calls."""
    if actual is None or len(actual) != len(expected):
        count = None if actual is None else len(actual)
        raise AssertionError(f"physical precompile count: actual={count}, expected={len(expected)}")
    for index, (observed, wanted) in enumerate(zip(actual, expected, strict=True)):
        if observed != wanted:
            raise AssertionError(f"physical precompile {index}: actual={observed}, expected={wanted}")


def check_physical_execution(execution, expected):
    """Require both repeated invocations and the runner's first-call projection."""
    calls = execution.get("calls", [])
    if len(calls) != 2:
        raise AssertionError("physical replay requires two invocations")
    check_precompile_trace(execution.get("deployment_precompile_trace"), [])
    check_precompile_trace(execution.get("precompile_trace"), expected)
    for call in calls:
        check_precompile_trace(call.get("precompile_trace"), expected)


def mutation_controls(execution, expected):
    """Mutate retained diagnostics; keep actual Boolean/hash results unchanged.

    These exercise oracle rejection, not altered contracts or engine outcomes.
    Both call positions are tested so a first-call-only oracle cannot pass.
    """
    check_physical_execution(execution, expected["precompile_trace"])
    controls = []
    for call_index in range(2):
        for mutation in ("missing", "extra", "reordered", "input", "output", "frontier",
                         "status", "reason", "precompile_called"):
            changed = deepcopy(execution)
            events = changed["calls"][call_index]["precompile_trace"]
            if mutation == "missing":
                del events[0]
            elif mutation == "extra":
                events.append(deepcopy(events[0]))
            elif mutation == "reordered":
                events[0], events[1] = events[1], events[0]
            else:
                field, value = {
                    "input": ("input", f"{int(events[0]['input'][:2], 16) ^ 1:02x}" + events[0]["input"][2:]),
                    "output": ("output", f"{int(events[0]['output'][:2], 16) ^ 1:02x}" + events[0]["output"][2:]),
                    "frontier": ("hash_event_frontier", events[0]["hash_event_frontier"] + 1),
                    "status": ("status", "halt"), "reason": ("reason", "PrecompileError"),
                    "precompile_called": ("precompile_called", False),
                }[mutation]
                events[0][field] = value
            # Preserve the top-level projection of the first invocation.
            changed["precompile_trace"] = deepcopy(changed["calls"][0]["precompile_trace"])
            for call in changed["calls"]:
                check_return(changed | call, (1).to_bytes(32, "big").hex(), expected["trace"])
            try:
                check_physical_execution(changed, expected["precompile_trace"])
            except AssertionError as error:
                controls.append({"call": call_index + 1, "mutation": mutation,
                                 "boolean_unchanged": True, "hashes_unchanged": True,
                                 "rejected": True, "diagnostic": str(error)})
            else:
                raise AssertionError(f"physical oracle accepted {mutation} in call {call_index + 1}")
    return controls
