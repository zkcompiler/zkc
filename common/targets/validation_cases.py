"""The shared refusal cases of the EVM target declaration.

`evm-validation-cases.json` lists edits of `evm.json` that both validators
must refuse: the generator here and the Rust SDK build (`crates/zkc/build.rs`).
Each case names the broken rule, and each validator reports that rule. This
module applies the edits; the validators are run by their own tests.

An edit is one operation at a `path` of object keys and list indices:

- `set` replaces or adds the value at `path`;
- `delete` removes the value at `path`;
- `duplicate` appends a copy of the list element at `path` to its list;
- `append` adds `value` to the list at `path`.
"""

import copy
import json
from pathlib import Path

CASES = Path(__file__).with_name("evm-validation-cases.json")
FORMAT = "zkc.evm-target-validation-cases/0"


def load():
    document = json.loads(CASES.read_text())
    if set(document) != {"format", "cases"} or document["format"] != FORMAT:
        raise AssertionError("unexpected validation case document")
    return document["cases"]


def apply(edits, declaration):
    """Return an edited copy of the declaration."""
    result = copy.deepcopy(declaration)
    for edit in edits:
        *parents, last = edit["path"]
        parent = result
        for key in parents:
            parent = parent[key]
        op = edit["op"]
        if op == "set":
            parent[last] = copy.deepcopy(edit["value"])
        elif op == "delete":
            del parent[last]
        elif op == "duplicate":
            parent.append(copy.deepcopy(parent[last]))
        elif op == "append":
            parent[last].append(copy.deepcopy(edit["value"]))
        else:
            raise AssertionError(f"unknown edit operation {op}")
    return result
