"""The shared validation cases of the installed-instance and installation rules.

`validation-cases.json` lists edits of the authored documents. Every accepted
case must pass all three validators: the catalog generator, the zkc-tblgen
backend and the Rust catalog build. Every refused case must be refused by each
of them, each with its own diagnostic. This module applies the edits; the
validators are run by their own tests.

An edit names its document (`declarations` or `installation`) and table, and
applies one operation:

- `insert` appends `value` as a new row;
- `duplicate` appends a copy of the row that `where` selects;
- `delete` removes that row;
- `set`, `append` and `remove` change the value at `path` inside that row:
  `set` replaces it, `append` adds `value` to the list, `remove` removes every
  element equal to `value` from the list, at least one.

`where` lists field values that exactly one row has. A path is a list of object
keys and list indices.
"""

import copy
import json
from pathlib import Path

CASES = Path(__file__).with_name("validation-cases.json")


def load():
    return json.loads(CASES.read_text())


def _row(rows, where):
    selected = [i for i, row in enumerate(rows) if all(row.get(k) == v for k, v in where.items())]
    if len(selected) != 1:
        raise AssertionError(f"edit selects {len(selected)} rows for {where}")
    return selected[0]


def _parent(value, path):
    for key in path[:-1]:
        value = value[key]
    return value, path[-1]


def apply(edits, declarations, installation):
    """Return edited copies of both documents."""
    documents = {"declarations": copy.deepcopy(declarations), "installation": copy.deepcopy(installation)}
    for edit in edits:
        rows = documents[edit["document"]][edit["table"]]
        op = edit["op"]
        if op == "insert":
            rows.append(copy.deepcopy(edit["value"]))
            continue
        index = _row(rows, edit["where"])
        if op == "duplicate":
            rows.append(copy.deepcopy(rows[index]))
        elif op == "delete":
            del rows[index]
        else:
            parent, key = _parent(rows[index], edit["path"])
            if op == "set":
                parent[key] = copy.deepcopy(edit["value"])
            elif op == "append":
                parent[key].append(copy.deepcopy(edit["value"]))
            elif op == "remove":
                before = len(parent[key])
                parent[key] = [item for item in parent[key] if item != edit["value"]]
                if len(parent[key]) == before:
                    raise AssertionError(f"edit removes nothing: {edit}")
            else:
                raise AssertionError(f"unknown edit operation {op}")
    return documents["declarations"], documents["installation"]
