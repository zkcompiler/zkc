#!/usr/bin/env python3
"""What the runtime accepts as a table storage layout.

Which layouts there are, and that each one gives the same answers as the Lean
reference, is a case of every suite that compares the two: see STORAGE_LAYOUTS
in the shared fixtures. What is left here is the option itself, which no
comparison would notice.
"""

import json

from journal import Journal
from toolchain import Toolchain, records


def main():
    journal = Journal(records())
    runtime = Toolchain().runtime
    # Use the documented command shape. The unsupported layout must be refused
    # before opening these absent inputs or invoking the checker.
    inputs = [journal.directory / name for name in ("source.json", "plan.json", "inputs.json", "checker")]
    for command in ("run", "run-physical"):
        refused = journal.attempt([runtime, command, *inputs, "--storage", "unknown"])
        assert refused.returncode == 1, refused
        assert json.loads(refused.stdout).get("code") == "unsupported-storage", refused.stdout
    journal.save()
    print(json.dumps({"status": "pass", "refused": "unsupported-storage"}))


def test_unknown_storage_layout_is_refused():
    main()


if __name__ == "__main__":
    main()
