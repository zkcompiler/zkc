#!/usr/bin/env python3
"""Every installed MSB table-family binding, through all three consumers."""

from binding_comparison import check_bindings
from journal import Journal
from toolchain import Toolchain, records

# The Lean reference these bindings are compared against.
CHECKER = "interactive-protocol"


def main():
    tools = Toolchain()
    journal = Journal(records())
    results = check_bindings(journal, tools.compiler, tools.runtime,
                             tools.checker(CHECKER))
    print(f"{len(results)} physical binding comparisons passed")


def test_physical_bindings():
    main()


if __name__ == "__main__":
    main()
