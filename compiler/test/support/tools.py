"""Locate the tools this build produced, by name.

A test here drives the compiler build's own tools and no other build's. That is
what puts it under CTest rather than under pytest, and it is why this module
offers no way to reach the native or the formal build: there is nothing here to
name one with.

CTest passes the exact file CMake built, through `$<TARGET_FILE:...>`, which no
directory-and-name rule can get wrong -- and the build directory does hold older
copies of several of these names from configurations that wrote them elsewhere.
Direct invocations use the compiler output directory selected by the shared
workspace configuration. Either way the path is checked before it is handed
back, and a tool that is not there is a failure naming the directory searched
and what to build.
"""

import os
from pathlib import Path
import sys

from toolchain import Toolchain, records_root
from workspace import validate_environment
from reporting import new_directory

ROOT = Path(__file__).resolve().parents[3]

# Where a test's evidence goes. `records_root` is the one definition of where
# this repository's tests write their reports, and is about directories rather
# than about builds; the subdirectory keeps these apart from the cross-build
# tests', which name themselves by a different rule.
REPORTS = records_root() / "compiler-test"

# Repeated requests in this process share only their own exclusive directory.
OPENED = {}

# Shared inputs for compiler, native and cross-language tests and benchmarks.
# Component-specific inputs can stay beside the tests that own them.
corpus = ROOT / "tests/fixtures"

# The authored protocols the compiler ships. Nine tests here spelled this
# path out beside their own copy of where the repository is; it is the same
# directory for the same reason the corpus is.
examples = ROOT / "examples/protocols"

# What each tool is called, what CMake calls the variable it passes it in, and
# where under the build directory to look when nothing passed it.
TOOLS = {
    "compiler": ("zkc-compile", "ZKC_CTEST_COMPILER", "."),
    "optimizer": ("zkc-opt", "ZKC_CTEST_OPTIMIZER", "."),
    "source_bench": ("zkc-source-bench", "ZKC_CTEST_SOURCE_BENCH", "."),
    "service_compiler": ("zkc-service-compile", "ZKC_CTEST_SERVICE_COMPILER", "examples/service"),
    "service_optimizer": ("zkc-service-opt", "ZKC_CTEST_SERVICE_OPTIMIZER", "examples/service"),
    "requirements_test": ("zkc-requirements-test", "ZKC_CTEST_REQUIREMENTS_TEST", "test"),
}


class Missing(Exception):
    """A tool a test needs is not where this build writes its outputs."""


def tool(which):
    """The executable a test names, as a path to run.

    Tests take these by name rather than by path, so no invocation carries one
    and none can be handed the wrong tool.
    """
    if which not in TOOLS:
        raise AttributeError(
            f"{which} is not a tool of this build. It has: {', '.join(sorted(TOOLS))}"
        )
    validate_environment()
    name, variable, folder = TOOLS[which]
    passed = os.environ.get(variable)
    if passed is not None and not passed.strip():
        raise Missing(f"{variable} must name an executable; an empty CTest target is invalid")
    if passed and Path(passed).is_file() and os.access(passed, os.X_OK):
        return Path(passed)
    if passed:
        # The variable naming a file that is not there is what this message was
        # written for; trusting the variable would skip it.
        raise Missing(locate(name, Path(passed).parent, variable))
    directory = Toolchain().directories["compiler"] / folder
    path = directory / name
    if path.is_file() and os.access(path, os.X_OK):
        return path
    raise Missing(locate(name, directory, variable))


def locate(name, directory, variable):
    """What to say about a tool that is not where it was looked for."""
    return (
        f"{name} is not in {directory}\n"
        f"  {variable} names it or this build writes there, and it is neither\n"
        f"  build it with: just build-compiler\n"
        f"  present there: {', '.join(present(directory)) or 'nothing'}"
    )


def present(directory):
    """The executables this build has actually produced, for a failure to name."""
    if not directory.is_dir():
        return []
    return sorted(entry.name for entry in directory.iterdir()
                  if entry.is_file() and not entry.suffix and os.access(entry, os.X_OK))


def __getattr__(name):
    """`from tools import compiler` resolves that one tool, and only when asked.

    A test that needs the compiler should not fail because an example this
    build also produces is missing.
    """
    if name in TOOLS:
        return tool(name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")


def records(case=None):
    """The directory the calling test writes its sources, plans and reports to.

    These tests used to work in a temporary directory and delete it on the way
    out, which threw away the plans and sources of exactly the run worth
    reading: the one that failed. What a test writes now stays under the
    build's reports, where CI keeps it and a developer can open it.

    The name is the test's own, which here is the file's: this directory
    registers every `.py` in it under its own name, so there is no convention
    to remember and none to get wrong. `case` is for a test that works in more
    than one place at once.

    The first request allocates an empty directory. Later requests in the same
    process return it; another invocation cannot overwrite that evidence.
    """
    origin = sys._getframe(1).f_globals.get("__file__")
    caller = Path(origin).resolve() if origin else None
    if caller is None or caller.parent != ROOT / "compiler/test":
        raise ValueError(
            f"records() names the directory after the test that calls it, and "
            f"{caller.name if caller else 'this caller'} is not one of them. "
            f"Something these tests share should be given the directory rather "
            f"than asking for one, or it will name every test's evidence after "
            f"itself."
        )
    identity = str(caller) + (f"::{case}" if case is not None else "")
    key = (REPORTS, identity, os.getpid())
    if key not in OPENED:
        label = caller.name + (f"::{case}" if case is not None else "")
        OPENED[key] = new_directory(REPORTS, identity, label)
    return OPENED[key]
