"""Locate the executables a cross-build test needs, by name.

A test here runs tools from three separate builds in separate processes and
compares what they do. It never looks inside another build's directory, and it
never receives an executable path from its caller: it names the tool it needs
and this module finds it. Which Lean reference a test compares against is part
of what the test is, so the test states it rather than the invocation.

    ZKC_COMPILER_BIN   zkc-compile, zkc-opt and the compiler's own examples
    ZKC_NATIVE_BIN     zkc, artifact-primitive and the runtime's examples
    ZKC_LEAN_BIN       the compiled Lean references

Missing means missing. A test that cannot find its tool fails, names the
directory that was searched and says what to build, rather than passing while
checking nothing or comparing against the wrong reference.
"""

import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]

sys.path.insert(0, str(ROOT / "scripts"))
from workspace import (  # noqa: E402
    DIRECTORIES, checkout_path, output_directory, reports_root, validate_environment,
)
from reporting import new_directory  # noqa: E402

BUILDS = {
    "compiler": "just build-compiler",
    "native": "just build-rust",
    "lean": "just build-lean",
}


class Missing(Exception):
    """A tool a test needs is not where that build writes its outputs."""


class Toolchain:
    """The three build output directories, and the executables inside them."""

    def __init__(self, **overrides):
        validate_environment()
        unknown = overrides.keys() - DIRECTORIES.keys()
        if unknown:
            raise ValueError(f"unknown build directories: {', '.join(sorted(unknown))}")
        self.directories = {
            kind: checkout_path(overrides[kind]) if kind in overrides else output_directory(kind)
            for kind in DIRECTORIES
        }

    def tool(self, kind, name):
        directory = self.directories[kind]
        path = directory / name
        if path.is_file() and os.access(path, os.X_OK):
            return path
        variable, _ = DIRECTORIES[kind]
        raise Missing(
            f"{name} is not in {path.parent}\n"
            f"  searched the {kind} build's output directory ({variable})\n"
            f"  build it with: {BUILDS[kind]}\n"
            f"  present there: {', '.join(self.present(kind)) or 'nothing'}"
        )

    def present(self, kind):
        """The executables this build has actually produced, for a failure to name.

        Lake writes a digest, a response file and a trace beside each binary; an
        extension is what separates those from the executable itself.
        """
        directory = self.directories[kind]
        if not directory.is_dir():
            return []
        return sorted(entry.name for entry in directory.iterdir()
                      if entry.is_file() and not entry.suffix and os.access(entry, os.X_OK))

    # The compiler build.

    @property
    def compiler(self):
        return self.tool("compiler", "zkc-compile")

    @property
    def optimizer(self):
        return self.tool("compiler", "zkc-opt")

    @property
    def source_bench(self):
        return self.tool("compiler", "zkc-source-bench")

    def service(self, name):
        """A tool from the compiler's own service example, by its name."""
        return self.tool("compiler", str(Path("examples/service") / name))

    def native_test(self, name):
        """A native API test executable, which CMake writes beside its source.

        The compiler build's own directory may still hold an older copy of one
        of these, from a configuration that wrote them there, so the directory
        is part of the name.
        """
        return self.tool("compiler", str(Path("test") / name))

    # The native build.

    @property
    def runtime(self):
        return self.tool("native", "zkc")

    @property
    def primitive(self):
        return self.tool("native", "artifact-primitive")

    def example(self, name):
        """A Rust example binary, by its name."""
        return self.tool("native", str(Path("examples") / name))

    # The formal build.

    def checker(self, name):
        """A compiled Lean reference, by its executable name.

        The ten references are not interchangeable: a source consumer refuses
        an artifact descriptor, and an artifact reference refuses a table plan.
        Passing the wrong one produces a plausible refusal rather than an
        obvious error, so the name belongs to the test.
        """
        return self.tool("lean", name)


# Repeated requests in one process share a directory. Other processes and
# later invocations allocate their own, without deleting earlier evidence.
OPENED = {}


def records_root():
    """Where this run leaves everything the tests write.

    One place, named one way, whether a test asks for its directory through
    `records` or through the fixture that knows which case is running.
    """
    return reports_root() / "tests"


def records(case=None):
    """The directory the calling test writes its sources, plans and reports to.

    The name is the test file's, not a string the test repeats: every one of
    these directories was named after the file it was written in, so writing it
    out again only created something a rename could leave behind. `case` is for
    a test that runs its subject more than once, so each run keeps its own.

    The first request allocates an empty directory; further requests for that
    caller and case return it. Its full source path is part of the identity.
    A different process or invocation cannot remove or reuse that directory.
    """
    caller = Path(sys._getframe(1).f_globals.get("__file__", "")).resolve()
    if not caller.name.startswith("test_"):
        raise ValueError(
            f"records() names the directory after the test file that calls it, and "
            f"{caller or 'this caller'} is not one. Something shared by several "
            f"tests should be given the directory rather than asking for one, or "
            f"it will name every test's evidence after itself."
        )
    identity = str(caller) + (f"::{case}" if case is not None else "")
    key = (records_root(), identity, os.getpid())
    if key not in OPENED:
        shown = caller.relative_to(ROOT) if caller.is_relative_to(ROOT) else caller.name
        label = str(shown) + (f"::{case}" if case is not None else "")
        OPENED[key] = new_directory(key[0], identity, label)
    return OPENED[key]
