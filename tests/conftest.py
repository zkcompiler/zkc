"""Fixtures every cross-build test shares.

A file under `tests/admission`, `artifact`, `execution`, `identity`, `kernels`,
`physical` or `protocol` is a test because pytest collects it, which is what
stops a test from sitting here unrun. The rest of this directory is not
collected and is not meant to be: `support` is the vocabulary the tests import,
`fixtures` the inputs they read, `consumer` a separate CMake project `just
test-install` builds, and `groth16` the Circom and snarkjs fixture generation,
whose own controls are collected from `groth16/tests`.

Where the three builds are, and where a run leaves what it wrote, is settled in
`support/toolchain.py` and shared by direct commands, just and Nix checks. These
fixtures are that, with the one thing a plain function cannot know added: which
case is running.
"""

import os
import shlex

import pytest

from differential import Run
from journal import Journal
from toolchain import Toolchain, records_root
from reporting import new_directory


@pytest.fixture(scope="session")
def toolchain():
    """Where the three builds put the executables these tests run."""
    return Toolchain()


@pytest.fixture(scope="session")
def records():
    """The directory this run writes its evidence into."""
    root = records_root()
    root.mkdir(parents=True, exist_ok=True)
    return root


@pytest.fixture
def directory(records, request):
    """An exclusive directory for this invocation of the complete test ID."""
    return new_directory(records, request.node.nodeid)


# Every table storage layout the runtime offers. A suite that compares native
# execution against the Lean reference says something about each of them, so
# the layout is a case of that suite rather than a separate test that re-runs
# it. `None` is the runtime's own default.
STORAGE_LAYOUTS = (None, "packed", "segmented")


@pytest.fixture
def storage(toolchain, directory):
    """A toolchain whose runtime has been told which storage layout to use.

    A suite asks its native build directory for `zkc`. A directory holding one
    wrapper of that name is a native build as far as it can tell, so the layout
    reaches it without the suite being handed a tool or knowing this happened.
    """
    def told(layout):
        if layout is None:
            return toolchain
        binary_directory = directory / "storage" / layout / "bin"
        binary_directory.mkdir(parents=True, exist_ok=True)
        wrapper = binary_directory / "zkc"
        script = (f'#!/bin/sh\nexec {shlex.quote(str(toolchain.runtime))} '
                  f'"$@" --storage {layout}\n')
        # Written under another name and moved into place, because workers run
        # in parallel over one path and a truncating write can be read
        # half-finished by the one already executing it.
        if not wrapper.exists() or wrapper.read_text() != script:
            staged = binary_directory / f"zkc.{os.getpid()}"
            staged.write_text(script)
            staged.chmod(0o755)
            staged.replace(wrapper)
        return Toolchain(native=binary_directory)
    return told


@pytest.fixture
def journal(directory):
    """A journal that keeps this test's evidence in this test's own directory.

    The same thing `Journal(records())` gives a test that is one case, for a
    test that is many: the directory comes from the fixture that knows which
    case is running, so the cases do not write over each other.

    A judgment recorded through `check` does not stop the test, which is the
    point of it -- a corpus that disagrees in three places says so once. It
    does have to reach the result, though, and a test that records failures and
    then forgets to look at them would otherwise pass green with them in its
    captured output. Looking is what happens here.
    """
    kept = Journal(directory)
    yield kept
    failed = [one["name"] for one in kept.failures]
    assert not failed, f"checks recorded as failures: {failed}"


@pytest.fixture
def run(toolchain, directory):
    """A source compiled and executed by both implementations.

    A test that asks for a second one gets a directory of its own for it. They
    write their sources and plans under fixed names, so two over one directory
    would leave the first subject checked against the second's.
    """
    made = []

    def make(checker="table-protocol"):
        folder = directory if not made else directory / f"subject-{len(made)}"
        folder.mkdir(parents=True, exist_ok=True)
        made.append(folder)
        return Run(toolchain, folder, checker)

    return make
