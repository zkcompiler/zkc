"""Isolated tools, reports, and command journals for native integration tests."""

import pytest

from journal import Journal
from toolchain import Toolchain, records_root
from reporting import new_directory


@pytest.fixture(scope="session")
def toolchain():
    """Where the compiler and Rust builds put the executables these tests run."""
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
