"""Let one failing check stop being the only one a run reports.

A file in this directory is one CTest test, and a bare `assert` ends the
process. Every check after the first failure then goes unrun and unreported:
measured on `frontend_pipeline.py`, a failure two hundred lines in left 388 of
its 521 checks, seventy-four per cent, unexecuted. A change that breaks four
things looks like it broke one, and finding the second costs another full run.

A case is a named group that is allowed to fail on its own. What fails is
recorded, the file carries on, and the run ends non-zero with every failure
named and its traceback intact:

    with case("a tampered binding attribute is refused"):
        ...

Nothing here is required. A file that uses no case behaves exactly as it did,
and a file can wrap one block and leave the rest alone; that is the point of
it being a context manager rather than a runner. The one thing a case must not
do is leave state that a later case needs. If two blocks share a value, they
are one case -- otherwise the second would fail for the first one's reason and
report something that is not true.

Only `Exception` is caught. A KeyboardInterrupt still stops the run, and so
does a `SystemExit` from a support layer that has decided the run cannot go on.
"""

import atexit
import os
import sys
import traceback
from contextlib import contextmanager

failures = []
passes = []


@contextmanager
def case(name):
    """Run a named group, and keep going if it fails."""
    try:
        yield
    except Exception:
        failures.append((name, traceback.format_exc()))
    else:
        passes.append(name)


def counted():
    """How many cases ran, for a file that reports its own numbers."""
    return len(passes) + len(failures)


@atexit.register
def _report():
    """Name every failed case, and make the run fail once for all of them.

    This runs on the way out rather than being called, so a file cannot pass by
    forgetting to ask. `os._exit` is what sets the status from here: raising
    SystemExit inside an exit handler does not change a process's exit code.
    Both streams are flushed first, because that call does not flush them.
    """
    if not failures:
        return
    print(
        f"\n{len(failures)} of {counted()} cases failed",
        file=sys.stderr,
    )
    for name, formatted in failures:
        print(f"\n--- {name}\n{formatted}", file=sys.stderr, end="")
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(1)
