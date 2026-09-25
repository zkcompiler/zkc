"""What a test does to a tool, and what it keeps of having done it.

Every test here drives tools as separate processes and judges what comes back.
Each of them used to write that again: twenty-one versions of one function,
differing in what bound the tool, what counted as a refusal, and what a failure
was allowed to say. None of those differences was a choice anyone made.

There are two ways a test treats a tool, and they are different enough to say
separately. `run` is for a step the test requires: it must succeed, or it must
refuse for the reason the test names, and anything else stops the test there.
`attempt` is for a step the test is judging: it records what happened and hands
it back, and the test says what it makes of it through `check`.

The same division runs one level up, in what a test does with the answer.
`assert` is for a step the test requires, where everything after it would be
meaningless: a precondition, a setup, an invariant. `check` is for one judgment
among several that are each worth making, so a corpus that disagrees in three
places says so once rather than three runs later. A test whose cases are the
axis is better off as pytest cases, which name and select themselves.

Either way the invocation is kept, and kept as it happens rather than at the
end: a test that fails is exactly the one whose commands are worth reading, so
waiting until it finishes to write them down would lose them precisely then. A
failure names the exact command that produced it without running anything again.

What a tool printed is kept when it is worth keeping: always when the command
did not end the way the test required, because that output is what a failure has
to show, and otherwise when the test names the step with `keep`, because it
knows which outputs it will want to read again. Keeping every one of them would
be tens of megabytes of plans nobody looks at.
"""

import re
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from processes import Interrupted, positive_timeout, run  # noqa: E402, F401

# Long enough for the slowest tool these tests drive, short enough that a hung
# one is a failure with a stack rather than a run that never returns.
TIMEOUT = 120


def names(said, identifier):
    """Whether the output names `identifier` as a whole diagnostic.

    A substring test passes on a longer identifier that contains this one --
    `library-call` inside `library-call-arity` -- and on a path to a work
    directory named after the case being run. The identifier must stand alone:
    neither neighbour may continue an identifier or a path.
    """
    edge = r"A-Za-z0-9_./-"
    pattern = rf"(?<![{edge}]){re.escape(identifier)}(?![{edge}])"
    return re.search(pattern, said) is not None


class Refused(AssertionError):
    """A tool did not end the way the test required."""


class Journal:
    """The tools a test ran, what they answered, and where it wrote it down."""

    def __init__(self, directory=None, timeout=TIMEOUT):
        self.directory = Path(directory) if directory is not None else None
        self.timeout = positive_timeout(timeout)
        self.commands = []
        self.checks = []
        self.written = {}
        self.last = None

    # Running a tool.

    def attempt(self, command, stdin=None, timeout=None, cwd=None, text=True,
                env=None, keep=None, cleanup_grace=1):
        """Run a tool and keep what it did, judging nothing.

        `cwd` is for a tool that reads what is around it, and `env` for one
        that has to be told where another build's outputs are. `text` is for a
        tool whose answer is bytes, where decoding it is the test's business
        rather than this one's. `keep` names the step, for a test that will
        want to read what the tool printed rather than only what it returned.
        """
        argv = [str(part) for part in command]
        budget = self.timeout if timeout is None else positive_timeout(timeout)
        started = time.perf_counter()
        record = {"argv": argv, "cwd": str(Path(cwd or Path.cwd()).resolve()),
                  "timeout_seconds": budget, "returncode": None, "stderr": "", "wall_seconds": None}
        self.last = None
        try:
            result = run(argv, input=stdin, text=text, capture_output=True,
                                    timeout=budget,
                                    cwd=cwd, env=env, cleanup_grace=cleanup_grace)
            self.last = result
            record["returncode"] = result.returncode
            record["stderr"] = self.decoded(result.stderr)
        except subprocess.TimeoutExpired as error:
            # The one failure that cannot be reproduced cheaply by hand is the
            # one that took two minutes to happen, so it is the one whose record
            # matters most. Keeping it after the call would lose exactly that.
            record["returncode"] = "timeout"
            record["stderr"] = self.decoded(error.stderr or b"")
            # TimeoutExpired carries bytes even when text=True was requested.
            self.last = subprocess.CompletedProcess(argv, None, error.stdout or b"",
                                                     error.stderr or b"")
            raise
        except Interrupted as error:
            record["returncode"] = "interrupted"
            record["signal"] = error.signum
            record["stderr"] = self.decoded(error.stderr or b"")
            self.last = subprocess.CompletedProcess(argv, None, error.stdout or b"",
                                                     error.stderr or b"")
            raise
        except OSError as error:
            record["returncode"] = "not-run"
            record["stderr"] = str(error)
            raise
        except BaseException as error:
            record["returncode"] = "aborted"
            record["stderr"] = self.decoded(getattr(error, "stderr", b""))
            record["error"] = f"{type(error).__name__}: {error}"
            self.last = subprocess.CompletedProcess(argv, None, getattr(error, "stdout", b"") or b"",
                                                     getattr(error, "stderr", b"") or b"")
            raise
        finally:
            record["wall_seconds"] = time.perf_counter() - started
            self.commands.append(record)
            if self.last is not None and (keep is not None or record["returncode"]):
                self.retain(keep)
            self.flush("commands.jsonl", self.commands)
        return result

    @staticmethod
    def decoded(value):
        return value if isinstance(value, str) else (value or b"").decode(errors="replace")

    def retain(self, name=None):
        """Keep what the command just run printed, and say so in its record.

        Under the name the test gave, taken the way `write` takes one, or else
        under the command's place in this run, which is enough to find it from
        the record.
        """
        record = self.commands[-1]
        if self.directory is None or "output" in record:
            return None
        printed = self.decoded(self.last.stdout)
        path = Path(name) if name is not None else Path(f"output/{len(self.commands) - 1:04d}")
        if not path.is_absolute():
            path = self.directory / path
        path = path.with_suffix(path.suffix or ".stdout")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(printed)
        record["output"] = str(path)
        return path

    def run(self, command, stdin=None, refuses=None, timeout=None, cwd=None,
            keep=None):
        """Run a step the test requires, and return what the tool printed.

        `refuses` names the diagnostic the tool must produce for the step to
        have ended acceptably. An empty string, or `True`, accepts any refusal,
        which is a weaker statement and worth writing rather than leaving to a
        bare exit code.
        """
        result = self.attempt(command, stdin=stdin, timeout=timeout, cwd=cwd,
                              keep=keep)
        if result.returncode < 0:
            raise Refused(f"{result.args} terminated by signal {-result.returncode}: "
                          f"{result.stderr or result.stdout}")
        said = result.stdout + result.stderr
        if refuses is None:
            if result.returncode:
                raise Refused(f"{result.args} failed: {result.stderr or result.stdout}")
        else:
            if not result.returncode:
                # It ended well and should not have, so nothing kept it yet.
                self.retain(keep)
                self.rewrite("commands.jsonl", self.commands)
                raise Refused(f"{result.args} was expected to refuse: {result.stdout}")
            if refuses not in (True, "") and not names(said, refuses):
                raise Refused(f"{result.args} refused, but not with {refuses!r}: {said}")
        return result.stdout

    def json(self, command, stdin=None, refuses=None, timeout=None, cwd=None,
             keep=None):
        """The same, for a tool whose answer is JSON."""
        out = self.run(command, stdin=stdin, refuses=refuses, timeout=timeout,
                       cwd=cwd, keep=keep)
        try:
            return json.loads(out)
        except ValueError:
            raise Refused(f"{command[0]} printed no JSON: {out[:200]}") from None

    def parse(self, result):
        """What a tool that has already run printed, or a record of what it did.

        A comparison that meets output it cannot read should say so as a
        difference, not stop the run, so this hands back what came out rather
        than raising.
        """
        try:
            return json.loads(result.stdout)
        except ValueError:
            return {"invalid-output": result.stdout, "stderr": result.stderr}

    # Saying what the test makes of it.

    def check(self, name, passed, detail=None):
        """Record a named judgment without stopping at the first that fails."""
        self.checks.append({"name": name, "pass": bool(passed), "detail": detail})
        self.flush("checks.jsonl", self.checks)
        if not passed:
            print("FAIL", name, detail, flush=True)
        return bool(passed)

    @property
    def failures(self):
        return [one for one in self.checks if not one["pass"]]

    # Keeping it.

    def write(self, name, value):
        """Write a value beside the test's other evidence, and say where.

        A name is taken as relative to that directory. A test that has already
        worked out a path, for a case of its own, can pass that instead.
        """
        path = Path(name)
        if not path.is_absolute():
            path = self.directory / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value) + "\n")
        return path

    def flush(self, name, value):
        """Write the running record out, if this journal has somewhere to put it.

        Called after every command and every judgment, so a test that stops in
        the middle has left the same record as one that reached the end. It
        appends what is new rather than writing the whole list again: a test
        that runs fifteen hundred commands would otherwise spend its time
        serializing the first of them fifteen hundred times, and the cost of
        keeping the record would grow with the square of what it records.

        One record to a line, so a run killed mid-write leaves every line
        before it readable.
        """
        if self.directory is None:
            return
        self.directory.mkdir(parents=True, exist_ok=True)
        path = self.directory / name
        written = self.written.get(name, 0)
        if written > len(value):
            written = 0
        mode = "a" if written else "w"
        with path.open(mode) as out:
            for record in value[written:]:
                out.write(json.dumps(record) + "\n")
        self.written[name] = len(value)

    def rewrite(self, name, value):
        """Write the record again from the start, for a line that has changed.

        A command keeps what it printed after the fact when the refusal a test
        required did not come, which is the one case where a line already on
        disk stops being what happened.
        """
        self.written.pop(name, None)
        self.flush(name, value)

    def save(self, name="commands.jsonl"):
        """The number of commands run, for a test that reports its own count.

        The record itself is already on disk; this only names it, for a test
        that wants the file under a name of its own.
        """
        if self.directory is not None and name != "commands.jsonl":
            self.write(name, self.commands)
        return len(self.commands)
