"""What a test asked the compiler, and what it keeps of having asked.

Every test here ran the compiler as a separate process and judged what came
back, and every one of them wrote that again: thirty-nine versions of one
function, differing in how long a tool was given, in what a refusal was called,
in whether its reason was looked for on standard error or on either stream, and
in whether the exit code had to be one or merely not zero. None of those
differences was a choice anyone made, and none of them kept the invocation, so
a failure was a Python traceback holding a tuple rather than the command that
produced it.

`Commands` is the journal the cross-build tests keep, given the tool this build
produced. `source` is the shape almost every test here uses: one subcommand
over one source, which the compiler reads from standard input. Anything else --
a tool that takes paths, the optimizer, a pass pipeline -- is `run` and `json`
from the journal itself, which take the whole command.

A test names what it wants the compiler to refuse with, so the refusal it got
for the wrong reason is a failure rather than a pass.
"""

from journal import Journal, Refused

from tools import compiler, optimizer

# Long enough for the slowest of these, short enough that a hung tool is a
# failure with a stack rather than a run that never returns. It replaces seven
# separate numbers between ten seconds and two minutes, none of them measured.
# The record these tests now keep says what they were worth: across 5,600
# invocations the slowest single call is 2.1s, so this is about thirty times
# the longest thing it has to allow.
TIMEOUT = 60


class Commands(Journal):
    """The tools a test ran, what they answered, and where it wrote it down."""

    def __init__(self, directory=None, tool=None, timeout=TIMEOUT):
        super().__init__(directory, timeout)
        self.tool = tool or compiler

    def run(self, command, *arguments, refuses=None, **keywords):
        """The journal's own, plus what a refusal from this compiler may print.

        A refusal here says nothing but why, and says it on standard error:
        there is no partial answer to read beside the reason. Six files in this
        directory each wrote that assertion out, in three spellings that
        differed only in what they then handed back.

        It is not true of every tool the cross-build tests drive -- a Lean
        checker answers `["refused", code]` on standard output and exits
        non-zero, because its answer is its output -- so it belongs with this
        compiler rather than in the journal both suites share.
        """
        printed = super().run(command, *arguments, refuses=refuses, **keywords)
        if refuses is not None and printed:
            raise Refused(f"{command} refused and still printed: {printed[:200]}")
        return printed

    def attempted(self, *command):
        """Run a tool and judge nothing: the call sites do that."""
        return self.attempt(command)

    def verified(self, ir, refuses=None, *options):
        """The optimizer over IR on standard input, verifying as it goes."""
        return self.run([optimizer, "--verify-each", *options], stdin=ir,
                        refuses=refuses)

    def source(self, subcommand, text=None, *options, refuses=None, keep=None,
               timeout=None, tool=None):
        """Run one subcommand over one source and return what it printed.

        The source is text the compiler reads from standard input, which is
        what `-` in the command line means. A subcommand that takes its subject
        as a path takes it in `options` instead and leaves `text` out.

        `refuses` names the diagnostic the compiler must produce. Naming it is
        the point: a source that is refused for a reason the test did not mean
        is not a passing control.
        """
        argv = [tool or self.tool, subcommand]
        argv += ["-", *options] if text is not None else list(options)
        return self.run(argv, stdin=text, refuses=refuses, keep=keep,
                        timeout=timeout)
