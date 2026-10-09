"""Record compiler invocations and require the expected diagnostic on refusal.

`source` runs a subcommand with source text on standard input. `run` and `json`
accept complete commands for path inputs, the optimizer and pass pipelines.
The journal retains the invocation and the output needed to diagnose failures.
"""

from journal import Journal, Refused

from tools import compiler, optimizer

# Bound each compiler invocation so a hung tool produces a recorded failure.
TIMEOUT = 60


class Commands(Journal):
    """The tools a test ran, what they answered, and where it wrote it down."""

    def __init__(self, directory=None, tool=None, timeout=TIMEOUT):
        super().__init__(directory, timeout)
        self.tool = tool or compiler

    def run(self, command, *arguments, refuses=None, **keywords):
        """Require compiler refusals to diagnose on stderr without stdout."""
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
