"""Run one source through the native path and the Lean reference, and compare.

This is the shape of nearly every cross-build test: write a source and its
input, compile it, execute the candidate natively, execute it again through an
independently implemented Lean reference, and require the two complete results
to agree. What differs between tests is the source and what they expect, not
this procedure.

The tools are run through a `Journal`, so a failure here names the exact
invocation that produced it and the commands stay on disk whether or not the
comparison agreed.
"""

import json

from journal import Journal, Refused
from source import invocation, request

__all__ = ["Refused", "Run"]


class Run:
    """One source, compiled and executed by both implementations."""

    def __init__(self, toolchain, directory, checker="table-protocol", journal=None):
        self.toolchain = toolchain
        self.directory = directory
        self.checker = toolchain.checker(checker)
        self.journal = journal if journal is not None else Journal(directory)

    @property
    def commands(self):
        return self.journal.commands

    def invoke(self, *command):
        return self.journal.attempt(list(command))

    def write(self, name, value):
        return self.journal.write(name, value)

    def compile(self, inputs, result, body, state=None, profile="finite-source-1"):
        """Compile a source, and keep the plan and the input beside it."""
        self.profile = profile
        self.source = self.write("source.json",
                                 request(inputs, result, body, profile))
        self.inputs = self.write("inputs.json", invocation(inputs, state))
        compiled = self.invoke(self.toolchain.compiler, "compile", self.source)
        if compiled.returncode:
            raise Refused(f"the compiler refused this source: {compiled.stderr}")
        self.plan = self.directory / "plan.json"
        self.plan.write_text(compiled.stdout)
        return json.loads(compiled.stdout)

    def native(self):
        """The candidate's complete result, as the runtime reports it."""
        return self.report("native", self.toolchain.runtime, "run",
                           self.source, self.plan, self.inputs, self.checker)

    def reference(self):
        """The same source's complete result, from the independent Lean model."""
        return self.report("lean", self.checker, "run",
                           self.source, self.plan, self.inputs)

    def report(self, name, *command):
        result = self.invoke(*command)
        (self.directory / f"{name}.json").write_text(result.stdout)
        if result.returncode < 0:
            raise Refused(f"{name} terminated by signal {-result.returncode}: {result.stderr}")
        try:
            return json.loads(result.stdout)
        except ValueError:
            raise Refused(f"{name} produced no report: {result.stderr}") from None

    def both(self):
        """The native and reference results, required to agree.

        Agreement is the evidence: the same source, run by two implementations
        written from the same specification, must produce the same outcome, the
        same residual state and the same observed events.
        """
        native, reference = self.native(), self.reference()
        assert native == reference, (
            f"the native path and the Lean reference disagree\n"
            f"  native:    {json.dumps(native, sort_keys=True)}\n"
            f"  reference: {json.dumps(reference, sort_keys=True)}"
        )
        return native
