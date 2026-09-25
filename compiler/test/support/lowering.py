"""The plan the compiler's own passes produce from a source, and the MLIR between.

Seven tests here walk the same three steps -- read the source into MLIR, run a
pipeline over it, read the result back out as a plan -- and each of them wrote
those steps again, differing only in which pipeline and in what they called the
intermediate files. The pipeline is a parameter because it is a real choice: a
test that wants to see what common subexpression elimination does to a plan
asks for it, and one that wants the lowering alone does not.

The MLIR is handed back rather than kept inside, because the tests that mutate
it are the reason this shape exists: a malformed child, a stale flow, an
attribute the dialect does not admit. They take the text, change one thing, and
run the optimizer over it expecting a refusal.
"""

import json

from tools import compiler, optimizer

PIPELINE = "lower-pir-to-plan"


def imported(commands, source):
    """The MLIR the compiler reads a source into."""
    return commands.run([compiler, "import", source])


def lowered(commands, text, folder, pipeline=PIPELINE, name="source"):
    """The MLIR that pipeline produces from that MLIR.

    Kept beside the test's other evidence, because when the export refuses it
    is usually this step that explains why -- and because a test that judges
    the passes rather than the plan judges this.
    """
    path = folder / f"{name}.mlir"
    path.write_text(text)
    return commands.run(
        [optimizer, path, f"--pass-pipeline=builtin.module({pipeline})"]
    )


def exported(commands, text, folder, name="plan"):
    """The JSON the compiler reads a plan back out as."""
    path = folder / f"{name}.mlir"
    path.write_text(text)
    return json.loads(commands.run([compiler, "export", path]))


def planned(commands, text, folder, pipeline=PIPELINE, name="source"):
    """The three steps together, for a test that judges only the plan."""
    return exported(commands, lowered(commands, text, folder, pipeline, name), folder)


def refused(commands, text, folder, name="invalid"):
    """What the optimizer says about MLIR a test has deliberately broken.

    A refusal, never a crash: a stack dump means the dialect met something it
    did not check for rather than something it rejected.
    """
    path = folder / f"{name}.mlir"
    path.write_text(text)
    result = commands.attempt([optimizer, path])
    assert result.returncode > 0, (name, result.stdout)
    assert "Stack dump" not in result.stderr, (name, result.stderr)
    return result.stderr
