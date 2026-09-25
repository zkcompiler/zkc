"""The plan MLIR produces from a source, and the stages it passed through.

Several tests need a plan that the compiler's own passes produced, rather than
one written by hand or by the Lean reference, and each of them was walking the
same three steps: read the source into MLIR, run the lowering, read the result
back out as a plan. The stages are kept beside the plan, because when the last
step refuses it is usually the one before it that explains why.

The pipeline is a parameter because it is a real choice: a test that wants to
see what common subexpression elimination does to a plan asks for it, and one
that wants the lowering alone does not.
"""

PIPELINE = "lower-pir-to-plan"


def lowered_plan(journal, compiler, optimizer, source, folder, pipeline=PIPELINE):
    """Lower an admitted source to a plan, keeping each stage in `folder`."""
    imported = journal.attempt([compiler, "import", source])
    assert imported.returncode == 0, imported.stderr
    source_mlir = folder / "source.mlir"
    source_mlir.write_text(imported.stdout)

    lowered = journal.attempt([optimizer, source_mlir,
                               f"--pass-pipeline=builtin.module({pipeline})"])
    assert lowered.returncode == 0, lowered.stderr
    plan_mlir = folder / "plan.mlir"
    plan_mlir.write_text(lowered.stdout)

    exported = journal.attempt([compiler, "export", plan_mlir])
    assert exported.returncode == 0, exported.stderr
    plan = folder / "plan.json"
    plan.write_text(exported.stdout)
    return plan
