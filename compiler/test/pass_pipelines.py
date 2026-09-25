"""Named pipelines retain the command-line and individual-pass transformations."""

import json

from cases import case
from commands import Commands
from source import envelope
from tools import compiler, corpus, optimizer, records

commands = Commands(records())
folder = commands.directory


def optimize(text, pipeline):
    return commands.run(
        [optimizer, f"--pass-pipeline=builtin.module({pipeline})"], stdin=text
    )


def export(text, protocol=False):
    path = folder / "candidate.mlir"
    path.write_text(text)
    return json.loads(
        commands.run([compiler, "protocol-export" if protocol else "export", path])
    )


context = [
    "trace",
    [["x", ["scalar", "f7"], ["shared"], "argument"]],
    ["scalar", "f7"],
    [["table-protocol", "1"]],
]
source = folder / "source.json"
source.write_text(
    json.dumps(envelope(context, ["apply", ["linear"], [0, 0, 0], ["return", 0]]))
)
logical = commands.run([compiler, "import", source])
for mode, simplify in [("", False), ("lazy", False), ("materialized", False),
                       ("lazy", True), ("materialized", True)]:
    with case(f"{mode or 'logical'} simplify={simplify}"):
        options = ([f"physical={mode}"] if mode else []) + (
            ["simplify=true"] if simplify else []
        )
        named = "zkc-table-pipeline" + (
            "{" + " ".join(options) + "}" if options else ""
        )
        pipeline_ir = optimize(logical, named)
        pipeline = export(pipeline_ir)
        flags = ([f"--physical={mode}"] if mode else []) + (
            ["--simplify"] if simplify else []
        )
        assert pipeline == json.loads(
            commands.run([compiler, "compile", source, *flags])
        )
        passes = (["simplify-table-regions"] if simplify else []) + [
            "lower-pir-to-plan"
        ] + ([f"lower-plan-to-physical{{mode={mode}}}"] if mode else [])
        assert pipeline == export(optimize(logical, ",".join(passes)))
        if simplify:
            assert '"poly.linear"' not in pipeline_ir

protocol = corpus / "linear-contractions.pir"
common = commands.run([compiler, "protocol-import", protocol])
for project_only, flags in [
    (True, []),
    (False, []),
    (False, ["--linear-contractions"]),
    (False, ["--release-storage"]),
    (False, ["--linear-contractions", "--release-storage"]),
]:
    with case(str((project_only, flags))):
        options = (
            ["project-only=true"]
            if project_only
            else [flag[2:] + "=true" for flag in flags]
        )
        pipeline = "zkc-participant-pipeline" + (
            "{" + " ".join(options) + "}" if options else ""
        )
        actual = export(optimize(common, pipeline), protocol=True)
        mode = "protocol-project" if project_only else "protocol-compile"
        expected = json.loads(commands.run([compiler, mode, protocol, *flags]))
        assert actual == expected
        passes = "zkc-project-participants"
        if not project_only:
            passes += ",zkc-plan-participants" + (
                "{" + " ".join(options) + "}" if options else ""
            )
        assert actual == export(optimize(common, passes), protocol=True)

with case("wrong-stage"):
    projected = optimize(common, "zkc-project-participants")
    result = commands.attempt(
        [optimizer, "--pass-pipeline=builtin.module(zkc-participant-pipeline)"],
        stdin=projected,
    )
    assert result.returncode > 0 and "interactive-projection-stage" in result.stderr
    assert not result.stdout and "Stack dump" not in result.stderr

with case("the compiler reports a refused projection as its own refusal"):
    # A carrier that is already projected cannot be projected again. The
    # compiler prints the refusal the way it prints its others, without the
    # location MLIR would give the whole module.
    projected = folder / "projected.json"
    projected.write_text(commands.run([compiler, "protocol-project", corpus / "linear-contractions.pir"]))
    for mode in ("protocol-project", "protocol-compile"):
        result = commands.attempt([compiler, mode, projected])
        assert result.returncode == 1 and not result.stdout, result.stderr
        assert result.stderr == "interactive-projection-stage\n", result.stderr

with case("invalid-option"):
    result = commands.attempt(
        [
            optimizer,
            "--pass-pipeline=builtin.module(zkc-table-pipeline{physical=unknown})",
        ],
        stdin=logical,
    )
    assert (
        result.returncode > 0
        and "unsupported-preparation-mode" in result.stderr
        and not result.stdout
        and "Stack dump" not in result.stderr
    )
