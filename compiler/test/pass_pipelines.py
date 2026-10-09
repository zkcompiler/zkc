"""The native named pipeline is equivalent to its public individual passes."""
import json
from commands import Commands
from tools import ROOT, records

commands = Commands(records())
source = (ROOT / "compiler/test/fixtures/mathematical/local-execution.mlir").read_text()

def optimize(pipeline):
    return commands.verified(source, None, f"--pass-pipeline=builtin.module({pipeline})")

for project_only, linear, release in ((True, False, False), (False, False, False),
                                     (False, True, False), (False, False, True),
                                     (False, True, True)):
    options = f"project-only={str(project_only).lower()} linear-contractions={str(linear).lower()} release-storage={str(release).lower()}"
    named = optimize(f"zkc-participant-pipeline{{{options}}}")
    passes = "zkc-project-protocol"
    if not project_only:
        passes += ",zkc-eliminate-polynomials,zkc-lower-math,zkc-select-physical{" + f"linear-contractions={str(linear).lower()} release-storage={str(release).lower()}" + "}"
    explicit = optimize(passes)
    assert named == explicit
    if not project_only:
        assert json.loads(commands.source("protocol-export", named)) == json.loads(commands.source("protocol-export", explicit))
    else:
        commands.source("protocol-export", named, refuses="interactive-module")
projected = optimize("zkc-project-protocol")
commands.verified(projected, "mathematical-module", "--zkc-participant-pipeline")
print(f"native named pipeline: {commands.save()} checks")
