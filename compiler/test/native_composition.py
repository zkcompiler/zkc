"""General mathematical compositions produce size-independent role programs."""

import json
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
fixtures = Path(__file__).parent / "fixtures/mathematical"
manifest = []
for family, suite, service, public, roles, draws in [
    ("qap-composition", "", "", ["0", "1", "3", "4", "5", "6"], ["P", "V"], []),
    ("air-composition", "merlin3.koala-bear.ext8-binomial3.rejection31le/1", "6", ["1", "2", "3", "4", "5"], ["P", "V"], [["draw", "challenge"]]),
    ("target-accumulation", "", "", ["0", "1", "2", "3"], ["P", "V"], []),
]:
    for suffix, options in [
        ("", ()),
        ("_plain", ("--no-simplify",)),
        ("_release", ("--release-storage",)),
    ]:
        name = family + suffix
        with case(name):
            source = fixtures / (family + ".mlir")
            p = [
                "zkc.native-proof-policy/4",
                "main",
                *roles,
                "0",
                suite,
                service,
                public,
                draws,
            ]
            policy = OUT / (name + ".policy")
            policy.write_text(json.dumps(p))
            candidate = OUT / (name + ".candidate.mlir")
            candidate.write_text(
                commands.run([compiler, "protocol-construct-proof", source, policy])
            )
            commands.run([compiler, "protocol-check-proof", source, policy, candidate])
            (OUT / (name + ".deployment")).write_text(
                commands.run([compiler, "protocol-proof", source, policy, *options])
            )
            manifest.append(dict(name=name, family=family))
(OUT / "manifest.json").write_text(json.dumps(manifest))
counted()
