#!/usr/bin/env python3
"""Check freshly printed readback, quantitative and receipt modules in isolation.

Uses existing dependencies; never runs a Lake build. Supply prechecked dependency
trees when the shared checkout is moving. Actual native roots retain their own
export/regeneration and full experiment controls.
"""
from argparse import ArgumentParser
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "lean"))
from bridges.structured.generate_component_roots import Generation  # noqa: E402


def main(argv=None):
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--dependency-path", action="append", type=Path, default=[])
    args = parser.parse_args(argv)
    args.check = False
    generation = Generation(args)
    (generation.directory / "results.json").write_text("[]\n")
    generation.prepare([
        "ZkcTools.StructuredSource.Root", "ZkcSecurity.Generation.SubjectABI",
        "ZkcSecurity.Generation.RootCompleteness", "ZkcSecurity.Generation.UniformRoot",
        "ZkcSecurity.Generation.SigmaCompleteness", "ZkcSecurity.Generation.SigmaCompleteness.Command",
        "ZkcSecurity.Tools.ClaimConstruction",
        "TestsSecurity.ABIInstallations.NoData", "TestsSecurity.ABIInstallations.Ordered",
        "TestsSecurity.RootAssemblyFixture", "TestsSecurity.RootAssemblyGeneration",
    ])
    sources = generation.directory / "sources"
    sources.mkdir(exist_ok=True)
    generation.execute([generation.lean, "--run",
                        generation.package / "checks/RunRootAssembly.lean", sources],
                       generation.package)
    results = []
    for module in json.loads((sources / "sources.json").read_text()):
        source = sources.joinpath(*module.split(".")).with_suffix(".lean")
        refused = module.endswith((".WrongBound", ".WrongSubject"))
        try:
            generation.compile(module, source, source_root=sources)
        except RuntimeError:
            log = Path(generation.commands[-1]["log"]).read_text()
            if not refused or "Type mismatch" not in log:
                raise
        else:
            if refused:
                raise RuntimeError(f"accepted incorrect endpoint: {module}")
        results.append({"module": module, "expected_type_refusal": refused, "passed": True,
                        "exit_code": generation.commands[-1]["returncode"],
                        "log": generation.commands[-1]["log"],
                        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
        (generation.directory / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(f"PASS {module}", flush=True)
    print(f"All {len(results)} common assembly generation controls passed.")


if __name__ == "__main__":
    main()
