"""The one compile and export pipeline of a subject.

For a proof Entry: emit the original MLIR, read the language interface, bundle
the native deployment (and, for executable subjects, the Entry package),
construct the proof candidate, export the constructed validator participant
and the original's structured snapshot, and compile declared variants. For an
interactive Entry: emit, read the interface and export the structured
snapshot. Every artifact is retained in the evidence directory, and the
identities the artifacts claim (source digests, policies, program digests) are
checked against each other.
"""

import json
from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import ROOT, digest  # noqa: E402
from bridges.common.native_entry import native_subject  # noqa: E402
from bridges.pipeline import source_claims  # noqa: E402


def options(subject, entry, extra=(), *, protocol=False):
    return ["--source-format=zkc", f"--{'subject' if protocol else 'entry'}={entry}", *subject.module_arguments(),
            *subject.compiler_options, *extra]


def proof_artifacts(runner, subject, compiler, directory, executable=False):
    """Compile the original and participant bytes independently of claim resolution."""
    directory.mkdir(parents=True, exist_ok=True)
    entry = subject.get("entries", "proof")
    common = options(subject, entry)
    prefix = f"{subject.name}:proof"

    def run(*arguments, name):
        return runner.run([compiler, *arguments], name=f"{prefix}:{name}").stdout

    source = run("language-emit", *common, name="emit").encode()
    (directory / "source.mlir").write_bytes(source)
    interface_text = run("language-interface", *common, name="interface")
    (directory / "interface.json").write_text(interface_text)
    interface = json.loads(interface_text)
    runner.check(f"{prefix}:interface-source", interface["original"] == digest(source))
    deployment_text = run("language-bundle", *common, name="bundle").rstrip("\n")
    (directory / "deployment.json").write_text(deployment_text)
    deployment = json.loads(deployment_text)
    runner.check(f"{prefix}:deployment-source", deployment[1] == digest(source))
    policy = deployment[2][1]
    (directory / "policy.json").write_text(json.dumps(policy))
    artifacts = dict(source=source, interface=interface, interface_text=interface_text, deployment=deployment,
                     deployment_text=deployment_text, policy=policy)
    if executable:
        package_text = run("language-package", *common, name="package")
        (directory / "package.zkpkg").write_bytes(package_text.encode())
        package = json.loads(package_text)
        program = deployment[4].encode()
        (directory / "program.json").write_bytes(program)
        runner.check(f"{prefix}:package-artifact", package["artifact"] == deployment_text)
        runner.check(f"{prefix}:package-original", package["original"].encode() == source)
        runner.check(f"{prefix}:deployment-program", deployment[5] == digest(program))
        artifacts.update(package=package, package_bytes=package_text.encode(), program=program)
    candidate = run("protocol-construct-proof", directory / "source.mlir", directory / "policy.json",
                    name="construct")
    (directory / "candidate.mlir").write_text(candidate)
    export_text = run("protocol-constructed-participant", directory / "source.mlir", directory / "policy.json",
                      directory / "candidate.mlir", name="participant")
    (directory / "participant.json").write_text(export_text)
    exported = json.loads(export_text)
    original_text = run("protocol-structured", directory / "source.mlir", f"--symbol={policy[1]}",
                        name="original")
    (directory / "original.json").write_text(original_text)
    runner.check(f"{prefix}:participant-source", exported[1] == "sha256:" + digest(source))
    runner.check(f"{prefix}:participant-policy", exported[3] == policy, json.dumps([exported[3], policy]))
    runner.check(f"{prefix}:original-source", json.loads(original_text)[2] == "sha256:" + digest(source))
    variants = {}
    for name, flags in subject.get("executable", "variants", {}).items():
        text = run("language-bundle", *options(subject, entry, flags), name=f"bundle:{name}").rstrip("\n")
        (directory / f"deployment-{name}.json").write_text(text)
        variants[name] = json.loads(text)
    artifacts.update(candidate=candidate, exported=exported, export_text=export_text,
                     original=json.loads(original_text), original_text=original_text, variants=variants)
    return artifacts


def proof_entry(runner, subject, compiler, directory, executable=False):
    """Compile a proof Entry and bind its independently exported source requests."""
    artifacts = proof_artifacts(runner, subject, compiler, directory, executable)
    entry = subject.get("entries", "proof")
    claim_text = runner.run([compiler, "language-check", *options(subject, entry), "--source-claims"],
                            name=f"{subject.name}:proof:source-claims").stdout
    (directory / "source-claims.json").write_text(claim_text)
    claim_report = source_claims.decode(claim_text)
    bound_claims = source_claims.bind_export(
        claim_report["source_claims"], entry=entry, source=artifacts["source"],
        interface_text=artifacts["interface_text"], original_text=artifacts["original_text"],
        participant_text=artifacts["export_text"], program=artifacts.get("program"))
    for claim in bound_claims["claims"]:
        claim["resolved_sites"] = source_claims.resolve_sites(
            artifacts["original"], artifacts["policy"], claim["site_bindings"])
    (directory / "bound-source-claims.json").write_text(json.dumps(bound_claims, indent=2) + "\n")
    artifacts["source_claims"] = bound_claims
    artifacts["source_claim_inventory"] = claim_report["source_claim_inventory"]
    return artifacts


def interactive_entry(runner, subject, compiler, directory):
    """Compile and export the explicitly selected interactive protocol."""
    directory.mkdir(parents=True, exist_ok=True)
    entry = subject.get("entries", "interactive")
    common = options(subject, entry, protocol=True)
    prefix = f"{subject.name}:interactive"
    source, interface_text, interface = native_subject(
        lambda command: runner.run(command, name=f"{prefix}:{command[1]}").stdout, compiler, common)
    (directory / "source.mlir").write_text(source, encoding="utf-8")
    (directory / "interface.json").write_text(interface_text)
    runner.check(f"{prefix}:interface-source", interface["original"] == digest(source.encode()))
    exported = runner.run([compiler, "protocol-structured", directory / "source.mlir",
                           f"--symbol={interface['protocol']}"], name=f"{prefix}:export").stdout
    (directory / "source.json").write_text(exported, encoding="utf-8")
    snapshot = json.loads(exported)
    runner.check(f"{prefix}:export-source", snapshot[2] == "sha256:" + digest(source.encode())
                 and snapshot[3] == interface["protocol"])
    claim_text = runner.run([compiler, "language-check", *common, "--source-claims"],
                            name=f"{prefix}:source-claims").stdout
    (directory / "source-claims.json").write_text(claim_text)
    claim_report = source_claims.decode(claim_text)
    bound = source_claims.bind_export(claim_report["source_claims"], entry=interface["entry"],
        source=source.encode(), interface_text=interface_text, original_text=exported)
    (directory / "bound-source-claims.json").write_text(json.dumps(bound, indent=2) + "\n")
    return dict(source=source, interface=interface, export_text=exported, snapshot=snapshot, source_claims=bound,
                source_claim_inventory=claim_report["source_claim_inventory"])


def relative(path):
    return str(Path(path).relative_to(ROOT))
