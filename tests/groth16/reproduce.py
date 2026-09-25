#!/usr/bin/env python3
"""Stage and reproduce the pinned Groth16 fixtures without changing source files."""

import argparse
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
SOURCE = Path(__file__).resolve().parent
sys.path.insert(0, str(SOURCE / "scripts"))
from common import check_files, read_json, sha256, write_json  # noqa: E402


def source_snapshot():
    return {
        str(path.relative_to(SOURCE)): sha256(path)
        for path in SOURCE.rglob("*")
        if path.is_file()
        and ".work" not in path.relative_to(SOURCE).parts
        and "__pycache__" not in path.relative_to(SOURCE).parts
    }


def command(arguments, cwd=None, env=None):
    subprocess.run([str(value) for value in arguments], cwd=cwd, env=env, check=True)


def git_output(checkout, *arguments):
    return subprocess.check_output(
        ["git", "-C", str(checkout), *arguments], text=True
    ).strip()


def check_checkout(checkout, pin):
    if git_output(checkout, "rev-parse", "HEAD") != pin["commit"]:
        raise ValueError(f"Checkout is not at pinned {pin['commit']}: {checkout}")
    if git_output(checkout, "status", "--porcelain", "--untracked-files=normal"):
        raise ValueError(f"Checkout must be clean: {checkout}")


def check_evidence(root):
    evidence = root / "evidence"
    for line in (evidence / "SHA256SUMS").read_text().splitlines():
        digest, relative = line.split("  ", 1)
        if sha256(evidence / relative) != digest:
            raise ValueError(f"Preserved evidence hash mismatch: {relative}")
    original_versions = read_json(evidence / "original-versions.json")
    if sha256(root / "package-lock.json") != original_versions["dependencyLockSha256"]:
        raise ValueError(
            "Maintained npm lock differs from the original verified dependency graph"
        )
    manifest = read_json(evidence / "artifact-manifest.json")["files"]
    controls = 0
    for depth, count, rows, variables, domain in (
        (2, 19, 726, 731, 1024),
        (16, 61, 4128, 4147, 8192),
    ):
        base = evidence / f"depth{depth}"
        result = read_json(base / "controls.json")
        if result["passed"] != count or len(result["results"]) != count:
            raise ValueError(f"Wrong control count at depth {depth}")
        if len({item["name"] for item in result["results"]}) != count:
            raise ValueError(f"Duplicate control at depth {depth}")
        controls += count
        intermediates = read_json(base / "intermediates.json")
        for name, value in (
            ("nConstraints", rows),
            ("nVars", variables),
            ("domainSize", domain),
        ):
            if intermediates[name] != value:
                raise ValueError(f"Wrong {name} at depth {depth}")
        for path in base.iterdir():
            relative = f"artifacts/depth{depth}/{path.name}"
            if relative in manifest:
                check_files(
                    root, {f"evidence/depth{depth}/{path.name}": manifest[relative]}
                )
    print(
        f"Preserved evidence verified: {controls} named fixture controls, 26 vector digests, 4 fixed proofs"
    )


def prepare_workdir(path):
    work = Path(path).expanduser().resolve()
    allowed_in_source = SOURCE / ".work"
    if work == SOURCE or SOURCE.is_relative_to(work):
        raise ValueError("Work directory must not contain the maintained package")
    if work.is_relative_to(SOURCE) and not work.is_relative_to(allowed_in_source):
        raise ValueError(
            "Inside the package, generated content is allowed only under .work"
        )
    marker = work / ".groth16-workdir.json"
    if work.exists() and any(work.iterdir()) and not marker.is_file():
        raise ValueError(f"Refusing nonempty, unmarked work directory: {work}")
    if marker.is_file() and read_json(marker).get("schema") != "zkc.groth16-workdir/1":
        raise ValueError(f"Unrecognized work-directory marker: {work}")
    work.mkdir(parents=True, exist_ok=True)
    return work


def writable_copy(path):
    """Normalize generated copies only, including copies from read-only sources."""
    for item in [path, *path.rglob("*")]:
        permissions = stat.S_IRUSR | stat.S_IWUSR
        if item.is_dir():
            permissions |= stat.S_IXUSR
        item.chmod(item.stat().st_mode | permissions)


def stage_source(work):
    for name in ("scripts", "circuits", "evidence"):
        target = work / name
        if target.exists():
            writable_copy(target)
            shutil.rmtree(target)
        shutil.copytree(
            SOURCE / name, target, ignore=shutil.ignore_patterns("__pycache__")
        )
        writable_copy(target)
    for name in ("package.json", "package-lock.json", "SOURCE_PINS.json"):
        target = work / name
        if target.exists():
            target.unlink()
        shutil.copy2(SOURCE / name, target)
        writable_copy(target)
    (work / "reference").mkdir(exist_ok=True)
    (work / "logs").mkdir(exist_ok=True)


def prepare_circomlib(args, work, pin):
    checkout = args.circomlib_source
    if checkout:
        checkout = checkout.expanduser().resolve()
    else:
        checkout = work / "tools/circomlib-git"
        if not checkout.exists():
            if args.offline:
                raise ValueError(
                    "Offline bootstrap needs --circomlib-source at the pinned commit"
                )
            checkout.mkdir(parents=True)
            command(["git", "init", "--quiet", checkout])
            command(
                ["git", "-C", checkout, "remote", "add", "origin", pin["repository"]]
            )
            command(
                [
                    "git",
                    "-C",
                    checkout,
                    "fetch",
                    "--depth",
                    "1",
                    "origin",
                    pin["commit"],
                ]
            )
            command(
                ["git", "-C", checkout, "checkout", "--quiet", "--detach", "FETCH_HEAD"]
            )
    check_checkout(checkout, pin)
    archive = work / "tools/circomlib.tar"
    archive.parent.mkdir(exist_ok=True)
    command(
        [
            "git",
            "-C",
            checkout,
            "archive",
            "--format=tar",
            "--output",
            archive,
            pin["commit"],
        ]
    )
    target = work / "vendor/circomlib"
    if target.exists():
        shutil.rmtree(target)
    target.mkdir(parents=True)
    with tarfile.open(archive) as stream:
        stream.extractall(target, filter="data")
    archive.unlink()
    return {
        "commit": pin["commit"],
        "repository": pin["repository"],
        "export": "git archive of verified clean checkout",
    }


def prepare_circom(args, work, pin):
    checkout = args.circom_source
    binary = args.circom
    if checkout:
        checkout = checkout.expanduser().resolve()
        check_checkout(checkout, pin)
        if not binary:
            binary = checkout / "target/release/circom"
            if not binary.is_file():
                # The source checkout stays immutable, including its ignored target directory.
                target = work / "tools/circom-target"
                build = [
                    "cargo",
                    "build",
                    "--release",
                    "--locked",
                    "--manifest-path",
                    checkout / "Cargo.toml",
                    "--target-dir",
                    target,
                ]
                if args.offline:
                    build.append("--offline")
                build_env = dict(os.environ, CARGO_HOME=str(work / "tools/cargo-home"))
                command(build, env=build_env)
                binary = target / "release/circom"
    if not binary:
        if args.mode in ("all", "reuse-setup"):
            raise ValueError(
                "Pass --circom built from the pinned source or --circom-source"
            )
        return None, {
            "invoked": False,
            "reason": "Reused hash-checked compiler artifacts",
        }
    binary = binary.expanduser().resolve()
    version = subprocess.check_output([str(binary), "--version"], text=True).strip()
    if version != f"circom compiler {pin['version']}":
        raise ValueError(f"Unexpected Circom version: {version}")
    digest = sha256(binary)
    if args.circom_sha256 and digest != args.circom_sha256:
        raise ValueError("Supplied Circom binary does not match --circom-sha256")
    return str(binary), {
        "version": version,
        "binarySha256": digest,
        "sourceCommitPin": pin["commit"],
        "sourceCheckoutVerified": bool(checkout),
        "buildOrigin": "Local build or user-supplied binary; version/hash recorded. An existing binary's build provenance is the caller's responsibility.",
    }


def import_artifacts(args, work):
    if not args.reuse_artifacts:
        return
    origin = args.reuse_artifacts.expanduser().resolve()
    if origin == work:
        raise ValueError(
            "--reuse-artifacts must differ from --workdir; omit it to reuse this workdir"
        )
    manifest = read_json(SOURCE / "evidence/artifact-manifest.json")["files"]
    if args.mode == "reuse-setup":
        manifest = {
            name: value
            for name, value in manifest.items()
            if name.startswith("artifacts/setup/")
        }
    check_files(origin, manifest)
    for relative in manifest:
        target = work / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(origin / relative, target)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "mode",
        choices=("all", "reuse-setup", "validate", "check-evidence"),
        nargs="?",
        default="all",
    )
    parser.add_argument(
        "--workdir",
        type=Path,
        help="Generated files; default: a fresh temporary directory",
    )
    parser.add_argument(
        "--reuse-artifacts",
        type=Path,
        help="Existing fixture/work directory, verified against preserved hashes before copying",
    )
    parser.add_argument(
        "--circom",
        type=Path,
        help="Explicit Circom 2.2.2 binary built from the pinned source",
    )
    parser.add_argument(
        "--circom-sha256",
        help="Optional caller-selected hash of the supplied native binary",
    )
    parser.add_argument(
        "--circom-source",
        type=Path,
        help="Clean local checkout at the pinned commit; build therefrom if needed",
    )
    parser.add_argument(
        "--circomlib-source",
        type=Path,
        help="Clean local checkout at the pinned commit; otherwise fetch it",
    )
    parser.add_argument(
        "--npm-cache",
        type=Path,
        help="npm tarball cache; default: inside the work directory",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="Use local pinned source and npm cache only",
    )
    parser.add_argument("--workers", type=int, default=4)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    if args.circom_sha256 and not (args.circom or args.circom_source):
        parser.error("--circom-sha256 requires --circom or --circom-source")
    before = source_snapshot()
    check_evidence(SOURCE)
    if args.mode == "check-evidence":
        return
    work = prepare_workdir(args.workdir or tempfile.mkdtemp(prefix="zkc-groth16-"))
    print(f"Work directory: {work}", flush=True)
    print(
        "WARNING: public deterministic trapdoors and fixed randomizers; TEST ONLY, NOT SECURE.",
        flush=True,
    )
    # Mark before dependency setup, so a failed network bootstrap can be retried.
    write_json(
        work / ".groth16-workdir.json",
        {"schema": "zkc.groth16-workdir/1", "mode": args.mode},
    )
    write_json(work / "RESULTS.json", {"status": "running", "mode": args.mode})
    try:
        stage_source(work)
        pins = read_json(SOURCE / "SOURCE_PINS.json")
        library = prepare_circomlib(args, work, pins["circomlib"])
        binary, compiler = prepare_circom(args, work, pins["circom"])
        write_json(
            work / ".groth16-workdir.json",
            {
                "schema": "zkc.groth16-workdir/1",
                "mode": args.mode,
                "circomBinary": binary,
                "circom": compiler,
                "circomlib": library,
                "workers": args.workers,
            },
        )
        env = dict(
            os.environ, PYTHONDONTWRITEBYTECODE="1", FIXTURE_WORKERS=str(args.workers)
        )
        cache = (args.npm_cache or work / ".npm-cache").expanduser().resolve()
        npm = [
            "npm",
            "ci",
            "--ignore-scripts",
            "--no-audit",
            "--no-fund",
            "--cache",
            cache,
        ]
        if args.offline:
            npm.append("--offline")
        command(npm, cwd=work, env=env)
        import_artifacts(args, work)
        manifest = read_json(SOURCE / "evidence/artifact-manifest.json")["files"]
        if args.mode == "validate":
            check_files(work, manifest)
        elif args.mode == "reuse-setup":
            check_files(
                work,
                {
                    name: value
                    for name, value in manifest.items()
                    if name.startswith("artifacts/setup/")
                },
            )
        if args.mode != "validate":
            build = [sys.executable, "scripts/build.py"]
            if args.mode == "reuse-setup":
                build.append("--reuse-setup")
            command(build, cwd=work, env=env)
        command([sys.executable, "scripts/validate.py"], cwd=work, env=env)
        command([sys.executable, "scripts/record_metadata.py"], cwd=work, env=env)
        write_json(work / "source-manifest.json", before)
        print(f"Validated fixture-only result: {work / 'RESULTS.json'}")
    except BaseException as error:
        write_json(
            work / "RESULTS.json",
            {"status": "failed", "mode": args.mode, "error": str(error)},
        )
        raise
    finally:
        if source_snapshot() != before:
            write_json(
                work / "RESULTS.json",
                {"status": "failed", "error": "Maintained source files changed"},
            )
            raise RuntimeError("Maintained source files changed during reproduction")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, RuntimeError, subprocess.CalledProcessError, OSError) as error:
        print(f"Reproduction failed: {error}", file=sys.stderr)
        sys.exit(1)
