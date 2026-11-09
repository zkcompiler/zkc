"""Standalone Lean elaboration using Lake's ModuleSetup and existing artifacts.

Use ``command(package, *lean_arguments)`` wherever a driver schedules Lean.
The returned process owns setup as well as elaboration, so the caller's timeout,
streams, environment and process-group cancellation cover both. Dependencies
must already be built: Lake's --no-build refuses stale or missing prerequisites.

Explicit LEAN_PATH entries are checked-artifact overlays, in their given order.
Resolve them by full module name, rather than Lean's first-component search.
There is no raw invocation fallback and no copied source compatibility tree.
"""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def command(package, *arguments, lake="lake"):
    """Return a subprocess command accepting ordinary Lean CLI arguments."""
    return [sys.executable, str(Path(__file__).resolve()),
            "--package", str(Path(package).resolve()), "--lake", str(lake),
            "--", *map(str, arguments)]


def _artifacts(roots):
    """Keep each winning module's complete artifact group from a single root."""
    result = {}
    for root in roots:
        # Lake lists optional library directories before they have any objects.
        # Missing imports still fail in setup/elaboration; unused roots need
        # no directory and do not authorize creating or rebuilding one.
        if not root.is_dir():
            continue
        visited = set()
        for parent, directories, files in os.walk(root, followlinks=True, onerror=_walk_error):
            identity = Path(parent).resolve()
            if identity in visited:
                directories[:] = []
                continue
            visited.add(identity)
            directories.sort()
            for filename in sorted(files):
                if not filename.endswith(".olean"):
                    continue
                path = Path(parent) / filename
                if not path.is_file():
                    continue
                module = ".".join(path.relative_to(root).with_suffix("").parts)
                if module in result:
                    continue
                stem = path.with_suffix("")
                parts = [str(path)]
                server, private = Path(str(stem) + ".olean.server"), Path(str(stem) + ".olean.private")
                if server.is_file():
                    parts.append(str(server))
                    if private.is_file():
                        parts.append(str(private))
                elif private.is_file():
                    raise ValueError(f"private Lean artifact has no server artifact: {path}")
                signature, ir = Path(str(stem) + ".ir.sig"), Path(str(stem) + ".ir")
                # Non-module files have one .ir; module files split signature/body.
                ir_parts = [str(signature)] if signature.is_file() else []
                if ir.is_file():
                    ir_parts.append(str(ir))
                result[module] = [parts, ir_parts]
    return result


def _walk_error(error):
    raise error


def _source(arguments):
    """Find the source before --run's uninterpreted application arguments."""
    if "--run" in arguments:
        index = arguments.index("--run") + 1
        if index >= len(arguments):
            raise ValueError("--run requires a Lean source file")
        return Path(arguments[index]).resolve()
    skip = False
    for argument in arguments:
        if skip:
            skip = False
        elif argument in ("-o", "-i", "-c", "-b", "-R", "--root"):
            skip = True
        elif not argument.startswith("-") and argument.endswith(".lean"):
            return Path(argument).resolve()
    raise ValueError("standalone Lean invocation requires a .lean source file")


def elaborate(package, arguments, lake):
    # Import only inside the worker; command construction needs no Lean process.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from support.lean_headers import HeaderParser

    source = _source(arguments)
    options = arguments[:arguments.index("--run")] if "--run" in arguments else arguments
    if any(arg == "--setup" or arg.startswith("--setup=") for arg in options):
        raise ValueError("ModuleSetup is owned by support.invocation")
    environment = dict(os.environ)
    # Always select the owning package's pin, even when launched from /tmp.
    environment["ELAN_TOOLCHAIN"] = (package / "lean-toolchain").read_text().strip()
    overlays = [Path(entry).resolve() for entry in environment.get("LEAN_PATH", "").split(os.pathsep) if entry]
    overlay_arts = _artifacts(overlays) if overlays else {}
    header = None
    if overlay_arts:
        with HeaderParser(lake=lake) as parser:
            details = parser.details(source.read_text(), source)
            header = {"isModule": parser.is_module(source.read_text(), source), "imports": [
                {"module": item["module"], "isExported": item["public"],
                 "isMeta": item["meta"], "importAll": item["all"]}
                for item in details if item["module"] not in overlay_arts]}
    setup_command = [lake, "--no-build", "setup-file", str(source)]
    if header is not None:
        setup_command.append(json.dumps(header))
    setup_result = subprocess.run(setup_command, cwd=package, env=environment,
                                  stdout=subprocess.PIPE, text=True)
    if setup_result.returncode:
        return setup_result.returncode
    setup = json.loads(setup_result.stdout)
    # ModuleSetup options otherwise override -D arguments in Lean 4.35. Keep
    # explicit caller controls authoritative (notably the audit's sorry cases).
    option_value = False
    for argument in options:
        if option_value or (argument.startswith("-D") and len(argument) > 2):
            assignment = argument if option_value else argument[2:]
            setup["options"].pop(assignment.partition("=")[0], None)
            option_value = False
        elif argument == "-D":
            option_value = True
    if overlay_arts:
        search = subprocess.check_output([lake, "env", "printenv", "LEAN_PATH"],
                                         cwd=package, env=environment, text=True).strip()
        roots = [(package / entry).resolve() for entry in search.split(os.pathsep) if entry]
        # Include transitive dependencies of generated modules too. An overlay
        # may import a second Zkc package absent from the top-level source header.
        setup["importArts"] = _artifacts(roots) | setup["importArts"] | overlay_arts
    environment = json.loads(subprocess.check_output(
        [lake, "env", sys.executable, "-c", "import json, os; print(json.dumps(dict(os.environ)))"],
        cwd=package, env=environment, text=True))
    lean = shutil.which("lean", path=environment["PATH"])
    if lean is None:
        raise ValueError("the selected Lake environment has no Lean executable")
    # Replace the worker so ordinary subprocess timeouts kill Lean itself. The
    # anonymous setup file survives exec through its descriptor and disappears
    # on process exit, including cancellation. No scratch source tree is needed.
    with tempfile.TemporaryFile(mode="w+") as stream:
        json.dump(setup, stream)
        stream.flush()
        stream.seek(0)
        os.set_inheritable(stream.fileno(), True)
        path = f"/dev/fd/{stream.fileno()}"
        os.execvpe(lean, [lean, "--setup", path, *arguments], environment)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path, required=True)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    arguments = args.arguments[1:] if args.arguments[:1] == ["--"] else args.arguments
    try:
        return elaborate(args.package, arguments, args.lake)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"error: standalone Lean setup failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
