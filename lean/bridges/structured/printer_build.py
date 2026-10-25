"""Let Lake cache printer elaboration, never theorem or assurance results.

The scratch package has one path dependency on the existing main package. Its
manifest mirrors that package's pinned dependencies; it never runs lake update.
Ordinary legacy imports deliberately retain Lean's complete import dependency
trace, including private proof and metaprogram artifacts. Lake replays the
printer's messages on a hit. The resulting text is still an untrusted candidate
for the existing generated-source comparison and kernel admission.
"""

from contextlib import contextmanager
import fcntl
import hashlib
import json
import re

from bridges.common.lean_render import ROOT, CheckFailed

LEAN = ROOT / "lean"
BEGIN = "ZKC_BODY_OUTPUT_BEGIN"
END = "ZKC_BODY_OUTPUT_END"


def write_changed(path, text):
    if not path.is_file() or path.read_text(encoding="utf-8") != text:
        path.write_text(text, encoding="utf-8")


@contextmanager
def workspace(data):
    # A separate printer per data module avoids evicting another subject's
    # output. Synchronize only writers to this scratch directory.
    key = hashlib.sha256(data.encode()).hexdigest()
    directory = LEAN / ".lake/body-printers" / key
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        manifest = json.loads((LEAN / "lake-manifest.json").read_text())
        dependencies = str((LEAN / manifest["packagesDir"]).resolve())
        manifest.update(name="zkc_body_printer", packagesDir=dependencies)
        manifest["packages"].insert(0, dict(type="path", name="zkc", dir=str(LEAN),
                                          inherited=False, configFile="lakefile.toml",
                                          manifestFile="lake-manifest.json"))
        write_changed(directory / "lake-manifest.json", json.dumps(manifest, indent=2) + "\n")
        write_changed(directory / "lean-toolchain", (LEAN / "lean-toolchain").read_text())
        write_changed(directory / "lakefile.toml",
                      'name = "zkc_body_printer"\npackagesDir = ' + json.dumps(dependencies) + '\n'
                      '[[require]]\nname = "zkc"\npath = ' + json.dumps(str(LEAN)) + '\n'
                      '[[lean_lib]]\nname = "Inventory"\nallowNonModules = true\n'
                      '[[lean_lib]]\nname = "Bodies"\nallowNonModules = true\n')
        yield directory


def messages(output, module=None):
    """Select the framed printer output from fresh Lean or replayed Lake logs."""
    if module:
        output = re.sub(rf"^info: {re.escape(module)}\.lean:\d+:\d+: ?", "", output, flags=re.M)
    lines = output.splitlines()
    if lines.count(BEGIN) != 1 or lines.count(END) != 1 or lines.index(BEGIN) >= lines.index(END):
        raise CheckFailed("body printer output is missing its unique message frame")
    return "\n".join(lines[lines.index(BEGIN) + 1:lines.index(END)]) + "\n"


def elaborate(runner, directory, module, source, data, lake):
    # Lean normalizes text line endings in build traces. Keep the source's raw
    # byte identity explicit as well, as the surrounding source pipeline does.
    data_path = LEAN.joinpath(*data.split(".")).with_suffix(".lean")
    raw = hashlib.sha256(data_path.read_bytes()).hexdigest()
    write_changed(directory / f"{module}.lean", f"-- snapshot source sha256: {raw}\n" + source)
    result = runner.run([lake, "build", module], cwd=directory, expect=None,
                        name=f"bodies:{module}.lean")
    if result.returncode != 0:
        raise CheckFailed(f"building body printer {module} failed:\n{result.stdout}{result.stderr}")
    return messages(result.stdout, module)
