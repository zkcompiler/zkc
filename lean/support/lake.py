"""Reaching Lake, for the drivers that check this library from outside it.

The Lean library checks what is inside its own environment: `DeclarationAudit`
walks the declarations and judges their axioms, dependencies and ownership.
What it cannot judge is the build around it -- whether the library builds from
nothing, whether its public foundation stands without external packages,
whether an outside consumer can depend on it through a real Lake path. Those
are answered by running `lake` and watching, which is why there are drivers
here at all.

Every one of them had written this layer again. `sha` was three identical
copies, the toolchain version was captured three ways, and the same missing
executable ended four different ways -- `SystemExit`, two spellings of
`ValueError`, and `parser.error` -- so what happened when Lake was absent
depended on which driver you ran.
"""

import hashlib
import shutil
import subprocess


class Unavailable(Exception):
    """The selected Lake executable is not on this machine."""


def resolve(name="lake"):
    """The Lake executable a driver was told to use, or a failure saying so.

    One exception for every driver: a machine without Lake is the same
    condition wherever it is met, and a caller that wants to exit rather than
    raise can say so itself.
    """
    found = shutil.which(name)
    if found is None:
        raise Unavailable(f"selected Lake executable is unavailable: {name}")
    return found


def sha(path):
    """The digest of a file, for evidence that names what it read."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def toolchain(lake):
    """The Lean version behind this Lake, recorded beside every result.

    A check of a build is worth nothing without saying which toolchain built
    it, and these drivers each run against whichever one is installed.
    """
    return subprocess.run([lake, "env", "lean", "--version"],
                          capture_output=True, text=True, check=True).stdout.strip()


def build(lake, cwd, log, env=None):
    """A build with no prior objects, with its output kept.

    `--no-cache` is the point: these drivers ask whether something builds, and
    a cache would answer for a previous build instead. The log is kept because
    a failure here is read afterwards rather than watched.
    """
    with open(log, "w") as stream:
        return subprocess.run([lake, "--no-cache", "build"], cwd=cwd, env=env,
                              stdout=stream, stderr=subprocess.STDOUT)
