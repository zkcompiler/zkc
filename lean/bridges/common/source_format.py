"""The source-format selection of every compiler invocation the Lean bridges make.

Every authored source package states its grammar in the required top-level
`source-format` key of its `zkc.toml`, `"zkc"` or `"zkc-layout"`, and the
compiler requires that selection as `--source-format` with every explicit
module map. The bridges never assume a grammar. The format of a module source
is the `source-format` of the package manifests that list it, found among the
manifests of its enclosing directories; a fixture source that no package lists
takes the format declared for its directory in `fixture-formats.toml`. The
sources of one invocation must agree. A missing or unknown selection, an
undeclared source and a mixed closure refuse before the compiler runs. Nothing
here reads source text to infer a grammar.
"""

from functools import lru_cache
from pathlib import Path
import tomllib

from bridges.common.lean_render import ROOT, Refused, require

FORMATS = ("zkc", "zkc-layout")
OPTION = "--source-format="
DECLARATIONS = Path(__file__).with_name("fixture-formats.toml")


def selected(value, origin):
    """A known format, or a refusal naming where the selection was read."""
    require(value is not None, f"{origin}: missing source-format")
    require(value in FORMATS, f"{origin}: unknown source-format {value!r}")
    return value


@lru_cache(maxsize=None)
def _manifest(path):
    with Path(path).open("rb") as stream:
        return tomllib.load(stream)


def of_manifest(path):
    """The `source-format` a package manifest states."""
    return selected(_manifest(Path(path).resolve()).get("source-format"), path)


@lru_cache(maxsize=1)
def _declarations():
    with DECLARATIONS.open("rb") as stream:
        data = tomllib.load(stream)
    require(set(data) == {"directories"}, f"{DECLARATIONS}: expected only a directories table")
    return {(ROOT / directory).resolve(): selected(value, f"{DECLARATIONS}: {directory}")
            for directory, value in data["directories"].items()}


def of_source(path, *, root=ROOT, declarations=None):
    """The format of one module source.

    The package manifests within `root` that list the source decide; they must
    agree. A source no manifest lists takes its nearest declared fixture
    directory's format.
    """
    root = Path(root).resolve()
    source = (root / path).resolve()
    require(source.is_relative_to(root), f"{path}: source outside {root}")
    owners = set()
    for directory in source.parents:
        manifest = directory / "zkc.toml"
        if manifest.is_file() and any((directory / listed).resolve() == source
                                      for listed in _manifest(manifest).get("modules", {}).values()):
            owners.add(of_manifest(manifest))
        if directory == root:
            break
    if owners:
        require(len(owners) == 1, f"{path}: its package manifests state different source formats")
        return owners.pop()
    declared = [(directory, value) for directory, value in
                (_declarations() if declarations is None else declarations).items()
                if source.is_relative_to(directory)]
    require(bool(declared), f"{path}: no package manifest lists it and no fixture declaration selects its "
                            "source format")
    return max(declared, key=lambda item: len(item[0].parts))[1]


def of_sources(paths, **options):
    """The one format all module sources of an invocation share."""
    paths = list(paths)
    require(bool(paths), "an invocation without module sources selects no source format")
    formats = {of_source(path, **options) for path in paths}
    require(len(formats) == 1, f"mixed source formats {sorted(formats)} in one invocation")
    return formats.pop()


def option(paths, **options):
    """The compiler option selecting the format of these module sources."""
    return OPTION + of_sources(paths, **options)


def module_sources(arguments):
    """The source paths of `--module=NAME=PATH` arguments, relative to the repository root."""
    sources = []
    for argument in arguments:
        argument = str(argument)
        if argument.startswith("--module="):
            name, separator, path = argument.removeprefix("--module=").partition("=")
            require(bool(name) and separator == "=" and bool(path), f"malformed module argument {argument!r}")
            sources.append(ROOT / path)
    return sources


def option_for_arguments(arguments, **options):
    """The compiler option selecting the format of the modules these arguments name."""
    return option(module_sources(arguments), **options)


def with_option(arguments, selection=None, **options):
    """These compiler arguments, preceded by a format selection: the explicit
    `selection` when a caller states one, otherwise the format of the modules
    they name."""
    arguments = [str(argument) for argument in arguments]
    if selection is not None:
        return [OPTION + selected(selection, "explicit source-format selection"), *arguments]
    return [option_for_arguments(arguments, **options), *arguments]


def require_option(arguments):
    """Refuse an invocation without exactly one known source-format selection."""
    selections = [str(argument).removeprefix(OPTION) for argument in arguments
                  if str(argument).startswith(OPTION)]
    if len(selections) != 1:
        raise Refused("a compiler invocation requires exactly one --source-format selection")
    selected(selections[0], "--source-format")
    return selections[0]
