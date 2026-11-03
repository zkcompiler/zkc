"""The source-format selection of every compiler invocation the Lean bridges make.

Every authored source package states its grammar, `"zkc"` or `"zkc-layout"`, in
its `zkc.toml`, and the compiler requires that selection as `--source-format`
with every explicit module map. The bridges never assume a grammar and never
read a manifest's selection themselves: the SDK's manifest reader owns that
rule. A package's selection is the `source_format` its project inspection
(`zkc inspect --view=project`) reports, after the SDK has refused a missing,
unknown or mixed selection anywhere in the package's closure, dependency-only
manifests included.

A project-backed invocation takes the selection of its root manifest
(`of_project`). For an explicit module map, a source belongs to the packages
that list it in the project graphs of the package manifests of its enclosing
directories, and takes their selection; a refused graph refuses the source.
Only a fixture source that no package lists takes the format declared for its
directory in `fixture-formats.toml`. The sources of one invocation must agree.
An undeclared source and a mixed invocation refuse before the compiler runs.
Nothing here reads source text to infer a grammar.

The SDK executable is the native build's `zkc` (`ZKC_NATIVE_BIN`). Its project
inspection reads only the project and its settings, so it needs no compiler.
Without the SDK a package's selection refuses rather than falling back to
another reading of its manifest.
"""

from functools import lru_cache
import json
from pathlib import Path
import subprocess
import sys
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
def _graph(manifest):
    """The SDK's project graph of a package manifest; the SDK's refusal code refuses."""
    # Only the package route runs the SDK, so only it resolves the SDK executable.
    if str(ROOT / "common/tests/support") not in sys.path:
        sys.path.append(str(ROOT / "common/tests/support"))
    from toolchain import Missing, Toolchain
    try:
        command = [Toolchain().runtime, "--json", "inspect", "--view=project", f"--project={manifest}"]
    except Missing as error:
        raise Refused(f"{manifest}: the SDK's project inspection selects its source format: {error}") from None
    result = subprocess.run(command, capture_output=True, text=True, timeout=120)
    try:
        report = json.loads(result.stdout)
    except json.JSONDecodeError:
        raise Refused(f"{manifest}: the SDK's project inspection failed: {result.stderr.strip()}") from None
    require(isinstance(report, dict) and report.get("format") == "zkc.tool-inspection/0",
            f"{manifest}: unexpected SDK inspection report")
    require(report.get("status") == "inspected",
            f"{manifest}: the SDK refuses the package: {report.get('code')}")
    graph = report.get("project_graph")
    require(isinstance(graph, dict) and graph.get("format") == "zkc.project-graph/0"
            and isinstance(graph.get("packages"), list), f"{manifest}: unexpected SDK project graph")
    return graph


def _package_format(manifest, package):
    """The selection the SDK reports for one package of a project graph."""
    require(isinstance(package, dict) and "source_format" in package,
            f"{manifest}: the SDK's project graph reports no source_format; rebuild the SDK")
    return selected(package["source_format"], f"{manifest}: SDK project graph")


def of_project(manifest):
    """The selection of a project-backed invocation: its root manifest's, as the SDK reports it."""
    manifest = Path(manifest).resolve()
    graph = _graph(manifest)
    roots = [package for package in graph["packages"]
             if isinstance(package, dict) and Path(package.get("manifest", "")).resolve() == manifest]
    require(len(roots) == 1, f"{manifest}: the SDK's project graph has no root package")
    return _package_format(manifest, roots[0])


@lru_cache(maxsize=1)
def _declarations():
    with DECLARATIONS.open("rb") as stream:
        data = tomllib.load(stream)
    require(set(data) == {"directories"}, f"{DECLARATIONS}: expected only a directories table")
    return {(ROOT / directory).resolve(): selected(value, f"{DECLARATIONS}: {directory}")
            for directory, value in data["directories"].items()}


def of_source(path, *, root=ROOT, declarations=None):
    """The format of one module source.

    The packages that list the source, in the SDK's project graphs of the
    package manifests of its enclosing directories within `root`, decide; they
    must agree. A source no package lists takes its nearest declared fixture
    directory's format.
    """
    root = Path(root).resolve()
    source = (root / path).resolve()
    require(source.is_relative_to(root), f"{path}: source outside {root}")
    owners = set()
    for directory in source.parents:
        manifest = directory / "zkc.toml"
        if manifest.is_file():
            for package in _graph(manifest)["packages"]:
                modules = package.get("modules", {}) if isinstance(package, dict) else {}
                if any(Path(listed).resolve() == source for listed in modules.values()):
                    owners.add(_package_format(manifest, package))
        if directory == root:
            break
    if owners:
        require(len(owners) == 1, f"{path}: its packages state different source formats")
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
