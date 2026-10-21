"""Conservative path ownership for migration and evaluation inventories.

Dependency layers come from the enforced declaration policy. Path ownership
does not decide what a changed theorem proves or whether an edit is a domain
installation. Ambiguous subject and adapter edits remain explicitly unresolved.
"""

from dataclasses import asdict, dataclass
from pathlib import PurePosixPath

from support.dependencies import POLICY, layer


@dataclass(frozen=True)
class Responsibility:
    responsibility: str | None
    edit_candidates: tuple[str, ...]
    reason: str
    module: str | None = None
    dependency_layer: str | None = None

    def record(self):
        return asdict(self)


def relative_path(value):
    """Require a canonical repository-relative path, including for deleted files."""
    if not isinstance(value, str) or not value or "\\" in value or "\0" in value:
        raise ValueError("expected a canonical repository-relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in ("", ".", "..") for part in value.split("/")):
        raise ValueError("expected a canonical repository-relative path")
    return path


def module_name(path):
    """Recognize repository Lean roots, without guessing ownership of integrations."""
    if path.suffix != ".lean":
        return None
    parts = path.parts
    if parts[:3] in (("lean", "integrations", "arklib"), ("lean", "integrations", "clean")):
        parts = parts[3:]
    elif parts[:2] == ("lean", "security"):
        parts = parts[2:]
    elif parts[:1] == ("lean",) and len(parts) > 1 and parts[1] != "integrations":
        parts = parts[1:]
    else:
        return None
    return ".".join(PurePosixPath(*parts).with_suffix("").parts)


def classify(value, policy=POLICY):
    path = relative_path(value)
    parts = path.parts
    if parts[:2] == ("docs", "private"):
        return Responsibility(None, (), "sealed evaluation path; excluded from inventory")
    if parts[:2] in (("lean", "checks"), ("lean", "support"), ("lean", "bridges"), ("lean", "clients")):
        return Responsibility("support-infrastructure", ("X",), "formal checking, generation or downstream-client tooling")
    module = module_name(path)
    if module is not None:
        owner = layer(module, policy)
        rules = {
            "core": ("language-and-compiler", ("X",), "semantic or admission foundation"),
            "probability": ("general-methods", ("S",), "probability support; deterministic splits need declaration review"),
            "families": ("family-packages", ("M", "S"), "family mathematics; reuse context determines the edit category"),
            "security-families": ("family-packages", ("M", "S"), "security family mathematics; reuse context determines the edit category"),
            "security": ("general-methods", ("S",), "shared security contracts and methods"),
            "adapters": (None, ("M", "S"), "adapter may supply family mathematics or general transport"),
            "subjects": (None, ("M", "I"), "subject mixes mathematics and instantiation; declaration review required"),
            "security-subjects": (None, ("M", "I"), "subject mixes mathematics and instantiation; declaration review required"),
            "optional-subjects": (None, ("M", "I"), "subject mixes mathematics and instantiation; declaration review required"),
            "clean-subjects": (None, ("M", "I"), "relation subject requires declaration review"),
            "clean": ("general-methods", ("S",), "shared relation adapter"),
            "tests": ("support-infrastructure", ("X",), "test infrastructure is not theorem evidence"),
            "tools": ("support-infrastructure", ("X",), "generation and audit infrastructure"),
        }
        if any(module == prefix or module.startswith(prefix + ".")
               for prefix in ("ZkcSecurity.Endpoint", "ZkcSecurity.Claims")):
            result = ("language-and-compiler", ("X",), "fixed claim interpretation and endpoint infrastructure")
        else:
            result = rules.get(owner, (None, (), "Lean module has no reviewed responsibility rule"))
        return Responsibility(*result, module=module, dependency_layer=owner)
    if parts[0] == "compiler":
        return Responsibility("language-and-compiler", ("X",),
                              "compiler change; a domain-only edit requires a reviewed semantic classification")
    if parts[0] == "crates":
        return Responsibility("language-and-compiler", ("X",),
                              "runtime or tool change; directory placement alone never establishes a domain-only edit")
    if parts[:2] == ("examples", "projects") and path.suffix == ".zkc":
        return Responsibility("protocol-authoring", ("P",), "authored protocol project source")
    if parts[0] == "libraries" and path.suffix == ".zkc":
        return Responsibility("protocol-authoring", ("P", "S"), "protocol source may be authored or shared-library code")
    if parts[0] in ("scripts", "nix") or parts[:2] == ("common", "tests"):
        return Responsibility("support-infrastructure", ("X",), "build or test infrastructure")
    if parts[0] == "lean" and path.name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "reproduce.py"):
        return Responsibility("support-infrastructure", ("X",), "formal package or reproducibility configuration")
    return Responsibility(None, (), "path has no reviewed responsibility rule")
