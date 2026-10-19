"""Read and validate subject manifests (`lean/subjects/<name>.toml`).

A manifest names everything the subject pipeline needs about one subject: its
sources, its Entries, which profiles apply, which files the pipeline generates
for it, and the data that later stages consume (normal-form request, family,
claims, requested assumptions, mutation kinds). The schema is
`zkc.subject/0`; `lean/subjects/README.md` documents it. Unknown tables and
fields are refused, so a misspelt field never silently changes what is checked.

The loader only reads and validates. It resolves paths against the repository
root and project manifests through the test projects' resolver; it runs
nothing.
"""

from dataclasses import dataclass, field
from pathlib import Path
import sys
import tomllib

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import NAMESPACE, ROOT, Refused, require  # noqa: E402

sys.path.append(str(ROOT / "common/tests/support"))
from project import project_inputs  # noqa: E402

SCHEMA = "zkc.subject/0"
SUBJECTS = ROOT / "lean/subjects"

STRING, BOOLEAN, STRINGS, TABLE, INTEGER = "string", "boolean", "strings", "table", "integer"


def _kind(value):
    if isinstance(value, bool):
        return BOOLEAN
    if isinstance(value, str):
        return STRING
    if isinstance(value, int):
        return INTEGER
    if isinstance(value, list) and all(isinstance(item, str) for item in value):
        return STRINGS
    if isinstance(value, dict):
        return TABLE
    return None


# Each table's fields and their kinds. A field whose kind is a set accepts any
# of its kinds; a table-valued field is checked by its own entry below.
FIELDS = {
    "": {"schema": STRING, "name": STRING},
    "source": {"modules": TABLE, "project": STRING, "compiler_options": STRINGS},
    "entries": {"proof": STRING, "interactive": STRING, "instantiation": STRING},
    "profiles": {"structured": BOOLEAN, "construction": BOOLEAN, "executable": BOOLEAN, "scalar": BOOLEAN},
    "generated": {"data": STRING, "bodies": STRING, "participant": STRING, "glue": STRING,
                  "program": STRING, "facts": STRING, "interactive_data": STRING,
                  "interactive_bodies": STRING, "interactive_views": STRING,
                  "interactive_export": STRING, "interactive_source": STRING,
                  "original_export": STRING, "artifacts": STRING, "claims": STRING},
    "normal_forms": {"request": STRING},
    "family": {"module": STRING, "instance": STRING, "kind": STRING, "construction": STRING},
    "claims": {"endpoint": STRING, "properties": STRINGS, "statement": STRING, "regime": STRING,
               "namespace": STRING, "contract": STRING, "artifacts": STRING, "application": STRING},
    "assumptions": {"requested": STRINGS},
    "mutations": {"kinds": STRINGS},
    "executable": {"threshold": {STRING, INTEGER}, "public": STRING, "witness": STRING, "variants": TABLE,
                   "exact": TABLE, "charge": STRING, "charge_arguments": STRINGS, "completeness_module": STRING,
                   "namespace": STRING},
    # Optional extensions (lean/subjects/README.md).
    "construction": {"admission": STRING, "views": STRING, "inputs": STRING, "names": STRINGS,
                     "model": STRING, "model_imports": STRINGS, "rule": STRING, "doc": STRING,
                     "omit": STRINGS},
    "bodies": {"entry": STRING, "interactive_entry": STRING, "closed": BOOLEAN},
    "interactive": {"views_doc": STRING},
    "receipt": {"theorem": STRING, "security_module": STRING, "completeness_module": STRING,
                "chain": STRINGS, "used": STRINGS, "unused": STRINGS},
    "scalar": {"contract": STRING, "namespace": STRING, "module": STRING, "binders": STRING,
               "arguments": STRING, "inputs": TABLE, "unfold": STRINGS, "properties": TABLE,
               "group": BOOLEAN, "composed": BOOLEAN},
}
REQUIRED = {"": ("schema", "name")}
CHOICES = {
    ("family", "kind"): ("sigma", "certificate", "upstream"),
    ("claims", "endpoint"): ("ideal-meaning", "executable-bytes"),
    ("claims", "statement"): ("fixed", "adaptive"),
    ("construction", "admission"): ("views", "external"),
    ("construction", "inputs"): ("values", "payloads"),
    ("construction", "rule"): ("compiled", "construction"),
}


def _validate(data, path):
    tables = {name: value for name, value in data.items() if isinstance(value, dict)}
    top = {name: value for name, value in data.items() if not isinstance(value, dict)}
    for table, values in [("", top), *tables.items()]:
        require(table in FIELDS, f"{path}: unknown table [{table}]")
        allowed = FIELDS[table]
        for key, value in values.items():
            require(key in allowed, f"{path}: unknown field {table + '.' if table else ''}{key}")
            expected = allowed[key]
            expected = expected if isinstance(expected, set) else {expected}
            require(_kind(value) in expected, f"{path}: {table}.{key} must be {' or '.join(sorted(expected))}")
            choices = CHOICES.get((table, key))
            require(choices is None or value in choices, f"{path}: {table}.{key} must be one of {choices}")
        for key in REQUIRED.get(table, ()):
            require(key in values, f"{path}: missing field {key}")
    require(data["schema"] == SCHEMA, f"{path}: schema must be {SCHEMA}")


@dataclass
class Subject:
    """One validated manifest with its paths resolved."""

    path: Path
    data: dict
    modules: dict = field(default_factory=dict)
    assets: dict = field(default_factory=dict)

    @property
    def name(self):
        return self.data["name"]

    def table(self, name):
        return self.data.get(name, {})

    def get(self, table, key, default=None):
        return self.table(table).get(key, default)

    def profile(self, name):
        return bool(self.get("profiles", name, False))

    def generated(self, key):
        value = self.get("generated", key)
        return None if value is None else ROOT / value

    def module_name(self, key):
        """The Lean module a generated file defines, from its path under `lean/`."""
        path = self.generated(key)
        if path is None:
            return None
        relative = path.relative_to(ROOT / "lean").with_suffix("")
        return ".".join(relative.parts)

    def module_arguments(self):
        return ([f"--module={name}={source.relative_to(ROOT)}" for name, source in sorted(self.modules.items())]
                + [f"--asset={name}={kind}={source.relative_to(ROOT)}"
                   for name, (kind, source) in sorted(self.assets.items())])

    @property
    def compiler_options(self):
        return list(self.get("source", "compiler_options", []))

    @property
    def project(self):
        value = self.get("source", "project")
        return None if value is None else ROOT / value

    def inputs(self, entry, kind):
        """The runtime input file of an Entry: explicit, or the project's convention."""
        explicit = self.get("executable", kind)
        if explicit is not None:
            return ROOT / explicit
        require(self.project is not None, f"{self.name}: executable inputs need a project or an explicit path")
        path = self.project / "inputs" / entry.replace("::", ".") / f"{kind}.json"
        return path if path.exists() else None


def load(path):
    path = Path(path)
    with path.open("rb") as stream:
        data = tomllib.load(stream)
    _validate(data, path.relative_to(ROOT) if path.is_relative_to(ROOT) else path)
    subject = Subject(path, data)
    require(path.stem == subject.name, f"{path}: the file name must be the subject name")
    project = subject.project
    if project is not None:
        modules, assets = project_inputs(project / "zkc.toml")
        subject.modules.update(modules)
        subject.assets.update(assets)
    for name, source in subject.get("source", "modules", {}).items():
        require(isinstance(source, str), f"{path}: source.modules.{name} must be a path")
        subject.modules[name] = (ROOT / source).resolve()
    for name, source in subject.modules.items():
        require(source.is_file(), f"{path}: module {name} does not exist: {source}")
    for key, value in subject.table("generated").items():
        require(not Path(value).is_absolute() and ".." not in Path(value).parts,
                f"{path}: generated.{key} must be a repository path")
    for key in ("glue", "data", "participant", "program", "facts", "bodies", "interactive_data",
                "interactive_bodies", "interactive_views"):
        module = subject.module_name(key)
        require(module is None or __import__("re").fullmatch(NAMESPACE, module) is not None,
                f"{path}: generated.{key} is not a Lean module path")
    if subject.profile("construction"):
        require(subject.get("entries", "proof") and subject.generated("participant") and subject.generated("data"),
                f"{path}: the construction profile needs entries.proof, generated.data and generated.participant")
    if subject.profile("executable"):
        require(subject.profile("construction") and subject.generated("program"),
                f"{path}: the executable profile needs the construction profile and generated.program")
    return subject


def load_all(names=None):
    """Every manifest in `lean/subjects`, or the named ones, sorted by name."""
    paths = sorted(SUBJECTS.glob("*.toml"))
    subjects = {}
    for path in paths:
        if path.name.endswith(".normal-forms.toml"):
            continue
        subject = load(path)
        require(subject.name not in subjects, f"duplicate subject {subject.name}")
        subjects[subject.name] = subject
    if names:
        missing = [name for name in names if name not in subjects]
        if missing:
            raise Refused(f"unknown subjects: {', '.join(missing)}")
        return [subjects[name] for name in names]
    return [subjects[name] for name in sorted(subjects)]
