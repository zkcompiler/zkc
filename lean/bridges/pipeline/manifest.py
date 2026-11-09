"""Read and validate subject manifests (`lean/subjects/<name>.toml`).

A manifest names everything the subject pipeline needs about one subject: its
sources, its Entries, which profiles apply, which files the pipeline generates
for it, and physical generation/import configuration. Source spec/verify and
typed Lean exports alone select claim meanings and proof methods. The schema is
`zkc.subject/0`; `lean/subjects/README.md` documents it. Unknown tables and
fields are refused, so a misspelt field never silently changes what is checked.

Generated file paths select physical modules through the package inventory.
The namespaces table explicitly selects their declaration namespaces. Existing
namespace fields must agree, and external admission views carry their own
views_namespace independently of their import module.

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
from support.packages import PACKAGES, module_owner, module_path  # noqa: E402

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
    "generated": {"data": STRING, "bodies": STRING, "views": STRING, "participant": STRING, "pair": STRING, "glue": STRING,
                  "program": STRING, "facts": STRING, "interactive_data": STRING,
                  "interactive_bodies": STRING, "interactive_views": STRING,
                  "interactive_export": STRING, "interactive_source": STRING,
                  "original_source": STRING, "original_export": STRING, "artifacts": STRING, "claims": STRING, "lowering": STRING},
    "namespaces": {key: STRING for key in ("data", "bodies", "views", "participant", "pair", "glue",
                   "program", "facts", "interactive_data", "interactive_bodies", "interactive_views",
                   "artifacts", "claims", "lowering")},
    "source_views": {"selections": STRINGS},
    "lean": {"namespace": STRING, "imports": STRINGS, "library": STRING},
    "assumptions": {"requested": STRINGS},
    "mutations": {"kinds": STRINGS},
    "executable": {"module": STRING, "threshold": {STRING, INTEGER}, "public": STRING, "witness": STRING, "variants": TABLE,
                   "exact": TABLE, "charge": STRING, "charge_arguments": STRINGS, "completeness_module": STRING,
                   "namespace": STRING},
    # Optional extensions (lean/subjects/README.md).
    "construction": {"namespace": STRING, "connection": STRING, "admission": STRING, "views": STRING, "views_namespace": STRING, "inputs": STRING, "names": STRINGS,
                     "model": STRING, "model_imports": STRINGS, "rule": STRING, "doc": STRING,
                     "library": STRING, "library_module": STRING,
                     "omit": STRINGS},
    "bodies": {"entry": STRING, "interactive_entry": STRING, "closed": BOOLEAN, "owners": TABLE},
    "interactive": {"views_doc": STRING},
    "receipt": {"theorem": STRING, "security_module": STRING, "completeness_module": STRING,
                "chain": STRINGS, "used": STRINGS, "unused": STRINGS},
    "scalar": {"contract": STRING, "namespace": STRING, "module": STRING, "binders": STRING,
               "arguments": STRING, "inputs": TABLE, "unfold": STRINGS, "properties": TABLE,
               "group": BOOLEAN, "composed": BOOLEAN},
}
REQUIRED = {"": ("schema", "name")}
CHOICES = {
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
    owners = data.get("bodies", {}).get("owners", {})
    require(all(isinstance(owner, str) and isinstance(name, str) for owner, name in owners.items()),
            f"{path}: body owner aliases must map source owners to presentation names")
    require(len(set(owners.values())) == len(owners), f"{path}: repeated body presentation name")
    require(data.get("generated", {}).get("views") is None or data.get("generated", {}).get("bodies"),
            f"{path}: generated.views requires generated.bodies")
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
        return None if value is None else (ROOT / value).resolve()

    def generated_package(self, key):
        """Actual Lake provider, independent of declaration namespaces."""
        path = self.generated(key)
        if path is None:
            return None
        for directory, _ in PACKAGES.values():
            if path.is_relative_to(directory):
                module = ".".join(path.relative_to(directory).with_suffix("").parts)
                if module_path(module) == path:
                    return directory
        raise Refused(f"{self.name}: generated.{key} is not owned by a Lean package")

    def module_name(self, key):
        """The module path relative to its unique owning Lake package."""
        path = self.generated(key)
        if path is None:
            return None
        return ".".join(path.relative_to(self.generated_package(key)).with_suffix("").parts)

    def namespace(self, key):
        """The explicit declaration namespace of a generated Lean output."""
        return self.get("namespaces", key)

    @property
    def construction_namespace(self):
        """Declaration owner, independent of the generated metadata module."""
        return self.get("construction", "namespace", self.namespace("glue"))

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
        require(subject.generated(key).is_relative_to(ROOT),
                f"{path}: generated.{key} must resolve inside the repository")
    for key in ("glue", "data", "participant", "pair", "program", "facts", "bodies", "views", "interactive_data",
                "interactive_bodies", "interactive_views", "artifacts", "claims", "lowering"):
        module = subject.module_name(key)
        require(module is None or __import__("re").fullmatch(NAMESPACE, module) is not None,
                f"{path}: generated.{key} is not a Lean module path")
    lean_outputs = {key for key, value in subject.table("generated").items() if Path(value).suffix == ".lean"}
    require(set(subject.table("namespaces")) == lean_outputs,
            f"{path}: namespaces must name exactly the generated Lean outputs")
    for key, namespace in subject.table("namespaces").items():
        require(__import__("re").fullmatch(NAMESPACE, namespace) is not None,
                f"{path}: namespaces.{key} must be a Lean namespace")
    for key, table in (("glue", "construction"), ("facts", "executable"),
                       ("artifacts", "lean"), ("claims", "lean"), ("lowering", "lean")):
        require(key not in lean_outputs or not subject.get(table, "namespace") or
                subject.namespace(key) == subject.get(table, "namespace"),
                f"{path}: namespaces.{key} must agree with {table}.namespace")
    if subject.generated("views"):
        require(subject.get("construction", "admission") == "external" and
                subject.get("construction", "views") == subject.module_name("views"),
                f"{path}: generated.views must be the construction admission module")
        require(subject.get("construction", "views_namespace") == subject.namespace("views"),
                f"{path}: construction.views_namespace must agree with namespaces.views")
    views_namespace = subject.get("construction", "views_namespace")
    require(subject.get("construction", "admission") != "external" or
            (subject.get("construction", "views") and isinstance(views_namespace, str) and
             __import__("re").fullmatch(NAMESPACE, views_namespace) is not None),
            f"{path}: external admission requires construction.views and construction.views_namespace")
    paths = [subject.generated(key) for key in subject.table("generated")]
    require(len(paths) == len(set(paths)), f"{path}: generated output paths must be distinct")
    require(not (subject.generated("claims") and subject.profile("executable")
                 and subject.generated("artifacts")) or subject.generated("lowering"),
            f"{path}: executable claims require generated.lowering")
    require(not subject.generated("lowering") or
            (subject.generated("artifacts") and subject.profile("executable")),
            f"{path}: generated.lowering requires executable generated.artifacts")
    require(not subject.generated("pair") or subject.profile("construction"),
            f"{path}: generated.pair requires the construction profile")
    namespace = subject.get("lean", "namespace")
    require(namespace is None or __import__("re").fullmatch(NAMESPACE, namespace) is not None,
            f"{path}: lean.namespace must be a Lean namespace")
    for key in ("namespace", "connection", "library", "library_module"):
        value = subject.get("construction", key)
        require(value is None or __import__("re").fullmatch(NAMESPACE, value) is not None,
                f"{path}: construction.{key} must be a Lean name")
    connection_library = subject.get("construction", "library")
    connection_library_module = subject.get("construction", "library_module")
    require((connection_library is None) == (connection_library_module is None),
            f"{path}: construction.library and construction.library_module must be supplied together")
    require(connection_library is None or
            (subject.profile("construction") and subject.get("construction", "rule", "compiled") == "compiled"),
            f"{path}: construction.library requires the compiled construction profile")
    connection = subject.get("construction", "connection")
    require(not subject.generated("claims") or connection,
            f"{path}: generated.claims requires a maintained construction.connection module")
    generated_modules = {subject.module_name(key) for key, value in subject.table("generated").items()
                         if Path(value).suffix == ".lean"}
    require(not connection or connection not in generated_modules,
            f"{path}: construction.connection must differ from every generated module")
    for module in subject.get("lean", "imports", []):
        require(__import__("re").fullmatch(NAMESPACE, module) is not None,
                f"{path}: lean.imports must contain Lean module names")
    module_selections = [*subject.get("lean", "imports", []),
                         *subject.get("construction", "model_imports", [])]
    for table, key in (("construction", "connection"), ("construction", "views"),
                       ("construction", "library_module"), ("executable", "module"),
                       ("executable", "completeness_module"),
                       ("receipt", "security_module"), ("receipt", "completeness_module"),
                       ("scalar", "module")):
        if subject.get(table, key):
            module_selections.append(subject.get(table, key))
    for name, value in subject.get("scalar", "properties", {}).items():
        require(isinstance(value, dict), f"{path}: scalar.properties.{name} must be a table")
        if "module" in value:
            module_selections.append(value["module"])
    for module in module_selections:
        require(isinstance(module, str) and __import__("re").fullmatch(NAMESPACE, module) is not None,
                f"{path}: module selections must be Lean module names")
        try:
            module_owner(module)
        except ValueError as error:
            raise Refused(f"{path}: {error}") from error
    require(not subject.generated("lowering") or subject.get("executable", "module"),
            f"{path}: generated.lowering requires executable.module")
    require(not subject.get("executable", "charge") or subject.get("executable", "completeness_module"),
            f"{path}: executable.charge requires executable.completeness_module")
    library = subject.get("lean", "library")
    require(library is None or __import__("re").fullmatch(NAMESPACE, library) is not None,
            f"{path}: lean.library must be a Lean declaration name")
    require(not subject.generated("claims") or (namespace and subject.get("lean", "imports")),
            f"{path}: generated.claims requires lean.namespace and lean.imports")
    require(not subject.generated("claims") or subject.generated("artifacts") or library,
            f"{path}: source claims need generated.artifacts or an explicit typed lean.library")
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
        subject = load(path)
        require(subject.name not in subjects, f"duplicate subject {subject.name}")
        subjects[subject.name] = subject
    if names:
        missing = [name for name in names if name not in subjects]
        if missing:
            raise Refused(f"unknown subjects: {', '.join(missing)}")
        return [subjects[name] for name in names]
    return [subjects[name] for name in sorted(subjects)]
