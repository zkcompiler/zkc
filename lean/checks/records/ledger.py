"""The claims ledger: the theorems behind each published row of what is proved.

`lean/checks/claims.toml` holds, row by row, the "What is proved" table of
`lean/README.md`: the subject, the claim as published, its owning documents and
the theorems that carry it. `lean/checks/claims.lock.json` records each cited
theorem's package, module and statement hashes. A check fails when a cited
theorem is missing from the declaration records (a stale name), when its
statement hashes differ from the lock (the statement changed, so the row must be
reviewed and the lock rewritten), when it depends on an axiom outside the
allowed set, or when the rendered table differs from the generated region of a
document. Equal hashes are regression evidence, not semantic preservation: a
definition the statement mentions may still have changed.
"""

import json
from pathlib import Path
import re
import tomllib

from .declarations import forbidden_axioms
from support.packages import PACKAGES as SOURCE_PACKAGES

LEAN = Path(__file__).resolve().parents[2]
LEDGER = LEAN / "checks/claims.toml"
LOCK = LEAN / "checks/claims.lock.json"
LEDGER_SCHEMA = "zkc.claims/0"
LOCK_FORMAT = "zkc.claims-lock/0"
COMMAND = "lean/checks/check_records.py --write"


def load_ledger(path=LEDGER):
    ledger = tomllib.loads(Path(path).read_text())
    if ledger.get("schema") != LEDGER_SCHEMA:
        raise ValueError(f"{path}: expected schema {LEDGER_SCHEMA}")
    for index, row in enumerate(ledger.get("proved", [])):
        for field in ("subject", "result", "owners", "theorems"):
            if field not in row:
                raise ValueError(f"{path}: row {index + 1} has no {field}")
        if not row["theorems"]:
            raise ValueError(f"{path}: row {row['subject']!r} cites no theorem")
    return ledger


def load_lock(path=LOCK):
    if not Path(path).exists():
        return {"format": LOCK_FORMAT, "theorems": {}}
    lock = json.loads(Path(path).read_text())
    if lock.get("format") != LOCK_FORMAT:
        raise ValueError(f"{path}: expected format {LOCK_FORMAT}")
    return lock


def cited(ledger):
    """Every cited theorem, in first-citation order."""
    names = []
    for row in ledger.get("proved", []):
        names += [name for name in row["theorems"] if name not in names]
    return names


def check(ledger, lock, records):
    """Findings of the ledger against the records of the selected packages.

    A theorem whose locked package was not emitted is skipped and counted; a
    theorem that is neither emitted nor locked is a stale name.
    """
    findings, checked, skipped = [], [], []
    locked = lock.get("theorems", {})
    packages = records.packages()
    for name in cited(ledger):
        entry = locked.get(name)
        record = records.get(name)
        if record is None:
            if entry is not None and entry.get("package") not in packages:
                skipped.append(name)
            elif any(r["name"] == name for r in records.declarations):
                findings.append(f"{name} is private; cite a public theorem")
            else:
                findings.append(f"stale theorem name: {name} is not a declaration of "
                                f"{', '.join(sorted(packages))}")
            continue
        checked.append(name)
        if record["kind"] != "theorem":
            findings.append(f"{name} is a {record['kind']}, not a theorem")
        forbidden = forbidden_axioms(record)
        if forbidden:
            findings.append(f"unresolved: {name} depends on {', '.join(forbidden)}")
        if entry is None:
            findings.append(f"unlocked theorem: {name}; review its row and run {COMMAND}")
            continue
        for kind in ("structural", "explicit"):
            if entry.get(kind) != record["statement"][kind]:
                findings.append(f"statement changed: {name} ({kind} hash {entry.get(kind)} is now "
                                f"{record['statement'][kind]}); review its row and run {COMMAND}")
        if entry.get("package") != record["package"] or entry.get("module") != record["module"]:
            findings.append(f"moved theorem: {name} is now in {record['module']} ({record['package']}); "
                            f"run {COMMAND}")
    for name in sorted(set(locked) - set(cited(ledger))):
        findings.append(f"the lock names a theorem no row cites: {name}; run {COMMAND}")
    return findings, checked, skipped


def write_lock(ledger, lock, records):
    """The lock with the emitted theorems' current hashes; entries of packages
    that were not emitted are kept, entries no row cites are dropped."""
    locked = dict(lock.get("theorems", {}))
    names = cited(ledger)
    result = {}
    for name in names:
        record = records.get(name)
        if record is not None:
            result[name] = {"package": record["package"], "module": record["module"],
                            "structural": record["statement"]["structural"],
                            "explicit": record["statement"]["explicit"]}
        elif name in locked:
            result[name] = locked[name]
    return {"format": LOCK_FORMAT, "theorems": dict(sorted(result.items()))}


def render_proved(ledger):
    """The "What is proved" table."""
    lines = ["| Subject | Result | Theorems | Owner |", "|---|---|---|---|"]
    for row in ledger.get("proved", []):
        theorems = ", ".join(f"`{name}`" for name in row["theorems"])
        owners = ", ".join(f"[{text}]({link})" for text, link in row["owners"])
        result = " ".join(row["result"].split())
        lines.append(f"| {row['subject']} | {result} | {theorems} | {owners} |")
    return "\n".join(lines) + "\n"


def begin(region):
    return f"<!-- BEGIN GENERATED {region}: {COMMAND} -->"


def end(region):
    return f"<!-- END GENERATED {region} -->"


def region(text, name):
    """The content of a generated region, or None when the document has none."""
    start, stop = begin(name), end(name)
    if start not in text:
        return None
    head, rest = text.split(start, 1)
    if stop not in rest:
        raise ValueError(f"generated region {name} is not closed")
    return rest.split(stop, 1)[0].strip("\n") + "\n"


def replace_region(text, name, content):
    start, stop = begin(name), end(name)
    head, rest = text.split(start, 1)
    _, tail = rest.split(stop, 1)
    return f"{head}{start}\n{content.rstrip(chr(10))}\n{stop}{tail}"


# Documents whose prose cites Lean declarations by qualified name, and the
# package that owns each root namespace.
DOCUMENTS = ["docs/status.md", "lean/README.md", "lean/docs/**/*.md", "lean/security/README.md", "lean/integrations/*/README.md"]
ROOTS = {"Zkc": "main", "ZkcExamples": "main", "ZkcTools": "main", "Tests": "main", "PIR": "main",
         "ZkcSecurity": "security", "TestsSecurity": "security", "ZkcArkLib": "arklib", "TestsArkLib": "arklib", "ZkcClean": "clean", "TestsClean": "clean"}
PACKAGE_DIRECTORIES = {"security": LEAN / "security", "main": LEAN, "arklib": LEAN / "integrations/arklib", "clean": LEAN / "integrations/clean"}
QUALIFIED = re.compile(r"`((?:" + "|".join(ROOTS) + r")\.[A-Za-z0-9_.']+)`")


def namespace_packages(root):
    """Find full declared namespaces independently of renamed module roots.

    This supplies ownership for documentation of an unselected package. Actual
    declarations of selected packages must still be present in emitted records.
    A namespace shared across packages never hides a missing selected name.
    """
    owners = {}
    for package, directory in PACKAGE_DIRECTORIES.items():
        source = root / directory.relative_to(LEAN.parent)
        files = [path for family in SOURCE_PACKAGES[package][1]
                 for path in (source / family).rglob('*.lean')]
        for path in files:
            # Independent nested namespaces have no reliable module ownership;
            # only explicit qualified namespace declarations supply this hint.
            for namespace in re.findall(r'^namespace ([A-Za-z][A-Za-z0-9_\'.]*\.[A-Za-z0-9_\'.]+)\s*$',
                                        path.read_text(), re.MULTILINE):
                owners.setdefault(namespace, set()).add(package)
    return owners


def check_documents(records, root=LEAN.parent):
    """Qualified Lean names cited in prose must still exist: as a declaration,
    as a namespace of declarations, or as a module or module directory. Names
    of packages that were not emitted are skipped and counted. This catches
    renames, not semantic drift."""
    findings, checked, skipped = [], 0, 0
    names = set(records.by_name)
    names |= {record["name"] for record in records.declarations}
    prefixes = set()
    for name in names:
        parts = name.split(".")
        prefixes |= {".".join(parts[:index]) for index in range(1, len(parts))}
    paths = sorted({path for pattern in DOCUMENTS for path in root.glob(pattern)})
    namespaces = namespace_packages(root)
    locked = load_lock().get('theorems', {})
    for path in paths:
        for token in sorted(set(QUALIFIED.findall(path.read_text()))):
            record = records.get(token)
            matches = [name for name in namespaces if token == name or token.startswith(name + '.')]
            owners = namespaces[max(matches, key=len)] if matches else set()
            if token not in names and token not in prefixes and owners and owners.isdisjoint(records.packages()):
                skipped += 1
                continue
            package = (record["package"] if record else locked[token]['package'] if token in locked
                       else ROOTS[token.split(".")[0]])
            if package not in records.packages():
                skipped += 1
                continue
            checked += 1
            module = PACKAGE_DIRECTORIES[package].joinpath(*token.split("."))
            if token in names or token in prefixes or module.with_suffix(".lean").exists() or module.is_dir():
                continue
            findings.append(f"stale name: {path.relative_to(root)} cites {token}, which is not a declaration, "
                            "namespace or module")
    return findings, checked, skipped
