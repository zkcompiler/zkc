"""Run the declaration-record emitter and read its output.

The emitter (`lean/ir/Zkc/Tools/IR/DeclarationRecords.lean`) writes one JSON line per
declaration written in the source of a package's module families, after a
header line. A package is selected by name; its families mirror the
declaration audit's scopes.
"""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

from support.lean_headers import HeaderParser
from support.packages import LEAN as LEAN, PACKAGES, package_directory, package_modules, selected

EMITTER = package_directory("ir") / "Zkc/Tools/IR/DeclarationRecords.lean"
ALLOWED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
FORMAT = "zkc.declarations/0"
REGISTRY = {"verification": ("ZkcSecurity.Registry.table", "ZkcSecurity.Registry.endpoints")}


def emission_groups(package, headers):
    """Partition all owned sources by the executable root their imports load.

    Lake's explicit lean_exe roots are the authority, including tools outside
    Commands. Follow imports through maintained dependencies so an isolated
    executable audit goes with its command, rather than the common inventory.
    An aggregate importing independent commands is invalid and must be repaired by
    its owner; dropping it from declaration coverage would conceal the failure.
    """
    modules, commands = {}, set()
    for name in selected([package]):
        owned = package_modules(name)
        modules.update(owned)
        config = tomllib.loads((PACKAGES[name][0] / 'lakefile.toml').read_text())
        for executable in config.get('lean_exe', []):
            root = executable['root']
            if root not in owned:
                raise ValueError(f'{name}: executable root has no owned source: {root}')
            commands.add(root)
    graph = {module: headers.imports(path.read_text(), path) for module, path in modules.items()}
    cache, active = {}, set()

    def roots(module):
        if module in cache:
            return cache[module]
        if module in active:
            raise ValueError(f'cyclic maintained imports during record emission: {module}')
        active.add(module)
        found = set()
        for dependency in graph[module]:
            if dependency in graph:
                found.update(roots(dependency))
        # A declared executable can forward an imported main (for example the
        # data-anchor control imports DeclarationRecords). Such a root belongs
        # to that same environment, rather than defining a second main provider.
        # A source redefining the imported main is rejected by the fresh build.
        if module in commands and not found:
            found.add(module)
        active.remove(module)
        cache[module] = frozenset(found)
        return cache[module]

    groups = {}
    for module in package_modules(package):
        reached = roots(module)
        if len(reached) > 1:
            raise ValueError(f'{module}: imports multiple executable roots: {sorted(reached)}')
        key = next(iter(reached), '')
        groups.setdefault(key, []).append(module)
    return [groups[key] for key in sorted(groups)], groups.get('', [])


def merge_emissions(parts, output):
    """Validate each shard's complete source selection, retaining each owner once.

    Common sources provide registry/property context in isolated environments.
    Their repeated records are context, not additional declarations. Keep all
    rows of the assigned modules, including private rows with the same rendered
    name and global mains whose owning modules distinguish their identities.
    """
    header, rows, covered = None, [], set()
    for path, context, assigned in parts:
        context_set, assigned_set = set(context), set(assigned)
        with path.open() as stream:
            current = json.loads(next(stream))
            if (current.get('format') != FORMAT or current.get('families') != context or
                    type(current.get('modules')) is not int or current['modules'] != len(context) or
                    type(current.get('declarations')) is not int or current['declarations'] < 0 or
                    current.get('axiom_provenance') != 'resolved-constant-info/0' or
                    current.get('reference_provenance') != 'checked-stored-module/0'):
                raise ValueError(f'{path}: invalid declaration shard or source coverage')
            if header is None:
                header = current.copy()
            elif ({k: v for k, v in current.items() if k not in ('families', 'modules', 'declarations')} !=
                  {k: v for k, v in header.items() if k not in ('families', 'modules', 'declarations')}):
                raise ValueError(f'{path}: inconsistent declaration shard metadata')
            if covered.intersection(assigned_set) or not assigned_set <= context_set:
                raise ValueError(f'{path}: duplicate or unselected declaration source coverage')
            covered.update(assigned)
            count = 0
            for line in stream:
                row = json.loads(line)
                if row.get('module') not in context_set or not isinstance(row.get('name'), str):
                    raise ValueError(f'{path}: record outside the selected source modules')
                count += 1
                if row['module'] in assigned_set:
                    rows.append(row)
            if count != current['declarations']:
                raise ValueError(f'{path}: declaration shard count mismatch')
    if header is None:
        raise ValueError('no declaration sources selected')
    header.update(families=sorted(covered), modules=len(covered), declarations=len(rows))
    rows.sort(key=lambda row: (row['name'], row['module']))
    with output.open('w') as stream:
        for row in [header, *rows]:
            stream.write(json.dumps(row, sort_keys=True, separators=(',', ':')) + '\n')


def emit(package, output, *, lake="lake", baseline=None, details=(), log=None):
    """Read fresh stored proofs in isolated environments and publish atomically."""
    directory, _ = PACKAGES[package]
    output = Path(output).resolve()
    # Lake invalidates the tool when its sources or imports change. Its output
    # is never cached: each invocation reads the actual stored proof bodies in
    # the audited package's environment, including private/opaque declarations.
    built = subprocess.run([lake, "build", "declaration-records"], cwd=package_directory("ir"),
                           stdout=log, stderr=subprocess.STDOUT if log else None, text=True)
    if built.returncode != 0:
        return built
    with HeaderParser(lake=lake) as headers:
        groups, common = emission_groups(package, headers)
    # Default targets may omit a command or a source without weakening its
    # ownership. Refresh every enumerated module, including isolated audits.
    modules = package_modules(package)
    if set(modules) != {module for group in groups for module in group}:
        raise ValueError('package source inventory changed during declaration selection')
    built = subprocess.run([lake, 'build', *['+' + module for module in modules]], cwd=directory,
                           stdout=log, stderr=subprocess.STDOUT if log else None, text=True)
    if built.returncode != 0:
        return built
    command = [lake, "env", str(package_directory("ir") / ".lake/build/bin/declaration-records")]
    if package in REGISTRY:
        table, endpoints = REGISTRY[package]
        command += ["--registry", table, "--endpoints", endpoints]
    for name in details:
        command += ["--detail", name]
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='declaration-records-', dir=output.parent) as temporary:
        temporary = Path(temporary)
        parts = []
        for index, assigned in enumerate(groups):
            context = sorted(set(common) | set(assigned))
            sources = [str(modules[module].relative_to(directory)) for module in context]
            path = temporary / f'{index}.jsonl'
            result = subprocess.run([*command, str(path), *sources], cwd=directory, stdout=log,
                                    stderr=subprocess.STDOUT if log else None, text=True)
            if result.returncode != 0:
                return result
            parts.append((path, context, assigned))
        combined = temporary / 'complete.jsonl'
        merge_emissions(parts, combined)
        # Compare the complete package, never a shard against a package baseline.
        differs = baseline is not None and Path(baseline).read_bytes() != combined.read_bytes()
        combined.replace(output)
    if differs:
        print(f'declaration records differ from {baseline}', file=log or sys.stderr)
        return subprocess.CompletedProcess(command, 1)
    return result


class Records:
    """The emitted records of one or more packages, indexed by name."""

    def __init__(self, headers=None, declarations=None):
        self.headers = headers or {}
        self.declarations = declarations or []
        self.by_name = {}
        for record in self.declarations:
            if "private" not in record.get("tags", []):
                self.by_name.setdefault(record["name"], record)

    @classmethod
    def load(cls, paths):
        headers, declarations = {}, []
        for package, path in paths.items():
            lines = Path(path).read_text().splitlines()
            if not lines:
                raise ValueError(f"{path}: empty declaration document")
            header = json.loads(lines[0])
            families = header.get("families")
            if (header.get("format") != FORMAT or not isinstance(families, list) or
                    any(not isinstance(name, str) or not name for name in families) or
                    len(set(families)) != len(families) or
                    type(header.get("modules")) is not int or header["modules"] != len(families) or
                    type(header.get("declarations")) is not int or header["declarations"] != len(lines) - 1 or
                    header.get("axiom_provenance") != "resolved-constant-info/0" or
                    header.get("reference_provenance") != "checked-stored-module/0"):
                raise ValueError(f"{path}: invalid declaration counts, coverage or provenance")
            headers[package] = header
            for line in lines[1:]:
                record = json.loads(line)
                if (record.get("module") not in families or
                        not isinstance(record.get("name"), str) or not record["name"] or
                        not isinstance(record.get("axioms"), list) or
                        any(not isinstance(name, str) for name in record["axioms"])):
                    raise ValueError(f"{path}: malformed or unselected stored declaration")
                record["package"] = package
                declarations.append(record)
        return cls(headers, declarations)

    def get(self, name):
        return self.by_name.get(name)

    def packages(self):
        return set(self.headers)

    def registry(self):
        """Combine compatible registry metadata from every emitted package."""
        entries, schemas, endpoints = {}, {}, {}
        found = False
        for header in self.headers.values():
            registry = header.get("registry")
            if registry is None:
                continue
            found = True
            for entry in registry:
                identifier = entry["identifier"]
                if identifier in entries and entries[identifier] != entry:
                    raise ValueError(f"conflicting registry identifier: {identifier}")
                schema = entry.get("schema")
                if schema and schema in schemas and schemas[schema] != entry:
                    raise ValueError(f"conflicting registry schema: {schema}")
                if schema:
                    schemas[schema] = entry
                entries[identifier] = entry
            for entry in header.get("endpoints") or []:
                key = (entry["endpoint"], entry["property"], entry["statement"])
                if key in endpoints and endpoints[key] != entry:
                    raise ValueError(f"conflicting registered endpoint: {key}")
                endpoints[key] = entry
        return (list(entries.values()) if found else None), list(endpoints.values())



def forbidden_axioms(record):
    return [name for name in record.get("axioms", []) if name not in ALLOWED_AXIOMS]
