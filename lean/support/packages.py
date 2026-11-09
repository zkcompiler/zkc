"""The maintained Lean package inventory and exact dependency checks.

Module names select source ownership; declaration namespaces are independent.
The shared lean directory is a harness, never a Lake package.
"""
from pathlib import Path
import json
import re
import tomllib

LEAN = Path(__file__).resolve().parents[1]
DIRECTORIES = {"program": "program", "ir": "ir", "protocol": "protocol",
               "verification": "verification", "arklib": "adapters/arklib",
               "clean": "adapters/clean", "applications": "applications"}
OWNERS = {"program": "Program", "ir": "IR", "protocol": "Protocol",
          "verification": "Verification", "arklib": "ArkLib", "clean": "Clean",
          "applications": "Applications"}
PACKAGES = {
    name: (LEAN / directory, (f"Zkc.Adapters.{OWNERS[name]}" if name in ("arklib", "clean")
                             else f"Zkc.{OWNERS[name]}",
                             f"Zkc.Tools.{OWNERS[name]}", f"Zkc.Tests.{OWNERS[name]}"))
    for name, directory in DIRECTORIES.items()
}
NAMES = {name: f"zkc_{name}" for name in PACKAGES}
DEPENDENCIES = {"program": (), "ir": ("program",), "protocol": ("program",),
                "verification": ("ir", "protocol"), "arklib": ("protocol",),
                "clean": ("ir",), "applications": ("verification", "arklib", "clean")}
UPSTREAM = {"program": {"mathlib"}, "ir": set(),
            "protocol": {"VCVio", "PolyFun", "CompPoly"}, "verification": set(),
            "arklib": {"Arklib"}, "clean": {"Clean", "CompPoly"}, "applications": set()}
CORE = ("program", "ir", "protocol", "verification")


def below(module, prefix):
    return module == prefix or module.startswith(prefix + ".")


def selected(packages=None):
    """Return a stable topological closure; None selects every maintained package."""
    requested = tuple(PACKAGES) if packages is None else tuple(packages)
    unknown = set(requested) - PACKAGES.keys()
    if unknown:
        raise ValueError(f"unknown Lean packages: {sorted(unknown)}")
    result, active = [], set()

    def visit(name):
        if name in active:
            raise ValueError(f"cyclic maintained package dependency: {name}")
        if name in result:
            return
        active.add(name)
        for dependency in DEPENDENCIES[name]:
            visit(dependency)
        active.remove(name)
        result.append(name)

    for name in PACKAGES:
        if name in requested:
            visit(name)
    # Canonicalize equal closures independently of argument order/redundancy.
    needed = set(result)
    result.clear()
    for name in PACKAGES:
        if name in needed:
            visit(name)
    return result


def add_selection(parser):
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--package", action="append", choices=tuple(PACKAGES),
                           help="select a package and its dependencies; repeat (default: all)")
    selection.add_argument("--core-only", action="store_true",
                           help="select program, ir, protocol and verification")


def selection(args):
    return selected(CORE if args.core_only else args.package)


def package_directory(name, root=LEAN):
    return root / DIRECTORIES[name]


def module_owner(module):
    """Resolve the longest full module prefix, never the first name component."""
    matches = [(len(prefix.split('.')), name) for name, (_, roots) in PACKAGES.items()
               for prefix in roots if below(module, prefix)]
    if not matches:
        raise ValueError(f"module has no maintained package: {module}")
    longest = max(length for length, _ in matches)
    owners = {name for length, name in matches if length == longest}
    if len(owners) != 1:
        raise ValueError(f"module has no unique maintained package: {module}")
    return owners.pop()


def is_owned_module(module):
    return any(below(module, prefix) for _, roots in PACKAGES.values() for prefix in roots)


def module_package(module):
    return PACKAGES[module_owner(module)][0]


def module_path(module, root=LEAN):
    return package_directory(module_owner(module), root).joinpath(*module.split('.')).with_suffix('.lean')


def _raise_walk_error(error):
    raise error


def package_modules(name, root=LEAN):
    """Enumerate every source once and refuse misplaced or legacy source roots."""
    directory = package_directory(name, root)
    if not directory.is_dir():
        raise ValueError(f"migrated package is missing: {directory}")
    result = {}
    for parent, directories, filenames in directory.walk(on_error=_raise_walk_error):
        # Do not even descend into Lake's dependency/cache trees.
        directories[:] = sorted(child for child in directories if not child.startswith('.'))
        for filename in sorted(filenames):
            path = parent / filename
            if path.suffix != '.lean' or filename.startswith('.'):
                continue
            relative = path.relative_to(directory)
            module = '.'.join(relative.with_suffix('').parts)
            if module_owner(module) != name:
                raise ValueError(f"misplaced maintained module: {path}")
            result[module] = path
    if not result:
        raise ValueError(f"migrated package has no sources: {directory}")
    return dict(sorted(result.items()))


def tool_module(package, name, root=LEAN):
    """Find one tool in its owning module root; never guess a compatibility path."""
    prefix = f'Zkc.Tools.{OWNERS[package]}'
    candidates = [module for module in package_modules(package, root)
                  if below(module, prefix) and module.rsplit('.', 1)[-1] == name]
    if len(candidates) != 1:
        raise ValueError(f'expected one {package} tool module named {name}: {candidates}')
    return candidates[0]


def library_globs(name, config):
    """Require explicit dotted ownership and coverage of every package root."""
    roots = PACKAGES[name][1]
    globs = []
    for library in config.get('lean_lib', []):
        if 'roots' not in library or 'globs' not in library:
            raise ValueError(f'{name}: library roots and globs must be explicit')
        for root in library['roots']:
            if module_owner(root) != name:
                raise ValueError(f'{name}: invalid library root: {root}')
        for glob in library['globs']:
            prefix = glob[:-2] if glob.endswith(('.+', '.*')) else glob
            if module_owner(prefix) != name:
                raise ValueError(f'{name}: invalid library glob: {glob}')
            globs.append(glob)
    present = package_modules(name)
    if any(root + '.+' not in globs for root in roots
           if any(below(module, root) for module in present)):
        raise ValueError(f'{name}: library globs omit maintained roots')
    return globs


def allowed_dependencies(name):
    packages = selected([name])
    return {NAMES[item] for item in packages if item != name} | set().union(*(UPSTREAM[item] for item in packages))


PROVIDERS = set(NAMES.values()) | set().union(*UPSTREAM.values())
FORBIDDEN_DEPENDENCIES = {name: PROVIDERS - allowed_dependencies(name) - {NAMES[name]}
                          for name in PACKAGES}


def closure(directory, ancestors=()):
    """Check exact manifests, provider identities, full Git pins and path cycles."""
    directory = directory.resolve()
    if directory in ancestors:
        raise ValueError(f"cyclic path dependency: {directory}")
    manifest = json.loads((directory / 'lake-manifest.json').read_text())
    config = tomllib.loads((directory / 'lakefile.toml').read_text())
    if manifest['name'] != config['name']:
        raise ValueError(f"manifest package mismatch: {directory}")
    locks = {entry['name']: entry for entry in manifest['packages']}
    if len(locks) != len(manifest['packages']):
        raise ValueError(f"duplicate locked dependency in {directory}")
    requirements = config.get('require', [])
    if len({dep['name'] for dep in requirements}) != len(requirements):
        raise ValueError(f'duplicate requirement: {directory}')
    for dep in requirements:
        locked = locks.get(dep['name'])
        if locked is None:
            raise ValueError(f"missing locked dependency: {directory}: {dep['name']}")
        if 'path' in dep:
            target = (directory / dep['path']).resolve()
            if locked['type'] != 'path' or (directory / locked['dir']).resolve() != target:
                raise ValueError(f"path dependency mismatch: {dep['name']}")
        elif (locked['type'] != 'git' or locked['rev'] != dep['rev'] or
              locked['url'].removesuffix('.git') != dep['git'].removesuffix('.git')):
            raise ValueError(f"pin mismatch: {dep['name']}")
    names = set(locks)
    for dep in locks.values():
        if dep['type'] == 'path':
            target = (directory / dep['dir']).resolve()
            provider = tomllib.loads((target / 'lakefile.toml').read_text())
            if provider['name'] != dep['name']:
                raise ValueError(f"locked path provider mismatch: {dep['name']}")
            names |= closure(target, (*ancestors, directory))
        elif dep['type'] != 'git' or not re.fullmatch('[0-9a-f]{40}', dep['rev']):
            raise ValueError(f"invalid locked Git pin: {dep['name']}")
    return names


def check_closure(package, directory):
    reached = closure(directory)
    config = tomllib.loads((directory / 'lakefile.toml').read_text())
    if config['name'] != NAMES[package]:
        raise ValueError(f'{package}: incorrect package identity')
    local = {dep['name'] for dep in config.get('require', []) if 'path' in dep}
    expected = {NAMES[dep] for dep in DEPENDENCIES[package]}
    if local != expected:
        raise ValueError(f'{package}: incorrect direct maintained dependencies: {sorted(local)}; expected {sorted(expected)}')
    if reached & FORBIDDEN_DEPENDENCIES[package]:
        raise ValueError(f'{package}: prohibited package closure: {sorted(reached & FORBIDDEN_DEPENDENCIES[package])}')
    root = directory.resolve().parents[len(Path(DIRECTORIES[package]).parts) - 1]
    providers = {NAMES[name]: package_directory(name, root).resolve() for name in PACKAGES}
    manifest = json.loads((directory / 'lake-manifest.json').read_text())
    for dep in manifest['packages']:
        if dep['name'] in providers and dep['type'] != 'path':
            raise ValueError(f"maintained dependency must be a path provider: {dep['name']}")
        if dep['type'] == 'path' and (dep['name'] not in providers or
                (directory / dep['dir']).resolve() != providers[dep['name']]):
            raise ValueError(f"unexpected maintained path dependency: {dep['name']}")
    direct_git = {dep['name'] for dep in config.get('require', []) if 'path' not in dep}
    if not direct_git <= allowed_dependencies(package):
        raise ValueError(f'{package}: unexpected direct upstream dependency: {sorted(direct_git - allowed_dependencies(package))}')
    required = allowed_dependencies(package)
    if not required <= reached:
        raise ValueError(f'{package}: missing required dependencies: {sorted(required - reached)}')
    return reached
