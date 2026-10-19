"""Select literal example recipes and copy their declared consumer closures."""
from pathlib import Path
import shutil
import tomllib

from project import project_inputs


def recipes(readme):
    """Only explicitly marked shell blocks are executable documentation."""
    result, current = [], None
    for line in Path(readme).read_text().splitlines():
        if line == '```sh zkc-example':
            assert current is None
            current = []
        elif line == '```' and current is not None:
            result.append('\n'.join(current) + '\n')
            current = None
        elif current is not None:
            current.append(line)
    assert current is None, 'unterminated example recipe'
    return result


def copy_consumer(project, root, destination):
    """Preserve relative manifest paths in a separate, minimal source tree."""
    manifests = []
    modules, assets = project_inputs(project / 'zkc.toml', manifests=manifests)
    directories = {project, *(manifest.parent for manifest in manifests
                             if tomllib.loads(manifest.read_text()).get('format') != 'zkc.workspace/0')}
    for directory in sorted(directories):
        for path in directory.rglob('*'):
            if not path.is_file() or any(part in ('build', '__pycache__')
                                         for part in path.relative_to(directory).parts):
                continue
            # Nested leaf packages remain independently selected.
            if any((parent / 'zkc.toml').is_file() and parent not in directories
                   for parent in path.parents if directory in parent.parents):
                continue
            target = destination / path.relative_to(root)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
    for path in {*manifests, *modules.values(), *(path for _, path in assets.values())}:
        target = destination / path.relative_to(root)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
    return destination / project.relative_to(root)
