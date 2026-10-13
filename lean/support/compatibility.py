"""Apply a declared dependency patch only to its exact recorded source revision."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(package):
    declaration = package / 'compatibility.json'
    if not declaration.is_file():
        return None
    config = json.loads(declaration.read_text())
    manifest = json.loads((package / 'lake-manifest.json').read_text())
    dependency, = [entry for entry in manifest['packages'] if entry['name'] == config['package']]
    if dependency['type'] != 'git' or dependency['rev'] != config['revision']:
        raise ValueError('compatibility patch revision differs from the owning manifest')
    source = package / manifest['packagesDir'] / config['package']
    head = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
    if head != config['revision']:
        raise ValueError('compatibility patch requires the recorded dependency revision')
    patch = package / config['patch']
    if digest(patch) != config['patch_sha256']:
        raise ValueError('compatibility patch digest mismatch')
    changed = subprocess.check_output(
        ['git', '-C', str(source), 'diff', '--name-only', '-z', 'HEAD']).decode().split('\0')
    untracked = subprocess.check_output(
        ['git', '-C', str(source), 'ls-files', '--others', '--exclude-standard', '-z']).decode().split('\0')
    if (set(changed) - {''} - config['files'].keys()) or any(untracked):
        raise ValueError('undeclared dependency source changes; compatibility patch refused')
    states = [{kind for kind in ('base_sha256', 'patched_sha256')
               if digest(source / name) == values[kind]} for name, values in config['files'].items()]
    if not states:
        raise ValueError('compatibility patch must declare its changed files')
    if all('patched_sha256' in state for state in states):
        return config
    if not all('base_sha256' in state for state in states):
        raise ValueError('unexpected dependency source contents; compatibility patch refused')
    subprocess.run(['git', '-C', str(source), 'apply', '--check', str(patch.resolve())], check=True)
    subprocess.run(['git', '-C', str(source), 'apply', str(patch.resolve())], check=True)
    if any(digest(source / name) != values['patched_sha256'] for name, values in config['files'].items()):
        raise ValueError('compatibility patch produced unexpected source contents')
    return config


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('package', type=Path)
    args = parser.parse_args()
    # Let Lake materialize missing pinned sources before checking their revision.
    subprocess.run(['lake', 'env', 'printenv', 'LEAN_SRC_PATH'], cwd=args.package,
                   check=True, stdout=subprocess.DEVNULL)
    prepare(args.package.resolve())
