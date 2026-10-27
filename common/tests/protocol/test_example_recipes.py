"""The literal README commands run in independent manifest consumer trees."""
import os

import pytest

from example_recipes import copy_consumer, recipes
from toolchain import ROOT

PROJECTS = sorted(path.parent for path in (ROOT / 'examples/projects').rglob('zkc.toml'))


@pytest.mark.parametrize('project', PROJECTS, ids=lambda path: str(path.relative_to(ROOT)))
def test_readme_recipe_runs_in_a_clean_consumer(toolchain, journal, directory, project):
    blocks = recipes(project / 'README.md')
    assert len(blocks) == 1, 'each example owns one literal quick-start recipe'
    consumer = copy_consumer(project, ROOT, directory / 'consumer')
    script = consumer / 'recipe.sh'
    script.write_text('set -eu\n' + blocks[0])
    # The installed tools receive the copied manifest; no compiler or test
    # adapter supplies hidden source modules to these commands.
    path = os.pathsep.join([str(toolchain.runtime.parent), str(toolchain.compiler.parent),
                            os.environ['PATH']])
    # These literal recipes have one command per non-comment line. Checking,
    # proving and verifying can each compile the project; the complete shell
    # workflow needs their combined allowance, not one tool's timeout.
    commands = sum(bool(line.strip()) and not line.lstrip().startswith('#')
                   for line in blocks[0].splitlines())
    journal.run(['env', f'PATH={path}', 'sh', script], cwd=consumer,
                timeout=journal.timeout * max(1, commands))
