"""External R1CS semantics and actual native protocol application boundaries."""

from commands import Commands
from tools import records
from relation_composition_cases import check_application_boundaries, prepare

commands = Commands(records())
check_application_boundaries(commands)
prepare(commands, commands.directory)
