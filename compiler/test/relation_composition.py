"""External R1CS semantics and actual native protocol application boundaries."""

from cases import case
from commands import Commands
from tools import records
from relation_composition_cases import (
    check_application_boundaries,
    check_composition_correspondence,
    check_r1cs_correspondence,
    check_relation_admission,
    prepare,
)

root = records()
with case("application boundaries"):
    check_application_boundaries(Commands(root / "application"))

# Each group prepares its own inputs; a failure cannot spoil later groups.
for name, check in [
    ("composition correspondence", check_composition_correspondence),
    ("r1cs correspondence", check_r1cs_correspondence),
    ("relation admission", check_relation_admission),
    ("execution carriers", prepare),
]:
    with case(name):
        commands = Commands(root / name.replace(" ", "-"))
        check(commands, commands.directory)
