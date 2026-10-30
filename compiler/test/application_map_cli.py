"""Exact-byte application maps are usable through the public compiler tool."""
import json
from cases import case, counted
from commands import Commands
from tools import compiler, optimizer, ROOT, records

commands = Commands(records())
commands.directory.mkdir(parents=True, exist_ok=True)
def artifact(name, text):
    path = commands.directory / name
    path.write_text(text)
    return path
fixture = ROOT / 'compiler/test/fixtures/application-map/nested.mlir'
source = fixture.read_text()
original = artifact('original.mlir', source)
prepared = commands.run([optimizer, '--zkc-preparation-pipeline=simplify=false'],
                        stdin=source)
candidate = artifact('candidate.mlir', prepared)

with case('produce and check the prepared application map'):
    record = commands.run([compiler, 'protocol-application-map', original,
                           candidate, '--symbol=main'])
    parsed = json.loads(record)
    assert parsed['format'] == 'zkc.application-map/0'
    proposal = artifact('map.json', record)
    commands.run([compiler, 'protocol-check-application-map', original,
                  candidate, proposal, '--symbol=main'])

with case('source bytes are part of the checked association'):
    changed = artifact('changed.mlir', '// retained bytes differ\n' + source)
    commands.run([compiler, 'protocol-check-application-map', changed,
                  candidate, proposal, '--symbol=main'],
                 refuses='application-map-identity')

with case('application coverage cannot be omitted'):
    modified = json.loads(record)
    assert modified['applications']
    modified['applications'].pop()
    missing = artifact('missing.json', json.dumps(modified))
    commands.run([compiler, 'protocol-check-application-map', original,
                  candidate, missing, '--symbol=main'],
                 refuses='application-map-correspondence')
counted()
