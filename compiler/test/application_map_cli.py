"""Exact-byte application maps are usable through the public compiler tool."""
import hashlib
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
# A source-compiled original, its prepared candidate and its exact source
# correspondence: written links follow the supplied document.
written_source = artifact('written.zkc', """module sample;
protocol Step roles(P,V)(x:bool@P)->(y:bool@V){let y@V=send P->V(x);return(y=y);}
protocol Run roles(P,V)(a:bool@P,b:bool@P)->(c:bool@V,d:bool@V){
  let c=Step roles(P,V)(a);
  let d=Step roles(P,V)(b);
  return(c=c,d=d);
}
""")
selection = ['--source-format=zkc', f'--module=sample={written_source}',
             '--subject=sample::Run']
written_original = artifact('written.mlir', commands.run(
    [compiler, 'language-emit', *selection]))
written_candidate = artifact('written-candidate.mlir', commands.run(
    [optimizer, '--zkc-preparation-pipeline=simplify=false'],
    stdin=written_original.read_text()))
checked = json.loads(commands.run(
    [compiler, 'language-check', *selection, '--source-correspondence']))
correspondence = checked['source_correspondence']
supplied = artifact('correspondence.json', json.dumps(correspondence))
symbol = '--symbol=' + correspondence['admission']['protocol_symbol']
digest = 'sha256:' + hashlib.sha256(supplied.read_bytes()).hexdigest()

with case('written links follow the supplied correspondence occurrences'):
    linked = json.loads(commands.run([
        compiler, 'protocol-application-map', written_original,
        written_candidate, symbol, f'--source-correspondence={supplied}']))
    assert linked['correspondence'] == {
        'format': 'zkc.source-correspondence/0', 'digest': digest}
    occurrences = {(o['definition'], o['site']): o['nodes']
                   for o in correspondence['occurrences']}
    expansions = [a for a in linked['applications'] if a['parent'] is not None]
    assert len(expansions) == 2
    for application in expansions:
        nodes = [nodes for (definition, _), nodes in occurrences.items()
                 if definition == application['source_definition']
                 and application['written']['node'] in nodes]
        assert len(nodes) == 1 and len(nodes[0]) == 1
        assert application['written']['instance'] == application['callee']
    linked_map = artifact('linked.json', json.dumps(linked))

with case('the command reports supplied links as conditional on their digest'):
    report = json.loads(commands.run([
        compiler, 'protocol-check-application-map', written_original,
        written_candidate, linked_map, symbol,
        f'--source-correspondence={supplied}']))
    assert report == {'written': 'conditional', 'correspondence': digest}

with case('a linked map refuses without its correspondence'):
    commands.run([compiler, 'protocol-check-application-map', written_original,
                  written_candidate, linked_map, symbol],
                 refuses='application-map-written')

with case('a malformed correspondence refuses rather than reading as absent'):
    malformed = dict(correspondence, authority=True)
    broken = artifact('malformed.json', json.dumps(malformed))
    for command in ('protocol-application-map',
                    'protocol-check-application-map'):
        arguments = [written_original, written_candidate]
        if command == 'protocol-check-application-map':
            arguments.append(linked_map)
        commands.run([compiler, command, *arguments, symbol,
                      f'--source-correspondence={broken}'],
                     refuses='application-map-written')
counted()
