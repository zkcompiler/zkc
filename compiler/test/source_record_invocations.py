"""Execute authored record-operation homonyms and retain their stop guards."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

commands = Commands(records())
reference = Path(compiler).parent / 'test/zkc-structured_reference-test'
symbol = 's1h6d3h52756e'
serial = 0


def execute(code, outcome):
    global serial
    serial += 1
    source = commands.directory / f'case-{serial}.zkc'
    source.write_text(code)
    original = commands.run([compiler, 'language-emit', '--source-format=zkc',
                             '--subject=m::Run', f'--module=m={source}'])
    path = commands.directory / f'case-{serial}.mlir'
    path.write_text(original)
    request = commands.write(f'case-{serial}.json', [])
    actual = json.loads(commands.run([reference, path, symbol, request]))
    assert actual == outcome, actual


for name in ['inspect_record', 'repack_record', 'unpack']:
    for route in ['plain', 'qualified', 'method', 'module_alias', 'import']:
        with case(f'{name}/{route} executes its authored stop'):
            result = '(Ticket,())' if name == 'inspect_record' else 'Ticket' if name == 'repack_record' else '()'
            parameters = 'x:Ticket,payload:()' if name == 'repack_record' else 'x:Ticket'
            arguments = 'x,()' if name == 'repack_record' else 'x'
            call = f'{name}({arguments})'
            if route == 'qualified':
                call = 'm::' + call
            elif route == 'method':
                call = f'x.{name}({"()" if name == "repack_record" else ""})'
            elif route == 'module_alias':
                call = 'authored::' + call
            finish = 'let done=finish(y.0);' if name == 'inspect_record' else 'let done=finish(y);' if name == 'repack_record' else ''
            declarations = f'''#[linear] struct Ticket{{}}
fn make()->Ticket{{return Ticket{{}};}}
fn {name}({parameters})->{result}{{stop "reject";}}
fn finish(x:Ticket)->(){{consume x;return ();}}
'''
            if route in ['module_alias', 'import']:
                declarations = ('module Api{' + declarations.replace('struct Ticket', 'pub struct Ticket').replace('fn ', 'pub fn ') +
                                f'}}use ::m::Api as authored;use ::m::Api::{{Ticket,make,finish,{name}}};')
            execute(f'''module m;
{declarations}
fn advance(x:Ticket)->(){{let y={call};{finish}return ();}}
protocol Run roles(P)()->(){{let x@P=make();let done@P=advance(x);return ();}}
''', ['stopped', 'reject'])

with case('installed qualified custody operations execute and retire the successor'):
    execute('''module m;
#[linear] struct Ticket{value:bool}
fn make()->Ticket{return Ticket{value:true};}
fn advance(x:Ticket)->Ticket{
 let observed=zkc::records::inspect_record(x);
 return zkc::records::repack_record(observed.0,observed.1);
}
fn finish(x:Ticket)->(){let fields=zkc::records::unpack(x);require fields.0;return ();}
protocol Run roles(P)()->(){let x@P=make();let y@P=advance(x);let done@P=finish(y);return ();}
''', ['returned', []])

commands.save()
print(f'source-record-invocations: {counted()} cases; evidence: {commands.directory}')
