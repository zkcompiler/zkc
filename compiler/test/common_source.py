"""Native common-source export controls; no Lean installation required."""
import hashlib
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records

commands = Commands(records())
fixtures = Path(__file__).parent / 'fixtures/mathematical'
field = '!algebra.field<"bls12-381.fr">'


def source(body='', result='%x', output=field, inputs=None, scopes=None):
    inputs = inputs or f'%x: {field}, %y: {field}'
    scopes = scopes or '[["P","V"],["P","V"]]'
    return f'''module {{ "protocol.module"() ({{
"protocol.func"() ({{
^entry({inputs}):
{body}
"protocol.return"({result}) : ({output})->()
}}) {{sym_name="main", function_type=({field},{field})->{output}, roles=["P","V"],
input_roles={scopes}, output_roles=[["V"]]}} : ()->()
}}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''


def export(text, refusal=None, symbol='main'):
    return commands.source('protocol-lean', text, '--symbol='+symbol, refuses=refusal)


with case('actual-source-identity-and-ordered-operands'):
    text=source(f'%a = algebra.field_subtract %y, %x : ({field},{field})->{field}', '%a')
    data=json.loads(export(text))
    assert data[1]=='sha256:'+hashlib.sha256(text.encode()).hexdigest()
    assert data[8]==[['pure',['field.subtract','bls12-381.fr'],[1,0]]]
    assert data[5]==[[0,1],[0,1]] and data[7]==[1]
    assert json.loads(export(text+'\n'))[1]!=data[1]

with case('original-unused-scope-error-is-not-erased'):
    export(source(f'%dead = algebra.field_add %x, %y : ({field},{field})->{field}',
                  '%y',scopes='[["P"],["V"]]'), 'common-source-original')

with case('unknown-selected-symbol'):
    export(source(), 'common-source-symbol', 'absent')

with case('whole-original-verification'):
    export('module { this-is-not-an-operation }', 'common-source-original')

with case('multiple-top-level-units'):
    export('module { module {} module {} }', 'common-source-module')

with case('wrong-profile'):
    export('module { module {} }', 'common-source-profile')

with case('multiple-results'):
    export((fixtures/'mixed.mlir').read_text(),'common-source-signature')

with case('unsupported-dialect-type'):
    export((fixtures/'sumcheck.mlir').read_text(),'common-source-type','terminal')

with case('unsupported-local-realization'):
    export((fixtures/'helper-realization.mlir').read_text(),'common-source-operation')

with case('text-depth-limit'):
    export('module {'*66+'}'*66,'mlir-depth-limit')

with case('instruction-limit'):
    body='\n'.join(f'%x{i} = algebra.field_add %x, %y : ({field},{field})->{field}' for i in range(1025))
    export(source(body),'common-source-limit')

with case('string-limit'):
    text=source().replace('sym_name="main"','sym_name="'+'a'*513+'"')
    export(text,'common-source-limit','a'*513)

with case('statement-is-retained'):
    data=json.loads(export((fixtures/'schnorr-services.mlir').read_text()))
    assert data[8][0][0]=='statement'
    assert data[8][0][3:]==[[1,1,0],[0,2,1]]

with case('actual-pure-relation-function'):
    helper = f'''func.func private @predicate(%a: {field}, %b: {field}) -> i1 {{
      %same = algebra.field_equal %a, %b : ({field}, {field}) -> i1
      return %same : i1
    }}'''
    text = source().replace('"protocol.func"()', helper + '\n"protocol.func"()', 1)
    data = json.loads(export(text, symbol='predicate'))
    assert data[1] == 'sha256:' + hashlib.sha256(text.encode()).hexdigest()
    assert data[2:4] == ['predicate', ['formula']]
    assert data[5:8] == [[[0], [0]], ['bool'], [0]]
    assert data[8] == [['pure', ['field.equal', 'bls12-381.fr'], [0, 1]]]

with case('formula-multiple-results'):
    helper = f'''func.func private @predicate(%a: {field}) -> ({field}, {field}) {{
      return %a, %a : {field}, {field}
    }}'''
    text = source().replace('"protocol.func"()', helper + '\n"protocol.func"()', 1)
    export(text, 'common-source-signature', 'predicate')

commands.save()
counted()
