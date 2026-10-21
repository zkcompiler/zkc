"""Entry syntax, generated nominal APIs and Host-stage refusal through the driver."""
import json

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)


def check(source, *, entry=None, inspect_api=False, refuses=None):
    path = OUT / f'source-{check.sequence}.zkc'
    check.sequence += 1
    path.write_text(source)
    args = [compiler, 'language-check', '--source-format=zkc', f'--module=sample={path}']
    if entry:
        args.append(f'--entry=sample::{entry}')
    if inspect_api:
        args += ['--declarations', '--api']
    result = commands.run(args, refuses=refuses)
    return None if refuses else json.loads(result)


check.sequence = 0
PROTOCOL = '''module sample;
domain F=field("bls12-381.fr");
pub protocol Work<C:Field> roles(P,V)(x:C@(P,V),y:C@P)->(value:C@P,ok:bool@V){
  let ok@V=true;return(value=x,ok=ok);
}
'''
PROOF = '''module sample;
protocol Work roles(P,V)(x:bool@(P,V),y:bool@P)->(value:bool@P,ok:bool@V){
  let ok@V=x;return(value=y,ok=ok);
}
pub proof Family=Work{prover P;verifier V;public{x};accept ok;construction authored;}
'''

with case('standalone entry calculation uses ordinary inferred Local results'):
    result = check('''module sample;
      entry fn Twice(x:index){return x+x;}
      pub entry fn Demo(x:index){return Twice(x)+1;}
    ''', entry='Demo', inspect_api=True)
    assert result['status'] == 'checked' and result['entry'] == 'sample::Demo'
    assert {'name': 'sample::Demo', 'kind': 'function'} in result['entries']
    declaration = next(d for d in result['declarations'] if d['name'] == 'sample::Demo')
    assert declaration['kind'] == 'entry' and len(declaration['outputs']) == 1
    public = next(d for d in result['api']['declarations'] if d['name'] == 'sample::Demo')
    assert public['stage'] == 'host' and len(public['outputs']) == 1

with case('generic protocol members parse after owner specialization'):
    check(PROTOCOL + '''entry fn Demo(x:F,y:F){
      let p=Work<F>::Inputs::P{x:x,y:y};
      let v=Work<F>::Inputs::V{x:x};
      return Work<F>::run(Work<F>::Inputs{P:p,V:v});
    }''', entry='Demo')

with case('proof verifier signature exposes candidate data and explicit rejection'):
    result = check(PROOF + '''pub entry fn Demo(public:Family::Public,candidate:Family::Proof){
      let result=Family::verify(public,candidate);
      return match result {Accepted(outputs)=>{true},Rejected()=>{false}};
    }''', entry='Demo', inspect_api=True)
    verifier = next(d for d in result['declarations'] if d['name'] == 'sample::Family::verify')
    assert [p['name'] for p in verifier['inputs']] == ['public', 'proof']
    graph = json.dumps(result['api'])
    assert 'VerifyResult' in graph and 'Rejected' in graph and 'Accepted' in graph

with case('ordinary Local Math and protocol stages refuse Host calls'):
    for declaration in [
        'fn Bad(x:bool){return E(x);}',
        'math fn Bad(x:bool){return E(x);}',
        'protocol Bad roles(P)(x:bool@P)->(y:bool@P){let y@P=E(x);return(y=y);}',
    ]:
        check('module sample; entry fn E(x:bool){return x;}' + declaration,
              refuses='source.stage')
    check(PROTOCOL + 'fn Bad(x:Work<F>::Inputs){return Work<F>::run(x);}',
          refuses='source.stage')

with case('proof specifications resolve generic relations before the outer signature pass'):
    check('''module sample;
      proof Family=Work<F>{prover P;verifier V;public{x};accept ok;
        target claim;construction authored;}
      domain F=field("bls12-381.fr");
      protocol Work<T:Field> roles(P,V)(x:T@(P,V),y:T@P)->(ok:bool@V)
        spec{target claim=Equal<T>(in.x@V,in.y) accept out.ok;}
        {let ok@V=x==x;return(ok=ok);}
      relation Equal<T:Field>(statement x:T,witness y:T){return x==y;}
      entry fn Demo(public:Family::Public,candidate:Family::Proof){
        return Family::verify(public,candidate);}
    ''')

with case('nominal candidates and native result construction remain distinct'):
    check(PROOF + 'entry fn Demo(){return Family::VerifyResult::Rejected();}',
          refuses='source.host-result')
    check(PROOF + '''proof Other=Work{prover P;verifier V;public{x};accept ok;construction authored;}
      entry fn Demo(x:Family::Public,p:Other::Proof){return Family::verify(x,p);}
    ''', refuses='source.type')

with case('entry cycles and unapproved source forms are refused'):
    check('module sample; entry fn Demo(x:bool)->bool{return Demo(x);}',
          refuses='source.cycle')
    for declaration in ['host fn Demo(){return ();}', 'workflow Demo(){return ();}']:
        check('module sample;' + declaration, refuses='source.syntax')
    check(PROTOCOL + 'run Old=Work<F>;', refuses='source.syntax')

counted()
