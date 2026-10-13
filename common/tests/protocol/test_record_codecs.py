"""Record byte provenance, ordered parsing and codec lifetime through the Host."""
import json
import pytest
from source_modules import library_modules
from test_constructions import SOURCE

CODEC = '''
type Bytes=builtin("bytes");
fn empty()->Bytes=primitive("bytes.empty");
fn concat(a:Bytes,b:Bytes)->Bytes=primitive("bytes.concat");
fn slice(b:Bytes,start:index,count:index)->Bytes=primitive("bytes.slice");
fn length(b:Bytes)->index=primitive("bytes.length");
fn field_bytes(f:F)->Bytes=primitive("encoding.field_be");
fn field_read(b:Bytes)->(bool,F)=primitive("encoding.field_from_be");
interface Codec {
  type Record:Copy+Drop;
  fn initialize(layout:())->Record effects(stop, opaque);
  fn write(r:Record)->Bytes effects(stop, opaque);
  fn finish(r:Record,proof:Bytes)->() effects(stop, opaque);
  fn encode(r:Record,value:(F,F))->(Record,Bytes) effects(stop, opaque);
  fn receive(r:Record,proof:Bytes)->(Record,(index,index)) effects(stop, opaque);
}
module Packing:Codec {
  type Record:Copy+Drop=(Bytes,index);
  fn initialize(layout:())->Record{return Record((empty(),0));}
  fn write(r:Record)->Bytes{let (b,n)=unpack(r);return b;}
  fn finish(r:Record,proof:Bytes)->(){let(b,n)=unpack(r);require length(proof)==n;return ();}
  fn encode(r:Record,value:(F,F))->(Record,Bytes){
    let(b,n)=unpack(r);
    let chunk=concat(field_bytes(value.0),field_bytes(value.1));
    return (Record((concat(b,chunk),n+64)),chunk);
  }
  fn receive(r:Record,proof:Bytes)->(Record,(index,index)){
    let(b,n)=unpack(r);return(Record((b,n+64)),(n,64));
  }
}
construction Encoded for Round<F> {
  BASE
  format Packing;
  on encode {commitment,response}(r,value){return Packing::encode(r,value);}
  on receive {commitment,response}(r,proof){return Packing::receive(r,proof);}
  on decode {commitment,response}(chunk){
    let(ok,a)=field_read(slice(chunk,0,32));require ok;
    let(ok,b)=field_read(slice(chunk,32,32));require ok;
    return(a,b);
  }
  on wire {commitment,response}(t,chunk){return t;}
}
proof Packed=Round<F>{prover P;verifier V;public{public,rounds};accept ok;
  construction Encoded;}
'''


@pytest.mark.parametrize('completion', [False, True])
@pytest.mark.parametrize('native', [False, True])
@pytest.mark.parametrize('nested', [False, True])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_record_codec_execution(toolchain, journal, directory, native, nested, flags, completion):
    text = SOURCE.replace('STATE', '(index,index)').replace('INITIAL', '(0,0)')
    text = text.replace('LOOP_START', 'for _ in 0..rounds roles(P,V) max 2 {\n' * 2 if nested else '')
    text = text.replace('LOOP_END', '}}' if nested else '')
    extra = CODEC
    if completion:
        text = text.replace('public:T@(P,V),', 'go:bool@(P,V),public:T@(P,V),')
        text = text.replace('->(ok:bool@V){', '->(ok:bool@V) completes{')
        text = text.replace('let first=send P->V((secret,secret));',
                            'let first=send P->V((secret,secret));\n'
                            'let ()=finish_if @P(go)();\n'
                            'let _=finish_if @V(go)(ok=true);')
        text = text.replace('public{public,rounds}', 'public{go,public,rounds}')
        extra = extra.replace('public{public,rounds}', 'public{go,public,rounds}')
    base = ('base fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);' if native else
            'base Derived<F,Provider>;')
    source = directory / 'main.zkc'
    source.write_text(text + extra.replace('BASE', base))
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile',
                             f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                             'sample::Packed', f'--output={package}', *flags])
    public_values = {'public': '5', 'rounds': '2'}
    if completion:
        public_values['go'] = True
    public = journal.write('public.json', public_values)
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}']
    if not native:
        args.append('--allow-authored')
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                             f'--witness={witness}', f'--output={proof}'])
    assert not produced['execution']['cleanup_errors']
    expected_length = 64 if completion else 128 * (4 if nested else 1)
    assert len(proof.read_bytes()) == expected_length
    assert proof.read_bytes()[:64] == (7).to_bytes(32, 'big') * 2
    verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert verified['status'] == 'accepted'
    assert not verified['execution']['cleanup_errors']
    if completion:
        public_values['go'] = False
        public.write_text(json.dumps(public_values))
        journal.json([toolchain.runtime, '--json', 'prove', *args,
                      f'--witness={witness}', f'--output={proof}'])
        assert len(proof.read_bytes()) == 128 * (4 if nested else 1)
        assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                             f'--proof={proof}'])['status'] == 'accepted'
    if nested:
        public_values['rounds'] = '0'
        public.write_text(json.dumps(public_values))
        journal.json([toolchain.runtime, '--json', 'prove', *args,
                      f'--witness={witness}', f'--output={proof}'])
        assert proof.read_bytes() == b''
        assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                             f'--proof={proof}'])['status'] == 'accepted'


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_record_codec_external_schnorr(toolchain, journal, directory, flags):
    from pathlib import Path
    from test_source_transcript import PUBLIC, VECTOR
    root = Path(__file__).resolve().parents[3]
    source = directory / 'main.zkc'
    source.write_text((root / 'common/tests/fixtures/constructions/schnorr.zkc').read_text() + '''
    use zkc::proof::{Stream};
    use zkc::encoding as encoding;
    construction External for Fixed {
      base Derived;
      format Stream;
      on encode commitment(r,value){return Stream::append(r,encoding::group_compressed(value));}
      on encode response(r,value){return Stream::append(r,encoding::field_be(value));}
      on receive commitment(r,proof){return Stream::take(r,48);}
      on receive response(r,proof){return Stream::take(r,32);}
      on decode commitment(chunk){let(valid,value)=encoding::group_from_compressed<G>(chunk);require valid;return value;}
      on decode response(chunk){let(valid,value)=encoding::field_from_be<G::Scalar>(chunk);require valid;return value;}
    }
    proof ExternalProof=Fixed{prover P;verifier V;public{tag,session,base,point};accept accepted;construction External;}
    ''')
    modules = {'sample': source, 'spongefish': root / 'libraries/spongefish/lib.zkc'}
    modules.update({f'zkc::{name}': root / f'libraries/zkc/{name}.zkc'
                    for name in ['bytes', 'encoding', 'shake128', 'proof']})
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             *library_modules('spongefish', 'sumcheck', overrides=modules),
                             'sample::ExternalProof', f'--output={package}', *flags])
    public = journal.write('public.json', PUBLIC)
    witness = journal.write('witness.json', {'scalar': '7', 'nonce': '11'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}', '--allow-authored']
    proof = directory / 'proof.bin'
    produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                             f'--witness={witness}', f'--output={proof}'])
    assert proof.read_bytes() == VECTOR
    assert not produced['execution']['cleanup_errors']
    accepted = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert accepted['status'] == 'accepted'
    oracle = toolchain.driver('spongefish_schnorr')
    reference = directory / 'reference'
    journal.json([oracle, 'export', reference])
    assert (reference / 'fixed.bin').read_bytes() == VECTOR
    assert journal.json([oracle, 'verify', proof])['accepted']
    assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                         f'--proof={reference / "reference.bin"}'])['status'] == 'accepted'
    modulus = int('73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001', 16)
    for name, payload, reason, work in [
        ('point', b'\xff' * 48 + VECTOR[48:], 'artifact-stopped', 564),
        ('scalar', VECTOR[:48] + modulus.to_bytes(32, 'big'), 'artifact-stopped', 808),
        ('false', VECTOR[:48] + bytes(32), 'artifact-rejected', 842),
        ('truncated', VECTOR[:-1], 'refused:bytes-bounds', 808),
        ('trailing', VECTOR + b'\0', 'artifact-stopped', 842),
    ]:
        candidate = directory / f'{name}.bin'
        candidate.write_bytes(payload)
        rejected = journal.json([toolchain.runtime, '--json', 'verify', *args,
                                 f'--proof={candidate}'], refuses=reason)
        assert rejected['execution']['external_work'] == work
        assert rejected['execution']['bytes'] == len(payload)
        assert not rejected['execution']['cleanup_errors']
        assert not journal.json([oracle, 'verify', candidate])['accepted']

GROUPED = '''module sample;
domain F=field("bls12-381.fr");
type Bytes=builtin("bytes");
fn empty()->Bytes=primitive("bytes.empty");
fn concat(a:Bytes,b:Bytes)->Bytes=primitive("bytes.concat");
fn length(b:Bytes)->index=primitive("bytes.length");
fn field_bytes(f:F)->Bytes=primitive("encoding.field_be");
fn field_read(b:Bytes)->(bool,F)=primitive("encoding.field_from_be");
interface Transcript {type State:Copy+Drop;fn initialize()->State effects(stop, opaque);}
module History:Transcript{type State:Copy+Drop=();fn initialize()->State{return State(());}}
interface Codec {
  type Record:Copy+Drop;
  fn initialize(rounds:index)->Record effects(stop, opaque);
  fn write(r:Record)->Bytes effects(stop, opaque);
  fn finish(r:Record,proof:Bytes)->() effects(stop, opaque);
  fn encode(r:Record,value:(F,F))->(Record,(Bytes,Bytes)) effects(stop, opaque);
  fn receive(r:Record,proof:Bytes)->(Record,((index,index),(index,index))) effects(stop, opaque);
}
module Grouped:Codec{
  type Record:Copy+Drop=(Bytes,Bytes,index,index);
  fn initialize(rounds:index)->Record{return Record((empty(),empty(),0,rounds));}
  fn write(r:Record)->Bytes{let(l,r,i,n)=unpack(r);return concat(l,r);}
  fn finish(r:Record,proof:Bytes)->(){
    let(l,r,i,n)=unpack(r);require i==n;require length(proof)==n*64;return ();
  }
  fn encode(r:Record,value:(F,F))->(Record,(Bytes,Bytes)){
    let(l,r,i,n)=unpack(r);let a=field_bytes(value.0);let b=field_bytes(value.1);
    return(Record((concat(l,a),concat(r,b),i+1,n)),(a,b));
  }
  fn receive(r:Record,proof:Bytes)->(Record,((index,index),(index,index))){
    let(l,r,i,n)=unpack(r);return(Record((l,r,i+1,n)),((i*32,32),((n+i)*32,32)));
  }
}
protocol Rounds roles(P,V)(rounds:index@(P,V),public:F@(P,V),secret:F@P,
                         challenges:Random<F>@V)->(ok:bool@V){
  let spare@P=Grouped::initialize(rounds);
  let unused@P=Grouped::write(spare);
  let mut accepted@V=true;
  for _ in 0..rounds roles(P,V) max 4 {
    #[site(pair)] let actual=send P->V((secret+public,secret));
    require @V(actual.0==actual.1+public);
    #[site(challenge)] let c=challenges.draw();
    #[site(delivery)] let received=send V->P(c);
    accepted=actual.0==actual.1+public;
  }
  return accepted;
}
construction Packed for Rounds{
  transcript History;replace challenges;format Grouped(rounds);
  on start(t,public){return t;}
  on message pair(t,value){return t;}
  on message delivery(t,value){return t;}
  on query challenge(t){return(t,1);}
  on encode pair(r,value){return Grouped::encode(r,value);}
  on receive pair(r,proof){return Grouped::receive(r,proof);}
  on decode pair(chunks:(Bytes,Bytes)){
    let(valid,a)=field_read(chunks.0);require valid;
    let(valid,b)=field_read(chunks.1);require valid;return(a,b);
  }
  on wire pair(t,chunks){return t;}
}
proof Demo=Rounds{prover P;verifier V;public{rounds,public};accept ok;construction Packed;}
'''


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_grouped_records_select_disjoint_round_chunks(toolchain, journal, directory, flags):
    source = directory / 'main.zkc'
    source.write_text(GROUPED)
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Demo', f'--output={package}', *flags])
    public = journal.write('public.json', {'rounds': '3', 'public': '5'})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}', '--allow-authored']
    proof = directory / 'proof.bin'
    journal.json([toolchain.runtime, '--json', 'prove', *args,
                  f'--witness={witness}', f'--output={proof}'])
    expected = (12).to_bytes(32, 'big') * 3 + (7).to_bytes(32, 'big') * 3
    assert proof.read_bytes() == expected
    verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
    assert verified['status'] == 'accepted'
    work = []
    for round in range(3):
        # R[] follows all of L[]. Parsing one round must not decode later R's.
        malformed = bytearray(expected)
        malformed[(3+round)*32:(4+round)*32] = b'\xff' * 32
        proof.write_bytes(malformed)
        rejected = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'],
                                 refuses='artifact-stopped')
        work.append(rejected['execution']['instructions'])
        assert rejected['execution']['iterations'] == round + 1
        assert not rejected['execution']['cleanup_errors']
    assert work[0] < work[1] < work[2] < verified['execution']['instructions']
    public.write_text(json.dumps({'rounds': '0', 'public': '5'}))
    journal.json([toolchain.runtime, '--json', 'prove', *args,
                  f'--witness={witness}', f'--output={proof}'])
    assert proof.read_bytes() == b''
    assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                         f'--proof={proof}'])['status'] == 'accepted'

@pytest.mark.parametrize('mutation,reason', [
    ('ingress', 'native-proof-codec-ingress'),
    ('slice-source', 'native-proof-codec-operand'),
    ('slice-body', 'native-proof-codec-slice'),
    ('decode-chunks', 'native-proof-codec-operand'),
    ('wire-chunks', 'native-proof-codec-wire-operand'),
    ('record-reset', 'native-proof-codec-record-chain'),
    ('raw-escape', 'native-proof-codec-internal-use'),
    ('range-escape', 'native-proof-codec-internal-use'),
    ('chunk-escape', 'native-proof-codec-internal-use'),
    ('record-count', 'native-proof-codec-internal-use'),
    ('missing-finish', 'native-proof-codec-exit'),
    ('stale-finish', 'native-proof-codec-finalizer-operand'),
    ('challenge-order', 'native-proof-codec-order'),
    ('coverage', 'native-proof-codec-coverage'),
    ('missing-wire', 'native-proof-codec-wire-operand'),
    ('stop-before-observe', 'native-proof-codec-order'),
])
def test_record_codec_admission_checks_actual_program(toolchain, journal, directory, mutation, reason):
    from test_constructions import reject_deployment
    source = directory / 'main.zkc'
    source.write_text(GROUPED)
    package = directory / 'proof.zkpkg'
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', 'sample::Demo', f'--output={package}'])
    deployment = json.loads(json.loads(package.read_text())['artifact'])
    program = json.loads(deployment[4])
    codec = deployment[2][6][7]
    encode, receive, decode, wire, slicer, origins = codec[6][0]
    verifier = program[3][1]
    body = verifier[6]
    initialize = next(op for op in body if op[0] == 'local' and op[2] == codec[2])
    loop = next(op for op in body if op[0] == 'loop')
    steps = loop[5]
    selected = {op[2]: op for op in steps if op[0] == 'local'}
    if mutation == 'ingress':
        selected[receive][3][-1] = selected[receive][3][0]
    elif mutation == 'slice-source':
        selected[slicer][3][0] = selected[receive][3][0]
    elif mutation == 'slice-body':
        helper = next(f for f in program[2] if f[1] == slicer)
        helper[4][0][4][1] = helper[2][2][0]  # length instead of offset
    elif mutation == 'decode-chunks':
        selected[decode][3].reverse()
    elif mutation == 'wire-chunks':
        selected[wire][3].reverse()
    elif mutation == 'record-reset':
        selected[receive][3][2] = selected[receive][3][3]
    elif mutation.endswith('escape'):
        ty = 'index@native.index/0' if mutation == 'range-escape' else 'bytes@native.bytes/0'
        value = (verifier[4][-1][0] if mutation == 'raw-escape' else
                 selected[receive][4][-1] if mutation == 'range-escape' else selected[slicer][4][0])
        # A typed, independently admissible ordinary function must not receive
        # internal codec values, even if its result is unused.
        program[2].append(['function', 'leak', [['input', ty]], [], [['return', []]], ['leak', []]])
        steps.insert(steps.index(selected[decode]) + 1, ['local', 'leak', 'leak', [value], []])
    elif mutation == 'record-count':
        loop[2][1] = initialize[4][2]
    elif mutation == 'missing-finish':
        body.remove(next(op for op in body if op[0] == 'local' and op[2] == codec[4]))
    elif mutation == 'stale-finish':
        finish = next(op for op in body if op[0] == 'local' and op[2] == codec[4])
        finish[3][2] = initialize[4][2]
    elif mutation == 'challenge-order':
        functions = {f[1]: f for f in program[2]}
        query = next(row[0] for row in deployment[2][6][6] if len(functions[row[0]][3]) == 1)
        # Source adapters use the same implementation marker for both event
        # kinds. Locate the challenge by its single-result callable signature.
        query_call = selected[query]
        steps.remove(query_call)
        steps.insert(steps.index(selected[decode]) + 1, query_call)
    elif mutation == 'stop-before-observe':
        program[2].append(['function', 'stop_here', [], [],
                           [['stop', 'stop_here', 'reject']], ['stop_here', []]])
        steps.insert(steps.index(selected[decode]) + 1, ['local', 'stop_here', 'stop_here', [], []])
    elif mutation == 'coverage':
        origins[1] = origins[0]
    elif mutation == 'missing-wire':
        steps.remove(selected[wire])
    deployment[4] = json.dumps(program)
    reject_deployment(toolchain, journal, directory, deployment, mutation, reason)

@pytest.mark.parametrize('go', [False, True])
@pytest.mark.parametrize('flags', [[], ['--release-storage']])
def test_empty_record_and_state_keep_conditional_finalization(toolchain, journal, directory, go, flags):
    source = directory / 'main.zkc'
    source.write_text('''module sample;
    domain F=field("bls12-381.fr");
    type Bytes=builtin("bytes");
    fn empty()->Bytes=primitive("bytes.empty");
    fn length(b:Bytes)->index=primitive("bytes.length");
    interface Transcript {type State:Copy+Drop;fn initialize()->State effects(stop, opaque);}
    module History:Transcript {type State:Copy+Drop=();fn initialize()->State{return State(());}}
    interface Codec {type Record:Copy+Drop;fn initialize(x:())->Record effects(stop, opaque);
      fn write(r:Record)->Bytes effects(stop, opaque);fn finish(r:Record,proof:Bytes)->() effects(stop, opaque);}
    module Empty:Codec {type Record:Copy+Drop=();fn initialize(x:())->Record{return Record(());}
      fn write(r:Record)->Bytes{return empty();}
      fn finish(r:Record,proof:Bytes)->(){require length(proof)==0;return ();}}
    protocol End roles(P,V)(go:bool@(P,V),challenges:Random<F>@V)->(ok:bool@V) completes {
      let ()=finish_if @P(go)();let _=finish_if @V(go)(ok=true);return true;
    }
    construction Closed for End {transcript History;replace challenges;format Empty;on start(t){return t;}}
    proof Demo=End{prover P;verifier V;public{go};accept ok;construction Closed;}
    ''')
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Demo', f'--output={package}', *flags])
    public = journal.write('public.json', {'go': go})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}', '--allow-authored']
    proof = directory / 'proof.bin'
    journal.json([toolchain.runtime, '--json', 'prove', *args, f'--output={proof}'])
    assert proof.read_bytes() == b''
    assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                         f'--proof={proof}'])['status'] == 'accepted'
    proof.write_bytes(b'\0')
    journal.json([toolchain.runtime, '--json', 'verify', *args,
                  f'--proof={proof}'], refuses='artifact-stopped')
    if go and not flags:
        import copy
        from test_constructions import reject_deployment
        original = json.loads(json.loads(package.read_text())['artifact'])
        for name, reason in [('branch', 'native-proof-codec-finalizer-body'),
                             ('condition', 'native-proof-codec-finalizer-operand'),
                             ('omission', 'native-proof-codec-exit')]:
            deployment = copy.deepcopy(original)
            candidate = json.loads(deployment[4])
            codec = deployment[2][6][7]
            validator = candidate[3][1]
            finalizer = next(op for op in validator[6] if op[0] == 'local' and op[2] == codec[8])
            if name == 'branch':
                function = next(f for f in candidate[2] if f[1] == codec[8])
                branch = function[4][0]
                branch[4], branch[5] = branch[5], branch[4]
            elif name == 'condition':
                candidate[2].append(['function', 'other_condition', [], ['bool@native.bool/0'],
                                     [['bool_constant', 'constant', 'v', False], ['return', ['v']]],
                                     ['other_condition', []]])
                validator[6].insert(validator[6].index(finalizer),
                                    ['local', 'other', 'other_condition', [], ['other']])
                finalizer[3][0] = 'other'
            else:
                validator[6].remove(finalizer)
            deployment[4] = json.dumps(candidate)
            reject_deployment(toolchain, journal, directory, deployment, name, reason)
        # A zero-slot writer has no Record operand with which to identify it.
        # Its result still must be the final hidden proof returned by this exit.
        deployment = copy.deepcopy(original)
        candidate = json.loads(deployment[4])
        codec = deployment[2][6][7]
        producer = candidate[3][0]
        conditional = next(op for op in producer[6] if op[0] == 'local' and op[2] == codec[7])
        producer[6][-1][1][-1] = conditional[4][0]
        deployment[4] = json.dumps(candidate)
        reject_deployment(toolchain, journal, directory, deployment,
                          'zero-record-write-result', 'native-proof-codec-exit')

@pytest.mark.parametrize('wire', [False, True])
def test_wire_observation_uses_original_bytes_before_permissive_decode(toolchain, journal, directory, wire):
    # Deliberately permissive framing: decode ignores one leading byte. Only an
    # explicit wire observation makes that byte contribute to the challenge.
    text = SOURCE.replace('STATE', 'Bytes').replace('INITIAL', 'empty()')
    text = text.replace('LOOP_START', '').replace('LOOP_END', '')
    text = text.replace('fn draw(t:State)->(State,T) effects(stop, opaque);',
                        'fn draw(t:State)->(State,T) effects(stop, opaque);fn wire(t:State,b:Bytes)->State effects(stop, opaque);')
    text = text.replace('return(t,1);', 'return(t,scalar_from_bytes(unpack(t)));')
    text = text.replace('fn draw(t:State)->(State,F){',
                        'fn wire(t:State,b:Bytes)->State{return State(b);}\n  fn draw(t:State)->(State,F){')
    extra = CODEC.replace('BASE', 'base Derived<F,Provider>;')
    extra = extra.replace('let chunk=concat(field_bytes(value.0),field_bytes(value.1));',
                          'let chunk=concat(append(empty(),0),concat(field_bytes(value.0),field_bytes(value.1)));')
    extra = extra.replace('n+64', 'n+65').replace('(n,64)', '(n,65)')
    extra = extra.replace('slice(chunk,0,32)', 'slice(chunk,1,32)').replace('slice(chunk,32,32)', 'slice(chunk,33,32)')
    extra = extra.replace('on wire {commitment,response}(t,chunk){return t;}',
                          'on wire {commitment,response}(t,chunk){return Provider::wire(t,chunk);}' if wire else '')
    source = directory / 'main.zkc'
    source.write_text(text + extra + '''
      fn append(b:Bytes,byte:index)->Bytes=primitive("bytes.append");
      fn scalar_from_bytes(b:Bytes)->F=primitive("encoding.field_reduce_be");
    ''')
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Packed', f'--output={package}'])
    public = journal.write('public.json', {'public': '5', 'rounds': '2'})
    witness = journal.write('witness.json', {'secret': '7'})
    args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}', '--allow-authored']
    proof = directory / 'proof.bin'
    journal.json([toolchain.runtime, '--json', 'prove', *args,
                  f'--witness={witness}', f'--output={proof}'])
    assert journal.json([toolchain.runtime, '--json', 'verify', *args,
                         f'--proof={proof}'])['status'] == 'accepted'
    changed = bytearray(proof.read_bytes())
    changed[0] = 1
    proof.write_bytes(changed)
    result = journal.json([toolchain.runtime, '--json', 'verify', *args,
                           f'--proof={proof}'], refuses='artifact-rejected' if wire else None)
    assert result['status'] == ('refused' if wire else 'accepted')
    # Finish checks framing even if the mathematical result is already false.
    proof.write_bytes(changed + b'\0')
    journal.json([toolchain.runtime, '--json', 'verify', *args,
                  f'--proof={proof}'], refuses='artifact-stopped')


@pytest.mark.parametrize('mutation,reason', [
    ('record-reset', 'native-proof-codec-record-chain'),
    ('wire-chunks', 'native-proof-codec-wire-operand'),
    ('chunk-escape', 'native-proof-codec-internal-use'),
    ('stale-write', 'native-proof-codec-finalizer-operand'),
    ('wrong-result', 'native-proof-codec-finalizer-operand'),
    ('result-escape', 'native-proof-codec-internal-use'),
    ('stop-before-observe', 'native-proof-codec-order'),
])
def test_record_codec_checks_producer_program(toolchain, journal, directory, mutation, reason):
    from test_constructions import reject_deployment
    source = directory / 'main.zkc'
    source.write_text(GROUPED)
    package = directory / 'proof.zkpkg'
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', 'sample::Demo', f'--output={package}'])
    deployment = json.loads(json.loads(package.read_text())['artifact'])
    program = json.loads(deployment[4])
    codec = deployment[2][6][7]
    encode, receive, decode, wire, slicer, origins = codec[6][0]
    producer = program[3][0]
    body = producer[6]
    initialize = next(op for op in body if op[0] == 'local' and op[2] == codec[2])
    loop = next(op for op in body if op[0] == 'loop')
    steps = loop[5]
    selected = {op[2]: op for op in steps if op[0] == 'local'}
    write = next(op for op in reversed(body) if op[0] == 'local' and op[2] == codec[3])
    if mutation == 'record-reset':
        selected[encode][3][2] = selected[encode][3][3]
    elif mutation == 'wire-chunks':
        selected[wire][3].reverse()
    elif mutation in ['chunk-escape', 'result-escape']:
        program[2].append(['function', 'leak', [['input', 'bytes@native.bytes/0']], [],
                           [['return', []]], ['leak', []]])
        target = steps if mutation == 'chunk-escape' else body
        anchor = selected[wire] if mutation == 'chunk-escape' else write
        value = selected[encode][4][-1] if mutation == 'chunk-escape' else write[4][0]
        target.insert(target.index(anchor) + 1, ['local', 'leak', 'leak', [value], []])
    elif mutation == 'stale-write':
        write[3][2] = initialize[4][2]
    elif mutation == 'wrong-result':
        body[-1][1][-1] = initialize[4][0]
    elif mutation == 'stop-before-observe':
        program[2].append(['function', 'stop_here', [], [],
                           [['stop', 'stop_here', 'reject']], ['stop_here', []]])
        steps.insert(steps.index(selected[wire]) + 1, ['local', 'stop_here', 'stop_here', [], []])
    deployment[4] = json.dumps(program)
    reject_deployment(toolchain, journal, directory, deployment, mutation, reason)


@pytest.mark.parametrize('native', [False, True])
@pytest.mark.parametrize('flags', [[], ['--release-storage']])
@pytest.mark.parametrize('roles', ['P,V', 'V'])
def test_codec_record_crosses_event_free_protocol_loop(toolchain, journal, directory, native, flags,
                                                      roles):
    text = SOURCE.replace('STATE', '(index,index)').replace('INITIAL', '(0,0)')
    text = text.replace('LOOP_START', '').replace('LOOP_END', '')
    text = text.replace(
        '#[site(challenge)]',
        f'for _ in 0..rounds roles({roles}) max 2 {{'
        'let keep@V=allowed(rounds);accepted=accepted && keep;}'
        '#[site(challenge)]')
    text = text.replace('accepted=last.0==first.0+c;', 'accepted=accepted && last.0==first.0+c;')
    text += '\nfn allowed(v:index)->bool{return v==2;}'
    base = ('base fiat_shamir("merlin3.bls12-381.fr64be/0",challenges);' if native else
            'base Derived<F,Provider>;')
    source = directory / 'main.zkc'
    source.write_text(text + CODEC.replace('BASE', base))
    package = directory / 'proof.zkpkg'
    compiled = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                             f'--module=sample={source}', 'sample::Packed', f'--output={package}', *flags])
    deployment = json.loads(json.loads(package.read_text())['artifact'])
    program = json.loads(deployment[4])
    loops = [any(op[0] == 'loop' for op in participant[6]) for participant in program[3]]
    assert loops == [roles == 'P,V', True]
    witness = journal.write('witness.json', {'secret': '7'})
    for rounds in [0, 2]:
        public = journal.write(f'public-{rounds}.json', {'public': '5', 'rounds': str(rounds)})
        args = [f'--package={package}', f'--sha256={compiled["package_sha256"]}', f'--public={public}']
        if not native:
            args.append('--allow-authored')
        proof = directory / f'proof-{rounds}.bin'
        produced = journal.json([toolchain.runtime, '--json', 'prove', *args,
                                 f'--witness={witness}', f'--output={proof}'])
        assert len(proof.read_bytes()) == 128
        assert not produced['execution']['cleanup_errors']
        verified = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])
        assert verified['status'] == 'accepted'
        assert not verified['execution']['cleanup_errors']
