#!/usr/bin/env python3
"""Propose kernel-checked realization equations for actual constructed subjects.

This module is not a verifier or a receipt issuer. Native re-export and source
contract checking belong to the caller. No input supplies Lean code or meanings.
"""
import argparse
import json
from pathlib import Path
import re

from snapshot import render as render_snapshot, array, primitive, seq

FIELD = '!algebra.field<"bls12-381.fr">'
GROUP = '!algebra.group<"bls12-381.g1">'
STATE = '!local.capability<"transcript:merlin3.bls12-381.fr64be/0">'
INDICES = '!algebra.indices'
SUITE = 'merlin3.bls12-381.fr64be/0'
OBSERVE = 'crypto.exec.indexed_transcript_observe_data'
CHALLENGE = 'crypto.exec.indexed_transcript_challenge'
RECEIVE = 'protocol.receive'


def require(condition, reason):
    if not condition:
        raise ValueError('constructed-realization-' + reason)


def origin_template(encoded):
    """Decode the exact bounded tagged carrier in Contracts/NativeOrigin.cpp."""
    require(isinstance(encoded, str) and len(encoded) <= 4096 and
            re.fullmatch(r'(?:[0-9a-f]{2})+', encoded), 'origin')
    raw = bytes.fromhex(encoded)
    offset = 0

    def item(depth=0):
        nonlocal offset
        require(depth < 5 and offset + 9 <= len(raw), 'origin')
        tag, count = raw[offset], int.from_bytes(raw[offset + 1:offset + 9], 'little')
        offset += 9
        if tag == 0:
            require(offset + count <= len(raw) and count <= 128, 'origin')
            value = raw[offset:offset + count].decode('ascii')
            offset += count
            require(value and all(33 <= ord(c) <= 126 for c in value), 'origin')
            return value
        require(tag == 1 and count <= 64, 'origin')
        return [item(depth + 1) for _ in range(count)]

    value = item()
    require(offset == len(raw) and isinstance(value, list) and len(value) == 5 and
            value[0] == 'zkc.native-origin-template/0' and value[2:4] == [[], []], 'origin')
    return value


def site_label(name):
    return 'label_' + name.encode('ascii').hex() + '_0'


def validate(data, protocol, receive_sites=None):
    """Strict supported metadata/signature profile; state/math are checked by Lean."""
    array(data, 12)
    require(len(array(data[10])) <= 256 and len(array(data[7])) <= 32, 'limit')
    rendered = render_snapshot(data, 'Validation')
    require(len(rendered) <= 2_000_000, 'limit')
    require(protocol in ('schnorr', 'sumcheck'), 'protocol')
    policy = json.loads(data[6])
    require(isinstance(policy, list) and len(policy) == 11 and
            policy[0] == 'zkc.native-proof-policy/0' and policy[1] == data[3] and
            policy[3] == data[4] and policy[4:6] == ['0', SUITE] and
            policy[9:] == ['zkc.framed/0', ''], 'policy')
    fields = 2 if protocol == 'schnorr' else 10
    require(data[8] == ([GROUP] * 2 if protocol == 'schnorr' else [FIELD] * 10) + [STATE]
            and data[9] == ['i1', STATE], 'ports')
    require(policy[7] == [str(i) for i in range(fields)] and
            policy[6] == ['4' if protocol == 'schnorr' else '10'], 'public-binding')
    default_sites = ['commitment', 'response'] if protocol == 'schnorr' else [
        'first0', 'first1', 'first2', 'second0', 'second1', 'second2']
    expected_sites = receive_sites if receive_sites is not None else list(map(site_label, default_sites))
    require(isinstance(expected_sites, list) and len(expected_sites) == len(default_sites) and
            all(isinstance(s, str) for s in expected_sites) and
            len(set(expected_sites)) == len(expected_sites), 'receive-selectors')
    expected_queries = 1 if protocol == 'schnorr' else 2
    require(len(policy[8]) == expected_queries and all(isinstance(p, list) and len(p) == 2
            and all(isinstance(s, str) for s in p) for p in policy[8]), 'draw-selectors')
    handler_names = {handler[0] for handler in data[7]}
    received, observed, queried = [], [], []
    operations = []
    variables = len(data[8])
    for instruction in data[10]:
        if instruction[0] == 'guard':
            require(instruction[1] < variables, 'reference')
            require(protocol == 'sumcheck' and re.fullmatch(r'\{site = "[A-Za-z0-9_]+"\}', instruction[2]), 'guard')
            continue
        if instruction[0] == 'project':
            require(instruction[3] < variables, 'reference')
            require(instruction[1] == [FIELD, STATE] and instruction[2] in (0, 1), 'project')
            variables += 1
            continue
        require(instruction[0] == 'apply', 'instruction')
        op = instruction[1]
        name, attributes, binding, origin, args, results = op
        require(len(instruction[2]) == len(args) and
                all(index < variables for index in instruction[2]), 'reference')
        variables += 1
        operations.append(op)
        path = origin.split('/')
        require(path[0] == data[5] and all(
            re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*:[A-Za-z_][A-Za-z0-9_]*', step)
            and step.split(':')[0] in handler_names for step in path[1:]), 'local-origin')
        if name == RECEIVE:
            match = re.fullmatch(r'\{peer = "([^"]+)", schema = "([^"]+)", site = "([^"]+)"\}', attributes)
            require(match is not None and match[1] == policy[2] and match[2] == match[3]
                    and not binding and not args, 'receive')
            received.append((match[3], op))
            continue
        pure = {
            'algebra.field_add': ([FIELD, FIELD], [FIELD]),
            'algebra.field_subtract': ([FIELD, FIELD], [FIELD]),
            'algebra.field_multiply': ([FIELD, FIELD], [FIELD]),
            'algebra.field_equal': ([FIELD, FIELD], ['i1']),
            'algebra.group_scale': ([GROUP, FIELD], [GROUP]),
            'algebra.group_add': ([GROUP, GROUP], [GROUP]),
            'algebra.group_equal': ([GROUP, GROUP], ['i1']),
        }
        if name in pure:
            require((args, results) == pure[name] and attributes == '{}' and not binding,
                    'arithmetic-metadata')
            require(('group' in name) == (protocol == 'schnorr'), 'arithmetic-domain')
            continue
        require(name in (OBSERVE, CHALLENGE, 'algebra.exec.indices_empty'), 'primitive')
        match = re.fullmatch(r'\{binding = @([A-Za-z_][A-Za-z0-9_]*), parameters = (\[.*\]), site = "(coordinates|transition)"\}', attributes)
        require(match is not None, 'primitive-metadata')
        symbol, parameters, site = match.groups()
        parameters = json.loads(parameters)
        if name == 'algebra.exec.indices_empty':
            require(args == [] and results == [INDICES] and parameters == [] and site == 'coordinates', 'coordinates')
            binding_args, contract = [], 'indices.empty'
        else:
            require(len(parameters) == 1 and site == 'transition', 'primitive-metadata')
            template = origin_template(parameters[0])
            require(template[1] == data[3], 'occurrence-entry')
            event = template[4]
            require(isinstance(event, list) and len(event) == (6 if name == OBSERVE else 7)
                    and event[1] == data[3], 'occurrence')
            if name == OBSERVE:
                require(len(args) == 3 and args[0] == STATE and args[2] == INDICES and
                        args[1] in (FIELD, GROUP) and results == [STATE] and
                        event[0] == 'message' and event[2] == event[3], 'observation')
                binding_args = [SUITE, 'field:bls12-381.fr' if args[1] == FIELD else 'group:bls12-381.g1']
                contract = 'transcript.native.indexed.observe.data'
                observed.append((event, op))
            else:
                require(args == [STATE, INDICES] and results == [FIELD, STATE] and
                        event[0] == 'query' and event[3:] == ['input_' + policy[6][0],
                            'random.bls12-381.fr/0', 'draw', policy[3]], 'challenge')
                binding_args, contract = [SUITE], 'transcript.native.indexed.challenge'
                queried.append((event[2], op))
        expected_binding = ('"local.binding"() <{arguments = ' + json.dumps(binding_args) +
                            ', contract = "' + contract + '", implementation = "", sym_name = "' +
                            symbol + '"}> : () -> ()')
        require(binding == expected_binding, 'binding')
    require(len(data[11]) == 2 and all(index < variables for index in data[11]), 'reference')
    require([s for s, _ in received] == expected_sites, 'receive-order')
    require([op[5] for _, op in received] == ([[GROUP], [FIELD]] if protocol == 'schnorr' else [[FIELD]] * 6), 'receive-types')
    require([s for s, _ in queried] == [p[0] for p in policy[8]], 'challenge-order')
    event_sites = [expected_sites[0], policy[8][0][1], expected_sites[1]] if protocol == 'schnorr' else (
        expected_sites[:3] + [policy[8][0][1]] + expected_sites[3:] + [policy[8][1][1]])
    require([e[2] for e, _ in observed] == event_sites, 'observation-order')
    for event, op in observed:
        delivery = event[2] in [p[1] for p in policy[8]]
        require(event[4:] == ([policy[3], policy[2]] if delivery else [policy[2], policy[3]]), 'observation-role')
        require(op[4][1] == (GROUP if protocol == 'schnorr' and event[2] == expected_sites[0] else FIELD), 'observation-type')
    return {'receives': [op for _, op in received], 'observations': [op for _, op in observed],
            'challenges': [op for _, op in queried], 'operations': operations}


def variable(index):
    return '.there (' * index + '.here' + ')' * index


def operands(indices):
    result = '.nil'
    for index in reversed(indices):
        result = f'.cons ({variable(index)}) ({result})'
    return result


def typed_program(data):
    body = f'.letOp (.pack {seq(data[9])}) ({operands(data[11])}) (.ret .here)'
    for instruction in reversed(data[10]):
        kind = instruction[0]
        if kind == 'apply':
            body = f'.letOp (.primitive ({primitive(instruction[1])})) ({operands(instruction[2])}) (\n{body})'
        elif kind == 'project':
            _, types, index, reference = instruction
            body = f'.letOp (.project {seq(types)} ⟨{index}, by decide⟩) ({operands([reference])}) (\n{body})'
        elif kind == 'guard':
            body = f'.branch ({variable(instruction[1])}) (\n{body}) (.stop .reject)'
        else:
            raise ValueError('constructed-realization-instruction')
    return body


def prelude(data, protocol, namespace):
    source = render_snapshot(data, namespace)
    source = source[:source.index('set_option maxRecDepth')]
    source = source.replace('public import Zkc.Source.Constructed',
                            f'public import Zkc.Protocols.{protocol.title()}.NativeConstruction\n'
                            'public import Zkc.Source.Constructed.Scalar\n'
                            'public import Zkc.Source.Constructed.Execution\npublic import Lean')
    source += '''
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
open Zkc.Source
'''
    source += f'def program : Program language (snapshot.inputs.map scalar) snapshot.outputs :=\n{typed_program(data)}\n'
    source += '''
def imported : Imported snapshot := ⟨program⟩
/-- Admission of the complete actual body, independently of protocol normalization. -/
theorem admitted : snapshot.check = .ok imported := by
  apply snapshot.check_program program
  · decide +kernel
  · decide +kernel

/-- Direct raw execution agrees for all primitive meanings and input values. -/
theorem raw_denotation {I : PIR.Signature} (selected : Meaning I)
    (values : Values (Values selected.Value) (snapshot.inputs.map scalar)) :
    snapshot.denoteRaw selected values = imported.denote selected values :=
  Snapshot.check_denoteRaw admitted selected values

/-- The flat carrier is evaluated without using lowering or typed elaboration. -/
theorem source_denotation {I : PIR.Signature} (selected : Meaning I)
    (values : Values (Values selected.Value) (snapshot.inputs.map scalar)) :
    snapshot.execute selected values = imported.denote selected values :=
  Snapshot.check_execute admitted selected values
'''
    return source


def schnorr(data, namespace, profile):
    source = prelude(data, 'schnorr', namespace)
    source += '''
open Zkc.Protocols.Schnorr
open Construction NativeConstruction
variable {Context F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
'''
    source += 'def occurrences : List Primitive := ' + seq(profile['operations'], primitive) + '\n'
    source += '''
def binding (context : Context) (base key : G) : Binding (OccurrenceContext Context) G :=
  ⟨snapshot.source, snapshot.candidate, ⟨context, snapshot.policy, occurrences⟩, base, key⟩

/-- Every returned value and the actual live transcript are preserved. -/
theorem full_denotation (bound : Binding Context G) (proof : G × F) :
    imported.denote (meaning proof) (inputs bound) =
      .call (bound, proof.1) (fun (challenge : F) =>
        .done (.cons (decide (proof.2 • bound.base = proof.1 + challenge • bound.key))
          (.cons (⟨bound, some proof.1, some challenge, true, some proof.2⟩ :
            Transcript Context F G) .nil))) := by
  simp [imported, program, Imported.denote, Program.denote, Meaning.interpretation,
    meaning, primitive, inputs, scalar, PIR.Proc.bind, Operands.eval, unpack, add_comm]
  rfl


/-- Explicit acceptance projection; the stronger returned-state law is above. -/
theorem projected_denotation (bound : Binding Context G) (proof : G × F) :
    (imported.denote (meaning proof) (inputs bound)).bind (fun reply => .done (result reply)) =
      .call (bound, proof.1) (fun (challenge : F) =>
        .done (some (decide (proof.2 • bound.base = proof.1 + challenge • bound.key)))) := by
  rw [full_denotation]
  rfl
'''
    return source



def sumcheck(data, namespace, profile):
    source = prelude(data, 'sumcheck', namespace)
    source += """
open Zkc.Protocols.Sumcheck
open NativeConstruction
open Zkc.Protocols.AlgebraicRounds (Message)
def schedule : Schedule where
"""
    for name in ('receives', 'observations', 'challenges'):
        source += f'  {name} := ' + seq(profile[name], primitive) + '\n'
    source += """
variable {Context F : Type} [Field F] [DecidableEq F]
def binding (context : Context) (coefficients : Common.Coefficients F) (claim : F) : Binding Context F :=
  ⟨snapshot.source, snapshot.candidate, context, schedule, coefficients, claim⟩

/-- Normalize the actual imported body to the complete full-prefix experiment. -/
theorem full_denotation (context : Context) (coefficients : Common.Coefficients F)
    (claim : F) (proof : Message F × Message F) :
    imported.denote (meaning schedule proof) (inputs (binding context coefficients claim)) =
      experiment (binding context coefficients claim) proof := by
  simp [imported, program, Imported.denote, Program.denote, Meaning.interpretation,
    meaning, primitive, inputs, binding, receiveValue, observe, challenge, schedule,
    scalar, PIR.Proc.bind, Operands.eval, unpack,
    experiment, Common.wireBoundary, Common.wireEvaluate, Common.evaluate,
    horner_evaluate, reordered_boundary]

/-- An explicit observation of the independently proved complete process. -/
theorem projected_denotation (context : Context) (coefficients : Common.Coefficients F)
    (claim : F) (proof : Message F × Message F) :
    (imported.denote (meaning schedule proof) (inputs (binding context coefficients claim))).bind
      (fun reply => .done (result reply)) =
    (experiment (binding context coefficients claim) proof).bind
      (fun reply => .done (result reply)) := by
  rw [full_denotation]
  rfl
"""
    return source

def audit(namespace, names):
    result = f'\nend {namespace}\n\nrun_cmd do\n'
    result += '  for name in [' + ', '.join('`' + namespace + '.' + name for name in names) + '] do\n'
    result += '''    let _ ← Lean.getConstInfo name
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "constructed realization uses unexpected axiom: {axiomName}"
  Lean.logInfo "CONSTRUCTED-REALIZATION-PASS"
'''
    return result


def render(data, protocol, namespace='ConstructedRealization', receive_sites=None):
    profile = validate(data, protocol, receive_sites)
    if protocol == 'schnorr':
        return schnorr(data, namespace, profile) + audit(namespace, ['admitted', 'raw_denotation', 'source_denotation', 'full_denotation', 'projected_denotation'])
    return sumcheck(data, namespace, profile) + audit(namespace, ['admitted', 'raw_denotation', 'source_denotation', 'full_denotation', 'projected_denotation'])



def read_snapshot(path):
    with path.open('rb') as stream:
        raw = stream.read(16_000_001)
    require(len(raw) <= 16_000_000, 'limit')
    depth, quoted, escaped = 0, False, False
    for byte in raw:
        if quoted:
            if escaped:
                escaped = False
            elif byte == 92:
                escaped = True
            elif byte == 34:
                quoted = False
        elif byte == 34:
            quoted = True
        elif byte in (91, 123):
            depth += 1
            require(depth <= 128, 'limit')
        elif byte in (93, 125):
            depth -= 1
    return json.loads(raw)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('snapshot', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--protocol', choices=['schnorr', 'sumcheck'], required=True)
    parser.add_argument('--namespace', default='ConstructedRealization')
    args = parser.parse_args()
    try:
        data = read_snapshot(args.snapshot)
        args.output.write_text(render(data, args.protocol, args.namespace))
    except (ValueError, OSError) as error:
        raise SystemExit(str(error)) from error


if __name__ == '__main__':
    main()
