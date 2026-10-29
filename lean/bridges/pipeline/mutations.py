"""Generic mutation kinds.

A kind is a structural edit applied to whatever an export contains: never to a
compiler-generated symbol. Each kind states its stage (the check that must
reject it), the property the edit violates, where it applies and the outcome
it expects. `targets` returns one mutated copy per applicable site; an empty
list means the kind is not applicable to this export, which a report states as
such and never counts as a refusal. The driver then verifies that every copy
differs from the original and still renders, so that a refusal is the rule's
and not a malformed input's.

Stages:
  construction  the constructed participant export, checked by
                `Zkc.Construction.checkCompiled` (structure and occurrence provenance);
                the expected outcome is a refusal code, and whether the
                construction rule alone accepts it;
  connection    the complete source-to-participant proposition, checked by the
                default typed derivation builder. The actual export must have
                a kernel-checked connection; a mutation must trigger a specific
                static alignment refusal, never a timeout or unrelated error.
                This is a method-refusal control, not a counterexample theorem;
  native        the constructed candidate MLIR, checked by the native
                `protocol-constructed-participant` before any export;
  lowering      the `zkc.program/0` validator program, checked by the Lean
                lowering rule `Zkc.Executable.checkLowering`; a refusal of any
                reason, or acceptance for a change the rule does not read;
  helpers       a local function of a called helper in the validator program,
                checked by the Lean helper rule `Zkc.Executable.checkHelpers`
                against the admitted program's checked helper of its name; a
                site applies where the rule accepts the actual helper, and the
                lowering rule, which reads a helper body only for its sorts and
                its freedom from transcript operations, accepts the copy.
"""

import copy
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import decode_tree, encode_tree  # noqa: E402

OBSERVE = "transcript.native.indexed.observe.data"
CHALLENGE = "transcript.native.indexed.challenge"
TRANSCRIPT_CONTRACTS = ("transcript.native.indexed.observe.data", "transcript.native.indexed.challenge")


@dataclass(frozen=True)
class Kind:
    """A mutation kind. `expected` is the refusal the kind targets; a construction
    kind is accepted when its stage's rule refuses it, and the actual code is
    recorded. Connection controls require a static alignment refusal from the
    proof-producing method. `construction_accepts` independently checks that the
    export still has valid transcript wiring and occurrence provenance."""
    name: str
    stage: str
    property: str
    expected: str
    construction_accepts: bool = False

    @property
    def refusing_rule(self):
        return self.expected.split("-", 1)[0] + "-"


KINDS = {}


def kind(name, stage, property_, expected, construction_accepts=False):
    def register(function):
        KINDS[name] = (Kind(name, stage, property_, expected, construction_accepts), function)
        return function
    return register


# ---------------------------------------------------------------------------
# The constructed participant export

def bound(item, contract):
    return item[0] == "exec.apply" and len(item[2]) == 3 and item[2][0] == contract


def nested(instructions):
    for item in instructions:
        yield item
        for region in item[5]:
            yield from nested(region[1])


def regions(instructions):
    """Each instruction list: the top level, then every region body in program order."""
    yield instructions
    for item in instructions:
        for region in item[5]:
            yield from regions(region[1])


def loops(instructions, scope):
    """Each loop with the number of exported references in scope at it: its
    block arguments are the index at `scope`, then the carried values."""
    for item in instructions:
        if item[0] == "protocol.loop":
            yield item, scope
            arguments, body, _ = item[5][0]
            yield from loops(body, scope + len(arguments))
        scope += len(item[4])


def environments(exported):
    """The exported types in scope at each instruction, by instruction identity:
    the inputs and earlier results, and in a loop body the loop's block
    arguments after the environment at the loop."""
    scopes = {}

    def visit(instructions, environment):
        for item in instructions:
            scopes[id(item)] = list(environment)
            for arguments, body, _ in item[5]:
                visit(body, environment + list(arguments))
            environment = environment + list(item[4])
    visit(exported[7], list(exported[5]))
    return scopes


def template_tree(item):
    return decode_tree(bytes.fromhex(dict(item[1])["parameters"][1][0]))[0]


def set_template(item, tree):
    dict(item[1])["parameters"][1][0] = encode_tree(tree).hex()


def mutated(exported, change):
    """Copies of the export, one per site `change` edits in the copy's instructions."""
    results = []
    site = 0
    while True:
        value = copy.deepcopy(exported)
        if not change(value, site):
            return results
        results.append(value)
        site += 1


def first_only(edit):
    """A change that edits only the first applicable site."""
    def change(value, site):
        return site == 0 and edit(value)
    return change


@kind("observe-reads-input", "construction", "an observation absorbs the message it receives",
      "construction-observe")
def observe_reads_input(exported):
    def edit(value):
        found = next((item for item in nested(value[7]) if bound(item, OBSERVE)), None)
        if found is None:
            return False
        scope = environments(value)[id(found)]
        replacement = next((index for index, ty in enumerate(value[5])
                            if ty == scope[found[3][1]] and index != found[3][1]), None)
        if replacement is None:
            return False
        found[3][1] = replacement
        return True
    return mutated(exported, first_only(edit))


@kind("observe-repeats-value", "construction", "each observation absorbs its own message",
      "construction-observe")
def observe_repeats_value(exported):
    def edit(value):
        scopes = environments(value)
        found = [item for item in nested(value[7]) if bound(item, OBSERVE)]
        for index, later in enumerate(found):
            for earlier in found[:index]:
                if earlier[3][1] != later[3][1] and earlier[3][1] < len(scopes[id(later)]) \
                        and scopes[id(earlier)][earlier[3][1]] == scopes[id(later)][later[3][1]]:
                    later[3][1] = earlier[3][1]
                    return True
        return False
    return mutated(exported, first_only(edit))


@kind("challenge-reads-host", "construction", "a challenge reads the transcript after the observations before it",
      "construction-challenge")
def challenge_reads_host(exported):
    host = len(exported[5]) - 1

    def edit(value):
        found = next((item for item in nested(value[7]) if bound(item, CHALLENGE)), None)
        if found is None or found[3][0] == host:
            return False
        found[3][0] = host
        return True
    return mutated(exported, first_only(edit))


@kind("challenge-names-delivery", "construction", "a challenge is bound to its query site (domain separation)",
      "construction-challenge-site")
def challenge_names_delivery(exported):
    validator = exported[3][3]

    def edit(value):
        deliveries = [item for item in nested(value[7]) if bound(item, OBSERVE)
                      and template_tree(item)[4][4] == validator]
        challenge = next((item for item in nested(value[7]) if bound(item, CHALLENGE)), None)
        if not deliveries or challenge is None:
            return False
        tree = template_tree(challenge)
        site = template_tree(deliveries[0])[4][2]
        if tree[4][2] == site:
            return False
        tree[4][2] = site
        set_template(challenge, tree)
        return True
    return mutated(exported, first_only(edit))


@kind("drop-guard", "connection", "every original guard is checked", "alignment-guard",
      construction_accepts=True)
def drop_guard(exported):
    def change(value, site):
        bodies = [body for body in regions(value[7]) if any(item[0] == "protocol.guard" for item in body)]
        if site >= len(bodies):
            return False
        body = bodies[site]
        body.remove(next(item for item in body if item[0] == "protocol.guard"))
        return True
    return mutated(exported, change)


def self_operand(predicate, value, site_limit=None):
    """Make the first instruction satisfying `predicate` read its first operand twice."""
    found = next((item for item in nested(value[7]) if predicate(item) and len(item[3]) == 2
                  and item[3][0] != item[3][1]), None)
    if found is None:
        return False
    found[3][1] = found[3][0]
    return True


@kind("equality-self", "connection", "a decision compares the values the original compares",
      "alignment-computation", construction_accepts=True)
def equality_self(exported):
    return mutated(exported, first_only(lambda value: self_operand(
        lambda item: item[0] in ("algebra.field_equal", "algebra.group_equal"), value)))


@kind("conjunction-self", "connection", "a conjunction reads both decisions", "alignment-computation",
      construction_accepts=True)
def conjunction_self(exported):
    return mutated(exported, first_only(lambda value: self_operand(lambda item: item[0] == "arith.andi", value)))


@kind("update-self", "connection", "a loop's update reads the values the original reads",
      "alignment-computation", construction_accepts=True)
def update_self(exported):
    def change(value, site):
        bodies = [region[1] for item in nested(value[7]) if item[0] == "protocol.loop" for region in item[5]]
        candidates = []
        for body in bodies:
            additions = [item for item in body if item[0] == "algebra.field_add" and item[3][0] != item[3][1]]
            if additions:
                candidates.append(additions[-1])
        if site >= len(candidates):
            return False
        candidates[site][3][1] = candidates[site][3][0]
        return True
    return mutated(exported, change)


@kind("stale-yield", "connection", "a loop carries its updated values", "alignment-loop-yield",
      construction_accepts=True)
def stale_yield(exported):
    def change(value, site):
        found = []
        for loop, scope in loops(value[7], len(value[5])):
            yielded = loop[5][0][2]
            position = next((index for index, reference in enumerate(yielded)
                             if reference != scope + 1 + index), None)
            if position is not None:
                found.append((yielded, position, scope + 1 + position))
        if site >= len(found):
            return False
        yielded, position, incoming = found[site]
        yielded[position] = incoming
        return True
    return mutated(exported, change)


@kind("call-reads-sibling", "connection", "a helper call reads its own operands", "alignment-helper",
      construction_accepts=True)
def call_reads_sibling(exported):
    def edit(value):
        calls = [item for item in value[7] if item[0] in ("protocol.local_call", "func.call") and len(item[3]) >= 2]
        for first, second in zip(calls, calls[1:]):
            if len(first[3]) == len(second[3]) and first[3][1:] != second[3][1:]:
                second[3][1:] = first[3][1:]
                return True
        return False
    return mutated(exported, first_only(edit))


# ---------------------------------------------------------------------------
# The native candidate

def native_domain_separator(candidate, exported):
    """The challenge template names the delivery site instead of the selected
    query site."""
    challenge = next((item for item in nested(exported[7]) if bound(item, CHALLENGE)), None)
    if challenge is None or not exported[3][8]:
        return []
    hex_text = dict(challenge[1])["parameters"][1][0]
    tree, _ = decode_tree(bytes.fromhex(hex_text))
    tree[4][2] = exported[3][8][0][1]
    if candidate.count(hex_text) != 1:
        return []
    return [candidate.replace(hex_text, encode_tree(tree).hex())]


def function_block(lines, name):
    """The line range of an actual Func definition in a printed candidate."""
    pattern = re.compile(r"func\.func(?: private| public)? @" + re.escape(name) + r"\(")
    first = next((index for index, line in enumerate(lines) if pattern.search(line)), None)
    if first is None:
        return None
    indentation = lines[first][:len(lines[first]) - len(lines[first].lstrip())]
    last = next(index for index in range(first + 1, len(lines)) if lines[index].rstrip() == indentation + "}")
    return first, last


def native_helper_constant(candidate, exported):
    """A constant in the body of the last helper the validator calls changes."""
    calls = [item for item in exported[7] if item[0] in ("protocol.local_call", "func.call")]
    if not calls:
        return []
    callee = dict(calls[-1][1])["callee"][1]
    lines = candidate.splitlines(keepends=True)
    block = function_block(lines, callee)
    if block is None:
        return []
    first, last = block
    body = "".join(lines[first:last + 1])
    match = re.search(r'parameters = \["([0-9]+)"\]', body)
    if match is None:
        return []
    changed = body[:match.start()] + f'parameters = ["{int(match[1]) + 1}"]' + body[match.end():]
    return ["".join(lines[:first]) + changed + "".join(lines[last + 1:])]


def native_challenge_reads_host(candidate, exported):
    """The validator's first challenge call reads the validator's initial
    transcript, which an earlier call already consumed."""
    lines = candidate.splitlines()
    challenge_bindings = []
    for line in lines:
        if '"runtime.binding"' in line and f'contract = "{CHALLENGE}"' in line:
            match = re.search(r'sym_name = "([\w.$-]+)"', line)
            if match:
                challenge_bindings.append(match[1])
    challenge_helpers = []
    for line in lines:
        match = re.search(r"func\.func(?: private| public)? @([\w.$-]+)\(", line)
        if match:
            block = function_block(lines, match[1])
            if block and any('"exec.apply"' in text and
                             any(re.search(r"binding = @" + re.escape(binding) + r"[, }]", text)
                                 for binding in challenge_bindings)
                             for text in lines[block[0]:block[1] + 1]):
                challenge_helpers.append(match[1])
    validator = exported[3][3]
    start = next((index for index, line in enumerate(lines)
                  if '"protocol.participant"()' in line and f'role = "{validator}"' in line), None)
    if start is None or not challenge_helpers:
        return []
    # The validator participant's arguments are the export's inputs: the data
    # inputs, then the initial transcript.
    transcript = len(exported[5]) - 1
    for index in range(start + 1, len(lines)):
        if '"protocol.participant"()' in lines[index]:
            break
        match = re.search(r'"protocol.local_call"\(([^)]*)\).*callee = @('
                          + "|".join(map(re.escape, challenge_helpers)) + r')[, }]', lines[index])
        if match:
            operands = [operand.strip() for operand in match[1].split(",")]
            if operands[0] == f"%arg{transcript}":
                return []
            operands[0] = f"%arg{transcript}"
            lines[index] = lines[index][:match.start(1)] + ", ".join(operands) + lines[index][match.end(1):]
            return ["\n".join(lines) + "\n"]
    return []


NATIVE = {
    "native-domain-separator": (Kind("native-domain-separator", "native",
                                     "a challenge is bound to its query site (domain separation)",
                                     "native-proof-correspondence"), native_domain_separator),
    "native-helper-constant": (Kind("native-helper-constant", "native",
                                    "a prepared helper body is the original's checked helper",
                                    "native-proof-correspondence"), native_helper_constant),
    "native-challenge-reads-host": (Kind("native-challenge-reads-host", "native",
                                         "a transcript capability is used once (affine)",
                                         "native-proof-candidate"), native_challenge_reads_host),
}


# ---------------------------------------------------------------------------
# The executable validator program

def validator_of(program, deployment):
    role = deployment[2][1][3]
    return next(item for item in program[3] if item[3] == role)


def reached(program, participant):
    """The local functions the validator calls, including from loop bodies, in program order."""
    names = set()

    def visit(body):
        for item in body:
            if item[0] == "local":
                names.add(item[2])
            if item[0] == "loop":
                visit(item[5])
    visit(participant[6])
    return [function for function in program[2] if function[1] in names]


def contracts(program):
    return {binding[0]: binding[1] for binding in program[1]}


def steps(items):
    """Every operation step of a function body, including inside its regions."""
    for item in items:
        if item[0] == "op":
            yield item
        elif item[0] == "if":
            yield from steps(item[4])
            yield from steps(item[5])
        elif item[0] == "for":
            yield from steps(item[7])


def helper_names(exported):
    """The helpers the constructed validator calls: their program functions are
    read by the lowering rule only for their sorts and freedom from transcript
    operations, and prepared separately."""
    return {dict(item[1])["callee"][1] for item in nested(exported[7]) if item[0] in ("protocol.local_call", "func.call")}


def calculations(program, participant, exported):
    """The validator's calculation functions: reached, neither helpers nor
    transcript functions. The lowering rule reads them operation by operation."""
    excluded = helper_names(exported) | transcript_functions(program)
    return [function for function in reached(program, participant) if function[1] not in excluded]


def transcript_functions(program):
    binding = contracts(program)
    return {function[1] for function in program[2]
            if any(binding.get(step[2]) in TRANSCRIPT_CONTRACTS for step in steps(function[4]))}


def observe_functions(program):
    binding = contracts(program)
    return {function[1] for function in program[2]
            if any(binding.get(step[2]) == TRANSCRIPT_CONTRACTS[0] for step in steps(function[4]))}


def bodies(participant):
    yield participant[6]
    for item in participant[6]:
        if item[0] == "loop":
            yield item[5]


def program_mutation(name, property_, expected="refused"):
    def register(function):
        KINDS[name] = (Kind(name, "lowering", property_, expected), function)
        return function
    return register


def program_copies(deployment, edit, exported=None):
    program = json.loads(deployment[4])
    changed = copy.deepcopy(program)
    applied = edit(changed, validator_of(changed, deployment)) if exported is None else \
        edit(changed, validator_of(changed, deployment), exported)
    return [changed] if applied else []


@program_mutation("lowering-swap-operands", "operands keep their order")
def lowering_swap_operands(deployment, exported):
    def edit(program, participant, exported):
        for function in calculations(program, participant, exported):
            for step in steps(function[4]):
                if len(step[4]) == 2 and step[4][0] != step[4][1]:
                    step[4] = list(reversed(step[4]))
                    return True
        return False
    return program_copies(deployment, edit, exported)


@program_mutation("lowering-operand-self", "a comparison reads the values the constructed validator compares")
def lowering_operand_self(deployment, exported):
    def edit(program, participant, exported):
        binding = contracts(program)
        for function in calculations(program, participant, exported):
            for step in steps(function[4]):
                if (binding.get(step[2]) or "").endswith(".equal") and len(step[4]) == 2 \
                        and step[4][0] != step[4][1]:
                    step[4] = [step[4][1], step[4][1]]
                    return True
        return False
    return program_copies(deployment, edit, exported)


@program_mutation("lowering-results-swapped", "the validator returns its results in order")
def lowering_results_swapped(deployment, exported):
    def edit(program, participant):
        final = participant[6][-1]
        if final[0] != "return" or len(final[1]) < 2 or len(set(final[1])) < 2:
            return False
        final[1] = list(reversed(final[1]))
        return True
    return program_copies(deployment, edit)


@program_mutation("lowering-observe-reads-input", "an observation absorbs the message it receives")
def lowering_observe_reads_input(deployment, exported):
    def edit(program, participant):
        observes = observe_functions(program)
        call = next((item for body in bodies(participant) for item in body
                     if item[0] == "local" and item[2] in observes and len(item[3]) >= 2), None)
        first = participant[4][0][0]
        if call is None or call[3][1] == first:
            return False
        call[3] = [call[3][0], first, *call[3][2:]]
        return True
    return program_copies(deployment, edit)


@program_mutation("lowering-observe-reads-message", "an observation absorbs its own message")
def lowering_observe_reads_message(deployment, exported):
    def edit(program, participant):
        observes = observe_functions(program)
        for body in bodies(participant):
            receive = next((item for item in body if item[0] == "receive"), None)
            calls = [item for item in body if item[0] == "local" and item[2] in observes]
            if receive is not None and len(calls) >= 2 and calls[-1][3][1] != receive[4]:
                calls[-1][3] = [calls[-1][3][0], receive[4], *calls[-1][3][2:]]
                return True
        return False
    return program_copies(deployment, edit)


@program_mutation("lowering-stale-transcript", "each transcript call reads the latest transcript")
def lowering_stale_transcript(deployment, exported):
    def edit(program, participant):
        transcripts = transcript_functions(program)
        for body in bodies(participant):
            calls = [item for item in body if item[0] == "local" and item[2] in transcripts]
            for previous, current in zip(calls, calls[1:]):
                if current[3] and current[3][0] in previous[4] and previous[3] and previous[3][0] != current[3][0]:
                    current[3] = [previous[3][0], *current[3][1:]]
                    return True
        return False
    return program_copies(deployment, edit)


@program_mutation("lowering-uninstalled-binding", "every operation names an installed implementation")
def lowering_uninstalled_binding(deployment, exported):
    def edit(program, participant, exported):
        transcripts = transcript_functions(program)
        functions = [function for function in reached(program, participant) if function[1] in transcripts] \
            + calculations(program, participant, exported)
        used = [step[2] for function in functions for step in steps(function[4])]
        binding = next((item for item in program[1] if used and item[0] == used[0]), None)
        if binding is None:
            return False
        binding[3] = "fast/" + binding[1]
        return True
    return program_copies(deployment, edit, exported)


@program_mutation("lowering-unchecked-representation", "a received message has its checked representation")
def lowering_unchecked_representation(deployment, exported):
    def edit(program, participant):
        receive = next((item for body in bodies(participant) for item in body if item[0] == "receive"), None)
        if receive is None or "@" not in receive[5]:
            return False
        logical, representation = receive[5].split("@", 1)
        receive[5] = f"{logical}@unchecked.{representation.replace('/', '.')}/0"
        return True
    return program_copies(deployment, edit)


@program_mutation("lowering-formal-retyped", "a function's formals keep their types")
def lowering_formal_retyped(deployment, exported):
    def edit(program, participant, exported):
        functions = calculations(program, participant, exported) or reached(program, participant)
        if not functions or not functions[0][2] or functions[0][2][0][1] == "bool@native.bool/0":
            return False
        functions[0][2][0][1] = "bool@native.bool/0"
        return True
    return program_copies(deployment, edit, exported)


@program_mutation("lowering-function-duplicated", "local functions are unique")
def lowering_function_duplicated(deployment, exported):
    def edit(program, participant):
        functions = reached(program, participant)
        if not functions:
            return False
        program[2].append(copy.deepcopy(functions[0]))
        return True
    return program_copies(deployment, edit)


def first_loop(participant):
    return next((item for item in participant[6] if item[0] == "loop"), None)


@program_mutation("lowering-loop-maximum-raised", "a loop keeps its static maximum")
def lowering_loop_maximum_raised(deployment, exported):
    def edit(program, participant):
        loop = first_loop(participant)
        if loop is None:
            return False
        loop[2][2] = str(int(loop[2][2]) + 1)
        return True
    return program_copies(deployment, edit)


@program_mutation("lowering-loop-count-retargeted", "a loop counts the original's count")
def lowering_loop_count_retargeted(deployment, exported):
    def edit(program, participant):
        loop = first_loop(participant)
        other = next((port[0] for port in participant[4] if loop is not None and port[0] != loop[2][1]), None)
        if loop is None or other is None:
            return False
        loop[2][1] = other
        return True
    return program_copies(deployment, edit)


@program_mutation("lowering-loop-carried-swapped", "a loop's carried values keep their positions")
def lowering_loop_carried_swapped(deployment, exported):
    def edit(program, participant):
        loop = first_loop(participant)
        if loop is None or len(loop[3]) < 2 or loop[3][0][1] == loop[3][1][1]:
            return False
        loop[3][0][1], loop[3][1][1] = loop[3][1][1], loop[3][0][1]
        return True
    return program_copies(deployment, edit)


@program_mutation("lowering-helper-retargeted", "a call names the constructed validator's helper")
def lowering_helper_retargeted(deployment, exported):
    def edit(program, participant, exported):
        helpers = helper_names(exported)
        call = next((item for item in participant[6] if item[0] == "local" and item[2] in helpers), None)
        names = [function[1] for function in program[2]]
        if call is None or call[2] not in names:
            return False
        others = names[names.index(call[2]) + 1:] + names[:names.index(call[2])]
        if not others:
            return False
        call[2] = others[0]
        return True
    return program_copies(deployment, edit, exported)


@program_mutation("lowering-helper-constant", "the rule reads a helper body only for its sorts and its freedom "
                  "from transcript operations; its meaning is a separate preparation obligation", "accepted")
def lowering_helper_constant(deployment, exported):
    def edit(program, participant, exported):
        calls = [item for body in bodies(participant) for item in body if item[0] == "local"]
        names = helper_names(exported)
        helpers = [call[2] for call in calls if call[2] in names]
        for name in reversed(helpers):
            function = next(item for item in program[2] if item[1] == name)
            for step in steps(function[4]):
                if len(step[3]) == 1 and re.fullmatch(r"[0-9]+", step[3][0]):
                    step[3] = [str(int(step[3][0]) + 1)]
                    return True
        return False
    return program_copies(deployment, edit, exported)


@program_mutation("lowering-retarget-operand", "an operation reads the values the constructed validator reads")
def lowering_retarget_operand(deployment, exported):
    def edit(program, participant, exported):
        for function in calculations(program, participant, exported):
            arguments = {name: physical for name, physical in function[2]}
            for step in steps(function[4]):
                if len(step[4]) == 2 and all(name in arguments for name in step[4]):
                    replacement = next((name for name, physical in function[2]
                                        if physical == arguments[step[4][1]] and name not in step[4]), None)
                    if replacement is not None:
                        step[4] = [step[4][0], replacement]
                        return True
        return False
    return program_copies(deployment, edit, exported)


# ---------------------------------------------------------------------------
# Helper bodies, checked by the helper rule

def helper_mutation(name, property_):
    def register(function):
        KINDS[name] = (Kind(name, "helpers", property_, "refused"), function)
        return function
    return register


def helper_copies(deployment, edit, exported):
    """One mutated copy per local function of a helper the constructed validator
    calls, in program order, each with the helper's name."""
    program = json.loads(deployment[4])
    names = helper_names(exported)
    copies = []
    for index, function in enumerate(program[2]):
        if function[1] not in names:
            continue
        changed = copy.deepcopy(program)
        if edit(changed, changed[2][index]):
            copies.append((changed, function[1]))
    return copies


def renamed(value, old, new):
    if isinstance(value, list):
        return [renamed(item, old, new) for item in value]
    return new if value == old else value


@helper_mutation("helper-rebound", "a helper body binds each name once, as its checked helper does")
def helper_rebound(deployment, exported):
    def edit(program, function):
        step = next((step for step in steps(function[4]) if step[5]), None)
        if step is None or not function[2]:
            return False
        function[4] = renamed(function[4], step[5][0], function[2][0][0])
        return True
    return helper_copies(deployment, edit, exported)


@helper_mutation("helper-binding", "a helper step uses the binding of its checked operation")
def helper_binding(deployment, exported):
    def edit(program, function):
        step = next(steps(function[4]), None)
        if step is None:
            return False
        table = {binding[0]: binding for binding in program[1]}
        current = table.get(step[2])
        if current is None:
            return False
        family = current[1].split(".", 1)[0]
        others = [binding for binding in program[1] if binding[1] != current[1] and binding[2] == current[2]
                  and binding[1] not in TRANSCRIPT_CONTRACTS]
        replacement = next((binding for binding in others if binding[1].split(".", 1)[0] == family),
                           others[0] if others else None)
        if replacement is None:
            return False
        step[2] = replacement[0]
        return True
    return helper_copies(deployment, edit, exported)


def accept_any(program, deployment):
    """Make every data comparison of the validator compare a value with itself,
    so that wrong messages are accepted: the receipt binding's mutated program."""
    participant = validator_of(program, deployment)
    binding = contracts(program)
    changed = False
    for function in reached(program, participant):
        for step in steps(function[4]):
            if binding.get(step[2]) in ("field.equal", "curve.equal") and len(step[4]) == 2:
                step[4] = [step[4][1], step[4][1]]
                changed = True
    return changed


def kinds_for(names):
    """The registered kinds a manifest lists, refusing unknown names."""
    table = {**KINDS, **NATIVE}
    unknown = [name for name in names if name not in table]
    if unknown:
        raise ValueError(f"unknown mutation kinds: {', '.join(unknown)}")
    return [(name, *table[name]) for name in names]


def listing():
    table = {**KINDS, **NATIVE}
    return [dict(name=name, stage=kind_.stage, property=kind_.property, expected=kind_.expected,
                 refusing_rule=kind_.refusing_rule if kind_.stage in {"construction", "connection"} else
                 "Zkc.Executable.checkHelpers" if kind_.stage == "helpers" else None,
                 construction_accepts=kind_.construction_accepts)
            for name, (kind_, _) in sorted(table.items())]
