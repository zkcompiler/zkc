"""Render the generated per-Entry Lean modules of a subject.

The generated construction glue states, for one compiled proof Entry, the
facts every downstream proof uses: the admitted original, the constructed
validator, the checked selection of its inputs and acceptance output, the
occurrence context, the three positional premises of
`Zkc.Construction.compiled_transform`, and its instance at the Entry's
published inputs. Every statement is checked by the kernel when the module is
built: Python proposes literal values read from the exports (positions, slots,
the context), the module states them, and `decide`, `rfl` or the generic
selection theorem (`Zkc.Construction.selection_sound`) proves them. A wrong
proposal is a build failure, never a trusted fact.

The executable facts module states, for the executable validator, the facts the
lowering rule's theorems take as premises: its accepted reading, its helper
calls, its static charge and message types when they are static, and admission
of the published inputs.
"""

import json
from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import NAMESPACE, Refused, require, text  # noqa: E402

# Lean identifiers a published input must not shadow in the generated module.
RESERVED = {"inputs", "outputs", "values", "handle", "initial", "proof", "challenge", "data", "decision",
            "acceptance", "verifier", "process", "program", "participant", "context", "selection", "table",
            "snapshot", "verifierInputs", "options", "length", "m", "F", "G", "fun", "do", "at", "by", "in",
            "end", "open", "let", "have", "show", "from", "where", "match", "with", "if", "then", "else"}

# Lean types of present values, by structured type tag.
VALUE_TYPES = {"bool": "Bool", "index": "Nat", "field": "F", "vector": "List F", "group": "G"}


def binder(name):
    """A Lean binder for a source input name: lower camel case, never reserved."""
    parts = [part for part in re.split(r"[^A-Za-z0-9]+", name) if part]
    require(parts, f"input name {name!r} has no identifier characters")
    result = parts[0][0].lower() + parts[0][1:] + "".join(part[:1].upper() + part[1:] for part in parts[1:])
    if not result[0].isalpha():
        result = "input" + result[:1].upper() + result[1:]
    return result + "Value" if result in RESERVED else result


def var(index):
    """The `Var` literal of a position."""
    term = ".here"
    for _ in range(index):
        term = f"(.there {term})"
    return term


def value_term(ty, name):
    """The exported value of a present input of structured type `ty`."""
    tag = ty[0]
    if tag == "bool":
        return f".data (.boolean {name})"
    if tag == "index":
        return f".index {name}"
    if tag == "vector":
        return f".vector {text(ty[1])} {name}"
    if tag in ("field", "group"):
        return f".data (.{tag} {text(ty[1])} {name})"
    raise Refused(f"unsupported published input type {ty}")


def payload_term(ty, name):
    tag = ty[0]
    if tag == "bool":
        return f".boolean {name}"
    if tag in ("field", "group"):
        return f".{tag} {text(ty[1])} {name}"
    raise Refused(f"input type {ty} has no transcript payload")


def scalar(ty):
    return ty[0] in ("bool", "field", "group")


def binders(names, types):
    """Group consecutive binders of the same Lean type: `(a b : G) (c : F)`."""
    groups = []
    for name, ty in zip(names, types):
        lean = VALUE_TYPES[ty[0]]
        if groups and groups[-1][1] == lean:
            groups[-1][0].append(name)
        else:
            groups.append(([name], lean))
    return " ".join(f"({' '.join(group)} : {lean})" for group, lean in groups)


class Entry:
    """The facts of one exported proof Entry that the generated glue states.

    `original` is the structured export of the Entry's original, `exported`
    the constructed participant export and `interface` the language
    interface. Nothing here is trusted: each value becomes a statement the
    kernel checks.
    """

    def __init__(self, original, exported, interface):
        self.original, self.exported = original, exported
        policy = exported[3]
        self.policy = policy
        root = next(item for item in original[7] if item[0] == "function" and item[1] == original[3])
        _, _, _, _, self.input_types, self.output_types, header, _, _, _ = root
        require(header and header[0] == "protocol", "the Entry root is not a protocol")
        _, self.roles, input_scopes, output_scopes = header
        self.validator = self.roles.index(policy[3])
        self.producer = self.roles.index(policy[2])
        self.acceptance_output = int(policy[4])
        self.public = [int(index) for index in policy[7]]
        self.services = [int(index) for index in policy[6]]
        self.service = self.services[0]
        validator_outputs = [index for index, scope in enumerate(output_scopes) if policy[3] in scope]
        require(self.acceptance_output in validator_outputs, "the acceptance output is not the validator's")
        self.position = validator_outputs.index(self.acceptance_output)
        protocol = next(item for item in interface["protocols"] if item["symbol"] == interface["protocol"])
        names = {item["index"]: item["name"] for item in protocol["inputs"]}
        self.source_names = [names[index] for index in self.public]
        self.names = [binder(name) for name in self.source_names]
        require(len(set(self.names)) == len(self.names), "published input names collide")
        self.types = [self.input_types[index] for index in self.public]
        contract = self.input_types[self.service]
        require(contract[0] == "service", "the replaced input is not a service")
        self.contract = contract[1]
        fields = sorted({instruction_field(item) for item in walk(exported[7])
                         if item[0] == "crypto.exec.indexed_transcript_challenge"})
        self.request = f"some (.draw {text(fields[0])})" if len(fields) == 1 else "none"
        self.draws = [(pair[0], pair[1]) for pair in policy[8]]

    def slots(self):
        """The validator's input slots, as `inputSlots` computes them."""
        result = []
        for index in range(len(self.input_types)):
            if index in self.public:
                result.append(("held", self.public.index(index)))
            elif index == self.service:
                result.append(("service", None))
            else:
                result.append(("absent", None))
        return result


def walk(instructions):
    for item in instructions:
        yield item
        for region in item[5]:
            yield from walk(region[1])


def instruction_field(item):
    match = re.fullmatch(r'!algebra\.field<"([^"\\]+)">', item[4][0])
    require(match is not None, "challenge result is not a field element")
    return match[1]


HEADER = """module

{imports}

@[expose] public section

/-! {doc} -/
"""


def imports(names):
    return "\n".join(f"public import {name}" for name in names)


def construction_glue(subject, entry, modules):
    """The generated glue module of a compiled proof Entry.

    `modules` names the data, participant, bodies and views modules, the glue
    namespace and the Bodies entries for `structured_views`.
    """
    namespace = modules["glue"]
    require(re.fullmatch(NAMESPACE, namespace) is not None, "invalid glue namespace")
    rule = subject.get("construction", "rule", "compiled")
    if rule == "construction":
        return construction_only_glue(subject, entry, modules)
    admission = subject.get("construction", "admission", "views")
    require(admission == "external" or modules.get("bodies"), "views admission needs printed Bodies")
    form = subject.get("construction", "inputs", "values")
    require(form == "values" or all(scalar(ty) for ty in entry.types),
            "the payload form needs scalar published inputs")
    model = subject.get("construction", "model")
    data, participant_module = modules["data"], modules["participant"]
    names, types = entry.names, entry.types
    args = " ".join(names)
    typed = binders(names, types)
    held = "".join(f".cons {name} (" for name in names) + ".nil" + ")" * len(names)
    if form == "payloads":
        inputs_type = "List (Payload F G)"
        inputs_body = "[" + ", ".join(payload_term(ty, name) for name, ty in zip(names, types)) + "]"
        published = f"(inputs {args}).map .data" if names else "(inputs).map .data"
    else:
        inputs_type = "List (Value F G)"
        inputs_body = "[" + ", ".join(value_term(ty, name) for name, ty in zip(names, types)) + "]"
        published = f"inputs {args}" if names else "inputs"
    components = []
    for kind, position in entry.slots():
        components.append(f"some {names[position]}" if kind == "held" else "some handle" if kind == "service"
                          else "none")
    verifier_inputs = "".join(f".cons ({component}) (" for component in components) + ".nil" + ")" * len(components)
    output = var(entry.acceptance_output)
    validator = entry.validator
    roles = "[" + ", ".join(text(role) for role in entry.roles) + "]"
    draws = "[" + ", ".join(f"({text(query)}, {text(delivery)})" for query, delivery in entry.draws) + "]"
    context_literal = (f"⟨{data}.snapshot.entry, {roles}, {entry.producer}, {validator}, {entry.service}, "
                       f"{text(entry.contract)}, {entry.request}, participant.policy.suite, {draws}⟩")
    module_imports = ["Zkc.Construction.Compiled", "Zkc.Source.Structured.CommonAdapter", data,
                      participant_module]
    if admission == "views":
        module_imports.insert(0, "Zkc.Source.Structured.UnitViews")
        module_imports.append(modules["bodies"])
    elif admission == "external":
        module_imports.append(subject.get("construction", "views"))
    module_imports += subject.get("construction", "model_imports", [])
    doc = subject.get("construction", "doc") or default_glue_doc(subject, modules)
    out = [HEADER.format(imports=imports(module_imports), doc=doc)]
    out.append(f"namespace {namespace}\nopen Zkc.Source Zkc.Source.Structured Zkc.Construction\n\n"
               "set_option smartUnfolding false\n")
    out.append("/-! ## The original Proof Entry -/\n")
    if admission == "views":
        helpers = ", ".join(f"{local} := {modules['bodies']}.{local}" for local in modules["helpers"])
        protocols = ", ".join(f"{local} := {modules['bodies']}.{local}" for local in modules["protocols"])
        out.append(f"structured_views {data}.snapshot\n  helpers [{helpers}]\n  protocols [{protocols}]\n\n"
                   f"theorem admitted : Structured.check {data}.snapshot = .ok program := kernel_admission\n")
    elif admission == "external":
        views = subject.get("construction", "views")
        out.append(f"abbrev program := {views}.program\n/-- The admitted original. -/\n"
                   f"abbrev imported : Structured.Imported {data}.snapshot :=\n  {views}.imported\n")
    out.append(f"""abbrev snapshot := {data}.snapshot
abbrev participant := {participant_module}.participant

/-! ## The constructed validator and its checked selection -/

set_option smartUnfolding true in
/-- The composed per-compile check accepts the actual export against the
admitted original. -/
theorem compiled : checkCompiled imported participant = .ok () := by decide +kernel

set_option smartUnfolding true in
/-- The selection of the export's inputs and acceptance output, constructed from
the admitted original and the export's policy. -/
def selection : Selection imported.program.payload.entry.outputs :=
  (select imported participant).get (by decide +kernel)

theorem selected : select imported participant = some selection := (Option.some_get _).symm

set_option smartUnfolding true in
/-- The selection check accepts the export. -/
theorem selection_checked : selection.check imported participant = true := by decide +kernel

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := selection.context

theorem context_admitted : exportContext {data}.snapshot participant = some context :=
  (select_sound imported participant selected).1

set_option smartUnfolding true in
/-- The derived context: entry, roster, producer and validator positions, the
replaced service input, its contract and the draw request its challenges
carry, the suite and the selected query/delivery sites. -/
theorem context_eq : context =
    {context_literal} := by
  decide +kernel

/-- The composed check's two rules, each on the actual export. -/
theorem compiled_rules : checkExport {data}.snapshot participant = .ok () ∧ check context participant = .ok () ∧
    project program context participant = .ok () := by
  have accepted := compiled
  unfold checkCompiled at accepted
  split at accepted
  · rename_i context' exported found
    rw [context_admitted] at found
    cases found
    obtain ⟨context'', found', checked⟩ := checkExport_sound exported
    rw [context_admitted] at found'
    cases found'
    exact ⟨exported, checked, accepted⟩
  · cases accepted
  · cases accepted

/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport {data}.snapshot participant = .ok () := compiled_rules.1

/-- The transcript-construction rule accepts the actual export. -/
theorem checked : check context participant = .ok () := compiled_rules.2.1

/-- The participant projection rule accepts the actual export. -/
theorem projected : project program context participant = .ok () := compiled_rules.2.2

set_option smartUnfolding true in
theorem validator_eq : context.validator = {validator} := by decide +kernel

set_option smartUnfolding true in
theorem producer_eq : context.producer = {entry.producer} := by decide +kernel

/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat := selection.position

theorem acceptance_admitted : exportAcceptance {data}.snapshot participant = some acceptancePosition :=
  (select_sound imported participant selected).2.1

set_option smartUnfolding true in
theorem acceptancePosition_eq : acceptancePosition = {entry.position} := by decide +kernel

variable {{F G : Type}} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The acceptance output selected by the policy, read from returned values. -/
def acceptance (values : List (Value F G)) : Option Bool :=
  match values[acceptancePosition]? with
  | some (.data (.boolean decision)) => some decision
  | _ => none

/-- The acceptance decision among the validator's outputs. -/
def decision (options : List (Option (Value F G))) : Option Bool :=
  match options[acceptancePosition]? with
  | some (some (.data (.boolean value))) => some value
  | _ => none

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- On every list of the returned length, the acceptance output is the decision
among the validator's outputs. -/
theorem acceptance_decision (values : List (Value F G))
    (length : values.length = participant.returned.length) :
    acceptance values = decision (values.dropLast.map some) :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).1 values length

/-- Data inputs of the constructed validator: the policy's public inputs, in
policy order. -/
def inputs {typed} : {inputs_type} :=
  {inputs_body}

/-- The validator's original inputs: the published values at their positions,
absent inputs of other roles, and the challenge service handle. -/
def verifierInputs {typed} (handle : Nat) :
    Values (Component (assignment F G)) program.payload.entry.inputs :=
  {verifier_inputs}

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs hold the validator's original inputs:
the published values at their exported positions and the handle as the replaced
service. -/
theorem inputs_related {typed} (handle : Nat) (initial : History F G) :
    HoldsValues handle ({published} ++ [.transcript initial])
      (inputSlots context participant.policy program.payload.entry.inputs)
      (verifierInputs (F := F) (G := G) {args} handle) :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).2.1 handle
    ({held}) [.transcript initial]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The constructed program's data inputs are the published inputs and the
initial transcript. -/
theorem inputs_arity {typed} :
    (inputs (F := F) (G := G) {args}).length + 1 = participant.inputs.length :=
  rfl
""".replace("{args}", args).replace("{published}", published).replace("{held}", held)
       .replace("{typed}", typed).replace("{inputs_type}", inputs_type).replace("{inputs_body}", inputs_body)
       .replace("{verifier_inputs}", verifier_inputs))
    if form == "payloads":
        out.append(f"""/-- The validator's original inputs, by original position. -/
def originalValue {typed} (handle : Nat) (index : Nat) : Option (Payload F G) :=
  ((inputPayloads (verifierInputs (F := F) (G := G) {args} handle))[index]?).join

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The host binds exactly `inputs`: the validator's original inputs at the
checked policy's public positions, in order. -/
theorem public_values {typed} (handle : Nat) :
    publicValues participant.policy (originalValue (F := F) (G := G) {args} handle) =
      some (inputs {args}) := by
  rfl
""")
    out.append(f"""/-- Helper calls of the constructed program denote the original's checked
helpers. -/
abbrev table : Structured.Meanings F G := helperTable program F G

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The decision among the validator's outputs is its acceptance output. -/
theorem decision_outputs (outputs : Values (Component (assignment F G)) program.payload.entry.outputs) :
    decision (validatorOutputs {validator} program.payload.entry.outputScopes outputs) = outputs.get {output} :=
  (selection_sound (F := F) (G := G) imported participant selected selection_checked).2.2.2 outputs

/-- The admitted root's validator process, read through its acceptance output. -/
def process {typed} (handle : Nat) : PIR.Process (participantInterface F G) (Option Bool) :=
  (program.participant F G {validator} (verifierInputs {args} handle)).bind fun outputs =>
    .done (outputs.get {output})

/-- The original validator, read through its acceptance output. -/
def verifier {typed} (handle : Nat) : PIR.Process (Actions F G) (Option Bool) :=
  (process {args} handle).interpret CommonAdapter.project

/-- The original validator, read through its outputs, is the verifier. -/
theorem original_verifier {typed} (handle : Nat) :
    ((program.participant F G context.validator (verifierInputs {args} handle)).bind fun outputs =>
      .done (decision (validatorOutputs context.validator program.payload.entry.outputScopes
        outputs))).interpret CommonAdapter.project = verifier {args} handle := by
  unfold verifier process
  rw [validator_eq]
  simp only [decision_outputs]

/-- The compiled verifier, under the ideal transcript model with any challenge
function in any lawful monad, is the Fiat–Shamir transform of the original
Proof Entry's validator: equal acceptance outcomes, stops and unread proof
suffixes, for every published input, initial transcript, proof and service
handle. An instance of `Zkc.Construction.compiled_selected`, whose positional
premises the checked selection discharges. -/
theorem compiled_transform {{m : Type → Type}} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) {typed} (handle : Nat) (initial : History F G)
    (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          ({published} ++ [.transcript initial]) proof =
      transform context challenge (verifier {args} handle) initial proof :=
  (compiled_selected imported participant compiled selected selection_checked).2 challenge handle
    ({held}) initial proof

/-- By the construction rule alone, the compiled verifier is the Fiat–Shamir
transform of the interactive reading of its exported instructions, read through
the acceptance output, for every service handle. -/
theorem spec_transform {{m : Type → Type}} [Monad m] [LawfulMonad m]
    (challenge : History F G → m F) (handle : Nat) (data : List (Value F G))
    (arity : data.length = {len(names)}) (initial : History F G) (proof : Proof F G) :
    (fun result => (mapOutcome acceptance result.1, result.2)) <$>
        ideal context challenge table participant.returned participant.instructions
          (data ++ [.transcript initial]) proof =
      transform context challenge
        ((spec context handle table participant.returned participant.instructions
          (data ++ [.transcript initial])).bind fun values => .done (acceptance values))
        initial proof := by
  rw [check_sound context challenge handle table participant checked data initial proof
    (by rw [arity]; rfl), transform_bind_done]
""".replace("{typed}", typed).replace("{args}", args).replace("{published}", published)
       .replace("{held}", held).replace("{output}", output).replace("{validator}", str(validator)))
    if model:
        out.append(f"""/-! ## The model the original validator is, by computation -/

/-- The admitted root's validator process is the model, by computation. -/
theorem process_equation {typed} (handle : Nat) :
    process (F := F) (G := G) {args} handle = ({model} {args} handle).interpret CommonAdapter.embed := by
  rfl

theorem verifier_correspondence {typed} (handle : Nat) :
    verifier (F := F) (G := G) {args} handle = {model} {args} handle := by
  rw [verifier, process_equation, CommonAdapter.project_embed]

/-- The constructed program's interactive reading is the model, with every
reply, stop and acceptance decision. Derived from the projection rule; no
computation specific to this Entry is involved. -/
theorem spec_equation {typed} (handle : Nat) (initial : History F G) :
    (spec context handle table participant.returned participant.instructions
        ({published} ++ [.transcript initial])).bind
      (fun values => .done (acceptance values)) =
      {model} {args} handle := by
  rw [spec_bind_congr context handle table participant.returned participant.instructions _ acceptance
    (fun values => decision (values.dropLast.map some)) acceptance_decision]
  have projected' := project_sound program context participant projected handle
    ({published}) initial (verifierInputs {args} handle)
    (inputs_related {args} handle initial) rfl
  calc (spec context handle table participant.returned participant.instructions
          ({published} ++ [.transcript initial])).bind
          (fun values => .done (decision (values.dropLast.map some)))
      = ((spec context handle table participant.returned participant.instructions
          ({published} ++ [.transcript initial])).bind
          (fun values => .done (values.dropLast.map some))).bind
          (fun options => .done (decision options)) := by
        rw [PIR.Process.bind_assoc]
        rfl
    _ = (((program.participant F G context.validator (verifierInputs {args} handle)).bind
          fun outputs => .done (validatorOutputs context.validator program.payload.entry.outputScopes
            outputs)).interpret CommonAdapter.project).bind
          (fun options => .done (decision options)) := by
        rw [projected']
    _ = ((program.participant F G context.validator (verifierInputs {args} handle)).bind
          fun outputs => .done (decision (validatorOutputs context.validator
            program.payload.entry.outputScopes outputs))).interpret CommonAdapter.project := by
        rw [PIR.Process.interpret_bind, PIR.Process.interpret_bind, PIR.Process.bind_assoc]
        rfl
    _ = {model} {args} handle := by
        rw [original_verifier, verifier_correspondence]
""".replace("{typed}", typed).replace("{args}", args).replace("{published}", published)
       .replace("{model}", model))
    out.append(f"end {namespace}\n")
    return omit_declarations("\n".join(out), subject.get("construction", "omit", []))


def omit_declarations(source, names):
    """Drop the named declarations: a hand module in the same namespace owns them.

    A declaration is the paragraph (blank-line separated) whose first command
    line declares it, with its documentation and options."""
    if not names:
        return source
    pattern = re.compile(r"^(?:theorem|def|abbrev) ([A-Za-z_][A-Za-z0-9_']*)", re.M)
    kept = []
    found = set()
    for paragraph in source.split("\n\n"):
        match = pattern.search(paragraph)
        if match and match[1] in names:
            found.add(match[1])
            continue
        kept.append(paragraph)
    missing = set(names) - found
    require(not missing, f"cannot omit undeclared glue names: {', '.join(sorted(missing))}")
    return "\n\n".join(kept)


def construction_only_glue(subject, entry, modules):
    """The glue of an Entry checked by the construction rule alone."""
    namespace, data, participant_module = modules["glue"], modules["data"], modules["participant"]
    names, types = entry.names, entry.types
    typed = binders(names, types)
    inputs_body = "[" + ", ".join(value_term(ty, name) for name, ty in zip(names, types)) + "]"
    doc = subject.get("construction", "doc") or default_glue_doc(subject, modules)
    return HEADER.format(imports=imports([data, participant_module, "Zkc.Construction.Structured"]), doc=doc) + f"""
namespace {namespace}
open Zkc.Construction

abbrev participant := {participant_module}.participant

set_option smartUnfolding true in
/-- The per-compile construction check accepts the actual export. -/
theorem accepted : checkExport {data}.snapshot participant = .ok () := by decide +kernel

/-- The occurrence context the check derives from the original roster and the
exported policy. -/
def context : Context := (exportContext {data}.snapshot participant).get (by decide +kernel)

theorem context_admitted : exportContext {data}.snapshot participant = some context := by
  rfl

set_option smartUnfolding true in
/-- Where the export returns the selected acceptance output. -/
def acceptancePosition : Nat :=
  (exportAcceptance {data}.snapshot participant).get (by decide +kernel)

theorem acceptance_admitted :
    exportAcceptance {data}.snapshot participant = some acceptancePosition := by
  rfl

set_option smartUnfolding true in
theorem acceptancePosition_eq : acceptancePosition = {entry.position} := by decide +kernel

/-- Data inputs of the constructed validator: the policy's public inputs, in
policy order. -/
def inputs {{F G : Type}} {typed} : List (Value F G) := {inputs_body}

end {namespace}
"""


def default_glue_doc(subject, modules):
    rule = subject.get("construction", "rule", "compiled")
    entry = subject.get("entries", "proof")
    if rule == "construction":
        return (f"Generated construction facts of the compiled `{entry}` Entry of the subject\n"
                f"`{subject.name}`. Regenerate with `lean/bridges/subject.py --write`.\n\n"
                f"`{modules['data'].rsplit('.', 1)[-1]}` is the Entry's original export and\n"
                f"`{modules['participant'].rsplit('.', 1)[-1]}` its constructed validator. The per-compile\n"
                "transcript-construction check accepts the pair (`accepted`); the participant\n"
                "projection rule is not applied to this Entry.")
    return (f"Generated construction facts of the compiled `{entry}` Entry of the subject\n"
            f"`{subject.name}`. Regenerate with `lean/bridges/subject.py --write`.\n\n"
            f"`{modules['data'].rsplit('.', 1)[-1]}` is the Entry's original export and\n"
            f"`{modules['participant'].rsplit('.', 1)[-1]}` its constructed validator. The composed\n"
            "transcript-construction and participant projection check accepts the pair\n"
            "(`compiled`), and the selection check (`selection_checked`) discharges the\n"
            "positional premises of the composed rules from data the kernel reads, so\n"
            "`compiled_transform` holds with no proof specific to this Entry: for every\n"
            "challenge function, the compiled verifier's ideal meaning is the Fiat–Shamir\n"
            "transform of the original validator.")


def views_module(namespace, data, bodies, helpers, protocols):
    """The Views module of an interactive unit admitted from its printed Bodies."""
    helper_entries = ", ".join(f"{local} := {bodies.rsplit('.', 1)[-1]}.{local}" for local in helpers)
    protocol_entries = ", ".join(f"{local} := {bodies.rsplit('.', 1)[-1]}.{local}" for local in protocols)
    data_short = data.rsplit(".", 1)[-1]
    return f"""module

public import Zkc.Source.Structured.UnitViews
public import {data}
public import {bodies}

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace {namespace}
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

structured_views {data_short}.snapshot
  helpers [{helper_entries}]
  protocols [{protocol_entries}]

theorem admitted : check {data_short}.snapshot = .ok program := kernel_admission

end {namespace}
"""


def body_names(snapshot, entry_name):
    """The printer's local names: the Entry protocol is `entry_name` and a unique
    relation formula is `formula`; other bodies keep the printer's defaults."""
    formulas = [relation[9] for relation in snapshot[5] if relation[9] is not None]
    names = {}
    if entry_name:
        names[snapshot[3]] = entry_name
    if len(formulas) == 1:
        names[formulas[0]] = "formula"
    return names


def facts_module(namespace, construction, program_module, facts, form):
    """The executable facts of a validator program the lowering rule accepts.

    `facts` holds the values Lean evaluated for the accepted reading: its static
    charge, its static message types, and whether it calls helpers."""
    names, types = construction["names"], construction["types"]
    typed = binders(names, types)
    args = " ".join(names)
    glue = construction["glue"]
    data = f"({glue}.inputs (F := F) (G := G) {args}).map .data" if form == "payloads" else \
        f"{glue}.inputs (F := F) (G := G) {args}"
    out = [HEADER.format(imports=imports([program_module, glue, "Zkc.Executable.NormalizationSoundness",
                                          "Zkc.Executable.Installed"]),
                         doc=f"Generated facts of the executable validator `{program_module.rsplit('.', 1)[-1]}`.\n"
                             "Regenerate with `lean/bridges/subject.py --write`. The per-compile lowering\n"
                             "rule accepts the validator against the constructed validator (`accepted`);\n"
                             "each fact below is checked by the kernel.")]
    out.append(f"""namespace {namespace}
open Zkc.Construction Zkc.Executable

abbrev validator : Validator := {program_module}.validator

set_option maxRecDepth 20000 in
/-- The reading of the executable validator. -/
def lowered : Lowered :=
  (checkLowering installed {glue}.participant validator).toOption.get (by decide +kernel)

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed {glue}.participant validator = .ok lowered :=
  ok_of_isSome _ _

set_option maxRecDepth 20000 in
/-- The helpers the constructed validator calls. -/
theorem helpers : Instruction.helpers {glue}.participant.instructions = {facts['helpers']} := by
  rw [← Instruction.helperList_eq]
  decide +kernel
""")
    if facts.get("calls") == 0:
        out.append(f"""/-- The constructed validator has no helper call. -/
theorem calls : Instruction.callList {glue}.participant.instructions = [] := by
  decide +kernel
""")
    if facts.get("total") is not None:
        out.append(f"""set_option maxRecDepth 20000 in
/-- A complete run charges {facts['total']} instructions. -/
theorem total : lowered.total? = some {facts['total']} := by decide +kernel
""")
    if facts.get("receives") is not None:
        out.append(f"""/-- The message types, in order. -/
abbrev receives : List PhysicalType :=
  {facts['receives']}

set_option maxRecDepth 20000 in
theorem plan_static : Plan.static lowered.plan = some receives := by decide +kernel

theorem plan_types {{F G : Type}} (data : List (Value F G)) : Plan.types data lowered.plan = receives :=
  Plan.types_static data plan_static
""")
    out.append(f"""variable {{F G : Type}} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the published inputs. -/
theorem admitted {typed} : validator.admits ({data}) = true := by
  rfl

end {namespace}
""")
    return "\n".join(out)


def lean_physical(value):
    return json.dumps(value)
