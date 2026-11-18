module

public import Zkc.Frontend.Emit.Reports

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Core

abbrev ExportM := Except String
def unsupported {α : Type} (what : String) : ExportM α := .error ("WK-CORE: unsupported " ++ what)

def list (xs : List String) := "[" ++ ", ".intercalate xs ++ "]"
def numbers (xs : List Nat) := list (xs.map toString)
def names (xs : List Nat) (variableRefs := false) := xs.foldr (fun x rest =>
  let head := if variableRefs then s!"⟨{x}, rfl⟩" else toString x
  s!"(.cons {head} {rest})") ".nil"

def ty {b : Emit.Bindings} (t : b.vocabulary.Ty) : ExportM String :=
  match t with
  | .bool => pure ".bool"
  | .nominal (.inl k) => pure s!"(.nominal (.inl ({reprStr (show Zkc.Vocabulary.TypeKey from k)})))"
  | _ => unsupported "Core value type in the written scalar/group profile"

def located {b : Emit.Bindings} (ts : List (LTy b.vocabulary)) : ExportM String := do
  return list (← ts.mapM fun a => do return s!"⟨{← ty (b := b) a.ty}, {numbers a.holders}⟩")

def row (k : Zkc.Vocabulary.RowKey) := s!"(show V.RowKey from .inl ({reprStr k}))"

def coin (k : Zkc.Vocabulary.LawKey) : ExportM String :=
  match k with
  | .uniform (.nominal t) => pure s!"(.coin (.uniform (.nominal ({reprStr t}))))"
  | _ => unsupported "sampling law"

def rawOp {b : Emit.Bindings} : ProtocolRaw b.vocabulary → ExportM String
  | .compute who (.row (.inl k)) => pure s!"(.compute {numbers who} (.row {row k}))"
  | .event (.flow .message who peers) t => do return s!"(.event (.flow .message {who} {numbers peers}) {← ty (b := b) t})"
  | .event (.given (.coin k) who peers) t => do return s!"(.event (.given {← coin k} {who} {numbers peers}) {← ty (b := b) t})"
  | _ => unsupported "protocol operation"

def rawStep {b : Emit.Bindings} : Instruction (ProtocolRaw b.vocabulary) (List Role) → ExportM String
  | .op k ns op args => do return s!".op ⟨{k.number}⟩ {numbers ns} {← rawOp (b := b) op} {numbers args}"
  | .guard k who v .reject => pure s!".guard ⟨{k.number}⟩ {numbers who} {v} .reject"
  | _ => unsupported "protocol instruction"

def typedOp {b : Emit.Bindings} {hs : Headers b.vocabulary} {ins outs} :
    ProtocolOp b.vocabulary hs ins outs → ExportM String
  | .compute who (.row key _ _) operands _ _ => do
    let .inl k := (show Sum Zkc.Vocabulary.RowKey Emit.PrimitiveName from key) | unsupported "external row"
    return s!"(ProtocolOp.compute (V := V) (hs := ⟨[], []⟩) {numbers who} (.row {row k} _ rfl) {← located (b := b) operands} rfl (by decide))"
  | .flow .message who peers _ _ => pure s!"(ProtocolOp.flow (V := V) (hs := ⟨[], []⟩) .message {who} {numbers peers} (by decide) (by decide))"
  | .given (.coin k) who peers [] t _ _ _ => do
    return s!"(ProtocolOp.given (V := V) (hs := ⟨[], []⟩) {← coin k} {who} {numbers peers} [] {← ty (b := b) t} ⟨_, rfl, rfl, rfl⟩ (by decide) (by decide))"
  | _ => unsupported "typed protocol operation"

def typedBody {b : Emit.Bindings} {hs : Headers b.vocabulary} :
    {Γ : Ctx (LTy b.vocabulary)} → {outs : List (LTy b.vocabulary)} →
    Term (protocolDialect b.vocabulary hs) Γ outs → ExportM String
  | _, _, .ret vs => pure s!"  .ret {names vs.names true}"
  | _, _, .step k (.op op args) ds rest => do
    return s!"  .op ⟨{k.number}⟩ {← typedOp (b := b) op} {names args.names true} {names ds.toList} <|\n{← typedBody rest}"
  | _, _, .step k (.guard who v _ .reject) _ rest => do
    return s!"  .guard ⟨{k.number}⟩ {numbers who} ⟨{v.name}, rfl⟩ ⟨rfl, by decide, by decide⟩ .reject <|\n{← typedBody rest}"
  | _, _, _ => unsupported "typed protocol instruction"

def renderDefinition {b : Emit.Bindings} : {hs : Headers b.vocabulary} → Defs b.vocabulary hs → ExportM (List Nat × String)
  | _, .protocol _ inputs body _ _ => do return (inputs.toList, ← typedBody (b := b) body)
  | _, _ => unsupported "admitted root shape"

/-- Reflect the stored program and its admitted term separately. The generated erasure
equality is checked by the kernel. A second declaration or an unrepresented instruction
is an export error. No protocol or source identifier participates in this traversal. -/
def program (p : SourcePackage) (ev : p.Admission) : ExportM String := do
  unless p.bindings.rows.isEmpty do unsupported "external primitive binding"
  let [.protocol key roles ins outs (.mk input steps output)] := p.named.definitions
    | unsupported "multi-definition root"
  let (typedInputs, typed) ← renderDefinition (b := p.bindings) ev.admitted.program.defs
  let instrs ← steps.mapM (rawStep (b := p.bindings))
  let portTypes ← located (b := p.bindings) ins
  let outTypes ← located (b := p.bindings) outs
  return "\n".intercalate [
    "abbrev V := (Zkc.Frontend.Emit.Bindings.mk [] (by decide)).vocabulary",
    s!"def stored : NamedProgram V := ⟨[.protocol ⟨{key.number}⟩ {roles} {portTypes} {outTypes}",
    s!"  (.mk {numbers input} [\n    {",\n    ".intercalate instrs}\n  ] {numbers output})]⟩",
    s!"abbrev ports : List (LTy V) := {portTypes}",
    s!"abbrev inputNames : Names ports := {names typedInputs}",
    s!"def body : Term (protocolDialect V ⟨[], []⟩) (Ctx.empty.extend inputNames) {outTypes} :=",
    typed, s!"abbrev header : ProtocolHeader V := ⟨⟨{key.number}⟩, {roles}, ports, {outTypes}, shapeOf body⟩",
    s!"def installed : Typed V := singletonProgram header inputNames body (by protocol_conditions body inputNames {roles})",
    "theorem erasure : stored = erase installed := by decide +kernel",
    "theorem readback {a : Admitted V} (h : admit stored ⟨[], [], [], [], []⟩ = .ok a) : a.program = installed :=",
    "  admitted_eq_of_readback h erasure",
    "theorem admitted_exists : ∃ a, admit stored ⟨[],[],[],[],[]⟩ = .ok a := by",
    "  have ok : (admit stored ⟨[],[],[],[],[]⟩).isOk = true := by decide +kernel",
    "  cases eq : admit stored ⟨[],[],[],[],[]⟩ with",
    "  | ok a => exact ⟨a,rfl⟩", "  | error e => rw [eq] at ok; contradiction", ""]

end Zkc.Frontend.Written
