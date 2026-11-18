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

partial def ty {b : Emit.Bindings} (t : b.vocabulary.Ty) : ExportM String := do
  match t with
  | .bool => pure ".bool"
  | .nominal (.inl k) => pure s!"(.nominal (.inl ({reprStr (show Zkc.Vocabulary.TypeKey from k)})))"
  | .tuple ts =>
    let items ← ts.toList.mapM (ty (b := b))
    return "(.tuple " ++ items.foldr (fun x rest => s!"(.cons {x} {rest})") ".nil" ++ ")"
  | _ => unsupported "Core value type in the written scalar/group profile"

def localRaw {b : Emit.Bindings} : LocalRaw b.vocabulary → ExportM String
  | .row (.inl key) => pure s!"(.row (.inl ({reprStr (show Zkc.Vocabulary.RowKey from key)})))"
  | .owned name ts args => do
    return s!"(.owned ({reprStr name}) {list (← ts.mapM (ty (b := b)))} {numbers args})"
  | .literal t data => do return s!"(.literal {← ty (b := b) t} {numbers data})"
  | _ => unsupported "nonprimitive function call in a written declaration"

mutual
  partial def functionRegion {b : Emit.Bindings} : Region (LocalRaw b.vocabulary) Unit → ExportM String
    | .mk ins steps outs => do
      return s!"(.mk {numbers ins} {list (← steps.mapM (functionStep (b := b)))} {numbers outs})"

  partial def functionStep {b : Emit.Bindings} : Instruction (LocalRaw b.vocabulary) Unit → ExportM String
    | .op k out op vs => do return s!".op ⟨{k.number}⟩ {numbers out} {← localRaw (b := b) op} {numbers vs}"
    | .guard k () x .reject => pure s!".guard ⟨{k.number}⟩ () {x} .reject"
    | .choose k () x outs yes no => do
      return s!".choose ⟨{k.number}⟩ () {x} {numbers outs} {← functionRegion yes} {← functionRegion no}"
    | _ => unsupported "control flow in a written function"
end

def storedFunction {b : Emit.Bindings} : Definition b.vocabulary → ExportM String
  | .fn k ins outs stop none ⟨[], []⟩ body [] => do
    let params ← ins.mapM (ty (b := b))
    let results ← outs.mapM (ty (b := b))
    return s!"⟨[.fn ⟨{k.number}⟩ {list params} {list results} {stop} none ⟨[],[]⟩ {← functionRegion body}]⟩"
  | _ => unsupported "function header in a written declaration"

def functionOp {b : Emit.Bindings} {hs ins outs} : LocalOp b.vocabulary hs ins outs → ExportM String
  | .row key _ _ => do
    let .inl k := (show Sum Zkc.Vocabulary.RowKey Emit.PrimitiveName from key) | unsupported "external row"
    return s!"(LocalOp.row (V := V) (fns := []) (.inl ({reprStr k})) _ rfl)"
  | .owned op => do
    let (name, types, args) := op.name
    return s!"(LocalOp.owned (V := V) (fns := []) ((OwnedOp.resolve (V := V) ({reprStr name}) {list (← types.mapM (ty (b := b)))} {numbers args}).get (by decide)).2.2)"
  | .literal t data _ => do return s!"(LocalOp.literal (V := V) (fns := []) {← ty (b := b) t} {numbers data} (by decide))"
  | _ => unsupported "unlinked local operation"

partial def functionBody {b : Emit.Bindings} {hs : List (FnHeader b.vocabulary)} :
    {Γ : Ctx b.vocabulary.Ty} → {outs : List b.vocabulary.Ty} → Term (localDialect b.vocabulary hs) Γ outs → ExportM String
  | _, _, .ret vs => pure s!".ret {names vs.names true}"
  | _, _, .step k (.op op args) ns tail => do
    return s!".op ⟨{k.number}⟩ {← functionOp (b := b) op} {names args.names true} {names ns.toList} <|\n{← functionBody tail}"
  | _, _, .step k (.guard _ c _ .reject) _ tail => do
    return s!".guard ⟨{k.number}⟩ () ⟨{c.name},rfl⟩ rfl .reject <|\n{← functionBody tail}"
  | _, _, .step k (.choose _ c _ _ yes no) ns tail => do
    return s!".step ⟨{k.number}⟩ (.choose () ⟨{c.name},rfl⟩ rfl (by intros; trivial) ({← functionBody yes}) ({← functionBody no})) {names ns.toList} <|\n{← functionBody tail}"
  | _, _, _ => unsupported "local instruction"

def renderFunction {b : Emit.Bindings} : {hs : Headers b.vocabulary} → Defs b.vocabulary hs → ExportM (List Nat × String)
  | _, .fn _ ns fn _ _ _ => do return (ns.toList, ← functionBody (b := b) fn)
  | _, _ => unsupported "local root"

def functionDeclarations (label : String) (p : SourcePackage) (ev : p.Admission) : ExportM String := do
  let [defn@(.fn k ins outs stop _ _ _ _)] := p.named.definitions | unsupported "local root"
  let (ns, typed) ← renderFunction (b := p.bindings) ev.admitted.program.defs
  let hdr := s!"⟨⟨{k.number}⟩, {list (← ins.mapM (ty (b := p.bindings)))}, {list (← outs.mapM (ty (b := p.bindings)))}, {stop}, none, ⟨[],[]⟩⟩"
  return "\n".intercalate [
    s!"def stored{label} : NamedProgram V := {← storedFunction defn}",
    s!"abbrev {label}Header : FnHeader V := {hdr}",
    s!"abbrev {label}Names : Names {label}Header.ins := {names ns}",
    s!"def {label}Body : Fn V [] {label}Header {label}Names :=\n{typed}",
    s!"def installed{label} := singletonFunction {label}Header {label}Names {label}Body (by function_conditions {label}Body {label}Names)",
    s!"theorem {label}Readback (a : Admitted V) (h : admit stored{label} ⟨[],[],[],[],[]⟩ = .ok a) : a.program = installed{label} := admitted_eq_of_readback h (by decide +kernel)",
    s!"theorem {label}Admitted : (admit stored{label} ⟨[],[],[],[],[]⟩).isOk = true := by decide +kernel"]
def located {b : Emit.Bindings} (ts : List (LTy b.vocabulary)) : ExportM String := do
  return list (← ts.mapM fun a => do return s!"⟨{← ty (b := b) a.ty}, {numbers a.holders}⟩")

def row (k : Zkc.Vocabulary.RowKey) := s!"(show V.RowKey from .inl ({reprStr k}))"

def coin (k : Zkc.Vocabulary.LawKey) : ExportM String :=
  match k with
  | .uniform (.nominal t) => pure s!"(.coin (.uniform (.nominal ({reprStr t}))))"
  | _ => unsupported "sampling law"

def rawOp {b : Emit.Bindings} : ProtocolRaw b.vocabulary → ExportM String
  | .compute who (.row (.inl k)) => pure s!"(.compute {numbers who} (.row {row k}))"
  | .compute who (.owned name types args) => do
    return s!"(.compute {numbers who} (.owned ({reprStr name}) {list (← types.mapM (ty (b := b)))} {numbers args}))"
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
  | .compute who (.owned op) operands _ _ => do
    let (name, types, args) := op.name
    let types ← types.mapM (ty (b := b))
    let owned := s!"(OwnedOp.resolve (V := V) ({reprStr name}) {list types} {numbers args}).get (by decide)"
    return s!"(ProtocolOp.compute (V := V) (hs := ⟨[], []⟩) {numbers who} (.owned ({owned}).2.2) {← located (b := b) operands} rfl (by decide))"
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
