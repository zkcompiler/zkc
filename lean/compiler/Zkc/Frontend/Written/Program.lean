module

public import Zkc.Frontend.Emit.Reports
public import Zkc.Frontend.Written.LeanTerms

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Core

def names (xs : List Nat) (variableRefs := false) := xs.foldr (fun x rest =>
  let head := if variableRefs then s!"⟨{x}, rfl⟩" else toString x
  s!"(.cons {head} {rest})") ".nil"

def localRaw {b : Emit.Bindings} : LocalRaw b.vocabulary → ExportM String
  | .row (.inl key) => pure s!"(.row (.inl ({reprStr (show Zkc.Vocabulary.RowKey from key)})))"
  | .owned name ts args => do
    return s!"(.owned ({reprStr name}) {list (← ts.mapM (ty (b := b)))} {numbers args})"
  | .literal t data => do return s!"(.literal {← ty (b := b) t} {numbers data})"
  | .call k => pure s!"(.call ⟨{k.number}⟩)"
  | .row (.inr _) => unsupported "external row"

mutual
  partial def functionRegion {b : Emit.Bindings} : Region (LocalRaw b.vocabulary) Unit → ExportM String
    | .mk ins steps outs => do
      return s!"(.mk {numbers ins} {list (← steps.mapM (functionStep (b := b)))} {numbers outs})"

  partial def functionStep {b : Emit.Bindings} : Instruction (LocalRaw b.vocabulary) Unit → ExportM String
    | .op k out op vs => do return s!".op ⟨{k.number}⟩ {numbers out} {← localRaw (b := b) op} {numbers vs}"
    | .guard k () x why => pure s!".guard ⟨{k.number}⟩ () {x} ({reprStr why})"
    | .choose k () x outs yes no => do
      return s!".choose ⟨{k.number}⟩ () {x} {numbers outs} {← functionRegion yes} {← functionRegion no}"
    | .cases k () x outs arms => do
      return s!".cases ⟨{k.number}⟩ () {x} {numbers outs} {list (← arms.mapM (functionRegion (b := b)))}"
    | .loop k () times init outs body => do
      return s!".loop ⟨{k.number}⟩ () ({reprStr times}) {numbers init} {numbers outs} {← functionRegion body}"
    | .block k n outs body => do
      return s!".block ⟨{k.number}⟩ {n} {numbers outs} {← functionRegion body}"
    | .attempt k () outs body => do
      return s!".attempt ⟨{k.number}⟩ () {numbers outs} {← functionRegion body}"
end

def storedFunction {b : Emit.Bindings} : Definition b.vocabulary → ExportM String
  | .fn k ins outs stop none ⟨[], []⟩ body [] => do
    let params ← ins.mapM (ty (b := b))
    let results ← outs.mapM (ty (b := b))
    return s!".fn ⟨{k.number}⟩ {list params} {list results} {stop} none ⟨[],[]⟩ {← functionRegion body}"
  | _ => unsupported "function header in a written declaration"

def memberTerm {α : Type} : {xs : List α} → {x : α} → Member xs x → String
  | _, _, .head => ".head"
  | _, _, .tail ref => s!"(.tail {memberTerm ref})"

def functionOp {b : Emit.Bindings} {hs ins outs} (headers : String) :
    LocalOp b.vocabulary hs ins outs → ExportM String
  | .row key _ _ => do
    let .inl k := (show Sum Zkc.Vocabulary.RowKey Emit.PrimitiveName from key) | unsupported "external row"
    return s!"(LocalOp.row (V := V) (fns := {headers}) (.inl ({reprStr k})) _ rfl)"
  | .owned op => do
    let (name, types, args) := op.name
    return s!"(LocalOp.owned (V := V) (fns := {headers}) ((OwnedOp.resolve (V := V) ({reprStr name}) {list (← types.mapM (ty (b := b)))} {numbers args}).get (by decide)).2.2)"
  | .literal t data _ => do
    return s!"(LocalOp.literal (V := V) (fns := {headers}) {← ty (b := b) t} {numbers data} (by decide))"
  | .call ref => return s!"(LocalOp.call (V := V) (fns := {headers}) {memberTerm ref})"

mutual
  partial def functionBody {b : Emit.Bindings} {hs : List (FnHeader b.vocabulary)} (headers : String) :
      {Γ : Ctx b.vocabulary.Ty} → {outs : List b.vocabulary.Ty} →
      Term (localDialect b.vocabulary hs) Γ outs → ExportM String
    | _, _, .ret vs => pure s!".ret {names vs.names true}"
    | _, _, .step k (.op op args) ns tail => do
      return s!".op ⟨{k.number}⟩ {← functionOp (b := b) headers op} {names args.names true} {names ns.toList} <|\n{← functionBody headers tail}"
    | _, _, .step k (.guard _ c _ why) _ tail => do
      return s!".guard ⟨{k.number}⟩ () ⟨{c.name},rfl⟩ rfl ({reprStr why}) <|\n{← functionBody headers tail}"
    | _, _, .step k (.choose (mid := mid) _ c _ _ yes no) ns tail => do
      let types := list (← mid.mapM (ty (b := b)))
      return s!".choose (mid := {types}) ⟨{k.number}⟩ () ⟨{c.name},rfl⟩ rfl (by intros; trivial) ({← functionBody headers yes}) ({← functionBody headers no}) {names ns.toList} <|\n{← functionBody headers tail}"
    | _, _, .step k (.cases (mid := mid) _ x _ _ arms) ns tail => do
      let types := list (← mid.mapM (ty (b := b)))
      return s!".cases (mid := {types}) ⟨{k.number}⟩ () ⟨{x.name},rfl⟩ ⟨_,_,rfl,rfl⟩ (by intros; trivial) {← functionArms headers arms} {names ns.toList} <|\n{← functionBody headers tail}"
    | _, _, .step k (.loop (carried := carried) (each := each) _ count _ init inputs body) ns tail => do
      let times := match count with
        | .fixed n => s!"(.fixed {n})"
        | .value v _ => s!"(.value ⟨{v.name},rfl⟩ rfl)"
      let carriedTypes := list (← carried.mapM (ty (b := b)))
      let eachTypes := list (← each.mapM (ty (b := b)))
      return s!".loop (carried := {carriedTypes}) (each := {eachTypes}) ⟨{k.number}⟩ () {times} (by intros; trivial) {names init.names true} {names inputs.toList} ({← functionBody headers body}) {names ns.toList} <|\n{← functionBody headers tail}"
    | _, _, .step k (.block (mid := mid) n inner) ns tail => do
      return s!".block (mid := {list (← mid.mapM (ty (b := b)))}) ⟨{k.number}⟩ {n} ({← functionBody headers inner}) {names ns.toList} <|\n{← functionBody headers tail}"
    | _, _, .step _ (.attempt _ impossible ..) .. => nomatch impossible

  partial def functionArms {b : Emit.Bindings} {hs : List (FnHeader b.vocabulary)} (headers : String) :
      {Γ : Ctx b.vocabulary.Ty} → {mid payloads : List b.vocabulary.Ty} →
      Arms (localDialect b.vocabulary hs) Γ mid payloads → ExportM String
    | _, _, _, .nil => pure ".nil"
    | _, _, _, .cons inputs arm rest => do
      return s!"(.cons {names inputs.toList} ({← functionBody headers arm}) {← functionArms headers rest})"
end

/-- Render each admitted function once, against exactly its preceding definitions. -/
def functionClosure {b : Emit.Bindings} (label : String) (root : Option Key) :
    {hs : Headers b.vocabulary} → Defs b.vocabulary hs → ExportM (List String × String)
  | _, .nil => pure ([], "(Typed.empty (V := V))")
  | _, .fn hdr ns body _ rest _ => do
    let (decls, earlier) ← functionClosure label root rest
    let name := if root == some hdr.key then label else s!"{label}Fn{hdr.key.number}"
    let params := list (← hdr.ins.mapM (ty (b := b)))
    let results := list (← hdr.outs.mapM (ty (b := b)))
    let headers := s!"{name}Dependencies.headers.fns"
    let installed := s!"{name}Program"
    return (decls ++ [
      s!"abbrev {name}Dependencies := {earlier}",
      s!"abbrev {name}Header : FnHeader V := ⟨⟨{hdr.key.number}⟩, {params}, {results}, {hdr.canStop}, none, ⟨[],[]⟩⟩",
      s!"abbrev {name}Names : Names {name}Header.ins := {names ns.toList}",
      s!"def {name}Body : Fn V {headers} {name}Header {name}Names :=\n{← functionBody headers body}",
      s!"def {installed} := {name}Dependencies.add (.fn {name}Header {name}Names {name}Body (by function_conditions {name}Body {name}Names) (by decide))"], installed)
  | _, .protocol .. => unsupported "protocol in a local function closure"

def functionDeclarations (label : String) (root : Key) (p : SourcePackage) (ev : p.Admission) : ExportM String := do
  unless p.bindings.rows.isEmpty do unsupported "external primitive binding"
  let some (.fn ref) := ev.admitted.program.find root | unsupported "missing selected function"
  let stored ← p.named.definitions.mapM (storedFunction (b := p.bindings))
  let (decls, installed) ← functionClosure label (some root) ev.admitted.program.defs
  return "\n".intercalate <| [s!"def stored{label} : NamedProgram V := ⟨{list stored}⟩"] ++ decls ++ [
    s!"abbrev installed{label} := {installed}",
    s!"abbrev {label}Root : Member installed{label}.headers.fns {label}Header := {memberTerm ref}",
    s!"theorem {label}Readback (a : Admitted V) (h : admit stored{label} ⟨[],[],[],[],[]⟩ = .ok a) : a.program = installed{label} := admitted_eq_of_readback h (by decide +kernel)",
    s!"theorem {label}Admitted : (admit stored{label} ⟨[],[],[],[],[]⟩).isOk = true := by decide +kernel"]

def located {b : Emit.Bindings} (ts : List (LTy b.vocabulary)) : ExportM String := do
  return list (← ts.mapM fun a => do return s!"⟨{← ty (b := b) a.ty}, {numbers a.holders}⟩")

def rawOp {b : Emit.Bindings} : ProtocolRaw b.vocabulary → ExportM String
  | .compute who op => do return s!"(.compute {numbers who} {← localRaw (b := b) op})"
  | .event (.flow .message who peers) t => do return s!"(.event (.flow .message {who} {numbers peers}) {← ty (b := b) t})"
  | .event (.given (.coin k) who peers) t => do return s!"(.event (.given {← coin k} {who} {numbers peers}) {← ty (b := b) t})"
  | _ => unsupported "protocol operation"

mutual
  partial def rawRegion {b : Emit.Bindings} : Region (ProtocolRaw b.vocabulary) (List Role) → ExportM String
    | .mk ins steps outs => do
      return s!"(.mk {numbers ins} {list (← steps.mapM (rawStep (b := b)))} {numbers outs})"

  partial def rawStep {b : Emit.Bindings} : Instruction (ProtocolRaw b.vocabulary) (List Role) → ExportM String
    | .op k ns op args => do return s!".op ⟨{k.number}⟩ {numbers ns} {← rawOp (b := b) op} {numbers args}"
    | .guard k who v .reject => pure s!".guard ⟨{k.number}⟩ {numbers who} {v} .reject"
    | .choose k who v ns yes no => do
      return s!".choose ⟨{k.number}⟩ {numbers who} {v} {numbers ns} {← rawRegion yes} {← rawRegion no}"
    | .loop k who count init ns body => do
      let times := match count with | .fixed n => s!"(.fixed {n})" | .count n => s!"(.count {n})"
      return s!".loop ⟨{k.number}⟩ {numbers who} {times} {numbers init} {numbers ns} {← rawRegion body}"
    | _ => unsupported "protocol instruction"
end

def typedOp {b : Emit.Bindings} {hs : Headers b.vocabulary} {ins outs} :
    ProtocolOp b.vocabulary hs ins outs → ExportM String
  | .compute who op operands _ _ => do
    return s!"(ProtocolOp.compute (V := V) (hs := protocolDependencies.headers) {numbers who} {← functionOp (b := b) "protocolDependencies.headers.fns" op} {← located (b := b) operands} rfl (by decide))"
  | .flow .message who peers _ _ => pure s!"(ProtocolOp.flow (V := V) (hs := protocolDependencies.headers) .message {who} {numbers peers} (by decide) (by decide))"
  | .given (.coin k) who peers [] t _ _ _ => do
    return s!"(ProtocolOp.given (V := V) (hs := protocolDependencies.headers) {← coin k} {who} {numbers peers} [] {← ty (b := b) t} ⟨_, rfl, rfl, rfl⟩ (by decide) (by decide))"
  | _ => unsupported "typed protocol operation"

partial def typedBody {b : Emit.Bindings} {hs : Headers b.vocabulary} :
    {Γ : Ctx (LTy b.vocabulary)} → {outs : List (LTy b.vocabulary)} →
    Term (protocolDialect b.vocabulary hs) Γ outs → ExportM String
  | _, _, .ret vs => pure s!"  .ret {names vs.names true}"
  | _, _, .step k (.op op args) ds rest => do
    return s!"  .op ⟨{k.number}⟩ {← typedOp (b := b) op} {names args.names true} {names ds.toList} <|\n{← typedBody rest}"
  | _, _, .step k (.guard who v _ .reject) _ rest => do
    return s!"  .guard ⟨{k.number}⟩ {numbers who} ⟨{v.name}, rfl⟩ ⟨rfl, by decide, by decide⟩ .reject <|\n{← typedBody rest}"
  | _, _, .step k (.choose (mid := mid) who v _ _ yes no) ds rest => do
    return s!"  .choose (mid := {← located (b := b) mid}) ⟨{k.number}⟩ {numbers who} ⟨{v.name}, rfl⟩ ⟨rfl, by decide, by decide⟩ (by decide) ({← typedBody yes}) ({← typedBody no}) {names ds.toList} <|\n{← typedBody rest}"
  | _, _, .step k (.loop (carried := carried) (each := each) who times _ init inputs inner) ds rest => do
    let count := match times with
      | .fixed n => s!"(.fixed {n})"
      | .value v _ => s!"(.value ⟨{v.name}, rfl⟩ ⟨rfl, by decide, by decide⟩)"
    return s!"  .loop (carried := {← located (b := b) carried}) (each := {← located (b := b) each}) ⟨{k.number}⟩ {numbers who} {count} (by decide) {names init.names true} {names inputs.toList} ({← typedBody inner}) {names ds.toList} <|\n{← typedBody rest}"
  | _, _, _ => unsupported "typed protocol instruction"

def protocolClosure {b : Emit.Bindings} :
    {hs : Headers b.vocabulary} → Defs b.vocabulary hs →
    ExportM (List String × String × List Nat × String)
  | _, .protocol _ ns body _ earlier => do
    let (decls, dependencies) ← functionClosure "Protocol" none earlier
    return (decls, dependencies, ns.toList, ← typedBody (b := b) body)
  | _, _ => unsupported "admitted protocol root"

/-- Preserve the local function table in both the stored package and the projected role. -/
def program (p : SourcePackage) (ev : p.Admission) : ExportM String := do
  unless p.bindings.rows.isEmpty do unsupported "external primitive binding"
  let some (.protocol key roles ins outs (.mk input steps output)) := p.named.definitions.getLast?
    | unsupported "protocol root"
  let stored ← p.named.definitions.dropLast.mapM (storedFunction (b := p.bindings))
  let (decls, dependencies, inputs, typed) ← protocolClosure (b := p.bindings) ev.admitted.program.defs
  let instrs ← steps.mapM (rawStep (b := p.bindings))
  let portTypes ← located (b := p.bindings) ins
  let outTypes ← located (b := p.bindings) outs
  return "\n".intercalate <| ["abbrev V := (Zkc.Frontend.Emit.Bindings.mk [] (by decide)).vocabulary"] ++ decls ++ [
    s!"abbrev protocolDependencies := {dependencies}",
    s!"def stored : NamedProgram V := ⟨{list stored} ++ [.protocol ⟨{key.number}⟩ {roles} {portTypes} {outTypes}",
    s!"  (.mk {numbers input} [\n    {",\n    ".intercalate instrs}\n  ] {numbers output})]⟩",
    s!"abbrev ports : List (LTy V) := {portTypes}",
    s!"abbrev inputNames : Names ports := {names inputs}",
    s!"def body : Term (protocolDialect V protocolDependencies.headers) (Ctx.empty.extend inputNames) {outTypes} :=",
    typed, s!"abbrev header : ProtocolHeader V := ⟨⟨{key.number}⟩, {roles}, ports, {outTypes}, shapeOf body⟩",
    s!"def installed : Typed V := protocolDependencies.add (.protocol header inputNames body (by protocol_conditions body inputNames {roles}) (by decide))",
    "theorem erasure : stored = erase installed := by decide +kernel",
    "theorem readback {a : Admitted V} (h : admit stored ⟨[], [], [], [], []⟩ = .ok a) : a.program = installed :=",
    "  admitted_eq_of_readback h erasure",
    "theorem admitted_exists : ∃ a, admit stored ⟨[],[],[],[],[]⟩ = .ok a := by",
    "  have ok : (admit stored ⟨[],[],[],[],[]⟩).isOk = true := by decide +kernel",
    "  cases eq : admit stored ⟨[],[],[],[],[]⟩ with",
    "  | ok a => exact ⟨a,rfl⟩", "  | error e => rw [eq] at ok; contradiction", ""]

end Zkc.Frontend.Written
