module

public import Zkc.Frontend.Written.Selection
public import Zkc.Frontend.Written.Algorithm
public import Zkc.Frontend.Written.Package

@[expose] public section
set_option autoImplicit false

namespace Zkc.Frontend.Written
open Zkc.Subject.Print
open Syntax

/-- Match ordered ordinary fields of the selected closed instance by source occurrence,
selector and type, including each role-filtered projection. -/
def checkFields (s : Compile.State) (protocol : InstanceId) (kind : ProtocolView) (place : Span)
    (expected : Array Typed.ViewField) : ExportM Compile.State := do
  let (actual, s) ← evaluate s place (Static.protocolViewFields protocol kind place)
  unless actual == expected do
    refuse place "WK-VIEW" "the ordinary source fields disagree with the selected port or event occurrences"
  return s

def portView (s : Compile.State) (protocol : InstanceId) (code : Typing.ProtocolCode) (where_ : Span) : ExportM (View × Compile.State) := do
  let #[.exchange p v pt ci, .draw owner #[peer] _ di, .exchange sender receiver fr ri] := code.flows
    | refuse where_ "WK-VIEW" "expected a commitment, a verifier draw and a response"
  unless code.roles.size == 2 && p != v && owner == v && peer == p && sender == p && receiver == v &&
      StandardNames.fieldOf? fr == some .bls12381Fr do
    refuse where_ "WK-VIEW" "incompatible message roles or types"
  let site i := do
    let some s := code.sites[i]? | refuse where_ "WK-VIEW" "missing emitted occurrence"
    unless s.part == "value" && s.instruction.isSome && s.iteration.isEmpty &&
        (Typing.SiteEntry.realizations code.sites s.event s.part).size == 1 do
      refuse s.place "WK-VIEW" "expected an unambiguous top-level event"
    pure s
  let (commitment, challenge, response) := (← site ci, ← site di, ← site ri)
  unless [commitment.fieldName, challenge.fieldName, response.fieldName].Nodup do
    refuse where_ "WK-VIEW" "two run fields have the same selector"
  let field (site : Typing.SiteEntry) (type : ClosedType) : Typed.ViewField :=
    ⟨.event site.event, site.fieldName, type⟩
  let comm := field commitment pt
  let draw := field challenge (StandardNames.fieldType .bls12381Fr)
  let reply := field response fr
  let verifier := code.roles.getD v ""
  let s ← checkFields s protocol .run where_ #[comm, draw, reply]
  let s ← checkFields s protocol (.received verifier) where_ #[comm, reply]
  let s ← checkFields s protocol (.coins verifier) where_ #[draw]
  return (⟨commitment, challenge, response, p, v, ← historySort pt where_⟩, s)

/-- The package of one function, in a namespace of its own, with the names by which the
statement of a selected clause refers to it. -/
def functionPackage (label : String) (p : SourcePackage) : ExportM String := do
  let printed := package p
  let [(k, false)] := printed.definitions | unsupported "function with other definitions"
  let scope := label ++ "Package"
  return "\n".intercalate [
    s!"namespace {scope}", printed.text ++ s!"end {scope}",
    s!"abbrev stored{label} := {scope}.stored",
    s!"abbrev {label}Header := {scope}.header{k.number}",
    s!"abbrev {label}Names := {scope}.names{k.number}",
    s!"abbrev {label}Body := {scope}.body{k.number}",
    s!"abbrev installed{label} := {scope}.installed",
    s!"theorem {label}Readback (a : Admitted V) (h : admit stored{label} ⟨[],[],[],[],[]⟩ = .ok a) : " ++
      s!"a.program = installed{label} := {scope}.readback h",
    s!"theorem {label}Admitted : (admit stored{label} ⟨[],[],[],[],[]⟩).isOk = true := by",
    s!"  obtain ⟨a, accepted⟩ := {scope}.admitted_exists",
    s!"  exact (congrArg Except.isOk accepted : _)"]

/-- Use the signature, typed tree and dependency closure of the ordinary function instance.
The property supplies its required signature and checks the source nominal identity. -/
def checkedClause (label : String) (s : Compile.State) (id : DeclarationId) (args : Array StaticValue)
    (at_ : Span) (validate : Compile.State → Array ClosedType → ClosedType → ExportM Unit) :
    ExportM (String × Compile.State) := do
  let ((inst, inputs, result), s) ← evaluate s at_ do
    let inst ← Static.instantiate id args ⟨s.program.nameOf id, at_⟩
    let (inputs, some result) ← Emit.signatureTypes inst | throw (.waiting "a closed result type")
    pure (inst, inputs, result)
  validate s inputs result
  let (_, s) ← evaluate s at_ (Typing.typeBody inst at_)
  let emitted ← (Typing.emitRoot s inst).mapError fun
    | .defect why | .waiting why | .noCoreForm why => s!"{at_.file}:{at_.render}: WK-FUNCTION: {why}"
  let package := emitted.package ⟨[],[],[],[],[]⟩
  let .ok _ := package.checkEvidence | refuse at_ "WK-FUNCTION" "admission refused the selected function"
  return (← functionPackage label package, s)

structure WrittenClause where
  parties : WrittenParties
  view : View
  publicNames : Array String
  contextFields : Array (String × String)
  selection : Selection
  source : ClauseSource
  verifierSpan : Span
  relationName : String
  relationSpan : Span
  extractorName : String
  extractorSpan : Span
  calculations : ExportM (String × String)
  storedRelation : String
  storedExtractor : String
  operands : List Nat

def declarations (s : Compile.State) (selection : Selection) : ExportM WrittenClause := do
  let scheme := selection.scheme
  let some key := s.results.key? scheme.protocol | refuse scheme.span "WK-ROOT" "missing instance"
  let some root := s.program.declarations[key.declaration]? | refuse scheme.span "WK-ROOT" "missing declaration"
  let .protocol proto := root.node | refuse scheme.span "WK-ROOT" "expected a protocol"
  let some (.protocol code) := s.results.body? scheme.protocol | refuse scheme.span "WK-ROOT" "missing typed protocol"
  if code.specificationOnly then refuse proto.span "WK-ROOT" "the selected protocol must be executable"
  let (view, s) ← portView s scheme.protocol code scheme.span
  let parties ← writtenParties scheme code.roles
  let item ← clause s key.declaration selection.clause scheme.span
  let relId ← closedDeclaration item.rel
  let extId ← closedDeclaration item.extractor
  let some rd := s.program.declarations[relId]? | refuse item.rel.span "WK-REF" "missing relation"
  let some ed := s.program.declarations[extId]? | refuse item.extractor.span "WK-REF" "missing extractor"
  let .relation r := rd.node | refuse item.rel.span "WK-REF" "expected a relation"
  let .def e := ed.node | refuse item.extractor.span "WK-REF" "expected a function"
  if let some (.spec sp) := e.modifier then refuse sp "WK-TYPE" "the extractor must be executable"
  for (id, sp) in [(extId, e.span), (relId, r.span)] do
    for spec in (← contractOf s id sp) do
      if let .requires sp .. := spec then refuse sp "WK-CLAUSE" "unsupported precondition on a selected declaration"
  let .body rb := r.binding | refuse r.span "WK-BODY" "relation must have a source body"
  let .body eb := e.binding | refuse e.span "WK-BODY" "extractor must have a source body"
  for d in [root, rd, ed] do
    unless (Static.deployedParameters s.program d).size == 1 &&
        (Static.specificationParameters s.program d).isEmpty &&
        d.scopes.all (fun i => (s.program.scopes[i]?).all (·.whereClause.isNone)) do
      refuse item.where_ "WK-TYPE" "expected one deployed group parameter and no additional constraints"
  let point := StandardNames.groupType .g1
  let scalar := StandardNames.fieldType .bls12381Fr
  unless key.arguments == #[.type point] do refuse scheme.span "WK-ROOT" "expected a G1 specialization"
  let some (.port ..) := proto.head.ports.back?
    | refuse proto.span "WK-PORT" "expected a prover witness"
  let publicNames ← proto.head.ports.pop.mapM fun
    | .port _ name _ _ false => pure name.text
    | _ => refuse proto.span "WK-PORT" "expected public group ports before the witness"
  let inputFields := publicNames.zipIdx.map (fun (name, i) => ⟨.port i, name, point⟩)
  let s ← checkFields s scheme.protocol (.inputs (code.roles.getD view.verifier "")) scheme.span inputFields
  let some schemeDecl := s.program.declarations[scheme.declaration]? | refuse scheme.span "WK-ROOT" "missing scheme"
  let mut contextFields := #[]
  let mut reserved := proto.head.ports.map fun
    | .port _ name .. | .spec _ name .. => name.text
  for line in scheme.lines do
    if let .context sp name type := line then
      if reserved.contains name.text then refuse sp "WK-PORT" s!"duplicate statement field {name.text}"
      reserved := reserved.push name.text
      let (closed, _) ← evaluate s type.span (Static.evalWrittenType {file := schemeDecl.file} type)
      let some standard := StandardNames.typeOf? closed
        | refuse type.span "WK-PORT" "the public context needs a supported standard value type"
      let rendered := ty (b := {}) (standard.mapNominal Sum.inl)
      contextFields := contextFields.push (name.text, rendered)
  unless !publicNames.isEmpty &&
      e.params.size == r.statement.size + 1 do
    refuse item.where_ "WK-PORT" "statement, relation and extractor arities must agree"
  let some #[w] := r.witness | refuse r.span "WK-TYPE" "expected one relation witness"
  let some runs := e.params.back? | refuse e.span "WK-VIEW" "missing extractor run view"
  if item.arguments.any (fun | .spec .. => true | _ => false) then
    refuse item.where_ "WK-PORT" "expected public statement arguments"
  let values ← match Lowered.pairValueArguments r.name.text (r.statement.map (·.name.text))
      item.arguments item.where_ with
    | .ok values => pure values
    | .error (span, message) => refuse span "FN6" message
  let operands ← values.mapM fun
    | .local _ port => pure port
    | e => refuse e.span "WK-PORT" "expected a public port operand"
  unless operands.all (· < publicNames.size) do
    refuse item.where_ "WK-PORT" "the relation needs a port outside the public statement"
  let bind (params : Array Param) : Locals := (params.zip operands).toList.map fun (p, v) =>
    (p.name.text, ⟨.point, component "statement" v (v + 1 == publicNames.size)⟩)
  let publics := Array.replicate operands.size point
  let (rt, s) ← checkedClause "Relation" s relId key.arguments r.span fun _ params result => do
    unless params == publics.push scalar && result == .bool do
      refuse r.span "WK-TYPE" "unexpected relation signature at the selected instance"
  let (et, _) ← checkedClause "Extractor" s extId key.arguments e.span fun state params result => do
    unless params.pop == publics && result == scalar do
      refuse e.span "WK-TYPE" "unexpected extractor signature at the selected instance"
    let some (.seq (.record leaf) (some 2)) := params.back?
      | refuse runs.type.span "WK-VIEW" "expected a two-leaf run view"
    unless state.results.key? leaf == some {key with view := some .run} do
      refuse runs.type.span "WK-VIEW" "different protocol specialization"
  let calculations : ExportM (String × String) := do
    let relation ← algorithm view ((w.name.text, ⟨.scalar,"witness"⟩) :: bind r.statement) .boolean rb
    let extraction ← algorithm view ((runs.name.text, ⟨.runs,""⟩) :: bind e.params.pop) .scalar eb
    return (relation, extraction)
  return ⟨parties,view,publicNames,contextFields,selection,item,proto.span,r.name.text,r.span,e.name.text,e.span,calculations,rt,et,operands.toList⟩

end Zkc.Frontend.Written
