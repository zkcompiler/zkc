module

public import ZkcTools.StructuredSource.NormalForm
public import ZkcTools.StructuredSource.Presentation.Syntax
public import Zkc.Source.Structured.NormalForm.Presentation
public import Zkc.Source.Structured.NormalForm.Sites
public import Zkc.Source.KernelRfl

@[expose] public section

/-! Untrusted, Lean-owned printing of the existing typed participant forms.

`render` consumes a Form, never a second execution of its source. `request`
uses the existing normalizer and its call-identity check. The returned source
is accepted only after its literal, call identities, and presentation equations
have been checked by the kernel. Expression hints are proposals, not laws.

Names have numeric identities; labels only decorate those identities. Sites,
helper signatures, callee signatures, callback bodies, and scope positions are
printed from the typed data, without a protocol registry or filesystem access.
-/

set_option autoImplicit false
namespace ZkcTools.StructuredSource.Presentation
open Lean Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm

variable {laws : List LawKey} {callees : List CalleeKey}

/-- Uniform roots may choose their existing F/G notation; domain mode keeps nominal carriers. -/
inductive Carriers where
  | domain (model : String)
  | uniform (field group : String)
  deriving Inhabited
def Carriers.model : Carriers → String
  | .domain model => paren model | .uniform f g => app "ringModel" [f, g]
def Carriers.value : Carriers → String
  | .domain model => paren model ++ ".Value" | .uniform f g => app "assignment" [f, g]
def Carriers.valueType (carriers : Carriers) (ty : Ty) : String :=
  match carriers, ty with
  | _, .index | _, .service _ => "Nat" | _, .boolean => "Bool"
  | .uniform f _, .field _ => f | .uniform f _, .vector _ => app "List" [f]
  | .uniform _ g, .group _ => g
  | .domain model, .field d => paren model ++ ".Field " ++ quoted d
  | .domain model, .vector d => app "List" [paren (paren model ++ ".Field " ++ quoted d)]
  | .domain model, .group d => paren model ++ ".Group " ++ quoted d
  | _, .indices | _, .groups _ | _, .oracle _ | _, .oracleSequence ..
  | _, .sequence _ | _, .product .. => app carriers.value [tyText ty]

def emptyLabels : (Δ : Scope) → Values (fun _ => Option String) Δ
  | [] => .nil | _ :: rest => .cons none (emptyLabels rest)

/-- All expression hints are untrusted. A helper is selected by its complete
signature; laws and callees by typed positions in this exact request. -/
structure Naming (laws : List LawKey) (callees : List CalleeKey) (Δ : Scope) where
  inputs : Values (fun _ => Option String) Δ := emptyLabels Δ
  carriers : Carriers := .domain "model"
  tables : String := "tables"
  results : String := "results"
  context : String := "ctx"
  runs : String := "runs"
  processes : String := "processes"
  helpers : List (Helper × String) := []
  lawResult : (entry : Fin laws.length) → Nat → Option String := fun _ _ => none
  callee : Fin callees.length → Option String := fun _ => none
  callback : (spec : RepeatSpec) →
    Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state → Option String := fun _ _ => none
  callbackBody : (spec : RepeatSpec) →
    Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state → Option String := fun _ _ => none
  /-- Optional readable head for the existing repeat denotation. Its complete
  application is still checked by the presentation equation. -/
  repeatHead : RepeatSpec → Option String := fun _ => none
  /-- Labels for newly bound values, by their globally unique numeric ID. -/
  label : Nat → Option String := fun _ => none

def labelSuffix (label : Option String) : String :=
  match label with
  | none => ""
  | some text =>
    let text := String.ofList (text.toList.filter fun c =>
      ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_')
    if text.isEmpty then "" else "_" ++ text
def binderName (id : Nat) (label : Option String) : String := "b" ++ toString id ++ labelSuffix label
def inputNames : {Δ : Scope} → Values (fun _ => Option String) Δ → Nat → List String
  | _, .nil, _ => []
  | _, .cons label rest, id => binderName id label :: inputNames rest (id + 1)

/-- Parenthesized substitution avoids precedence changes in optional readable laws. -/
def fill (template : String) (args : List String) : String :=
  args.zipIdx.foldl (fun text (arg, i) => text.replace ("{" ++ toString i ++ "}") (paren arg)) template

variable {initial : Scope}

mutual
  def termText (naming : Naming laws callees initial) (names : List String) {Δ : Scope} {ty : Ty} :
      Term laws Δ ty → String
    | .var b => names[b.index]!
    | .result b p => paren names[b.index]! ++ ".get " ++ positionText p.index
    | .capability _ handle => toString handle
    | .index n => toString n | .bool b => boolText b
    | .field d n => app "fieldLiteral" [naming.carriers.model ++ ".toFieldModel", quoted d, toString n]
    | .groupZero d => "(0 : " ++ naming.carriers.valueType (.group d) ++ ")"
    | .calc op _ args p =>
      let texts := termsText naming names args
      let binary (symbol : String) := paren (texts[0]! ++ " " ++ symbol ++ " " ++ texts[1]!)
      match op with
      | .fieldAdd _ | .groupAdd _ => binary "+"
      | .fieldSubtract _ => binary "-" | .fieldMultiply _ => binary "*"
      | .booleanAnd => binary "&&" | .booleanOr => binary "||"
      | .booleanEqual => binary "==" | .booleanNotEqual => binary "!="
      | .booleanXor => app "xor" texts
      | .fieldEmbed extension base => app (naming.carriers.model ++ ".embed") (quoted extension :: quoted base :: texts)
      | .groupScale group field => app (naming.carriers.model ++ ".smul")
          [quoted group, quoted field, texts[1]!, texts[0]!]
      | .select _ => paren ("if " ++ texts[0]! ++ " then " ++ texts[1]! ++ " else " ++ texts[2]!)
      | _ => app (app "Op.evalTotal" [naming.carriers.model, opText op, "rfl", valuesText texts] ++ ".get")
          [positionText p.index]
    | .law entry args p =>
      let args := termsText naming names args
      match naming.lawResult entry p.index with
      | some template => paren (fill template args)
      | none => app (app (paren naming.results ++ ".result") [finText entry.val, valuesText args] ++ ".get")
          [positionText p.index]
  def termsText (naming : Naming laws callees initial) (names : List String) {Δ : Scope} {types : List Ty} :
      Terms laws Δ types → List String
    | .nil => [] | .cons x xs => paren (termText naming names x) :: termsText naming names xs
end

def compText (naming : Naming laws callees initial) (names : List String) {Δ : Scope} {ty : Ty} :
    Comp laws Δ ty → String
  | .absent => "none" | .present term => app "some" [paren (termText naming names term)]
  | .input b => names[b.index]!
  | .read b p => paren names[b.index]! ++ ".get " ++ positionText p.index
def compsText (naming : Naming laws callees initial) (names : List String) {Δ : Scope} :
    {types : List Ty} → Values (Comp laws Δ) types → List String
  | _, .nil => [] | _, .cons x xs => paren (compText naming names x) :: compsText naming names xs
def argumentsText (naming : Naming laws callees initial) (names : List String) {Δ : Scope} :
    {scope : Scope} → Values (Argument laws Δ) scope → List String
  | [], .nil => []
  | .value _ :: _, .cons x xs => paren (termText naming names x) :: argumentsText naming names xs
  | .component _ :: _, .cons x xs => paren (compText naming names x) :: argumentsText naming names xs
  | .results _ :: _, .cons x xs => valuesText (termsText naming names x) :: argumentsText naming names xs
  | .tuple _ :: _, .cons x xs => valuesText (compsText naming names x) :: argumentsText naming names xs

inductive Finish (out : List Ty) where
  | outputs
  | presented (spec : Values (fun _ => Carried) out)

def presentedText (naming : Naming laws callees initial) (names : List String) {Δ : Scope} :
    {out : List Ty} → Values (fun _ => Carried) out → Values (Comp laws Δ) out → List String
  | _, .nil, .nil => []
  | _, .cons .absent rest, .cons _ values => presentedText naming names rest values
  | _, .cons .present rest, .cons comp values =>
    (match comp.term? with
      | some term => paren (termText naming names term)
      | none => "none") :: presentedText naming names rest values
  | _, .cons .optional rest, .cons comp values => paren (compText naming names comp) :: presentedText naming names rest values
def tupleText : List String → String
  | [] => "()" | [x] => x | x :: xs => paren (x ++ ", " ++ tupleText xs)

def helperExpression (naming : Naming laws callees initial) (helper : Helper) : String :=
  (naming.helpers.find? (fun entry => entry.1 == helper)).map (paren ∘ Prod.snd) |>.getD (helperText helper)
def siteExpression (naming : Naming laws callees initial) (site : String) : String :=
  app "qualifyProtocolSite" [paren naming.context ++ ".applicationPrefix", quoted site]
def roleExpression (naming : Naming laws callees initial) (role : Nat) : String :=
  app (paren naming.context ++ ".roles") [toString role]
def valuesType (naming : Naming laws callees initial) (types : List Ty) (components : Bool) : String :=
  app "Values" [if components then app "Component" [naming.carriers.value] else naming.carriers.value, typesText types]
def pad (indent : Nat) : String := String.ofList (List.replicate indent ' ')

/-- The state is a numeric binder supply, independent of labels or source names. -/
def fresh (naming : Naming laws callees initial) : StateM Nat String := do
  let id ← get
  set (id + 1)
  return binderName id (naming.label id)

def processText (naming : Naming laws callees initial) {out : List Ty} (finish : Finish out) :
    {Δ : Scope} → List String → Form laws callees Δ out → Nat → StateM Nat String
  | _, names, .done values, indent => pure (pad indent ++ ".done " ++ (match finish with
      | .outputs => paren (valuesText (compsText naming names values) ++ " : " ++ valuesType naming out true)
      | .presented spec => tupleText (presentedText naming names spec values)))
  | _, _, .halt reason, indent => pure (pad indent ++ ".halt " ++ stopText reason)
  | _, names, .send ty site peer value next, indent => do
    let action := app ".send" ["(ty := " ++ tyText ty ++ ")", siteExpression naming site,
      roleExpression naming peer, paren (termText naming names value)]
    return pad indent ++ ".call " ++ action ++ " fun _ =>\n" ++ (← processText naming finish names next indent)
  | _, names, .receive ty site peer next, indent => do
    let name ← fresh naming
    let action := app ".receive" [tyText ty, siteExpression naming site, roleExpression naming peer]
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ ".call " ++ action ++ " fun (" ++ binder ++ " : " ++ naming.carriers.valueType ty ++ ") =>\n" ++
      tail
  | _, names, .query site request args next, indent => do
    let name ← fresh naming
    let action := app ".query" [siteExpression naming site, quoted request, valuesText (termsText naming names args)]
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ ".call " ++ action ++ " fun (" ++ binder ++ " : " ++
      naming.carriers.valueType (services.result request) ++ ") =>\n" ++
      tail
  | _, names, .split subject absent present, indent => do
    let name ← fresh naming
    let absent ← processText naming finish names absent (indent + 2)
    let present ← processText naming finish (name :: names) present (indent + 2)
    return pad indent ++ "match " ++ compText naming names subject ++ " with\n" ++
      pad indent ++ "| none =>\n" ++ absent ++ "\n" ++ pad indent ++ "| some " ++
      (if (expressionIdentifiers present).contains name then name else "_" ++ name) ++ " =>\n" ++ present
  | _, names, .guard equality left right next, indent => do
    let left := paren (termText naming names left)
    let right := paren (termText naming names right)
    let decision := app "Equality.decide" [naming.carriers.model, equalityText equality, left, right]
    return pad indent ++ "@ite _ (" ++ left ++ " = " ++ right ++ ") " ++ decision ++ "\n" ++
      pad indent ++ "  (\n" ++ (← processText naming finish names next (indent + 4)) ++ ")\n" ++
      pad indent ++ "  (.halt .reject)"
  | _, names, .byLaw _ _ next, indent => processText naming finish names next indent
  | _, names, .strict helper args next, indent => do
    let name ← fresh naming
    let process := app "invoke" [paren naming.tables ++ ".closed", helperExpression naming helper,
      valuesText (termsText naming names args)]
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ process ++ ".bind fun (" ++ binder ++ " : " ++ valuesType naming helper.outputs false ++ ") =>\n" ++
      tail
  | _, names, .compute op _ args next, indent => do
    let name ← fresh naming
    let process := app "Evaluation.operationOn" [naming.carriers.model, "(.silent _)",
      paren naming.tables ++ ".closed", opText op, valuesText (termsText naming names args),
      app "Op.calculationRegions" [opText op, "rfl"]]
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ process ++ ".bind fun (" ++ binder ++ " : " ++ valuesType naming op.results false ++ ") =>\n" ++
      tail
  | _, names, .math helper args next, indent => do
    let name ← fresh naming
    let process := app "invoke" [paren naming.tables ++ ".components", helperExpression naming helper,
      valuesText (compsText naming names args)]
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ process ++ ".bind fun (" ++ binder ++ " : " ++ valuesType naming helper.outputs true ++ ") =>\n" ++
      tail
  | _, names, .owned owner helper args next, indent => do
    let name ← fresh naming
    let process := app "Participant.owned" [roleExpression naming owner, roleExpression naming owner,
      app "invoke" [paren naming.tables ++ ".closed", helperExpression naming helper], valuesText (compsText naming names args)]
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ process ++ ".bind fun (" ++ binder ++ " : " ++ valuesType naming helper.outputs true ++ ") =>\n" ++
      tail
  | _, names, .repeat spec site callback count state captures next, indent => do
    let name ← fresh naming
    let callback := (naming.callback spec callback).map paren |>.getD
      (app (paren naming.runs ++ ".callback") [repeatText spec, regionText callback])
    let arguments := [paren (compText naming names count),
      valuesText (compsText naming names state), valuesText (compsText naming names captures), callback]
    let process := match naming.repeatHead spec with
      | some head => app head arguments
      | none => app (paren naming.runs ++ ".run") (repeatText spec :: arguments ++ [quoted site])
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ process ++ ".bind fun (" ++ binder ++ " : " ++ valuesType naming spec.state true ++ ") =>\n" ++
      tail
  | _, names, .apply callee _ roles site args next, indent => do
    let name ← fresh naming
    let argsType := app "Binders" [naming.carriers.model,
      listText ((calleeAt callees callee).pattern.scope.map slotText)]
    let process := match naming.callee callee with
      | none => app naming.processes [finText callee.val]
      | some expression => paren (expression ++ " : ProtocolContext → " ++ argsType ++ " → " ++
          app "PIR.Process" [app "Interface" [naming.carriers.model],
            valuesType naming (calleeAt callees callee).signature.outputs true])
    let process := app process [app (paren naming.context ++ ".enter") [quoted site, natsText roles],
      paren ("by change " ++ argsType ++ "; exact " ++ valuesText (argumentsText naming names args))]
    let tail ← processText naming finish (name :: names) next indent
    let binder := if (expressionIdentifiers tail).contains name then name else "_" ++ name
    return pad indent ++ process ++ ".bind fun (" ++ binder ++ " : " ++
      valuesType naming (calleeAt callees callee).signature.outputs true ++ ") =>\n" ++
      tail

structure Rendered where
  form : String
  process : String
  binders : List String
  sites : List Site
  formJson : Json

def slotType (naming : Naming laws callees initial) : Slot → String
  | .value ty => naming.carriers.valueType ty
  | .component ty => app "Option" [paren (naming.carriers.valueType ty)]
  | .results types => valuesType naming types false | .tuple types => valuesType naming types true
def finishText : {out : List Ty} → Values (fun _ => Carried) out → String
  | _, .nil => ".nil"
  | _, .cons position rest => app ".cons" [(match position with
      | .absent => ".absent" | .present => ".present" | .optional => ".optional"), finishText rest]
def processType (naming : Naming laws callees initial) {out : List Ty} (finish : Finish out) : String :=
  app "PIR.Process" [app "Interface" [naming.carriers.model], match finish with
    | .outputs => valuesType naming out true
    | .presented spec => app "Tuple" [naming.carriers.value,
        listText ((carried spec).map fun (ty, optional) => paren (tyText ty ++ ", " ++ boolText optional))]]

/-- Full open-process equation, with the same model, tables, caller context,
callback interpretation, callee processes and input components on both sides. -/
def denotation (naming : Naming laws callees initial) {out : List Ty} (finish : Finish out)
    (form : String) (binders : List String) : String :=
  let args := [naming.carriers.model, paren naming.tables, paren naming.results, paren naming.context,
    paren naming.runs, paren naming.processes]
  match finish with
  | .outputs => app (paren form ++ ".denote") (args ++ [valuesText binders])
  | .presented spec => app (paren form ++ ".denoteWith") (args ++
      [app "finishLeaf" [naming.carriers.model, paren naming.results, finishText spec], valuesText binders])

/-- Ambient parameters/arguments are ordinary Lean source supplied by the
caller. Binder labels do not become expressions or declaration identifiers. -/
structure Declaration where
  name : String := "view"
  parameters : String := ""
  arguments : List String := []

/-- A finite module fragment. The caller puts it in its ordinary imports and
namespace, with the same open namespaces as this module. No proof is trusted.
The literal is deliberately independent of all readable helper/name hints.
An optional type expression can refer to shared law/callee catalogues; its
indices must still agree with the literal and all generated kernel equations. -/
def declarations {Δ : Scope} {out : List Ty} (naming : Naming laws callees Δ) (finish : Finish out)
    (printed : Rendered) (decl : Declaration := {})
    (formTypeExpression : Option String := none) : String :=
  let form := decl.name ++ "Form"
  let process := decl.name ++ "Process"
  let parameters := " ".intercalate ((Δ.zip printed.binders).map fun (slot, name) =>
    "(" ++ name ++ " : " ++ slotType naming slot ++ ")")
  let binders := (printed.binders.map paren)
  let siteData := listText (printed.sites.map fun site =>
    "(⟨" ++ natsText site.path ++ ", " ++ quoted site.kind ++ ", " ++ quoted site.site ++
      "⟩ : Zkc.Source.Structured.NormalForm.Site)")
  let finishes := match finish with
    | .outputs => ""
    | .presented spec => "\ntheorem " ++ decl.name ++ "_finishes : " ++ form ++ ".finishes " ++
        finishText spec ++ " = true := by\n  decide +kernel\n"
  let processParameters := explicitParameters (decl.parameters ++ " " ++ parameters)
    (decl.arguments ++ printed.binders) (processType naming finish ++ printed.process)
  "noncomputable def " ++ form ++ " : " ++ formTypeExpression.getD (formType laws callees Δ out) ++ " :=\n  " ++ printed.form ++
    "\n\nnoncomputable def " ++ process ++ " " ++ processParameters ++ " :\n    " ++
    processType naming finish ++ " :=\n" ++ printed.process ++
    "\n\ntheorem " ++ decl.name ++ "_calls : " ++ form ++ ".CallsMatch := by\n  kernel_rfl\n\n" ++
    "theorem " ++ decl.name ++ "_presentation " ++ decl.parameters ++ " " ++ parameters ++ " :\n    " ++
    denotation naming finish form binders ++ " =\n      " ++ app process (decl.arguments ++ binders) ++
    " := by\n  kernel_rfl\n" ++ finishes ++ "\ntheorem " ++ decl.name ++ "_sites :\n    " ++
    "Zkc.Source.Structured.NormalForm.sites " ++ form ++ " [] =\n      " ++ siteData ++
    " := by\n  decide +kernel\n"

/-- No success markers or proof placeholders are emitted for mismatched calls
or impossible callback return shapes. Printed expressions still need checking. -/
def render {Δ : Scope} {out : List Ty} (naming : Naming laws callees Δ) (finish : Finish out)
    (form : Form laws callees Δ out) : Except String Rendered := do
  unless NormalForms.callsMatch form do throw "presentation-call-identity"
  match finish with
  | .outputs => pure ()
  | .presented spec => unless form.finishes spec do throw "presentation-return-shape"
  let names := inputNames naming.inputs 0
  let process := (processText naming finish names form 2).run' Δ.length
  return ⟨formLiteral form, process, names, sites form [], NormalForms.formJson form⟩

/-- Preserve callee identity when several declarations share an ABI. Both
choices use the source normalizer; checked call equality authorizes the result. -/
def normalizeMatched {Γ out : List Ty} (signature : Signature)
    (body : Region protocolDialect Γ out) (role roster : Nat) (pattern : InputPattern Γ) :
    Except String (Bool × Form signature.laws signature.callees pattern.scope out) := do
  let byName := normalize {signature with names := true} body role roster pattern
  match normalize {signature with names := false} body role roster pattern with
  | .ok form => if NormalForms.callsMatch form then return (false, form) else return (true, ← byName)
  | .error refusal => match byName with
    | .ok form => return (true, form)
    | .error _ => throw refusal

/-- Use the same normalizer and policy as the existing compiled tool. Roster
selection tries only actual normalizer results and returns the selected size. -/
def request {Γ out : List Ty} (signature : Signature) (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (naming : Naming signature.laws signature.callees pattern.scope)
    (finish : Finish out := .outputs) (minimizeRoster : Bool := false) : Except String (Nat × Bool × Rendered) := do
  let normalizeAt := fun roster => normalizeMatched signature body role roster pattern
  let (roster, names, form) ←
    if minimizeRoster && role == 0 then
      match normalizeAt 1 with
      | .ok (names, form) => pure (1, names, form)
      | .error _ => do let (names, form) ← normalizeAt roster; pure (roster, names, form)
    else do let (names, form) ← normalizeAt roster; pure (roster, names, form)
  return (roster, names, ← render naming finish form)

/-- A usable default telescope over arbitrary domain-model carriers. Current
uniform roots can instead supply their existing F/G telescope and expressions. -/
def genericDeclaration (laws : List LawKey) (callees : List CalleeKey) (name : String := "view") : Declaration where
  name := name
  parameters := "(model : DomainModel) (tables : Tables model) (results : LawResults model " ++
    listText (laws.map lawText) ++ ") (ctx : ProtocolContext) (runs : Runs model) " ++
    "(processes : CalleeProcesses model " ++ listText (callees.map calleeText) ++ ")"
  arguments := ["model", "tables", "results", "ctx", "runs", "processes"]

/-- The exact retained source selection, before normalization. `path` addresses
the original region (0/1 for bind body/continuation, 0/1 for repeat callback/
continuation). It is independent of the paths inside the resulting Form. -/
structure Selected where
  definition : CheckedProtocol
  selection : NormalForms.BodySelection definition.body
  pattern : InputPattern selection.body.1
  signature : Signature
  role : Nat
  roster : Nat
  protocolName : String

def Selected.inputs (selected : Selected) : List Ty := selected.selection.body.1
def Selected.outputs (selected : Selected) : List Ty := selected.selection.body.2.1
def Selected.body (selected : Selected) : Region protocolDialect selected.inputs selected.outputs :=
  selected.selection.body.2.2
def Selected.path (selected : Selected) : List Nat := selected.selection.path

/-- Decode the existing nine-slot normal-form request using the existing tool's
decoders. No new normal-form or semantic wire representation is introduced. -/
def select (program : Program) (request : Json) : Except String Selected := do
  let [protocolName, repeatSite, role, roster, pattern, laws, strict, kept, callees] ← Format.array request
    | throw "normal-form-request"
  let protocolName ← Format.string protocolName
  let [definition] := program.payload.protocols.filter (·.name == protocolName)
    | throw "normal-form-protocol"
  let selection ← NormalForms.selectBody definition.body repeatSite
  let role ← Format.decimal (← Format.string role)
  let roster ← Format.decimal (← Format.string roster)
  let laws ← (← Format.array laws).mapM (NormalForms.decodeLaw program.payload.definitions)
  let .bool strict := strict | throw "normal-form-request"
  let kept ← (← Format.array kept).mapM fun item => do
    let name ← Format.string item
    let some definition := program.payload.definitions.find? (·.name == name) | throw "normal-form-helper"
    pure definition.helper
  let callees ← (← Format.array callees).mapM (NormalForms.decodeCallee program)
  let pattern ← NormalForms.decodePattern selection.body.1 (← Format.array pattern)
  return ⟨definition, selection, pattern, ⟨laws, strict, false, kept, callees⟩, role, roster, protocolName⟩

def signatureLiteral (signature : Signature) : String :=
  "(⟨" ++ ", ".intercalate [listText (signature.laws.map lawText), boolText signature.strict,
    boolText signature.names, listText (signature.kept.map helperText), listText (signature.callees.map calleeText)] ++ "⟩ : Signature)"

/-- Ready dispatcher API. The coordinator supplies typed naming and its owning
module telescope, or uses the generic defaults. `bodyExpression` is normally
the admitted source selector; the fallback is exact syntax serialization.
The generated normalization theorem must remain tied to that admitted selector
when integrated. The output also preserves source selection, form sites,
complete signatures, roster and the normalizer's name-selection policy. -/
def run (program : Program) (normalizerRequest : Json)
    (naming : (selected : Selected) → Naming selected.signature.laws selected.signature.callees selected.pattern.scope :=
      fun _ => {})
    (declaration : (selected : Selected) → Declaration := fun selected =>
      genericDeclaration selected.signature.laws selected.signature.callees)
    (bodyExpression : Option String := none) (minimizeRoster : Bool := false)
    (finish : (selected : Selected) → Finish selected.outputs := fun _ => .outputs) : Except String Json := do
  let selected ← select program normalizerRequest
  let naming := naming selected
  let finish := finish selected
  let (roster, names, printed) ← request selected.signature selected.body selected.role selected.roster
    selected.pattern naming finish minimizeRoster
  let declaration := declaration selected
  let signature := {selected.signature with names := names}
  let source := declarations (out := selected.outputs) naming finish printed declaration ++
    "\ntheorem " ++ declaration.name ++ "_normalized :\n    normalize " ++ signatureLiteral signature ++
    " " ++ paren (bodyExpression.getD (regionText selected.body) ++ " : Region protocolDialect " ++
      typesText selected.inputs ++ " " ++ typesText selected.outputs) ++ " " ++ toString selected.role ++ " " ++
    toString roster ++ " " ++ paren (patternText selected.pattern ++ " : InputPattern " ++ typesText selected.inputs) ++
    " = .ok " ++ declaration.name ++
    "Form := by\n  kernel_rfl\n"
  return .mkObj [("status", .str "rendered"), ("protocol", .str selected.protocolName),
    ("source_path", .arr (selected.path.map NormalForms.nat).toArray),
    ("role", NormalForms.nat selected.role), ("roster", NormalForms.nat roster), ("names", .bool names),
    ("scope", .arr (selected.pattern.scope.map NormalForms.slotJson).toArray),
    ("form", printed.formJson), ("lean_form", .str printed.form), ("lean_process", .str printed.process), ("lean_source", .str source),
    ("sites", .arr (printed.sites.map fun site => .mkObj [("path", .arr (site.path.map NormalForms.nat).toArray),
      ("kind", .str site.kind), ("site", .str site.site)]).toArray)]

end ZkcTools.StructuredSource.Presentation
