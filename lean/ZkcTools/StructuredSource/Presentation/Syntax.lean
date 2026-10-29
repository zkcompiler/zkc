module

public import Lean
public import Zkc.Source.Structured.NormalForm.Normalize

@[expose] public section

/-! Pure syntax printing shared by connection proposals and source presentations.
The output is an untrusted literal. This layer performs no source selection,
file access, process interpretation or proof construction; each consumer checks
its proposed syntax against the independently fixed source and target. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.Presentation
open Lean Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm

/-- Lean's string representation escapes quotes, backslashes and control characters. -/
def quoted (text : String) : String := reprStr text

/-- Identifier references in printer-owned expressions, excluding string literals. -/
def expressionIdentifiers (source : String) : List String := Id.run do
  let mut names := []
  let mut token := ""
  let mut inString := false
  let mut escaped := false
  for c in source.toList do
    if inString then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inString := false
    else if c.isAlphanum || c == '_' || c == '\'' then
      token := token.push c
    else
      if !token.isEmpty then names := token :: names
      token := ""
      if c == '"' then inString := true
  return if token.isEmpty then names else token :: names

/-- Retain positional parameters while marking unused declaration binders explicitly.
References in the telescope matter too: `(n : Nat) (x : Fin n)` must keep `n`
even when the body ignores both values. Mask the exact printed introductions
before collecting identifiers, leaving all type and default-value references.
This lexical hint never supplies evidence; emitted declarations are checked. -/
def explicitParameters (parameters : String) (names : List String) (body : String) : String :=
  let parameterTypes := names.foldl (fun text name =>
    text.replace ("(" ++ name ++ " :") "(:") parameters
  let used := expressionIdentifiers (body ++ " " ++ parameterTypes)
  names.foldl (fun text name =>
    if used.contains name then text
    else text.replace ("(" ++ name ++ " :") ("(_" ++ name ++ " :")) parameters

def paren (text : String) : String := "(" ++ text ++ ")"
def app (head : String) (args : List String) : String :=
  paren (" ".intercalate (head :: args))
def listText (items : List String) : String := "[" ++ ", ".intercalate items ++ "]"
def valuesText (items : List String) : String := items.foldr (fun x xs => app ".cons" [x, xs]) ".nil"
def positionText (index : Nat) : String :=
  (List.replicate index ()).foldr (fun _ tail => app ".there" [tail]) ".here"
def finText (index : Nat) : String := "⟨" ++ toString index ++ ", by decide⟩"
def stopText : PIR.Stop → String
  | .reject => ".reject" | .abort => ".abort" | .exhausted => ".exhausted"
  | .incomplete => ".incomplete" | .refused => ".refused"
def boolText (value : Bool) : String := if value then "true" else "false"
mutual
  def tyText : Ty → String
    | .boolean => ".boolean" | .index => ".index" | .indices => ".indices"
    | .field d => app ".field" [quoted d] | .vector d => app ".vector" [quoted d]
    | .group d => app ".group" [quoted d] | .service d => app ".service" [quoted d]
    | .groups d => app ".groups" [quoted d]
    | .oracle kind => app ".oracle" [oracleKindText kind]
    | .oracleSequence kind maximum => app ".oracleSequence" [oracleKindText kind, toString maximum]
    | .sequence element => app ".sequence" [tyText element]
    | .product identity constructor fields =>
      app ".product" [quoted identity, quoted constructor, fieldsText fields]
  def oracleKindText : OracleKind → String
    | .table row rows => app ".table" [tyText row,
        match rows with | none => "none" | some n => app "some" [toString n]]
  def fieldsText : ProductFields → String
    | .nil => ".nil"
    | .cons type rest => app ".cons" [tyText type, fieldsText rest]
end
def typesText (types : List Ty) : String := listText (types.map tyText)
def natsText (values : List Nat) : String := listText (values.map toString)
def scopesText (scopes : List (List Nat)) : String := listText (scopes.map natsText)
def helperText (helper : Helper) : String :=
  "(⟨" ++ quoted helper.name ++ ", " ++ (if helper.kind == .math then ".math" else ".local") ++
    ", " ++ typesText helper.inputs ++ ", " ++ typesText helper.outputs ++ "⟩ : Helper)"
def signatureText (signature : ProtocolSignature) : String :=
  "(⟨" ++ ", ".intercalate [quoted signature.name, listText (signature.roles.map quoted),
    typesText signature.inputs, typesText signature.outputs, scopesText signature.inputScopes,
    scopesText signature.outputScopes] ++ "⟩ : ProtocolSignature)"
def repeatText (spec : RepeatSpec) : String :=
  "(⟨" ++ ", ".intercalate [typesText spec.state, typesText spec.captures, natsText spec.roles,
    scopesText spec.stateScopes, toString spec.maximum] ++ "⟩ : RepeatSpec)"

def primitiveText : Primitive → String
  | .indexConstant n => app ".indexConstant" [toString n]
  | .indexEqual => ".indexEqual" | .indexLess => ".indexLess" | .indexAdd => ".indexAdd"
  | .indexMul => ".indexMul" | .indexSub => ".indexSub" | .indexDiv => ".indexDiv" | .indexMod => ".indexMod"
  | .vectorEmpty d => app ".vectorEmpty" [quoted d] | .vectorLength d => app ".vectorLength" [quoted d]
  | .vectorSum d => app ".vectorSum" [quoted d] | .vectorSplit d => app ".vectorSplit" [quoted d]
  | .vectorAppend d => app ".vectorAppend" [quoted d] | .vectorEqual d => app ".vectorEqual" [quoted d]
  | .fieldEqual d => app ".fieldEqual" [quoted d]

def collectionText : Collection → String
  | .vector field => app ".vector" [quoted field]
  | .sequence element => app ".sequence" [tyText element]

def domainNodeText {inputs : List Ty} {context : List (List Ty)} {items : List Ty} :
    DomainNode inputs context items → String
  | .elements collection container => app ".elements" [collectionText collection, positionText container.index]
  | .indices collection container => app ".indices" [collectionText collection, positionText container.index]
  | .range lower upper => app ".range" [positionText lower.index, positionText upper.index]
  | .zip types operands => app ".zip" [listText (types.map typesText),
      valuesText (operands.indices.map positionText)]
  | .product types operands => app ".product" [listText (types.map typesText),
      valuesText (operands.indices.map positionText)]

def domainBodyText {inputs : List Ty} : {context : List (List Ty)} → {items : List Ty} →
    DomainBody inputs context items → String
  | _, _, .ret value => app ".ret" [positionText value.index]
  | _, _, .letNode node next => app ".letNode" [domainNodeText node, domainBodyText next]

def domainText (spec : DomainSpec) : String :=
  "⟨" ++ ", ".intercalate [quoted spec.name, typesText spec.inputs, typesText spec.items,
    domainBodyText spec.body] ++ "⟩"

def collectText (spec : CollectSpec) : String :=
  "⟨" ++ ", ".intercalate [domainText spec.domain, collectionText spec.collection,
    typesText spec.captures, quoted spec.body, quoted spec.predicate,
    if spec.kind == .math then ".math" else ".local"] ++ "⟩"

/-- Syntax serialization only: callback regions are retained, never executed here. -/
def opText : Op → String
  | .exec primitive => app ".exec" [primitiveText primitive]
  | .indexConstant n => app ".indexConstant" [toString n] | .indexEqual => ".indexEqual"
  | .indexLess => ".indexLess" | .indexPowerOfTwo => ".indexPowerOfTwo"
  | .vectorLength d => app ".vectorLength" [quoted d]
  | .multilinearRestrictPrefix d => app ".multilinearRestrictPrefix" [quoted d]
  | .fieldConstant d n => app ".fieldConstant" [quoted d, toString n]
  | .fieldAdd d => app ".fieldAdd" [quoted d] | .fieldSubtract d => app ".fieldSubtract" [quoted d]
  | .fieldMultiply d => app ".fieldMultiply" [quoted d] | .fieldEqual d => app ".fieldEqual" [quoted d]
  | .fieldEmbed extension base => app ".fieldEmbed" [quoted extension, quoted base]
  | .groupIdentity d => app ".groupIdentity" [quoted d] | .groupAdd d => app ".groupAdd" [quoted d]
  | .groupScale g f => app ".groupScale" [quoted g, quoted f] | .groupEqual d => app ".groupEqual" [quoted d]
  | .booleanConstant b => app ".booleanConstant" [boolText b]
  | .booleanAnd => ".booleanAnd" | .booleanOr => ".booleanOr" | .booleanXor => ".booleanXor"
  | .booleanEqual => ".booleanEqual" | .booleanNotEqual => ".booleanNotEqual"
  | .select ty => app ".select" [tyText ty] | .boundedAt d => app ".boundedAt" [quoted d]
  | .makeProduct identity constructor fields =>
    app ".makeProduct" [quoted identity, quoted constructor, fieldsText fields]
  | .getProduct identity constructor fields type field =>
    app ".getProduct" [quoted identity, quoted constructor, fieldsText fields, tyText type,
      positionText field.index]
  | .invoke helper => app ".invoke" [helperText helper]
  | .map spec => app ".map" ["⟨" ++ ", ".intercalate [quoted spec.helperName, quoted spec.field,
      listText (spec.rowwise.map boolText)] ++ "⟩"]
  | .fold spec =>
    app ".fold" ["⟨" ++ ", ".intercalate [domainText spec.domain, typesText spec.state, typesText spec.captures,
      quoted spec.step, quoted spec.predicate, if spec.kind == .math then ".math" else ".local"] ++ "⟩"]
  | .collect spec => app ".collect" [collectText spec]
  | .branch captures outputs => app ".branch" [typesText captures, typesText outputs]
  | .loop state captures => app ".loop" [typesText state, typesText captures]
  | .loopCondition state captures => app ".loopCondition" [typesText state, typesText captures]
  | .guard => ".guard" | .mark site => app ".mark" [quoted site]

def protocolOpText : ProtocolOp → String
  | .calculate op _ => app ".calculate" [opText op, "rfl"]
  | .localCall helper _ owner site => app ".localCall" [helperText helper, "rfl", toString owner, quoted site]
  | .guard owner site => app ".guard" [toString owner, quoted site]
  | .exchange ty sender receiver site => app ".exchange" [tyText ty, toString sender, toString receiver, quoted site]
  | .restrict ty roles => app ".restrict" [tyText ty, natsText roles]
  | .assemble ty roles => app ".assemble" [tyText ty, natsText roles]
  | .draw owner field site => app ".draw" [toString owner, quoted field, quoted site]
  | .statement relation types selectors acceptance => app ".statement" [quoted relation, typesText types,
      listText (selectors.map quoted), toString acceptance]
  | .mark site => app ".mark" [quoted site]
  | .protocolApply signature roles site => app ".protocolApply" [signatureText signature, natsText roles, quoted site]
  | .repeat spec site => app ".repeat" [repeatText spec, quoted site]

def operandsText {Γ : List Ty} : {types : List Ty} → Operands Γ types → String
  | _, .nil => ".nil"
  | _, .cons x xs => app ".cons" [positionText x.index, operandsText xs]

mutual
  /-- Syntax of an independently checked helper body; no operation is executed. -/
  def helperRegionText {Γ out : List Ty} : Region dialect Γ out → String
    | .ret values => app ".ret" [operandsText values]
    | .stop reason => app ".stop" [stopText reason]
    | .bind body next => app ".bind" [helperRegionText body, helperRegionText next]
    | .letOp op args bodies next => app ".letOp" [opText op, operandsText args,
        helperRegionsText bodies, helperRegionText next]
  def helperRegionsText {signatures : List (List Ty × List Ty)} : Regions dialect signatures → String
    | .nil => ".nil"
    | .cons body rest => app ".cons" [helperRegionText body, helperRegionsText rest]
end

mutual
  def regionText {Γ out : List Ty} : Region protocolDialect Γ out → String
    | .ret values => app ".ret" [operandsText values]
    | .stop reason => app ".stop" [stopText reason]
    | .bind body next => app ".bind" [regionText body, regionText next]
    | .letOp op args bodies next => app ".letOp" [protocolOpText op, operandsText args,
        regionsText bodies, regionText next]
  def regionsText {signatures : List (List Ty × List Ty)} : Regions protocolDialect signatures → String
    | .nil => ".nil"
    | .cons body rest => app ".cons" [regionText body, regionsText rest]
end

def inputText {ty : Ty} : Input ty → String
  | .absent => ".absent" | .present => ".present" | .optional => ".optional"
  | .capability service handle => app ".capability" [quoted service, toString handle]
  | .index n => app ".index" [toString n] | .field d n => app ".field" [quoted d, toString n]
  | .bool b => app ".bool" [boolText b]
def patternText : {Γ : List Ty} → InputPattern Γ → String
  | _, .nil => ".nil" | _, .cons x xs => app ".cons" [inputText x, patternText xs]
def lawText (law : LawKey) : String :=
  let outputText : LawOutput → String
    | .result => ".result" | .argument n => app ".argument" [toString n] | .literal n => app ".literal" [toString n]
  let pinText : LawPin → String
    | .free => ".free" | .input n => app ".input" [toString n] | .literal n => app ".literal" [toString n]
  let shape := match law.shape with
    | .returns outputs => app ".returns" [listText (outputs.map outputText)]
    | .stops reason => app ".stops" [stopText reason]
    | .passes positions => app ".passes" [natsText positions]
  "(⟨" ++ ", ".intercalate [helperText law.helper, shape, listText (law.pins.map pinText)] ++ "⟩ : LawKey)"
def calleeText (callee : CalleeKey) : String :=
  "(⟨" ++ ", ".intercalate [signatureText callee.signature, toString callee.role, patternText callee.pattern,
    listText (callee.pins.map fun pin => match pin with | none => "none" | some n => app "some" [toString n])] ++ "⟩ : CalleeKey)"
def slotText : Slot → String
  | .value ty => app ".value" [tyText ty] | .component ty => app ".component" [tyText ty]
  | .results types => app ".results" [typesText types] | .tuple types => app ".tuple" [typesText types]
def formType (laws : List LawKey) (callees : List CalleeKey) (Δ : Scope) (out : List Ty) : String :=
  app "Form" [listText (laws.map lawText), listText (callees.map calleeText), listText (Δ.map slotText), typesText out]

variable {laws : List LawKey} {callees : List CalleeKey}

mutual
  def termLiteral {Δ : Scope} {ty : Ty} : Term laws Δ ty → String
    | .var b => app ".var" [positionText b.index]
    | .result b p => app ".result" [positionText b.index, positionText p.index]
    | .capability service handle => app ".capability" [quoted service, toString handle]
    | .index n => app ".index" [toString n] | .bool b => app ".bool" [boolText b]
    | .field d n => app ".field" [quoted d, toString n] | .groupZero d => app ".groupZero" [quoted d]
    | .calc op _ args p => app ".calc" [opText op, "rfl", termsLiteral args, positionText p.index]
    | .law entry args p => app ".law" [finText entry.val, termsLiteral args, positionText p.index]
  def termsLiteral {Δ : Scope} {types : List Ty} : Terms laws Δ types → String
    | .nil => ".nil"
    | .cons x xs => app ".cons" [termLiteral x, termsLiteral xs]
end

def compLiteral {Δ : Scope} {ty : Ty} : Comp laws Δ ty → String
  | .absent => ".absent" | .present term => app ".present" [termLiteral term]
  | .input b => app ".input" [positionText b.index]
  | .read b p => app ".read" [positionText b.index, positionText p.index]
def compsLiteral {Δ : Scope} : {types : List Ty} → Values (Comp laws Δ) types → String
  | _, .nil => ".nil"
  | _, .cons x xs => app ".cons" [compLiteral x, compsLiteral xs]
def argumentsLiteral {Δ : Scope} : {scope : Scope} → Values (Argument laws Δ) scope → String
  | [], .nil => ".nil"
  | .value _ :: _, .cons x xs => app ".cons" [termLiteral x, argumentsLiteral xs]
  | .component _ :: _, .cons x xs => app ".cons" [compLiteral x, argumentsLiteral xs]
  | .results _ :: _, .cons x xs => app ".cons" [termsLiteral x, argumentsLiteral xs]
  | .tuple _ :: _, .cons x xs => app ".cons" [compsLiteral x, argumentsLiteral xs]
def equalityText {ty : Ty} : Equality ty → String
  | .field d => app ".field" [quoted d] | .group d => app ".group" [quoted d] | .index => ".index"
  | .boolean => ".boolean"

def formLiteralWith (callbackName : (spec : RepeatSpec) →
    Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state → Option String)
    {out : List Ty} : {Δ : Scope} → Form laws callees Δ out → String
  | _, .done values => app ".done" [compsLiteral values]
  | _, .halt reason => app ".halt" [stopText reason]
  | _, .send ty site peer value next => app ".send" [tyText ty, quoted site, toString peer,
      termLiteral value, formLiteralWith callbackName next]
  | _, .receive ty site peer next => app ".receive" [tyText ty, quoted site, toString peer, formLiteralWith callbackName next]
  | _, .query site request args next => app ".query" [quoted site, quoted request, termsLiteral args, formLiteralWith callbackName next]
  | _, .split subject absent present => app ".split" [compLiteral subject, formLiteralWith callbackName absent, formLiteralWith callbackName present]
  | _, .guard equality left right next => app ".guard" [equalityText equality, termLiteral left,
      termLiteral right, formLiteralWith callbackName next]
  | _, .strict helper args next => app ".strict" [helperText helper, termsLiteral args, formLiteralWith callbackName next]
  | _, .compute op _ args next => app ".compute" [opText op, "rfl", termsLiteral args, formLiteralWith callbackName next]
  | _, .math helper args next => app ".math" [helperText helper, compsLiteral args, formLiteralWith callbackName next]
  | _, .byLaw entry helper next => app ".byLaw" [finText entry.val, helperText helper, formLiteralWith callbackName next]
  | _, .owned owner helper args next => app ".owned" [toString owner, helperText helper, compsLiteral args, formLiteralWith callbackName next]
  | _, .repeat spec site callback count state captures next => app ".repeat" [repeatText spec,
      quoted site, (callbackName spec callback).getD (regionText callback), compLiteral count, compsLiteral state, compsLiteral captures, formLiteralWith callbackName next]
  | Δ, .apply callee signature roles site args next =>
    let argsType := app "Values" [app "Argument" [listText (laws.map lawText), listText (Δ.map slotText)],
      listText ((calleeAt callees callee).pattern.scope.map slotText)]
    -- `change` exposes the dependent scope before elaborating heterogeneous
    -- arguments; a type ascription alone does not unfold a callee's pattern.
    app ".apply" [finText callee.val, signatureText signature, natsText roles, quoted site,
      paren ("by change " ++ argsType ++ "; exact " ++ argumentsLiteral args), formLiteralWith callbackName next]

def formLiteral {out : List Ty} {Δ : Scope} (form : Form laws callees Δ out) : String :=
  formLiteralWith (fun _ _ => none) form

end ZkcTools.StructuredSource.Presentation
