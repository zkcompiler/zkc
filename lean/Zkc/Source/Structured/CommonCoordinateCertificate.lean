module

public import Zkc.Source.Structured.CommonCoordinate

@[expose] public section

/-! Finite source-bound coordinate certificates. The proposer traverses the retained typed
body, substitutes actual call operands and role maps, and introduces a fresh lexical binder
for each repeat. A certificate contains structural witnesses, never a semantic callback.
Repeat state and call results are deliberately unknown in this profile. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

structure Pair where
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def Pair.selected (pair : Pair) (roles : Nat → Nat) (selected : List Nat) : Bool :=
  let mapped := selected.map roles
  mapped.contains pair.left && mapped.contains pair.right

def maskSymbols {scope : Scope} (pair : Pair) (roles : Nat → Nat) :
    {types : List Ty} → List (List Nat) → Symbols scope types → Symbols scope types
  | _, _, .nil => .nil
  | _, scopes, .cons head tail =>
    .cons (if pair.selected roles (scopes.headD []) then head else none)
      (maskSymbols pair roles (scopes.drop 1) tail)

def inputSymbols (pair : Pair) (roles : Nat → Nat) (types : List Ty)
    (scopes : List (List Nat)) : Symbols (types.map Slot.value) types :=
  maskSymbols pair roles scopes (inputTerms types)
where
  inputTerms : (types : List Ty) → Symbols (types.map Slot.value) types
    | [] => .nil
    | ty :: types =>
      let head : Option (Expression (.value ty :: types.map Slot.value) ty) :=
        match ty with
        | .index => some (.var .here)
        | _ => none
      .cons head (mapValues (fun term ↦ term.map (Term.rename (fun position ↦ .there position)))
        (inputTerms types))

def calculation {scope : Scope} (op : Op) (args : Symbols scope op.arguments) :
    Symbols scope op.results :=
  if allowed : scalar op = true then
    ((collect args).map (calculated op allowed)).getD (unknown scope op.results)
  else unknown scope op.results

def transfer {scope : Scope} (pair : Pair) (roles : Nat → Nat)
    (op : ProtocolOp) : Symbols scope op.arguments → Symbols scope op.results :=
  match op with
  | .calculate op _ => calculation op
  | .restrict _ selected => fun args ↦
    .cons (if pair.selected roles selected then args.get .here else none) .nil
  | _ => fun _ ↦ unknown scope _

def supported {scope : Scope} (pair : Pair) (roles : Nat → Nat)
    (op : ProtocolOp) : Symbols scope op.arguments → Bool :=
  match op with
  | .oracle (.sequenceAt _ _ selected) _ => fun args ↦
    !(pair.selected roles selected) || (args.get (.there .here)).isSome
  | _ => fun _ ↦ true

def atomic : ProtocolOp → Bool
  | .repeat .. | .protocolApply .. => false
  | _ => true

structure Cursor where
  definition : Nat
  applications : List (Nat × List Nat) := []
  block : List Nat := [7]
  next : Nat := 0
  row : List Nat := []
  deriving Repr

def Cursor.after (cursor : Cursor) : ProtocolOp → Cursor
  | .mark _ => {cursor with row := cursor.block ++ [1, cursor.next], next := cursor.next + 1}
  | _ => cursor

def Cursor.child (cursor : Cursor) : Cursor :=
  {cursor with block := cursor.row ++ [4, 0, 3], next := 0, row := []}

def Cursor.enter (cursor : Cursor) (definition : Nat) : Cursor :=
  {definition := definition, applications := cursor.applications ++ [(cursor.definition, cursor.row)]}

inductive Binding where
  | input (definition port : Nat) (type : Ty)
  | counter (definition : Nat) (applications : List (Nat × List Nat)) (row : List Nat)
  deriving DecidableEq, Repr

abbrev Origins (scope : Scope) := Values (fun _ ↦ Binding) scope

def inputOrigins (definition : Nat) (types : List Ty) : Origins (types.map Slot.value) :=
  go types 0
where
  go : (types : List Ty) → Nat → Origins (types.map Slot.value)
    | [], _ => .nil
    | ty :: types, port => .cons (.input definition port ty) (go types (port + 1))

def weakenSymbols {scope : Scope} {types : List Ty} (values : Symbols scope types) :
    Symbols (.value .index :: scope) types :=
  mapValues (fun term ↦ term.map (Term.rename (fun position ↦ .there position))) values

def callbackSymbols {scope : Scope} (pair : Pair) (roles : Nat → Nat) (spec : RepeatSpec)
    (args : Symbols scope (.index :: (spec.state ++ spec.captures))) :
    Symbols (.value .index :: scope) (.index :: (spec.state ++ spec.captures)) :=
  let captures := (Values.split spec.state (laterEntries args)).2
  .cons (some (.var .here))
    ((unknown (.value .index :: scope) spec.state).append
      (weakenSymbols (maskSymbols pair roles
        (List.replicate spec.captures.length spec.roles) captures)))

set_option genSizeOf false in
/-- The indices fix the actual retained body and all formal-to-actual substitutions.
The only proof fields are finite source, signature and local side checks. -/
inductive Plan (snapshot : Snapshot) (definitions : List CheckedProtocol) (pair : Pair) :
    {scope : Scope} → {inputs outputs : List Ty} → (Nat → Nat) → Cursor → Origins scope →
    (body : Region protocolDialect inputs outputs) → Symbols scope inputs → Type where
  | ret {scope inputs outputs roles cursor origins args} {env : Symbols scope inputs} :
      Plan snapshot definitions pair (scope := scope) (outputs := outputs) roles cursor origins (.ret args) env
  | stop {scope inputs outputs roles cursor origins reason} {env : Symbols scope inputs} :
      Plan snapshot definitions pair (scope := scope) (outputs := outputs) roles cursor origins (.stop reason) env
  | step {scope inputs outputs roles cursor origins op args bodies next}
      {env : Symbols scope inputs}
      (leaf : atomic op = true) (noRegions : op.regions = [])
      (coordinate : supported pair roles op (args.eval env.get) = true)
      (tail : Plan snapshot definitions pair roles (cursor.after op) origins next
        ((transfer pair roles op (args.eval env.get)).append env)) :
      Plan snapshot definitions pair (scope := scope) (outputs := outputs) roles cursor origins
        (.letOp op args bodies next) env
  | bind {scope inputs middle outputs roles cursor origins body next}
      {env : Symbols scope inputs}
      (inside : Plan snapshot definitions pair roles cursor origins body env)
      (tail : Plan snapshot definitions pair roles cursor origins next ((unknown scope middle).append env)) :
      Plan snapshot definitions pair (outputs := outputs) roles cursor origins (.bind body next) env
  | apply {scope inputs outputs roles cursor origins signature selected site args next}
      {env : Symbols scope inputs} (definition : CheckedProtocol)
      (member : definition ∈ definitions) (same : definition.signature = signature)
      (inside : Plan snapshot definitions pair (roles ∘ roleSubstitution selected)
        (cursor.enter (snapshot.definitions.findIdx (·.name == definition.name))) origins
        (same ▸ (show Region protocolDialect definition.signature.inputs definition.signature.outputs
          from definition.body))
        (maskSymbols pair (roles ∘ roleSubstitution selected)
          signature.inputScopes (args.eval env.get)))
      (tail : Plan snapshot definitions pair roles cursor origins next
        ((unknown scope signature.outputs).append env)) :
      Plan snapshot definitions pair (outputs := outputs) roles cursor origins
        (.letOp (.protocolApply signature selected site) args .nil next) env
  | repeat {scope inputs outputs roles cursor origins spec site args body next}
      {env : Symbols scope inputs}
      (inside : Plan snapshot definitions pair roles cursor.child
        (.cons (.counter cursor.definition cursor.applications cursor.row) origins) body
        (callbackSymbols pair roles spec (args.eval env.get)))
      (tail : Plan snapshot definitions pair roles cursor origins next
        ((unknown scope spec.state).append env)) :
      Plan snapshot definitions pair (outputs := outputs) roles cursor origins
        (.letOp (.repeat spec site) args (.cons body .nil) next) env

end Zkc.Source.Structured.CommonCoordinate
