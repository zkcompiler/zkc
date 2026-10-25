module

public import Zkc.Source.Format
public import Zkc.Source.Structured.Limits

@[expose] public section

/-! Typed protocol specialization metadata, independent of runtime types.
Validation applies to decoded and hand-constructed records alike. Native
frontend admission owns Unicode NFC; this model preserves exact UTF-8 strings
and neither normalizes them nor claims to check Unicode normalization.
An origin selects a candidate and establishes no body correspondence. -/

namespace Zkc.Source.Structured
open Lean

inductive OriginNominalKind where
  | record | variant | associated | moduleType
  deriving BEq, Repr

inductive OriginTerm where
  | natural (decimal : String)
  | field (identity : String)
  | group (identity : String)
  | domain (sort identity : String)
  | asset (sort identity : String)
  | boolean | index | unit
  | tuple (elements : List OriginTerm)
  | array (element : OriginTerm) (length : String)
  | nominal (kind : OriginNominalKind) (path : String) (arguments : List OriginTerm)
  | builtin (name : String) (arguments : List OriginTerm)
  | formal (name : String) (arguments : List OriginTerm)
  deriving BEq, Repr

structure ProtocolOrigin where
  path : String
  arguments : List (String × OriginTerm)
  deriving BEq, Repr

/-- The function kind determines which wire grammar is used. Math has none. -/
inductive FunctionOrigin where
  | local (name : String) (bindings : List (String × String))
  | protocol (value : ProtocolOrigin)
  deriving BEq, Repr

def originStringValid (value : String) (limit : Nat := Limits.originStringBytes) : Bool :=
  !value.isEmpty && value.utf8ByteSize ≤ limit && !(value.toList.contains '\x00')

def originIdentifierInitial (c : Char) : Bool :=
  c.toNat ≥ 128 || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

def originIdentifierRest (c : Char) : Bool :=
  originIdentifierInitial c || ('0' ≤ c && c ≤ '9')

def originPathTailValid : List Char → Bool
  | [] => true
  | ':' :: ':' :: first :: rest => originIdentifierInitial first && originPathTailValid rest
  | c :: rest => originIdentifierRest c && originPathTailValid rest

/-- Qualified source path syntax, without a Unicode normalization claim. -/
def originPathValid (value : String) (limit : Nat := Limits.originStringBytes) : Bool :=
  originStringValid value limit && match value.toList with
    | [] => false
    | first :: rest => originIdentifierInitial first && originPathTailValid rest

def originParameterValid (value : String) : Bool :=
  originStringValid value && match value.toList with
    | [] => false
    | first :: rest => originIdentifierInitial first && rest.all originIdentifierRest

def originDecimalValid (value : String) : Bool :=
  (Source.Format.canonicalDecimal value Limits.originStringBytes).isSome

def OriginTerm.valid : Nat → OriginTerm → Bool
  | 0, _ => false
  | depth + 1, term =>
    let termsValid := fun terms => terms.length ≤ Limits.listEntries && terms.all (OriginTerm.valid depth)
    match term with
    | .natural value => originDecimalValid value
    | .field name | .group name => originStringValid name
    | .domain sort name | .asset sort name => originStringValid sort && originStringValid name
    | .boolean | .index | .unit => true
    | .tuple terms => termsValid terms
    | .array element length => element.valid depth && originDecimalValid length
    | .nominal _ path terms => originPathValid path && termsValid terms
    | .builtin name terms | .formal name terms => originStringValid name && termsValid terms

/-- A bounded worklist also checks hand-constructed trees without relying on
the JSON byte budget. Every constructor consumes one visit. -/
def originTermsWithin : Nat → List OriginTerm → Bool
  | 0, terms => terms.isEmpty
  | _ + 1, [] => true
  | remaining + 1, term :: rest =>
    let children := match term with
      | .tuple terms | .nominal _ _ terms | .builtin _ terms | .formal _ terms => terms
      | .array element _ => [element]
      | _ => []
    originTermsWithin remaining (children ++ rest)

def ProtocolOrigin.valid (origin : ProtocolOrigin) : Bool :=
  originPathValid origin.path Limits.originPathBytes &&
  origin.arguments.length ≤ Limits.originBindings &&
  (origin.arguments.map Prod.fst).eraseDups.length == origin.arguments.length &&
  origin.arguments.all (fun (name, term) => originParameterValid name && term.valid Limits.nesting) &&
  originTermsWithin Limits.originTerms (origin.arguments.map Prod.snd)

def FunctionOrigin.valid : FunctionOrigin → Bool
  | .protocol origin => origin.valid
  | .local name bindings => originStringValid name && bindings.length ≤ Limits.originBindings &&
    (bindings.map Prod.fst).eraseDups.length == bindings.length &&
    bindings.all (fun (key, value) => originStringValid key && originStringValid value)

namespace OriginFormat

def array (json : Json) (limit : Nat) : Except String (List Json) := do
  let .arr values := json | throw "structured-origin-array"
  if values.size > limit then throw "structured-origin-list-limit"
  return values.toList

def string (json : Json) (limit : Nat := Limits.originStringBytes) : Except String String := do
  let .str value := json | throw "structured-origin-string"
  unless originStringValid value limit do throw "structured-origin-string"
  return value

def decimal (json : Json) : Except String String := do
  let value ← string json
  unless originDecimalValid value do throw "structured-origin-decimal"
  return value

def nominalKind : Json → Except String OriginNominalKind
  | .str "record" => pure .record
  | .str "variant" => pure .variant
  | .str "associated" => pure .associated
  | .str "module" => pure .moduleType
  | _ => throw "structured-origin-nominal-kind"

def term : Nat → Json → Except String OriginTerm
  | 0, _ => throw "structured-origin-depth"
  | depth + 1, json => do
    match ← array json 4 with
    | [.str "nat", value] => return .natural (← decimal value)
    | [.str "field", name] => return .field (← string name)
    | [.str "group", name] => return .group (← string name)
    | [.str "domain", sort, name] => return .domain (← string sort) (← string name)
    | [.str "asset", sort, name] => return .asset (← string sort) (← string name)
    | [.str "bool"] => return .boolean
    | [.str "index"] => return .index
    | [.str "unit"] => return .unit
    | [.str "tuple", terms] => return .tuple (← (← array terms Limits.listEntries).mapM (term depth))
    | [.str "array", element, length] => return .array (← term depth element) (← decimal length)
    | [.str "nominal", kind, path, terms] =>
      let path ← string path
      unless originPathValid path do throw "structured-origin-path"
      return .nominal (← nominalKind kind) path (← (← array terms Limits.listEntries).mapM (term depth))
    | [.str "builtin", name, terms] =>
      return .builtin (← string name)
        (← (← array terms Limits.listEntries).mapM (term depth))
    | [.str "formal", name, terms] =>
      return .formal (← string name)
        (← (← array terms Limits.listEntries).mapM (term depth))
    | _ => throw "structured-origin-term"

def protocol (json : Json) : Except String ProtocolOrigin := do
  let [path, arguments] ← array json 2 | throw "structured-origin"
  let arguments ← (← array arguments Limits.originBindings).mapM fun pair => do
    let [name, value] ← array pair 2 | throw "structured-origin-binding"
    return (← string name, ← term Limits.nesting value)
  let value : ProtocolOrigin := ⟨← string path Limits.originPathBytes, arguments⟩
  unless value.valid do throw "structured-origin"
  return value

def localOrigin (json : Json) : Except String FunctionOrigin := do
  let [name, bindings] ← array json 2 | throw "structured-origin"
  let bindings ← (← array bindings Limits.originBindings).mapM fun pair => do
    let [key, value] ← array pair 2 | throw "structured-origin-binding"
    return (← string key, ← string value)
  let value := FunctionOrigin.local (← string name) bindings
  unless value.valid do throw "structured-origin"
  return value

end OriginFormat

def OriginNominalKind.wireName : OriginNominalKind → String
  | .record => "record" | .variant => "variant" | .associated => "associated" | .moduleType => "module"

def OriginTerm.toJson : OriginTerm → Json
  | .natural value => Lean.toJson ["nat", value]
  | .field name => Lean.toJson ["field", name]
  | .group name => Lean.toJson ["group", name]
  | .domain sort name => Lean.toJson ["domain", sort, name]
  | .asset sort name => Lean.toJson ["asset", sort, name]
  | .boolean => Lean.toJson ["bool"] | .index => Lean.toJson ["index"] | .unit => Lean.toJson ["unit"]
  | .tuple terms => Lean.toJson [Lean.toJson "tuple", Lean.toJson (terms.map OriginTerm.toJson)]
  | .array element length => Lean.toJson [Lean.toJson "array", element.toJson, Lean.toJson length]
  | .nominal kind path terms => Lean.toJson [Lean.toJson "nominal", Lean.toJson kind.wireName,
      Lean.toJson path, Lean.toJson (terms.map OriginTerm.toJson)]
  | .builtin name terms => Lean.toJson [Lean.toJson "builtin", Lean.toJson name, Lean.toJson (terms.map OriginTerm.toJson)]
  | .formal name terms => Lean.toJson [Lean.toJson "formal", Lean.toJson name, Lean.toJson (terms.map OriginTerm.toJson)]

def ProtocolOrigin.toJson (origin : ProtocolOrigin) : Json :=
  Lean.toJson [Lean.toJson origin.path, Lean.toJson (origin.arguments.map fun (name, term) => Lean.toJson [Lean.toJson name, term.toJson])]

/-- Tagged canonical arrays preserve the distinction between Local and protocol
origins. No display formatter or `Repr` representation is an identity codec. -/
def FunctionOrigin.toJson : FunctionOrigin → Json
  | .local name bindings => Lean.toJson [Lean.toJson "local", Lean.toJson name,
      Lean.toJson (bindings.map fun (key, value) => Lean.toJson [key, value])]
  | .protocol origin => Lean.toJson [Lean.toJson "protocol", origin.toJson]

end Zkc.Source.Structured
