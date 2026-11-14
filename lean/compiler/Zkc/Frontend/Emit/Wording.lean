module

public import Zkc.Frontend.Emit.Check
public import Zkc.Frontend.Static.Infer

@[expose] public section

set_option autoImplicit false

/-!
# The wording of a refusal of facts

The core says which requirement an application does not meet, which of its conditions, and
what was known of the operands; the node says what the source wrote. The message of the
reference for the two is made here: one table, by the requirement and the form of the node.
The frontend holds no fact of its own: what it says of a value ("can be as large as 9") is
what the core reported.
-/

namespace Zkc.Frontend.Emit

open Syntax
open Static
open Zkc.Core (Requirement)
open Zkc.Core.Explain (Explained Condition)

/-- A refusal as it is logged: its rule, its place and its message. -/
structure Worded where
  rule : String
  span : Span
  message : String
  deriving Inhabited

/-- The rule of the reference that a requirement of the core belongs to, when no form of the
source has a message of its own for it. -/
def ruleOf : Requirement → String
  | .ordered | .positive => "TY8"
  | .position | .slice => "TY7"
  | .size | .bound | .domain => "TY5"
  | .maximum => "CT4"
  | .reservedStop | .noDomain => "CORE"

/-- The conversion inside a conversion that applies the refining operation of a requirement,
with the types it converts between. -/
partial def refining? (requirement : Requirement) :
    Typed.Conversion → ClosedType → ClosedType → Option (ClosedType × ClosedType)
  | .bounded, source, target => if requirement == .bound then some (source, target) else none
  | .sized, source, target => if requirement == .size then some (source, target) else none
  | .nonzero, source, target => if requirement == .domain then some (source, target) else none
  | .elements inner, .seq element _, .seq other _ => refining? requirement inner element other
  | .components inner, .tuple components _, .tuple targets _ =>
    (List.range components.size).findSome? fun index =>
      match inner[index]?.getD none, components[index]?, targets[index]? with
      | some conversion, some source, some target => refining? requirement conversion source target
      | _, _, _ => none
  | .andThen first middle second, source, target =>
    (refining? requirement first source middle).orElse fun _ =>
      refining? requirement second middle target
  | _, _, _ => none

/-- What a message quotes for a natural operand: a number as it is written, otherwise the text
at its place. -/
def operandText (expr : Typed.Expr) : CompileM String :=
  match expr with
  | .staticValue _ value .number => pure (toString value)
  | other => textAt other.span

def quoteText : Typed.Quote → CompileM String
  | .span span => textAt span
  | .text text => pure text

/-- The place from the start of one expression to the end of another. -/
def spanOver (first last : Span) : Span :=
  { first with stopLine := last.stopLine, stopColumn := last.stopColumn, stopByte := last.stopByte }

/-- What a requirement of the core asks to be known, in the words of the source, for a form
that has no message of its own. -/
def needOf : Requirement → String
  | .ordered => "that the natural subtracted is at most the natural it is subtracted from"
  | .positive => "that the divisor is at least 1"
  | .position => "that the index is below the length of the collection"
  | .slice => "that the bounds of the slice are in order and within the collection"
  | .size => "that the collection has the size expected"
  | .bound => "that the natural is below the bound of the index expected"
  | .domain => "that the operands are in the domain of the operation"
  | .maximum => "a static bound of the count of the loop"
  | .reservedStop => "that no stop names a reserved reason"
  | .noDomain => "a row that says where the operation is defined"

/-- The message of the reference for an application that the core does not justify, at its
node. -/
def word (node : Option Typed.Node) (explained : Explained) : CompileM Worded := do
  let upper (position : Nat) : Option Nat := (explained.operands[position]?).bind (·.hi)
  let generic (span : Span) : Worded :=
    { rule := ruleOf explained.requirement, span
      message := s!"this needs {needOf explained.requirement}, which is not known here: write a `guard` of it before this place" }
  match node, explained.requirement with
  -- a function bound to a row that is defined on a part of its inputs
  | some (.expr (.apply info (.instance inst) _)), .domain =>
    let text ← textAt info.span
    let results := (← get).results
    let row : Option Typing.Row := match results.body? inst with
      | some (.row id) => results.rows[id]?
      | _ => none
    let named : Option (String × String) := row.bind fun (entry : Typing.Row) =>
      match entry.kind with
      | Typing.RowKind.restricted (some domain) => some (entry.key.name, domain.name)
      | _ => none
    match named with
    | some (name, domain) =>
      return { rule := "TY5", span := info.span
               message := s!"`{text}` applies the row `{name}`, which is defined where `{domain}` holds of its arguments: that is not known here; write a `guard` of it before the application" }
    | none => return generic info.span
  | some (.expr (.apply info (.operation .natSub) #[left, right])), .ordered =>
    let text ← textAt info.span
    let a ← textAt left.span
    let b ← textAt right.span
    return { rule := "TY8", span := info.span
             message := s!"`{text}` subtracts naturals: `{b} <= {a}` is not known; write `guard {b} <= {a}` before it" }
  | some (.expr (.apply info (.operation _) #[_, right])), .positive =>
    let text ← textAt info.span
    let divisor ← textAt right.span
    return { rule := "TY8", span := info.span
             message := s!"`{text}` divides naturals: `1 <= {divisor}` is not known; write `guard 1 <= {divisor}` before it" }
  | some (.expr (.apply info (.operation .seqAt) #[xs, index])), .position =>
    let xsText ← textAt xs.span
    let indexText ← operandText index
    match xs.type with
    | .seq _ (some size) =>
      match upper 1 with
      | some hi =>
        return { rule := "TY7", span := info.span
                 message := s!"`{indexText}` can be as large as {hi}; `{xsText}` has {size} elements" }
      | none =>
        return { rule := "TY7", span := info.span
                 message := s!"`{indexText}` is a `nat`; an index of `{xsText}` is an `index<{size}>`: take it from a range, or write `guard {indexText} < {size}`" }
    | _ =>
      let length := s!"length({xsText})"
      return { rule := "TY7", span := info.span
               message := s!"`{← textAt info.span}` reads a collection whose length is a run-time value: `{indexText} < {length}` is not known; write `guard {indexText} < {length}` before it" }
  | some (.expr (.apply info (.operation .seqSlice) arguments)), .slice =>
    let some xs := arguments[0]? | return generic info.span
    let some first := arguments[1]? | return generic info.span
    let xsText ← textAt xs.span
    let a ← operandText first
    let b ← match arguments[2]? with
      | some last => operandText last
      | none => pure s!"length({xsText})"
    match explained.condition, xs.type with
    | .order, _ =>
      return { rule := "TY7", span := info.span
               message := s!"`{xsText}[{a}..{b}]` needs `{a} <= {b}`, which is not known; write `guard {a} <= {b}` before it" }
    | .upperSize, .seq _ (some size) =>
      match upper 2 with
      | some hi =>
        return { rule := "TY7", span := info.span
                 message := s!"`{b}` can be as large as {hi}; `{xsText}` has {size} elements" }
      | none =>
        return { rule := "TY7", span := info.span
                 message := s!"`{b}` is a `nat`; a bound of a slice of `{xsText}` is at most {size}: write `guard {b} <= {size}`" }
    | .upperLength, _ =>
      return { rule := "TY7", span := info.span
               message := s!"`{xsText}[{a}..{b}]` needs `{b} <= length({xsText})`, which is not known; write `guard {b} <= length({xsText})` before it" }
    | _, _ => return generic info.span
  | some (.expr (.convert info conversion value quote)), requirement =>
    let some (source, target) := refining? requirement conversion value.type info.type
      | return generic info.span
    let text ← quoteText quote
    match requirement, target with
    | .bound, .index bound =>
      match upper 0 with
      | some hi =>
        return { rule := "TY8", span := info.span
                 message := s!"`{text}` can be as large as {hi}; `index<{bound}>` is expected" }
      | none =>
        return { rule := "TY8", span := info.span
                 message := s!"`{text}` is a `nat` without an upper bound; `index<{bound}>` is expected: take it from a range, or write `guard {text} < {bound}`" }
    | .size, .seq _ (some size) =>
      return { rule := "TY5", span := info.span
               message := s!"`{text}` is a `{← renderTypeM source}`; `{← renderTypeM target}` is expected: write `guard length({text}) == {size}`" }
    | .domain, _ =>
      return { rule := "TY5", span := info.span
               message := s!"`{text}` is a `{← renderTypeM source}`; `{← renderTypeM target}` is expected: write `guard {text} != 0`" }
    | _, _ => return generic info.span
  | some (.stmt (.for _ (.loop _ (.range start stop none) _ _) _)), .ordered =>
    let a ← textAt start.span
    let b ← textAt stop.span
    return { rule := "CT6", span := spanOver start.span stop.span
             message := s!"the range `{a}..{b}` needs `{a} <= {b}`, which is not known: write `guard {a} <= {b}`" }
  | some (.expr expr), _ => return generic expr.span
  | some (.stmt stmt), _ =>
    let span := match stmt with
      | .bind mark .. | .unpack mark .. | .update mark .. | .guard mark .. | .if mark ..
      | .match mark .. | .for mark .. | .scope mark _ | .event mark .. | .error mark _ => mark.span
    return generic span
  -- the core places a requirement at an application, and every application that the emitter
  -- writes carries the number of its node: a requirement without a node is a defect here
  | none, _ =>
    throw (.defect s!"a requirement of the core at no node of the tree: {reprStr explained.requirement}")

end Zkc.Frontend.Emit
