module

public import Zkc.Frontend.Semantics.Instantiate.Roots

@[expose] public section

set_option autoImplicit false

/-!
# A type found in a state that is discarded

The body of a loop of no iteration is typed apart, for the type of each collected name alone,
and what the typing made is forgotten: the state of the compiler is put back (TY10, TY16). A
type found on the way may name an instance that the typing made, a record at static arguments
that nothing else of the program uses. Putting the state back deletes that instance, and the
number that the type holds is then the number of whatever instance is made next.

`remakeType` makes such a type again in the state that was put back. An instance that the
state already has keeps its number: the table grows at its end, so an entry below the size of
the table is the same entry before and after. An instance above it is requested again by its
key, read from the discarded state: its declaration at its static arguments, which are made
again in the same way where they name instances. The type then names instances that exist,
and nothing else that the body made remains: no body is typed for a function that only the
loop calls.
-/

namespace Zkc.Frontend.Instances

open Syntax
open Static

mutual
  /-- A type of the discarded state, in the present state. -/
  partial def remakeType (discarded : Compile.State) (place : Span) :
      ClosedType → CompileM ClosedType
    | .nonzero field => .nonzero <$> remakeType discarded place field
    | .seq element size => (.seq · size) <$> remakeType discarded place element
    | .tuple components names => (.tuple · names) <$> components.mapM (remakeType discarded place)
    | .nominal row arguments => .nominal row <$> arguments.mapM (remakeValue discarded place)
    | .record inst => .record <$> remakeInstance discarded place inst
    | .«variant» inst => .«variant» <$> remakeInstance discarded place inst
    | .specification inst => .specification <$> remakeInstance discarded place inst
    | .«opaque» «module» member arguments sorts => do
      return .«opaque» (← remakeInstance discarded place «module») member
        (← arguments.mapM (remakeValue discarded place)) sorts
    | type => pure type

  /-- A static value of the discarded state, in the present state. -/
  partial def remakeValue (discarded : Compile.State) (place : Span) :
      StaticValue → CompileM StaticValue
    | .type type => .type <$> remakeType discarded place type
    | .«module» inst => .«module» <$> remakeInstance discarded place inst
    | value => pure value

  /-- The instance of the present state with the key that an instance of the discarded state
  has. -/
  partial def remakeInstance (discarded : Compile.State) (place : Span) (inst : InstanceId) :
      CompileM InstanceId := do
    if inst < (← get).table.entries.size then return inst
    let some entry := discarded.table.entries[inst]?
      | throw (.defect "a type names an instance that no state holds")
    let key := entry.key
    let arguments ← key.arguments.mapM (remakeValue discarded place)
    let owner ← key.owner.mapM (remakeInstance discarded place)
    let description ← describeInstance key.declaration arguments key.specification owner
    match key.opaqueFor with
    | none =>
      instantiate key.declaration arguments { description, span := place }
        (specification := key.specification) (owner := owner)
    | some (reference, equated) =>
      let real ← instantiate key.declaration arguments { description, span := place }
        (specification := key.specification)
      opaqueModule reference equated real
end

end Zkc.Frontend.Instances
