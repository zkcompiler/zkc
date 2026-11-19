module

public import Std.Data.HashSet
public import Zkc.Frontend.Lowered.Tree
public import Zkc.Frontend.Semantics.Static

@[expose] public section
namespace Zkc.Frontend.Static

/-- A static environment: the values of the parameters in scope, `Self` in an interface, and
the file whose table of resolutions the syntax being evaluated is read with. In a body, the
static names in scope and the indices of loops over static ranges that are typed as run-time
naturals (TY2, TY10). -/
structure Env where
  file : FileId
  values : StaticEnvironment := {}
  self? : Option StaticValue := none
  /-- The static names in scope, by name, with their values. -/
  locals : Std.HashMap String Nat := {}
  /-- The indices of loops typed per iteration that are in scope, by name. -/
  indices : Std.HashSet String := {}
  deriving Inhabited

/-- The caller's lexical environment and the callee's proof parameters in declaration order.
A missing expression inherits the parameter with the very same scope and index. -/
structure SpecificationClosure where
  lexical : Env
  arguments : Array (ParameterRef × Option Lowered.Expr)

end Zkc.Frontend.Static
