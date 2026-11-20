module

public import Zkc.Frontend.Typed.Summary
public import Zkc.Vocabulary.Project

@[expose] public section

namespace Zkc.Frontend.Emit

open Zkc.Vocabulary.Project

/-!
How the frontend names what a project binds: a closed source type as a parameter of a
primitive, and a source row as the name of a primitive. The types themselves are the
vocabulary's (`Zkc.Vocabulary.Project`).
-/

mutual
  /-- A closed source type as a static argument of a primitive. -/
  def parameterOfType : ClosedType → Parameter
    | .bool => .type .bool .nil
    | .nat => .type .nat .nil
    | .rational => .type .rational .nil
    | .index n => .type (.index n) .nil
    | .nonzero t => .type .nonzero (.cons (parameterOfType t) .nil)
    | .seq t size => .type (.seq size) (.cons (parameterOfType t) .nil)
    | .tuple ts _ => .type .tuple (ts.attach.foldr (fun t rest => .cons (parameterOfType t.val) rest) .nil)
    | .nominal name args => .type (.nominal name) (parametersOfValues args)
    | .record i => .type (.record i) .nil
    | .variant i => .type (.variant i) .nil
    | .specification i => .type (.specification i) .nil
    | .opaque i member args _ => .type (.opaqueMember i member) (parametersOfValues args)
  termination_by t => sizeOf t
  decreasing_by all_goals first | decreasing_tactic | (have := Array.sizeOf_lt_of_mem t.property; simp_all +arith; omega)
  /-- Static values as the static arguments of a primitive. -/
  def parametersOfValues (values : Array StaticValue) : Parameters :=
    values.attach.foldr (fun arg rest => .cons (match _h : arg.val with
      | .natural n => .natural n
      | .module i => .moduleRef i
      | .type t => parameterOfType t) rest) .nil
  termination_by sizeOf values
  decreasing_by have := Array.sizeOf_lt_of_mem arg.property; rw [_h] at this; simp +arith at this; omega
end

/-- The name of the primitive that a source row binds. -/
def primitiveName (source : Typing.RowKey) : PrimitiveName :=
  ⟨source.name, source.statics.foldr (fun arg rest => .cons (match arg with
    | .nat n => .natural n
    | .type t => parameterOfType t) rest) .nil⟩

/-- Two declarations of one primitive must describe the same value signature and domain.
The identity comparison uses the same interpretation of type arguments as the linker. -/
def sameRowSignature (a b : Typing.Row) : Bool :=
  let kindAgrees := match a.kind, b.kind with
    | .pure, .pure | .sampling, .sampling => true
    | .restricted x, .restricted y => decide (x.map primitiveName = y.map primitiveName)
    | _, _ => false
  kindAgrees && decide (a.inputs.map parameterOfType = b.inputs.map parameterOfType) &&
    decide (a.outputs.map parameterOfType = b.outputs.map parameterOfType)

end Zkc.Frontend.Emit
