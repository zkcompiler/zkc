module

public import Zkc.Core.Program.LinkedVocabulary
public import Zkc.Frontend.Typed.Summary
public import Zkc.Vocabulary.Standard

@[expose] public section

namespace Zkc.Frontend.Emit

/-- A source type in a primitive's static arguments. A record, variant or module
instance refers to its declaration in the same compilation. Tuple labels and sort
constraints describe source syntax and add no new runtime type identity. -/
inductive TypeHead where
  | bool | nat | rational | index (bound : Nat) | nonzero
  | seq (size : Option Nat) | tuple | nominal (row : String)
  | record (inst : InstanceId) | variant (inst : InstanceId)
  | specification (inst : InstanceId) | opaqueMember (inst : InstanceId) (member : String)
  deriving DecidableEq, Repr, Hashable

mutual
  inductive Parameter where
    | natural (value : Nat)
    | moduleRef (inst : InstanceId)
    | type (head : TypeHead) (args : Parameters)
  inductive Parameters where
    | nil
    | cons (head : Parameter) (tail : Parameters)
end

deriving instance DecidableEq for Parameter, Parameters
deriving instance Repr for Parameter, Parameters
deriving instance Hashable for Parameter, Parameters

namespace Parameter
mutual
  def ofType : ClosedType → Parameter
    | .bool => .type .bool .nil
    | .nat => .type .nat .nil
    | .rational => .type .rational .nil
    | .index n => .type (.index n) .nil
    | .nonzero t => .type .nonzero (.cons (ofType t) .nil)
    | .seq t size => .type (.seq size) (.cons (ofType t) .nil)
    | .tuple ts _ => .type .tuple (ts.attach.foldr (fun t rest => .cons (ofType t.val) rest) .nil)
    | .nominal name args => .type (.nominal name) (ofValues args)
    | .record i => .type (.record i) .nil
    | .variant i => .type (.variant i) .nil
    | .specification i => .type (.specification i) .nil
    | .opaque i member args _ => .type (.opaqueMember i member) (ofValues args)
  termination_by t => sizeOf t
  decreasing_by all_goals first | decreasing_tactic | (have := Array.sizeOf_lt_of_mem t.property; simp_all +arith; omega)
  def ofValues (values : Array StaticValue) : Parameters :=
    values.attach.foldr (fun arg rest => .cons (match _h : arg.val with
      | .natural n => .natural n
      | .module i => .moduleRef i
      | .type t => ofType t) rest) .nil
  termination_by sizeOf values
  decreasing_by have := Array.sizeOf_lt_of_mem arg.property; rw [_h] at this; simp +arith at this; omega
end
end Parameter

structure PrimitiveName where
  name : String
  arguments : Parameters
  deriving DecidableEq, Repr, Hashable

def primitiveName (source : Typing.RowKey) : PrimitiveName :=
  ⟨source.name, source.statics.foldr (fun arg rest => .cons (match arg with
    | .nat n => .natural n
    | .type t => Parameter.ofType t) rest) .nil⟩

/-- Two declarations of one primitive must describe the same value signature and domain.
The identity comparison uses the same interpretation of type arguments as the linker. -/
def sameRowSignature (a b : Typing.Row) : Bool :=
  let kindAgrees := match a.kind, b.kind with
    | .pure, .pure | .sampling, .sampling => true
    | .restricted x, .restricted y => decide (x.map primitiveName = y.map primitiveName)
    | _, _ => false
  kindAgrees && decide (a.inputs.map Parameter.ofType = b.inputs.map Parameter.ofType) &&
    decide (a.outputs.map Parameter.ofType = b.outputs.map Parameter.ofType)

abbrev LinkedType := Core.Ty (Sum Zkc.Vocabulary.TypeKey Parameter)

structure PrimitiveSignature where
  inputs : List LinkedType
  outputs : List LinkedType
  deriving DecidableEq

/-- A single signature for each project binding, including bindings reached through
different declarations with the same primitive spelling and evaluated static arguments. -/
structure Bindings where
  rows : List (PrimitiveName × PrimitiveSignature) := []
  distinct : (rows.map Prod.fst).Nodup := by decide

def Bindings.signature (b : Bindings) (k : PrimitiveName) : Option PrimitiveSignature :=
  b.rows.lookup k

def Bindings.insert (b : Bindings) (key : PrimitiveName) (signature : PrimitiveSignature) :
    Except PrimitiveName Bindings :=
  match h : b.signature key with
  | none => .ok ⟨(key, signature) :: b.rows, by
      apply List.nodup_cons.mpr
      refine ⟨?_, b.distinct⟩
      intro member
      obtain ⟨p, hp, same⟩ := List.mem_map.mp member
      have different := List.lookup_eq_none_iff.mp h p hp
      simp [same] at different⟩
  | some prior => if prior = signature then .ok b else .error key

def Bindings.primitives (b : Bindings) : Core.PurePrimitives Zkc.Vocabulary.standard Parameter PrimitiveName where
  signature key := (b.signature key).map fun s => (s.inputs, s.outputs)

abbrev Bindings.vocabulary (b : Bindings) : Core.Vocabulary := b.primitives.vocabulary

end Zkc.Frontend.Emit
