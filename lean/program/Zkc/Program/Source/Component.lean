module

public import Zkc.Program.Source.Region
public import Zkc.Program.Source.RoleFamily
public import Zkc.Program.Interpretation

@[expose] public section

/-! Optional components are a second interpretation of the existing Region.
Nested callbacks use the original nonoptional meaning. Operation implementations
decide how to handle absent operands; strict lifting reuses the original operation.
These definitions provide no static availability or participant-formation check.
-/
set_option autoImplicit false
namespace Zkc.Source

variable {Ty : Type} {Value : Ty → Type}

abbrev Component (Value : Ty → Type) : Ty → Type := fun ty => Option (Value ty)

def Values.present : {types : List Ty} → Values Value types → Values (Component Value) types
  | [], .nil => .nil
  | _ :: _, .cons value rest => .cons (some value) rest.present

def Values.absent (Value : Ty → Type) : (types : List Ty) → Values (Component Value) types
  | [] => .nil
  | _ :: rest => .cons none (Values.absent Value rest)

@[simp] theorem Values.get_present {types : List Ty} {ty : Ty}
    (values : Values Value types) (ref : Var types ty) :
    values.present.get ref = some (values.get ref) := by
  induction values with
  | nil => cases ref
  | cons value rest ih => cases ref with
    | here => rfl
    | there ref => exact ih ref

@[simp] theorem RoleFamily.sequence_present {types : List Ty} (values : Values Value types) :
    RoleFamily.sequence values.present = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [Values.present, RoleFamily.sequence, ih]

theorem Operands.eval_present {types args : List Ty}
    (env : Environment Value types) (operands : Operands types args) :
    operands.eval (fun ref => some (env ref)) = (operands.eval env).present := by
  induction operands with
  | nil => rfl
  | cons value rest ih => simp only [Operands.eval, Values.present, ih]

theorem Environment.prepend_present {types added : List Ty}
    (env : Environment Value types) (values : Values Value added) :
    @Eq (Environment (Component Value) (added ++ types))
      (Environment.prepend (fun ref => some (env ref)) values.present)
      (fun ref => some (env.prepend values ref)) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    funext ty ref
    cases ref with
    | here => rfl
    | there ref => exact congrFun (congrFun ih _) ref

variable {dialect : Dialect} {interface : PIR.Signature}

/-- Component operands/results, with nonoptional callbacks. -/
abbrev ComponentOperations (meaning : RegionMeaning dialect interface) :=
  (op : dialect.Op) → Values (Component meaning.Value) (dialect.arguments op) →
    Values (RegionFunction meaning.Value interface) (dialect.regions op) →
      PIR.Process interface (Values (Component meaning.Value) (dialect.results op))

/-- Absence skips this operation; present operands preserve all effects and stops.
This rule is appropriate for strict leaves, not dependency-precise named calls. -/
def strictComponent (meaning : RegionMeaning dialect interface) : ComponentOperations meaning :=
  fun op args bodies =>
    match RoleFamily.sequence args with
    | none => .done (Values.absent meaning.Value (dialect.results op))
    | some values => (meaning.operation op values bodies).bind fun result => .done result.present

def Region.component (meaning : RegionMeaning dialect interface)
    (operations : ComponentOperations meaning) {Γ out} :
    Region dialect Γ out → Environment (Component meaning.Value) Γ →
      PIR.Process interface (Values (Component meaning.Value) out)
  | .ret values, env => .done (values.eval env)
  | .stop reason, _ => .halt reason
  | .letOp op args bodies next, env =>
      (operations op (args.eval env) (bodies.denote meaning)).bind fun values =>
        next.component meaning operations (env.prepend values)
  | .bind body next, env =>
      (body.component meaning operations env).bind fun values =>
        next.component meaning operations (env.prepend values)

/-- Agreement on all-present inputs, for arbitrary nonoptional callbacks. -/
def ComponentOperations.Adequate (meaning : RegionMeaning dialect interface)
    (operations : ComponentOperations meaning) : Prop :=
  ∀ op args bodies, operations op args.present bodies =
    (meaning.operation op args bodies).bind fun result => .done result.present

theorem strictComponent_adequate (meaning : RegionMeaning dialect interface) :
    ComponentOperations.Adequate meaning (strictComponent meaning) := by
  intro op args bodies
  simp only [strictComponent, RoleFamily.sequence_present]

/-- Missing any strict operand skips the whole operation, even with no results. -/
theorem strictComponent_absent (meaning : RegionMeaning dialect interface)
    (op : dialect.Op) (args : Values (Component meaning.Value) (dialect.arguments op))
    (bodies : Values (RegionFunction meaning.Value interface) (dialect.regions op))
    (absent : RoleFamily.sequence args = none) :
    strictComponent meaning op args bodies =
      .done (Values.absent meaning.Value (dialect.results op)) := by
  simp only [strictComponent, absent]

/-- A reached strict stop retains its reason, including empty and unused results. -/
theorem strictComponent_stops (meaning : RegionMeaning dialect interface)
    (op : dialect.Op) (args : Values meaning.Value (dialect.arguments op))
    (bodies : Values (RegionFunction meaning.Value interface) (dialect.regions op))
    (reason : PIR.Stop) (stops : meaning.operation op args bodies = .halt reason) :
    strictComponent meaning op args.present bodies = .halt reason := by
  rw [strictComponent_adequate meaning op args bodies, stops]
  rfl

theorem Values.get_absent {T : Type} {V : T → Type} {types : List T} {ty : T}
    (ref : Var types ty) : (Values.absent V types).get ref = none := by
  induction ref with
  | here => rfl
  | there ref ih => exact ih

/-- Presence is exact on a returned path; this theorem does not assert return. -/
theorem strictComponent_return_presence {d : Dialect} {I : PIR.Signature}
    (m : RegionMeaning d I) (op : d.Op)
    (args : Values (Component m.Value) (d.arguments op))
    (bodies : Values (RegionFunction m.Value I) (d.regions op))
    (result : Values (Component m.Value) (d.results op))
    (returned : strictComponent m op args bodies = .done result)
    {ty : d.Ty} (ref : Var (d.results op) ty) :
    (result.get ref).isSome = (RoleFamily.sequence args).isSome := by
  cases sequenced : RoleFamily.sequence args with
  | none =>
    rw [strictComponent_absent m op args bodies sequenced] at returned
    cases returned
    simp only [Values.get_absent, Option.isSome_none]
  | some values =>
    simp only [strictComponent, sequenced] at returned
    cases process : m.operation op values bodies with
    | done output =>
      simp only [process, PIR.Process.bind, PIR.Process.done.injEq] at returned
      subst result
      simp only [Values.get_present, Option.isSome_some]
    | halt reason => simp only [process, PIR.Process.bind] at returned; cases returned
    | call action next => simp only [process, PIR.Process.bind] at returned; cases returned

/-- All-present adequacy preserves the complete process, including stops, actions
and nested regions. Callbacks on both sides use precisely the same meaning. -/
theorem Region.component_present (meaning : RegionMeaning dialect interface)
    (operations : ComponentOperations meaning) (adequate : operations.Adequate meaning)
    {Γ out} (region : Region dialect Γ out) (env : Environment meaning.Value Γ) :
    region.component meaning operations (fun ref => some (env ref)) =
      (region.denote meaning env).bind fun result => .done result.present := by
  induction region using Region.rec (motive_2 := fun _ _ => True) with
  | ret values => simp only [Region.component, Region.denote, PIR.Process.bind, Operands.eval_present]
  | stop reason => rfl
  | letOp op args bodies next _ nextIH =>
    have operationPresent := adequate op (args.eval env) (bodies.denote meaning)
    simp only [Region.component, Region.denote, Operands.eval_present, operationPresent,
      PIR.Process.bind_assoc, PIR.Process.bind, Environment.prepend_present, nextIH]
  | bind body next bodyIH nextIH =>
    simp only [Region.component, Region.denote, bodyIH, PIR.Process.bind_assoc,
      PIR.Process.bind, Environment.prepend_present, nextIH]
  | nil => trivial
  | cons => trivial

end Zkc.Source
