module

public import Zkc.Core.Laws
public import Zkc.Core.FiatShamir
public import Zkc.Core.Interpret

public section

/-! Toward the structural theorem of a threading step.

The structural property of the Fiat–Shamir step is an equation of processes, kept apart
from any security statement: for a side that contains exactly one transcript role, the
meaning of a definition's image is the meaning of the definition, interpreted by a
handler that carries the transcript state (`PIR.Process.interpretWith`). The handler
answers a draw of the side's transcript role by deriving, lets an absorbed message
through and absorbs it, and renumbers the definition in the site of every other effect.

This module has what the proof of that equation by induction on `threadRegion` needs
and what is proved of it:

- `Renaming.Agrees`: the new environment holds every old value at its image. The lemmas
  extend it by the operations that `threadRegion` and `plainRegion` use on a renaming
  (`operands`, `extend`, `to`, `keep`, `keepAll`).
- `Emitted.Runs`: what an emitted sequence does, as a process that yields the
  environment of the context it leaves; the laws for one operation and for a sequence.
- `Emitted.Silent`: an emitted sequence that does nothing observable. What a step emits
  for a role outside the side is silent (`at_outside_silent`, `Absorber.emit_outside`,
  `Deriver.emit_outside`); a pure row of a role in the side yields the model's results
  (`at_pure_runs`).

The equation is proved for every handler that fits a region (`Fits`,
`threadRegion_meaning`, `definition_threads`). The handler of a step is defined in
`Core/ThreadHandler.lean` from the marks of what the step rewrote; that it fits the body
of every definition of a program is derived in `Core/ThreadFits.lean`, and the equation
for the output of `stepProtocols` over a program in `Core/ThreadProgram.lean`. The side
holds exactly one transcript role throughout: for a side that holds both, an exchange
between them performs no effect, so no handler of effects can absorb its value.
-/

set_option autoImplicit false

namespace Zkc.Source

/-! ## Environments across a renaming -/

/-- The new environment holds every old value at its image. -/
@[expose] def Renaming.Agrees {Ty : Type} {Value : Ty → Type} {Γ Δ : List Ty} (rename : Renaming Γ Δ)
    (old : Environment Value Γ) (new : Environment Value Δ) : Prop :=
  ∀ {ty : Ty} (reference : Var Γ ty), new (rename.rename reference) = old reference

namespace Renaming.Agrees

variable {Ty : Type} {Value : Ty → Type} {Γ Δ : List Ty} {rename : Renaming Γ Δ}
  {old : Environment Value Γ} {new : Environment Value Δ}

/-- Renamed operands have the old values. -/
theorem operands (agrees : rename.Agrees old new) :
    ∀ {types : List Ty} (values : Operands Γ types),
      Operands.eval new (rename.operands values) = Operands.eval old values
  | _, .nil => rfl
  | _, .cons reference rest => by
      exact congr (congrArg Values.cons (agrees reference)) (operands agrees rest)

/-- The new context grows; the old values stay where they were. -/
theorem extend {Δ' : List Ty} (agrees : rename.Agrees old new) (grows : Extends Δ Δ')
    (later : Environment Value Δ')
    (same : ∀ {ty : Ty} (reference : Var Δ ty), later (reference.extend grows) = new reference) :
    (rename.extend grows).Agrees old later := by
  intro ty reference
  show later ((Mapping.extend rename grows).apply reference rfl) = _
  rw [Mapping.apply_extend, same]
  exact agrees reference

/-- An old value is bound whose image is a value the new environment already holds. -/
theorem to (agrees : rename.Agrees old new) {ty : Ty} (image : Var Δ ty) (value : Value ty)
    (holds : new image = value) : (rename.to image).Agrees (old.push value) new := by
  intro other reference
  cases reference with
  | here => exact (congrArg new (Mapping.apply_bind_here ..)).trans holds
  | there reference => exact (congrArg new (Mapping.apply_bind_there ..)).trans (agrees reference)

/-- One value is bound on both sides. -/
theorem keep (agrees : rename.Agrees old new) {ty : Ty} (value : Value ty) :
    Renaming.Agrees (rename.keep ty ty fun _ same => same.symm) (old.push value)
      (new.push value) := by
  intro other reference
  cases reference with
  | here => exact congrArg (new.push value) (Mapping.apply_keep_here ..)
  | there reference =>
      exact (congrArg (new.push value) (Mapping.apply_keep_there ..)).trans (agrees reference)

/-- The same values are bound on both sides. -/
theorem keepAll :
    ∀ {added : List Ty} {Γ Δ : List Ty} {rename : Renaming Γ Δ} {old : Environment Value Γ}
      {new : Environment Value Δ}, rename.Agrees old new → ∀ (values : Values Value added),
        (rename.keepAll added).Agrees (old.bindAll values) (new.bindAll values)
  | _, _, _, _, _, _, agrees, .nil => agrees
  | _, _, _, _, _, _, agrees, .cons value rest => keepAll (agrees.keep value) rest

end Renaming.Agrees

/-! ## What an emitted sequence does -/

/-- An emitted sequence, run in an environment, is a process that yields the
environment of the context it leaves; whatever follows it runs in that environment. -/
@[expose] def Emitted.Runs {dialect : Dialect} {I : PIR.Signature} {Δ results : List dialect.Ty}
    (emitted : Emitted dialect Δ results) (meaning : RegionMeaning dialect I)
    (env : Environment meaning.Value Δ)
    (process : PIR.Process I (Environment meaning.Value emitted.context)) : Prop :=
  ∀ {out : List dialect.Ty} (next : Region dialect emitted.context out),
    (emitted.wrap next).denote meaning env = process.bind fun later => next.denote meaning later

namespace Emitted

variable {dialect : Dialect} {I : PIR.Signature} {Δ : List dialect.Ty}

/-- One operation runs as its meaning; the environment gains its results. -/
theorem operation_runs (meaning : RegionMeaning dialect I) (op : dialect.Op)
    (arguments : Operands Δ (dialect.arguments op)) (bodies : Regions dialect (dialect.regions op))
    (env : Environment meaning.Value Δ) :
    (Emitted.operation op arguments bodies).Runs meaning env
      ((meaning.operation op (Operands.eval env arguments) (bodies.denote meaning)).bind
        fun values => .done (Environment.bindAll env values)) := by
  intro out next
  show (meaning.operation op _ _).bind _ = _
  rw [PIR.Process.bind_assoc]
  rfl

/-- A sequence runs as its first part, then its second part in the environment the
first left. -/
theorem andThen_runs {first second results : List dialect.Ty} (meaning : RegionMeaning dialect I)
    (before : Emitted dialect Δ first) (after : Emitted dialect before.context second)
    (values : Operands after.context results) (env : Environment meaning.Value Δ)
    (process : PIR.Process I (Environment meaning.Value before.context))
    (later : Environment meaning.Value before.context →
      PIR.Process I (Environment meaning.Value after.context))
    (runsBefore : before.Runs meaning env process)
    (runsAfter : ∀ middle, after.Runs meaning middle (later middle)) :
    (before.andThen after values).Runs meaning env (process.bind later) := by
  intro out next
  refine (runsBefore (after.wrap next)).trans ?_
  refine Eq.trans ?_ (PIR.Process.bind_assoc process later _).symm
  exact congrArg (PIR.Process.bind process) (funext fun middle => runsAfter middle next)

/-- An emitted sequence does nothing observable: it yields an environment that holds
the earlier values. -/
def Silent {results : List dialect.Ty} (emitted : Emitted dialect Δ results)
    (meaning : RegionMeaning dialect I) (env : Environment meaning.Value Δ) : Prop :=
  ∃ later : Environment meaning.Value emitted.context,
    emitted.Runs meaning env (.done later) ∧
      ∀ {ty : dialect.Ty} (reference : Var Δ ty),
        later (reference.extend emitted.grows) = env reference

/-- A silent sequence followed by a silent sequence is silent. -/
theorem Silent.andThen {first second results : List dialect.Ty} (meaning : RegionMeaning dialect I)
    (before : Emitted dialect Δ first) (after : Emitted dialect before.context second)
    (values : Operands after.context results) (env : Environment meaning.Value Δ)
    (silentBefore : before.Silent meaning env)
    (silentAfter : ∀ middle, after.Silent meaning middle) :
    (before.andThen after values).Silent meaning env := by
  obtain ⟨middle, runsBefore, keepsBefore⟩ := silentBefore
  obtain ⟨final, runsAfter, keepsAfter⟩ := silentAfter middle
  refine ⟨final, fun next => (runsBefore (after.wrap next)).trans (runsAfter next), ?_⟩
  intro ty reference
  exact (congrArg final (Var.ext (Nat.add_assoc ..).symm)).trans
    ((keepsAfter (reference.extend before.grows)).trans (keepsBefore reference))

/-- The environment after one operation holds the earlier values. -/
theorem operation_keeps (meaning : RegionMeaning dialect I) (op : dialect.Op)
    (arguments : Operands Δ (dialect.arguments op)) (bodies : Regions dialect (dialect.regions op))
    (env : Environment meaning.Value Δ) (values : Values meaning.Value (dialect.results op))
    {ty : dialect.Ty} (reference : Var Δ ty) :
    Environment.bindAll env values
        (reference.extend (Emitted.operation op arguments bodies).grows) = env reference :=
  Environment.bindAll_weaken env values reference

end Emitted

end Zkc.Source

namespace Zkc.Core

open Zkc.Source

/-! ## One role's transcript operations

A role outside the side does nothing: what the step emits for it yields an environment
that holds the earlier values. This is the law of the absorbing form and of the deriving
form for the other role's side, for both kinds of suite.

For a role in the side, one operation with a pure row yields the environment with the
model's results (`at_pure_runs`); the law of a whole form for the role's own side, which
composes two of these and names the resulting state, is `Absorber.emit_yields` and
`Deriver.emit_yields` in `Core/ThreadFiatShamir.lean`. -/

section Laws

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {side : Side} {identity : Nat} {path : List Nat}

local notation "𝒟" => ProtocolDialect operations functions protocols deployed

/-- A local operation of a role outside the side is silent. -/
theorem at_outside_silent {role : Nat} (absent : side role = false)
    (op : LocalOp operations functions deployed) {Δ : List Located}
    (arguments : Operands Δ (Located.atRole role op.arguments))
    (bodies : Regions (LocalDialect operations functions deployed) op.regions)
    (env : Environment (SideValue model side) Δ) :
    (Emitted.operation (dialect := 𝒟) (.at role op bodies) arguments .nil).Silent
      (sideMeaning model functionTable table identity path side) env :=
  ⟨Environment.bindAll env
      (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
        (absentHeldValues (side role) absent op.results)),
    fun _ => sideMeaning_step_done (at_absent (model := model) (functionTable := functionTable)
      (table := table) absent),
    fun reference => Environment.bindAll_weaken env _ reference⟩

/-- A role outside the side absorbs nothing. -/
theorem Absorber.emit_outside {state type : Ty} {role : Nat} (absent : side role = false)
    (absorber : Absorber operations functions state type) {Δ : List Located}
    (current : Var Δ ⟨state, role⟩) (value : Var Δ ⟨type, role⟩)
    (env : Environment (SideValue model side) Δ) :
    (absorber.emit (protocols := protocols) (deployed := deployed) role current value).Silent
      (sideMeaning model functionTable table identity path side) env := by
  cases absorber with
  | row name absorb =>
      refine Emitted.Silent.andThen (sideMeaning model functionTable table identity path side) _ _ _ env
        (at_outside_silent absent _ _ _ env) ?_
      intro middle
      exact at_outside_silent absent _ _ _ middle
  | handler callee => exact at_outside_silent absent _ _ _ env

/-- A role outside the side derives nothing. -/
theorem Deriver.emit_outside {state output : Ty} {role : Nat} (absent : side role = false)
    (deriver : Deriver operations functions state output) {Δ : List Located}
    (current : Var Δ ⟨state, role⟩) (env : Environment (SideValue model side) Δ) :
    (deriver.emit (protocols := protocols) (deployed := deployed) role current).Silent
      (sideMeaning model functionTable table identity path side) env := by
  cases deriver with
  | row name derive _ =>
      refine Emitted.Silent.andThen (sideMeaning model functionTable table identity path side) _ _ _ env
        (at_outside_silent absent _ _ _ env) ?_
      intro middle
      exact at_outside_silent absent _ _ _ middle
  | handler callee => exact at_outside_silent absent _ _ _ env

/-- A pure row of a role in the side: the environment gains the model's results. -/
theorem at_pure_runs {role : Nat} (member : side role = true) {inputs outputs : List Ty}
    (row : Var operations ⟨inputs, outputs, .pure⟩)
    (applies : OperationSignature.applies ⟨inputs, outputs, .pure⟩ = true) {Δ : List Located}
    (arguments : Operands Δ (Located.atRole role inputs))
    (env : Environment (SideValue model side) Δ) :
    (Emitted.operation (dialect := 𝒟) (.at role (.op row applies) .nil) arguments .nil).Runs
      (sideMeaning model functionTable table identity path side) env
      (.done (Environment.bindAll env
        (remapValues (F := SideValue model side) (fun type => ⟨type, role⟩) _
          (holdValues (side role) (model.pure (.of row) applies
            (presentValues (side role) member (unmapValues _ _ (Operands.eval env arguments)))))))) :=
  fun _ => sideMeaning_step_done (at_pure (model := model) (functionTable := functionTable)
    (table := table) member)

end Laws

end Zkc.Core
