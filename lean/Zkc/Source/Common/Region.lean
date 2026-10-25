module

public import Zkc.Source.Common.Import

@[expose] public section

/-! The current scalar import carrier as canonical regions.

The operation profile retains source action metadata and uses the same sorts,
with optional participant values. Its operations have no nested callbacks;
calculations and their lexical scopes are represented structurally. The supplied
mathematical meaning, services and condition policy are exactly those of Common.
This is an equality between Lean processes, not a native execution or security
theorem, and does not extend the native scalar format. Role-specific lowering
partly resolves locality. The operation type retains the selected participant,
so the resulting region cannot use another participant's meaning.
-/

set_option autoImplicit false

namespace Zkc.Source.Common

/-- Typed leaf descriptors for one participant's projection. The nominal `self`
parameter keeps the selected role in the dialect even when a descriptor has no
role-dependent fields. Statement metadata remains in the syntax even though its
runtime interpretation is the identity. -/
inductive ParticipantOp (Role : Type) (language : Language)
    (services : Participant.Services language.Ty) (self : Role) where
  | mathematical (op : language.Op)
  | restrict (sort : language.Ty) (selected : Bool)
  | exchange (sort : language.Ty) (site : String) (sender receiver : Role)
  | query (site : String) (owner : Role) (op : services.Op)
  | guard (site : String) (owner : Role)
  | statement (types : List language.Ty) (relation : String) (selectors : List Role)

abbrev participantDialect (Role : Type) (language : Language)
    (services : Participant.Services language.Ty) (self : Role) : Dialect where
  Ty := language.Ty
  Op := ParticipantOp Role language services self
  arguments
    | .mathematical op => language.arguments op
    | .restrict sort _ | .exchange sort .. => [sort]
    | .query _ _ op => services.arguments op
    | .guard .. => [language.condition]
    | .statement types .. => types
  results
    | .mathematical op => [language.result op]
    | .restrict sort _ | .exchange sort .. => [sort]
    | .query _ _ op => [services.result op]
    | .guard .. | .statement .. => []
  regions _ := []

variable {Role : Type} [DecidableEq Role] {language : Language}
    {services : Participant.Services language.Ty}

/-- Only the owner requires query arguments (including any service handle).
Receivers use the actual reply, independently of their local sender operand.
Missing mathematical components remain values; owned action inputs may stop. -/
def participantMeaning (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) :
    RegionMeaning (participantDialect Role language services self)
      (Participant.interface Role language.Ty services meaning.Value) where
  Value := fun sort => Option (meaning.Value sort)
  operation
    | .mathematical op, args, .nil =>
        .done (Values.singleton ((RoleFamily.sequence args).map (meaning.operation op)))
    | .restrict _ selected, .cons value .nil, .nil =>
        .done (Values.singleton (Participant.restrict selected value))
    | .exchange _ site sender receiver, .cons value .nil, .nil =>
        (Participant.exchange self sender receiver site value).bind fun received =>
          .done (Values.singleton received)
    | .query site owner op, args, .nil =>
        (Participant.query self owner site op args).bind fun value =>
          .done (Values.singleton value)
    | .guard _ owner, .cons value .nil, .nil =>
        (Participant.guard self owner (value.map condition)).bind fun _ => .done .nil
    | .statement .., _, .nil => .done .nil

/-- A small structural adapter into the Common operation profile. Mathematical
projection's separate reference adapter does not need a generic dialect embedding. -/
def lowerCalculation (self : Role) {Γ ty} :
    Mathematical.Block Role language Γ ty →
      Region (participantDialect Role language services self) Γ [ty]
  | .ret value => .ret (Values.singleton value)
  | .letOp op args next => .letOp (.mathematical op) args .nil (lowerCalculation self next)
  | .restrict (selected := sort) scope value next =>
      .letOp (.restrict sort (scope self)) (Values.singleton value) .nil
        (lowerCalculation self next)
  | .bind body next => .bind (lowerCalculation self body) (lowerCalculation self next)

/-- Every mathematical node retains exactly its independent component meaning,
including absent inputs and unused intermediate results. -/
theorem denote_lowerCalculation (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) {Γ ty}
    (body : Mathematical.Block Role language Γ ty)
    (env : Environment (fun sort => Option (meaning.Value sort)) Γ) :
    (lowerCalculation (services := services) self body).denote
        (participantMeaning meaning condition self) env =
      .done (Values.singleton (body.evalAt meaning self env)) := by
  induction body with
  | ret value => rfl
  | letOp op args next ih => exact ih _
  | restrict scope value next ih => exact ih _
  | bind body next bodyIH nextIH =>
      simp only [lowerCalculation, Region.denote, bodyIH, PIR.Process.bind,
        Mathematical.Block.evalAt]
      exact nextIH _

/-- Lower every current scalar constructor without hiding an entire program or
calculation in an operation. Bind retains the caller context and suffix once. -/
def Program.toRegion (self : Role) {Γ ty} : Program Role language services Γ ty →
    Region (participantDialect Role language services self) Γ [ty]
  | .ret value => .ret (Values.singleton value)
  | .calculate body next => .bind (lowerCalculation self body) (next.toRegion self)
  | .exchange (sent := sort) site sender receiver value next =>
      .letOp (.exchange sort site sender receiver) (Values.singleton value) .nil
        (next.toRegion self)
  | .query site owner op args next =>
      .letOp (.query site owner op) args .nil (next.toRegion self)
  | .guard site owner condition next =>
      .letOp (.guard site owner) (Values.singleton condition) .nil (next.toRegion self)
  | .statement (types := types) relation selectors args next =>
      .letOp (.statement types relation selectors) args .nil (next.toRegion self)

/-- Universal open-process equality: all participant values, services, condition
policies, environments and actual replies are covered, with no admission premise.
Every stop and the order of sends, receives and queries are preserved. -/
theorem Program.denote_toRegion (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) {Γ ty}
    (program : Program Role language services Γ ty)
    (env : Environment (fun sort => Option (meaning.Value sort)) Γ) :
    (program.toRegion self).denote (participantMeaning meaning condition self) env =
      (program.denote meaning condition self env).bind
        (fun value => .done (Values.singleton value)) := by
  induction program with
  | ret value => rfl
  | calculate body next ih =>
      simp only [toRegion, Region.denote, denote_lowerCalculation, PIR.Process.bind, denote]
      exact ih _
  | exchange site sender receiver value next ih =>
      simp only [toRegion, Region.denote, participantMeaning, Values.singleton,
        Operands.eval, Regions.denote, denote, PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext received
      exact ih _
  | query site owner op args next ih =>
      simp only [toRegion, Region.denote, participantMeaning, Regions.denote, denote,
        PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext value
      exact ih _
  | guard site owner ref next ih =>
      simp only [toRegion, Region.denote, participantMeaning, Values.singleton,
        Operands.eval, Regions.denote, denote, PIR.Process.bind_assoc, PIR.Process.bind]
      congr 1
      funext reply
      exact ih _
  | statement relation selectors args next ih => exact ih _

/-- Exact deterministic execution, including all handler stops, state and events.
The only result conversion is the explicit singleton wrapper. -/
theorem Program.run_toRegion (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) {Γ ty}
    (program : Program Role language services Γ ty)
    (env : Environment (fun sort => Option (meaning.Value sort)) Γ)
    {S E : Type} (handler : PIR.Handler (Participant.interface Role language.Ty services meaning.Value) S E)
    (state : S) :
    ((program.toRegion self).denote (participantMeaning meaning condition self) env).run
        handler state =
      ((program.denote meaning condition self env).bind
        (fun value => .done (Values.singleton value))).run handler state := by
  rw [denote_toRegion]

/-- Equality also holds for any monadic handler; no naturality or lawful-monad
premise is needed to transport equality of the entire open process. -/
theorem Program.runM_toRegion {m : Type → Type} [Monad m]
    (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) {Γ ty}
    (program : Program Role language services Γ ty)
    (env : Environment (fun sort => Option (meaning.Value sort)) Γ)
    {S E : Type} (handler : PIR.MonadHandler m (Participant.interface Role language.Ty services meaning.Value) S E)
    (state : S) :
    ((program.toRegion self).denote (participantMeaning meaning condition self) env).runM
        handler state =
      ((program.denote meaning condition self env).bind
        (fun value => .done (Values.singleton value))).runM handler state := by
  rw [denote_toRegion]

namespace Native

/-- Preserve the import carrier's final output-role filter as an ordinary
restriction after execution, so hidden outputs do not skip actions or stops. -/
def Imported.toRegion (imported : Imported) (self : Nat) :
    Region (participantDialect Nat Native.language Native.services self) imported.snapshot.inputs
      [imported.snapshot.result] :=
  .bind (imported.program.toRegion self)
    (.letOp (.restrict imported.snapshot.result (decide (self ∈ imported.snapshot.outputRoles)))
      (Values.singleton .here) .nil (.ret (Values.singleton .here)))

theorem Imported.denote_toRegion (imported : Imported)
    (meaning : Mathematical.Meaning Native.language) (condition : meaning.Value .boolean → Bool)
    (self : Nat)
    (inputs : Values (fun ty => Option (meaning.Value ty)) imported.snapshot.inputs) :
    (imported.toRegion self).denote (participantMeaning meaning condition self) inputs.get =
      (imported.denote meaning condition self inputs).bind
        (fun value => .done (Values.singleton value)) := by
  simp only [toRegion, Region.denote, Program.denote_toRegion, Imported.denote,
    PIR.Process.bind_assoc]
  congr 1

end Native
end Zkc.Source.Common
