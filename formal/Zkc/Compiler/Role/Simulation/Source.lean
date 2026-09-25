import Zkc.Compiler.Role.Simulation.Alignment
import Zkc.Compiler.Role.Execution
import Zkc.Source.Protocol.Meaning

/-! Source-derived alignment for actual typed common programs and stored tables.
The joint input environment is an actual value assignment, never a universally
inhabited foreign-value oracle. Focus exposes only the selected role's ports. -/
set_option autoImplicit false
namespace Zkc.Compiler.Role.Simulation
open Zkc.Source Zkc.Source.Protocol
open Zkc.Source.LocatedExecution (Frame Origin)

variable {Party Entry Binding Schema : Type} [DecidableEq Party]
  {language : Language} {locals : List (DefinitionSignature language.Ty)}
  {Value : language.Ty → Type}

abbrev jointInterface := Protocol.interface Party Entry Binding Schema language locals Value
abbrev roleInterface := Protocol.Role.interface Party Entry Binding Schema language locals Value

def location (origin : Origin Party Entry Binding) : Protocol.Role.Location Entry Binding :=
  ⟨origin.entry, origin.instanceId, origin.path, origin.site⟩

def sourceView (self : Party) (op : (jointInterface (Party := Party) (Entry := Entry) (Binding := Binding)
    (Schema := Schema) (locals := locals) (Value := Value)).Op) :
    View jointInterface (Protocol.Role.interface Party Entry Binding Schema language locals Value) op :=
  match op with
  | .local origin callee args =>
      if origin.role = self then .request (.local (location origin) callee args) id else .silent
  | .message origin schema receiver _ value =>
      if origin.role = self then .request (.send (location origin) schema receiver value) (fun _ => ())
      else if receiver = self then .request (.receive _ (location origin) schema origin.role) id
      else .silent
  | .stop origin reason =>
      if origin.role = self then .request (.stop (location origin) reason) id
      else .terminal .incomplete (fun reply => nomatch reply)

def focus {Γ : List (Port Party language.Ty)} (self : Party)
    (env : Source.Environment (PortValue Value) Γ) : Protocol.Role.Environment Value self Γ :=
  fun ref => env ref

def focusValues {Γ : List (Port Party language.Ty)} (self : Party)
    (values : Values (PortValue Value) Γ) : Protocol.Role.Environment Value self Γ :=
  focus self values.get

omit [DecidableEq Party] in
@[simp] theorem focus_push {Γ : List (Port Party language.Ty)} (self : Party)
    (env : Source.Environment (PortValue Value) Γ) {ty : language.Ty} (value : Value ty) :
    @Eq (Protocol.Role.Environment Value self ((self, ty) :: Γ))
      (focus self (env.push value)) (Protocol.Role.Environment.push (focus self env) value) := by
  funext ty ref
  cases ref <;> rfl

omit [DecidableEq Party] in
@[simp] theorem focus_skip {Γ : List (Port Party language.Ty)} (self owner : Party)
    (different : owner ≠ self) (env : Source.Environment (PortValue Value) Γ)
    {ty : language.Ty} (value : Value ty) :
    @Eq (Protocol.Role.Environment Value self ((owner, ty) :: Γ))
      (focus self (env.push value)) (Protocol.Role.Environment.skip different (focus self env)) := by
  funext ty ref
  cases ref with
  | here => exact False.elim (different rfl)
  | there ref => rfl

omit [DecidableEq Party] in
@[simp] theorem focus_capture {Γ Δ : List (Port Party language.Ty)} (self : Party)
    (env : Source.Environment (PortValue Value) Γ) (args : Operands Γ Δ) :
    @Eq (Protocol.Role.Environment Value self Δ)
      (focusValues self (Operands.eval env args)) (Protocol.Role.Environment.capture (focus self env) args) := by
  funext ty ref
  exact Operands.get_eval env args ref

omit [DecidableEq Party] in
@[simp] theorem focus_read {Γ : List (Port Party language.Ty)} (self : Party)
    (env : Source.Environment (PortValue Value) Γ) {types : List language.Ty}
    (args : Operands Γ (owned self types)) :
    localValues self (Operands.eval env args) = Protocol.Role.Environment.read (focus self env) args := by
  induction types with
  | nil => cases args; rfl
  | cons ty types ih =>
      cases args with
      | cons ref rest => exact congrArg (Values.cons (Value := Value) (env ref)) (ih rest)

omit [DecidableEq Party] in
@[simp] theorem focus_prepend {Γ Δ : List (Port Party language.Ty)} (self : Party)
    (env : Source.Environment (PortValue Value) Γ) (values : Values (PortValue Value) Δ) :
    @Eq (Protocol.Role.Environment Value self (Δ ++ Γ))
      (focus self (env.prepend values))
      (Protocol.Role.Environment.prepend (focus self env) (focusValues self values)) := by
  induction values with
  | nil => rfl
  | @cons port Δ value rest ih =>
      funext ty ref
      cases ref with
      | here => rfl
      | there ref =>
          change (env.prepend rest) ref =
            Protocol.Role.Environment.prepend (focus self env)
              (focusValues self (.cons value rest)) (.there ref)
          rw [Protocol.Role.Environment.prepend_there]
          exact congrFun (congrFun ih _) ref

variable {scope : List (Signature Party language.Ty)}

/-- The compositional premise is per actual stored callee and is discharged below. -/
theorem source_aligned (self : Party)
    (calls : Protocol.CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) scope)
    (roleCalls : Protocol.Role.CallMeaning (Entry := Entry) (Binding := Binding)
      (Schema := Schema) (locals := locals) (Value := Value) self scope)
    (callees : ∀ {signature} (ref : Var scope signature) entry binding path args,
      Aligned (sourceView self) (focusValues self) (calls ref entry binding path args)
        (roleCalls ref entry binding path (focusValues self args)))
    {Γ results} (source : Protocol.Program Nat Party Binding Schema language locals scope Γ results)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (env : Source.Environment (PortValue Value) Γ) :
    Aligned (sourceView self) (focusValues self)
      (source.denote calls entry binding path env)
      (Protocol.Role.denote self roleCalls entry binding path source (focus self env)) := by
  induction source generalizing path with
  | ret args =>
      simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned]
      congr 1
      exact (focus_capture self env args).symm
  | stop site owner reason =>
      by_cases same : owner = self
      · simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned, sourceView,
          same, if_true, location]
        exact ⟨_, rfl, fun reply => nomatch reply⟩
      · simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned, sourceView,
          same, if_false]
  | localCall site owner callee args next ih =>
      by_cases same : owner = self
      · subst owner
        simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned, sourceView,
          if_true, dite_true, location]
        rw [focus_read self env args]
        exact ⟨_, rfl, fun value => by simpa only [focus_push, id_eq] using ih path (env.push value)⟩
      · simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned, sourceView,
          same, if_false, dite_false]
        intro value
        simpa only [focus_skip self owner same] using ih path (env.push value)
  | message site schema sender receiver different value next ih =>
      by_cases sending : sender = self
      · subst sender
        simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned, sourceView,
          if_true, dite_true, location, focus]
        refine ⟨_, rfl, fun received => ?_⟩
        simpa only [focus_skip self receiver (Ne.symm different)] using
          ih path (env.push received)
      · by_cases receiving : receiver = self
        · subst receiver
          simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned, sourceView,
            sending, if_false, dite_false, if_true, dite_true, location]
          exact ⟨_, rfl, fun received => by
            simpa only [focus_push, id_eq] using ih path (env.push received)⟩
        · simp only [Protocol.Program.denote, Protocol.Role.denote, Aligned, sourceView,
            sending, receiving, if_false, dite_false]
          intro received
          simpa only [focus_skip self receiver receiving] using ih path (env.push received)
  | invoke site callee args next ih =>
      simp only [Protocol.Program.denote, Protocol.Role.denote]
      have child := callees callee.callee entry callee.binding (path ++ [.invocation site])
        (Operands.eval env args)
      rw [focus_capture] at child
      apply aligned_bind _ _ _ _ _ child
      intro values
      simpa only [focus_prepend] using ih path (env.prepend values)
  | @«repeat» Γ results ports site count initial body next bodyIH nextIH =>
      simp only [Protocol.Program.denote, Protocol.Role.denote]
      let result : Nat × Values (PortValue Value) ports →
          Nat × Protocol.Role.Environment Value self ports := fun acc =>
        (acc.1, focusValues self acc.2)
      have bodyLaw : ∀ acc : Nat × Values (PortValue Value) ports,
          Aligned (sourceView self) result
            ((body.denote calls entry binding (path ++ [.iteration site acc.1])
              (env.prepend acc.2)).bind fun values => .done (acc.1 + 1, values))
            ((Protocol.Role.denote self roleCalls entry binding
              (path ++ [.iteration site acc.1]) body
              (Protocol.Role.Environment.prepend (focus self env) (focusValues self acc.2))).bind
                fun values => .done (acc.1 + 1, values)) := by
        intro acc
        apply aligned_bind _ (focusValues self) _
        · simpa only [focus_prepend] using bodyIH (path ++ [.iteration site acc.1])
            (env.prepend acc.2)
        · intro values; rfl
      let jointStep := fun acc : Nat × Values (PortValue Value) ports =>
        (body.denote calls entry binding (path ++ [.iteration site acc.1])
          (env.prepend acc.2)).bind fun values => .done (acc.1 + 1, values)
      let roleStep : Nat × Protocol.Role.Environment Value self ports →
          PIR.Proc (Protocol.Role.interface Party Entry Binding Schema language locals Value)
            (Nat × Protocol.Role.Environment Value self ports) := fun acc =>
        (Protocol.Role.denote self roleCalls entry binding (path ++ [.iteration site acc.1])
          body (Protocol.Role.Environment.prepend (focus self env) acc.2)).bind
            fun values => .done (acc.1 + 1, values)
      have loop := aligned_repeat (sourceView self) result jointStep roleStep bodyLaw count
        (0, Operands.eval env initial)
      dsimp only [result] at loop
      rw [focus_capture] at loop
      apply aligned_bind _ _ _ _ _ loop
      intro acc
      simpa only [focus_prepend] using nextIH path (env.prepend acc.2)
  | bind body next bodyIH nextIH =>
      simp only [Protocol.Program.denote, Protocol.Role.denote]
      apply aligned_bind _ _ _ _ _ (bodyIH path env)
      intro values
      simpa only [focus_prepend] using nextIH path (env.prepend values)

/-- Every constructor, fixed loop and actual acyclic stored callee; no universal
source/role correctness law is assumed as an interface. -/
theorem definitions_aligned (self : Party)
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (args : Values (PortValue Value) signature.arguments) :
    Aligned (sourceView self) (focusValues self)
      (definitions.denote ref entry binding path args)
      ((projectDefinitions self definitions).denote ref entry binding path (focusValues self args)) := by
  rw [denote_projectDefinitions]
  induction definitions generalizing signature entry binding path with
  | nil => cases ref
  | snoc previous signature body ih =>
      cases ref with
      | here =>
          exact source_aligned self previous.denote (Protocol.Role.denoteDefinitions self previous)
            (fun ref entry binding path args => ih ref entry binding path args)
            body entry binding path args.get
      | there ref => exact ih ref entry binding path args

end Zkc.Compiler.Role.Simulation
