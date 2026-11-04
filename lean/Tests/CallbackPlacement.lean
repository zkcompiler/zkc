import Zkc.Source.Structured.CallbackPlacement

/-! A guarded custody callback exercises a different source/control shape from
the arithmetic GKR callbacks. Site and custody processes have arbitrary replies
and stops; transport must preserve them before projecting the loop state. -/
set_option autoImplicit false
namespace Tests.CallbackPlacement
open Zkc.Source Zkc.Source.Structured
attribute [local implicit_reducible] Op.arguments Op.results Op.regions

private def guardedBody :
    Region dialect [.index, .resourceUnit "slot", .boolean] [.resourceUnit "slot", .boolean] :=
  .letOp (.mark "entered") .nil .nil <|
  .letOp .guard (.cons (.there (.there .here)) .nil) .nil <|
  .letOp (.passUnit "slot") (.cons (.there .here) .nil) .nil <|
  .ret (.cons .here (.cons (.there (.there (.there .here))) .nil))

private def source (model : DomainModel) {I : PIR.Signature} (sites : SiteObservations I) :
    RegionFunction model.Value I
      ([.index, .resourceUnit "slot", .boolean], [.resourceUnit "slot", .boolean]) :=
  fun arguments ↦ guardedBody.denote (Evaluation.meaningOn model sites []) arguments.get

private def placed (model : DomainModel) {I : PIR.Signature} (sites : SiteObservations I) :
    RegionFunction model.Value I
      ([.index, .resourceUnit "slot", .boolean], [.resourceUnit "slot", .boolean]) :=
  fun arguments ↦ (sites.mark "entered").bind fun _ =>
    if arguments.get (.there (.there .here)) then
      (sites.passUnit "slot" (arguments.get (.there .here))).bind fun token =>
        .done (.cons token (.cons (arguments.get (.there (.there .here))) .nil))
    else .halt .reject

/-- This equation includes the guard and custody transfer for every observation
process. No successful transfer or selected external reply is assumed. -/
theorem guarded_equation (model : DomainModel) {I : PIR.Signature}
    (sites : SiteObservations I) (arguments) :
    source model sites arguments = placed model sites arguments := by
  cases arguments with
  | cons index arguments => cases arguments with
    | cons token arguments => cases arguments with
      | cons enabled arguments =>
        cases arguments
        cases enabled <;> simp only [source, placed, guardedBody, Region.denote, Regions.denote,
          Evaluation.meaningOn, Evaluation.operationOn,
          Operands.eval, Values.get, Environment.prepend, Environment.push,
          PIR.Process.bind_assoc, PIR.Process.bind, Bool.false_eq_true, ite_false, ite_true]

/-- Exact callback transport retains arbitrary effects, including custody, at
every iteration. It does not require returned captures to be unchanged. -/
theorem guarded_loop (model : DomainModel) {I : PIR.Signature} (sites : SiteObservations I)
    (lower upper token : Nat) (enabled : Bool) :
    Evaluation.denoteLoopOn [.resourceUnit "slot"] [.boolean] (placed model sites)
        lower upper (.cons token .nil) (.cons enabled .nil) =
      Evaluation.denoteLoopOn [.resourceUnit "slot"] [.boolean] (source model sites)
        lower upper (.cons token .nil) (.cons enabled .nil) :=
  Evaluation.denoteLoopOn_callback_eq _ _ (guarded_equation model sites) _ _ _ _

private abbrev replies : PIR.Signature := ⟨String, fun _ ↦ Nat⟩
private def sites : SiteObservations replies where
  mark name := .call name fun _ => .done ()
  passUnit name _ := .call name fun reply =>
    if reply = 0 then .halt .refused else .done reply

/-- A reached rejection keeps its observed prefix and terminal handler state. -/
theorem guarded_rejection (model : DomainModel) (reply : Nat) :
    (Evaluation.denoteLoopOn [.resourceUnit "slot"] [.boolean] (placed model sites)
      0 1 (.cons 7 .nil) (.cons false .nil)).run
        (fun name (state : Nat) ↦ ⟨.returned reply, state + 1, [name]⟩) 3 =
      ⟨.stopped .reject, 4, ["entered"]⟩ := rfl

theorem custody_refusal (model : DomainModel) :
    (Evaluation.denoteLoopOn [.resourceUnit "slot"] [.boolean] (placed model sites)
      0 1 (.cons 7 .nil) (.cons true .nil)).run
        (fun name (state : Nat) ↦ ⟨.returned (0 : Nat), state + 1, [name]⟩) 3 =
      ⟨.stopped .refused, 5, ["entered", "slot"]⟩ := rfl

theorem custody_success (model : DomainModel) :
    (Evaluation.denoteLoopOn [.resourceUnit "slot"] [.boolean] (placed model sites)
      0 1 (.cons 7 .nil) (.cons true .nil)).run
        (fun name (state : Nat) ↦ ⟨.returned (8 : Nat), state + 1, [name]⟩) 3 =
      ⟨.returned (.cons 8 .nil), 5, ["entered", "slot"]⟩ := rfl

/-- A stopping handler also retains its state and events before the guard. -/
theorem handler_stop (model : DomainModel) (reason : PIR.Stop) :
    (Evaluation.denoteLoopOn [.resourceUnit "slot"] [.boolean] (placed model sites)
      0 1 (.cons 7 .nil) (.cons true .nil)).run
        (fun name (state : Nat) ↦ ⟨.stopped reason, state + 1, [name]⟩) 3 =
      ⟨.stopped reason, 4, ["entered"]⟩ := rfl

/-- A zero-trip loop does not execute the guarded callback or its observations. -/
example (model : DomainModel) :
    Evaluation.denoteLoopOn [.resourceUnit "slot"] [.boolean] (placed model sites)
      0 0 (.cons 7 .nil) (.cons false .nil) = .done (.cons 7 .nil) := rfl

/-- Identical projected state does not prove equality of complete captures. -/
theorem changed_capture_refused (model : DomainModel) :
    (PIR.Process.done (.cons 7 (.cons true .nil)) :
      PIR.Process replies (Values model.Value [.resourceUnit "slot", .boolean])) ≠
        .done (.cons 7 (.cons false .nil)) := by
  intro same
  cases same

run_elab do
  for declaration in [``guarded_equation, ``guarded_loop, ``guarded_rejection,
      ``custody_refusal, ``custody_success, ``handler_stop, ``changed_capture_refused,
      ``Evaluation.denoteLoopOn_callback_eq, ``Evaluation.denoteLoopOn_states_of_equation] do
    for dependency in ← Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "nonstandard axiom in callback transport: {declaration}: {dependency}"
end Tests.CallbackPlacement
