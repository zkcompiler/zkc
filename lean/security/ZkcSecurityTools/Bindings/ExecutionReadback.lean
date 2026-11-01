module

public import ZkcSecurity.Bindings.Transcript.SampledCompiled
public import Zkc.Construction.DomainCalculations
public meta import ZkcTools.ConstructionBindings.ProcessViewTactic

@[expose] public meta section

/-! Equation-based normalization of constructed execution and readback.

Clients select actual participant equations and unfold their generated spines
with `unfold_component_bodies` first. These tactics reuse the existing Process
view equations and Domain handler; they neither interpret instructions nor
select a success predicate. Helpers and loops remain opaque component slots.
Additional laws and definitions are explicit, so unsupported operations and
unresolved guards remain ordinary goals. Only the left-hand execution is
normalized; the expected result and success predicate stay caller-owned.
Every rewrite is kernel checked.
-/

set_option autoImplicit false
namespace ZkcSecurity.Tools.Bindings.ExecutionReadback
open Lean

/-- Normalize finite runtime frames, exact operand readback and occurrence
qualification. Local capability checks remain checks on the actual context,
port, request and coordinates; no sampling assumption is introduced. -/
macro "normalize_domain_process " "[" laws:Parser.Tactic.simpLemma,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic => do
  let definitions ← definitions.getElems.mapM fun term =>
    `(Parser.Tactic.simpLemma| $term:term)
  -- Keep the splice nonempty even when the caller supplies no extra rules.
  let lemmas := definitions ++ laws.getElems ++ #[← `(Parser.Tactic.simpLemma| and_true)]
  `(tactic| conv_lhs => simp (config := { failIfUnchanged := false }) [$lemmas,*,
    Zkc.Construction.Domain.View.participant, Zkc.Construction.Domain.View.sequence,
    Zkc.Construction.Domain.View.calculation, Zkc.Construction.Domain.View.guard,
    Zkc.Construction.Domain.View.append, Zkc.Construction.Domain.View.empty,
    Zkc.Construction.Domain.View.receive, Zkc.Construction.Domain.View.send,
    Zkc.Construction.Domain.View.indicesEmpty, Zkc.Construction.Domain.View.indicesAppend,
    Zkc.Construction.Domain.View.observe, Zkc.Construction.Domain.View.challenge,
    Zkc.Construction.Domain.read, Zkc.Construction.Domain.sortsMatch,
    Zkc.Construction.Domain.Value.sort, Zkc.Construction.Domain.Value.encode,
    Zkc.Construction.Domain.Payload.ofValue, Zkc.Construction.Domain.dataType,
    PIR.Process.bind,
    Zkc.Construction.Domain.Calculations.fieldAdd,
    Zkc.Construction.Domain.Calculations.fieldSubtract,
    Zkc.Construction.Domain.Calculations.fieldMultiply,
    Zkc.Construction.Domain.Calculations.fieldEqual,
    Zkc.Construction.Domain.Calculations.fieldConstant,
    Zkc.Construction.Domain.Calculations.indexConstant,
    Zkc.Construction.Domain.Calculations.indexEqual,
    Zkc.Construction.Domain.Calculations.booleanConstant,
    Zkc.Construction.Domain.Calculations.booleanEqual,
    Zkc.Construction.Domain.View.localService,
    Zkc.Construction.Domain.localCoordinates,
    Zkc.Construction.Domain.localOrigin, Zkc.Construction.Domain.templateOrigin,
    Zkc.Construction.Domain.queryOrigin, Zkc.Construction.Domain.atCoordinates,
    Zkc.Construction.Domain.Payload.value,
    Zkc.Construction.Template.origin, Zkc.Construction.Template.qualify,
    Zkc.Construction.Template.applicationPrefix, Zkc.Construction.Template.repeats,
    Zkc.Construction.Context.query, Zkc.Construction.Context.role,
    Zkc.Construction.Origin.query, Zkc.Construction.Origin.message,
    Zkc.Construction.Request.draw, Zkc.Construction.Context.fiatShamir,
    Zkc.Construction.Context.replacement?, Zkc.Construction.Context.request,
    Zkc.Construction.Context.contract, Zkc.Construction.Context.suite,
    Zkc.Source.Structured.Ty.isHandle])

/-- Expose the existing handler's exact execution, including stops, state,
observations, unread proof and fresh authorized private draws. This does not
unfold a public oracle or assert that a continuation succeeds. -/
macro "normalize_domain_execution " "[" laws:Parser.Tactic.simpLemma,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic => do
  let definitions ← definitions.getElems.mapM fun term =>
    `(Parser.Tactic.simpLemma| $term:term)
  let lemmas := definitions ++ laws.getElems ++ #[← `(Parser.Tactic.simpLemma| and_true)]
  `(tactic| (focus
    all_goals conv_lhs => simp (config := { failIfUnchanged := false }) [$lemmas,*,
      Zkc.Construction.Domain.run, PIR.Process.runM,
      Zkc.Construction.Domain.handler, PIR.Execution.followM,
      ZkcSecurity.FiatShamir.SampledCompiled.authorized_samples,
      ZkcSecurity.FiatShamir.SampledCompiled.unauthorized_refuses]
    all_goals conv_lhs => simp (config := { failIfUnchanged := false }) [$lemmas,*,
    Zkc.Construction.Domain.run, PIR.Process.runM,
    Zkc.Construction.Domain.handler, PIR.Execution.followM,
    ZkcSecurity.FiatShamir.SampledCompiled.services,
    ZkcSecurity.FiatShamir.SampledCompiled.privateServices,
    ZkcSecurity.FiatShamir.SampledCompiled.allowed,
    Zkc.Construction.Context.role, Zkc.Construction.Domain.Raw,
    Zkc.Construction.Domain.drawRequest,
    List.contains_cons, List.contains_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.cons_append, List.nil_append,
    beq_self_eq_true, ite_true, ite_false, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, List.append_nil,
    bind_pure_comp, pure_bind, bind_assoc]
    all_goals simp (config := { failIfUnchanged := false }) only [bind_pure_comp]))

end ZkcSecurity.Tools.Bindings.ExecutionReadback
