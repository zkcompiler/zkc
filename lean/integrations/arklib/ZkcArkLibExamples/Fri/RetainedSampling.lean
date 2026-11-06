module

public import ZkcArkLibExamples.Fri.RetainedQueries

@[expose] public section

/-! Domination at the installed scalar verifier call. A distribution law is
needed only for the checked primitive request at its qualified site. Other
operations may mutate hidden state, stop, or suppress later requests. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.RetainedSampling
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriScalarLoop Phases OracleComp
variable {model : DomainModel} {S E : Type}

/-- Draw first, then allow arbitrary stateful handling of that value. -/
structure Fresh (handler : PIR.MonadHandler ProbComp (OracleProtocol.Interface model) S E)
    (service : Nat) where
  afterDraw : Fin 32 → S → ProbComp (PIR.Execution S E Unit)
  sample : ∀ state,
    (OracleProtocol.finiteIndex model (site "s13") contract service 32).runM handler state = (do
      let x ← $ᵗ (Fin 32)
      repack (fun _ ↦ x) <$> afterDraw x state)

private theorem prefix_le {I : PIR.Signature} {A B : Type}
    (handler : PIR.MonadHandler ProbComp I S E) (prior : PIR.Process I A)
    (next : A → PIR.Process I B) (state : S) (event : B → Prop) (upper : ENNReal)
    (bound : ∀ x s, Pr{let r ← (next x).runM handler s}[returned event r] ≤ upper) :
    Pr{let r ← (prior.bind next).runM handler state}[returned event r] ≤ upper := by
  rw [PIR.runM_bind]
  apply prEvent_bind_le_of_forall_le
  intro head
  exact prEvent_followM_le head _ event upper bound

theorem fold_le (handler : PIR.MonadHandler ProbComp (OracleProtocol.Interface model) S E)
    (service : Nat) (fresh : Fresh handler service) (items : List Nat) (prior : Positions)
    (state : S) (event : Positions → Prop) :
    Pr{let r ← (Finite.fold (fun xs i ↦ (OracleProtocol.iterationObservations model).within
      loop.site i (step model service xs)) items prior).runM handler state}[returned event r] ≤
      Pr{let ys ← productPositions 5 items.length}[event (prior ++ List.ofFn ys)] := by
  induction items generalizing prior state with
  | nil =>
    simp [Finite.fold, productPositions, PIR.Process.runM, returned]
  | cons i rest ih =>
    simp only [Finite.fold, IterationObservations.within_eq, step, draw, bind, pure,
      PIR.Process.bind_assoc, PIR.Process.bind]
    apply prefix_le
    intro _ afterEntry
    apply prefix_le
    intro _ afterMarks
    rw [PIR.runM_bind, fresh.sample]
    simp only [List.length_cons, productPositions, bind_assoc, bind_map_left]
    simp only [← bind_pure_comp, bind_assoc]
    apply prEvent_bind_mono_of_support
    intro x _
    simp only [bind_pure_comp, ← map_bind]
    apply prEvent_bind_le_of_forall_le
    intro handled
    rw [prEvent_followM]
    cases handled with
    | mk outcome after events =>
      cases outcome with
      | stopped reason => exact bot_le
      | returned ack =>
        cases ack
        dsimp only [repack, PIR.Execution.follow]
        apply prefix_le
        intro _ afterDelivery
        apply prefix_le
        intro _ afterLeave
        simpa only [map_pure, pure_bind, bind_pure_comp, Functor.map_map, Function.comp_def,
          IterationObservations.within_eq, step, draw, bind, pure, PIR.Process.bind_assoc, PIR.Process.bind,
          List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.append_assoc, List.singleton_append]
          using ih (prior ++ [x]) afterLeave

open FriSource FriSourceBodies
attribute [local implicit_reducible] protocol1Signature

/-- The successful result of the actual installed call, before conditioning on
success, is dominated by eight independent uniform positions. The observer
sees the actual returned SSA value, including its role mask. -/
theorem installed_le (handler : PIR.MonadHandler ProbComp (OracleProtocol.Interface model) S E)
    (service : Nat) (fresh : Fresh handler service) (state : S)
    (event : Values (Component (verifierValue model)) protocol1Signature.outputs → Prop) :
    Pr{let r ← (invokeProtocol (verifierTable model) protocol1Signature context 1
      (.cons (OracleProtocol.concrete model .index 8)
        (.cons (OracleProtocol.concrete model (.service contract) service) .nil))).runM handler state}[
      returned event r] ≤ Pr{let ys ← $ᵗ (Fin 8 → Fin 32)}[event (packed model (List.ofFn ys))] := by
  rw [RetainedQueries.installed]
  apply prefix_le
  intro _ afterPrelude
  have mapEq := congrArg (fun p ↦ p.bind (fun xs ↦ PIR.Process.done (packed model xs)))
    (RetainedQueries.positions_eq model service)
  simp only [PIR.Process.bind_assoc, PIR.Process.bind] at mapEq
  rw [← mapEq, prEvent_runM_repack]
  refine (fold_le handler service fresh (List.range' 0 8) [] afterPrelude
    (fun xs ↦ event (packed model xs))).trans_eq ?_
  change Pr{let ys ← productPositions 5 8}[event (packed model (List.ofFn ys))] = _
  exact
    (productPositions_sameDist 5 8).prEvent_eq (fun ys ↦ event (packed model (List.ofFn ys)))

end ZkcSecurity.ArkLib.Fri.RetainedSampling
