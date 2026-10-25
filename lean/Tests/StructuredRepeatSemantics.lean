import Zkc.Source.Structured.RepeatLaws
import Zkc.Source.Structured.ClosedProjection
import Mathlib.Algebra.Ring.Int.Defs

/-! Independent controls of the optional retained repeat meaning. These include
malformed operation-level scopes, huge logical counts, mixed optional state,
immutable captures, observed headers, shared callback tables and stopped effects.
They do not assert source admission, native refinement or cryptographic security. -/

set_option autoImplicit false
namespace Tests.StructuredRepeatSemantics
open Zkc.Source Zkc.Source.Structured

private abbrev signals : PIR.Signature := ⟨Nat, fun _ => Unit⟩
private def emptySpec : RepeatSpec := ⟨[], [.index], [0], [], 4⟩
private def mixedSpec : RepeatSpec := ⟨[.index, .index], [.index], [0, 1], [[0], [1]], 4⟩
private def alwaysStop {inputs outputs : List Ty} :
    RegionFunction (Component (assignment Int Int)) signals (inputs, outputs) := fun _ => .halt .reject

/-- Outside short-circuits count, captures, callback and even malformed scopes. -/
theorem outside_huge_malformed :
    denoteRepeat { mixedSpec with stateScopes := [[8], []] } {} 2 (some (2^128))
      (.cons (some 11) (.cons (some 22) .nil)) (.cons none .nil) alwaysStop =
        .done (.cons none (.cons none .nil)) := rfl

theorem outside_missing_count :
    denoteRepeat mixedSpec {} 2 none (.cons none (.cons none .nil))
      (.cons none .nil) alwaysStop = .done (.cons none (.cons none .nil)) := rfl

theorem active_missing_count :
    denoteRepeat mixedSpec {} 0 none (.cons none (.cons none .nil))
      (.cons none .nil) alwaysStop = .halt .incomplete := rfl

/-- No u64 overflow branch or huge allocation occurs in the logical helper. -/
theorem huge_count_refused :
    denoteRepeat emptySpec {} 0 (some (2^128)) .nil (.cons none .nil) alwaysStop =
      .halt .refused := rfl

theorem count_above_maximum :
    denoteRepeat emptySpec {} 0 (some 5) .nil (.cons none .nil) alwaysStop = .halt .refused := rfl

theorem zero_masks_initial :
    denoteRepeat mixedSpec {} 0 (some 0) (.cons (some 11) (.cons (some 22) .nil))
      (.cons none .nil) alwaysStop = .done (.cons (some 11) (.cons none .nil)) := rfl

theorem zero_missing_state :
    denoteRepeat mixedSpec {} 1 (some 0) (.cons none (.cons none .nil))
      (.cons none .nil) alwaysStop = .done (.cons none (.cons none .nil)) := rfl

private def unusedCapture : RegionFunction (Component (assignment Int Int)) signals
    (.index :: emptySpec.state ++ emptySpec.captures, emptySpec.state) := fun _ => .done .nil
private def strictCapture : RegionFunction (Component (assignment Int Int)) signals
    (.index :: emptySpec.state ++ emptySpec.captures, emptySpec.state) := fun args =>
  match args.get (.there .here) with
  | none => .halt .incomplete
  | some _ => .done .nil

theorem positive_unused_missing_capture :
    denoteRepeat emptySpec {} 0 (some 2) .nil (.cons none .nil) unusedCapture = .done .nil := rfl

theorem reached_missing_capture :
    denoteRepeat emptySpec {} 0 (some 1) .nil (.cons none .nil) strictCapture = .halt .incomplete := rfl

theorem zero_strict_capture_not_reached :
    denoteRepeat emptySpec {} 0 (some 0) .nil (.cons none .nil) strictCapture = .done .nil := rfl

private def replaceState : RegionFunction (Component (assignment Int Int)) signals
    (.index :: mixedSpec.state ++ mixedSpec.captures, mixedSpec.state) := fun args =>
  match args.get (.there (.there .here)) with
  | none => .done (.cons (args.get (.there (.there (.there .here)))) (.cons (some 99) .nil))
  | some _ => .halt .reject

/-- Every input/yield mask prevents the illicit V component reaching P's next
callback. An ordinary optional capture can replace the owned state component. -/
theorem every_yield_masked :
    denoteRepeat mixedSpec {} 0 (some 2) (.cons (some 11) (.cons (some 22) .nil))
      (.cons (some 7) .nil) replaceState = .done (.cons (some 7) (.cons none .nil)) := rfl

private def indexSpec : RepeatSpec := ⟨[.index], [.index], [0], [[0]], 8⟩
private def indexAndCapture : RegionFunction (Component (assignment Int Int)) signals
    (.index :: indexSpec.state ++ indexSpec.captures, indexSpec.state) := fun args =>
  match args.get .here, args.get (.there .here), args.get (.there (.there .here)) with
  | some index, some state, some original => .done (.cons (some (state + index + original)) .nil)
  | _, _, _ => .halt .incomplete

theorem induction_and_original_count_distinct :
    denoteRepeat indexSpec {} 0 (some 2) (.cons (some 0) .nil) (.cons (some 2) .nil)
      indexAndCapture = .done (.cons (some 5) .nil) := rfl

theorem shifted_indices :
    Repeat.loop indexSpec {} 0 (.cons (some 2) .nil) indexAndCapture 4 2
      (.cons (some 0) .nil) = .done (.cons (some 13) .nil) := rfl

private def stopSecond : RegionFunction (Component (assignment Int Int)) signals
    (.index :: emptySpec.state ++ emptySpec.captures, emptySpec.state) := fun args =>
  match args.get .here with
  | none => .halt .incomplete
  | some index => .call index fun _ => if index = 1 then .halt .reject else .done .nil
private def signalHandler : PIR.Handler signals Nat Nat := fun signal state =>
  ⟨.returned (), state + 1, [signal]⟩

/-- The second iteration's effect and state survive; later iterations and the
outer suffix are absent. Empty carried state does not turn halt into success. -/
theorem stopped_effects_and_state :
    ((denoteRepeat emptySpec {} 0 (some 4) .nil (.cons none .nil) stopSecond).bind
      (fun _ => .call 99 (fun _ => .done ()))).run signalHandler 10 =
        ⟨.stopped .reject, 12, [0, 1]⟩ := rfl

theorem zero_retains_earlier_effect :
    ((PIR.Process.call (I := signals) 42 (fun _ => denoteRepeat emptySpec {} 0 (some 0)
      .nil (.cons none .nil) alwaysStop))).run signalHandler 10 =
        ⟨.returned .nil, 11, [42]⟩ := rfl

private def headerSpec : RepeatSpec := ⟨[.index], [], [0], [[0]], 2⟩
private def markedLoop : Region protocolDialect [.index, .index] [.index] :=
  .letOp (.mark "header") .nil .nil
    (.letOp (.repeat headerSpec "header") (.cons .here (.cons (.there .here) .nil))
      (.cons (.stop .reject) .nil) (.ret (.cons .here .nil)))

/-- The header is an ordinary preceding source mark, retained outside the roster. -/
theorem outside_retains_header :
    markedLoop.denote (participantMeaning (F := Int) (G := Int) ⟨[], []⟩ 1)
      (Values.get (.cons none (.cons none .nil))) =
        .call (.mark "header") (fun _ => .done (.cons none .nil)) := rfl

theorem zero_retains_header :
    markedLoop.denote (participantMeaning (F := Int) (G := Int) ⟨[], []⟩ 0)
      (Values.get (.cons (some 0) (.cons (some 8) .nil))) =
        .call (.mark "header") (fun _ => .done (.cons (some 8) .nil)) := rfl

theorem zero_forgets_only_header :
    (markedLoop.denote (participantMeaning (F := Int) (G := Int) ⟨[], []⟩ 0)
      (Values.get (.cons (some 0) (.cons (some 8) .nil)))).interpret forgetSites =
        .done (.cons (some 8) .nil) := rfl

private def retainedOuter : Region protocolDialect [.index, .index, .index] [.index, .index, .index] :=
  .letOp (.repeat headerSpec "loop") (.cons .here (.cons (.there .here) .nil))
    (.cons (.ret (.cons .here .nil)) .nil)
    (.ret (.cons .here (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil))))

/-- The isolated induction argument can replace state without rebinding the
caller's original count or an outer value used by the ordinary source suffix. -/
theorem suffix_retains_outer_values :
    retainedOuter.denote (participantMeaning (F := Int) (G := Int) ⟨[], []⟩ 0)
      (Values.get (.cons (some 2) (.cons (some 11) (.cons (some 7) .nil)))) =
        .done (.cons (some 1) (.cons (some 2) (.cons (some 7) .nil))) := rfl

private def leafSignature : ProtocolSignature :=
  ⟨"Leaf", ["sender", "receiver"], [.index], [.index], [[0, 1]], [[0, 1]]⟩
private def leafBody : Region protocolDialect [.index] [.index] :=
  .letOp (.exchange .index 0 1 "send") (.cons .here .nil) .nil (.ret (.cons .here .nil))
private def leaf : CheckedProtocol where
  toProtocolSignature := leafSignature
  raw := leafBody.erase
  body := leafBody
  formed := leafBody.elaborate_erase
private def capturedTable : ProtocolTable (assignment Int Int) (observedInterface Int Int) :=
  extendProtocolTable (observedSites Int Int) observeAction ⟨[], []⟩ [] leaf
private def mappedSpec : RepeatSpec := ⟨[.index], [], [0, 2], [[0, 2]], 2⟩
private def callbackApply : Region protocolDialect [.index, .index] [.index] :=
  .letOp (.protocolApply leafSignature [2, 0] "apply") (.cons (.there .here) .nil) .nil
    (.ret (.cons .here .nil))
private def mappedLoop : Region protocolDialect [.index, .index] [.index] :=
  .letOp (.repeat mappedSpec "loop") (.cons .here (.cons (.there .here) .nil))
    (.cons callbackApply .nil) (.ret (.cons .here .nil))
private def mappedContext : ProtocolContext := ({} : ProtocolContext).enter "outer" [2, 0, 3]

/-- Callback applications use the captured table and fixed root self. Repeat
adds no site prefix; the nested non-involutive injection maps receiver to2. -/
theorem callback_table_and_root_context :
    (mappedLoop.denote
      (participantMeaning (F := Int) (G := Int) ⟨[], []⟩ 2 capturedTable mappedContext)
      (Values.get (.cons (some 1) (.cons none .nil)))).interpret forgetSites =
        .call (.receive .index "apply_19_apply_5_outer_apply_send" 3)
          (fun reply => .done (.cons (some reply) .nil)) := rfl

/-- Scope selection uses mapped coordinates, even for an outside count of zero. -/
theorem mapped_outside :
    mappedLoop.denote (participantMeaning (F := Int) (G := Int) ⟨[], []⟩ 0 capturedTable mappedContext)
      (Values.get (.cons (some 0) (.cons (some 8) .nil))) =
        .done (.cons none .nil) := rfl

private abbrev service : Ty := .service "random.bls12-381.fr/0"
private def serviceSpec : RepeatSpec := ⟨[], [service, service], [0], [], 2⟩
private def serviceBody : Region protocolDialect [.index, service, service] [] :=
  .letOp (.draw 0 "bls12-381.fr" "first") (.cons (.there .here) .nil) .nil
    (.letOp (.draw 0 "bls12-381.fr" "second")
      (.cons (.there (.there (.there .here))) .nil) .nil (.ret .nil))
private def queryProcess (site : String) (handle : Nat) : PIR.Process (participantInterface Int Int) Int :=
  .call (.query site "bls12-381.fr" (.cons handle .nil)) .done
private def aliasProcess (first second : Nat) : PIR.Process (participantInterface Int Int) Unit :=
  (queryProcess "prelude" first).bind fun _ =>
    ((denoteRepeat serviceSpec {} 0 (some 2) .nil (.cons (some first) (.cons (some second) .nil))
      (fun args => serviceBody.denote
        (participantMeaningWith (.silent (participantInterface Int Int)) (participantActions Int Int)
          ⟨[], []⟩ 0) args.get))).bind fun _ =>
        (queryProcess "suffix" first).bind fun _ => .done ()

/-- Actual service handles are immutable captures across both iterations. A
same-owner alias is one handle in six ordered queries, including prelude/suffix. -/
theorem aliased_service_order (handle : Nat) :
    aliasProcess handle handle =
      .call (.query "prelude" "bls12-381.fr" (.cons handle .nil)) (fun _ =>
      .call (.query "first" "bls12-381.fr" (.cons handle .nil)) (fun _ =>
      .call (.query "second" "bls12-381.fr" (.cons handle .nil)) (fun _ =>
      .call (.query "first" "bls12-381.fr" (.cons handle .nil)) (fun _ =>
      .call (.query "second" "bls12-381.fr" (.cons handle .nil)) (fun _ =>
      .call (.query "suffix" "bls12-381.fr" (.cons handle .nil)) (fun _ => .done ())))))) := rfl

theorem distinct_service_order (first second : Nat) :
    aliasProcess first second =
      .call (.query "prelude" "bls12-381.fr" (.cons first .nil)) (fun _ =>
      .call (.query "first" "bls12-381.fr" (.cons first .nil)) (fun _ =>
      .call (.query "second" "bls12-381.fr" (.cons second .nil)) (fun _ =>
      .call (.query "first" "bls12-381.fr" (.cons first .nil)) (fun _ =>
      .call (.query "second" "bls12-381.fr" (.cons second .nil)) (fun _ =>
      .call (.query "suffix" "bls12-381.fr" (.cons first .nil)) (fun _ => .done ())))))) := rfl

/-- The closed profile refuses the callback before consulting operation shape. -/
theorem closed_repeat_refused :
    closedRootTree markedLoop.erase = .error "structured-protocol-region" := rfl

private abbrev replySignals : PIR.Signature := ⟨Nat, fun _ => Nat⟩
private def transportSpec (maximum : Nat) : RepeatSpec :=
  ⟨[.index, .index], [], [0, 1], [[0], [1]], maximum⟩
private def embeddedState (value : Nat) :
    Values (Component (assignment Int Int)) [.index, .index] :=
  .cons (some value) (.cons none .nil)
private def replyStep (value : Nat) : PIR.Process replySignals Nat :=
  .call value fun reply => if reply = 0 then .halt .reject else .done (value + reply)
private def replyBody : RegionFunction (Component (assignment Int Int)) replySignals
    ([.index, .index, .index], [.index, .index]) := fun args =>
  match args.get (.there .here) with
  | none => .halt .incomplete
  | some value => .call value fun reply =>
    if reply = 0 then .halt .reject
    else .done (.cons (some (value + reply)) (.cons (some 999) .nil))

/-- Symbolic shifted counts preserve arbitrary replies and rejection, while the
returned embedding discards the callback's unauthorized second state component. -/
theorem embedded_shifted_effects (maximum start count initial : Nat) :
    Repeat.loop (transportSpec maximum) {} 0 .nil replyBody start count
      (embeddedState initial) =
        (PIR.repeatN count replyStep initial).bind
          (fun result => .done (embeddedState result)) := by
  have same : ∀ value index,
      Repeat.step (transportSpec maximum) {} 0 .nil replyBody (embeddedState value) index =
        (replyStep value).bind (fun result => .done (embeddedState result)) := by
    intro value index
    change (PIR.Process.call (I := replySignals)
      (A := Values (Component (assignment Int Int)) [.index, .index]) value (fun reply =>
        if reply = 0 then .halt .reject else
          .done (.cons (some (value + reply)) (.cons (some 999) .nil)))).bind _ = _
    simp only [PIR.Process.bind, replyStep]
    congr 1
    funext reply
    split <;> rfl
  rw [Repeat.loop_embed (transportSpec maximum) {} 0 .nil replyBody
    embeddedState (fun value _ => replyStep value) start count initial same,
    Finite.fold_range_repeatN]
  rfl

/-- Admission and both generic transport laws give the full process for any
maximum and admitted count, without enumerating either natural parameter. -/
theorem embedded_admitted_effects (maximum count initial : Nat) (bound : count ≤ maximum) :
    denoteRepeat (transportSpec maximum) {} 0 (some count) (embeddedState initial)
      .nil replyBody =
        (PIR.repeatN count replyStep initial).bind
          (fun result => .done (embeddedState result)) := by
  rw [repeat_admitted (transportSpec maximum) {} 0 (embeddedState initial)
    .nil replyBody count rfl bound]
  exact embedded_shifted_effects maximum 0 count initial

private def countingInteraction : PIR.Interaction signals where
  Role := Unit
  Phase := Nat
  owner := fun _ => ()
  enabled := fun _ _ => True
  advance := fun phase _ _ => phase + 1

private def phaseBody : RegionFunction (Component (assignment Int Int)) signals
    ([.index, .index], [.index]) := fun args =>
  match args.get .here with
  | none => .halt .incomplete
  | some index => .call index fun _ => .done (.cons (some (index + 1)) .nil)
private def stateBody : RegionFunction (Component (assignment Int Int)) signals
    ([.index, .index], [.index]) := fun args =>
  match args.get (.there .here) with
  | none => .halt .incomplete
  | some state => .call state fun _ => .done (.cons (some (state + 1)) .nil)

/-- The callback indexed by iteration equals the callback indexed by state only
on reached states; the phase invariant follows the actual interaction returns. -/
theorem phase_sensitive_congruence (start count : Nat) :
    Repeat.loop headerSpec {} 0 .nil phaseBody start count (.cons (some start) .nil) =
      Repeat.loop headerSpec {} 0 .nil stateBody start count (.cons (some start) .nil) := by
  apply Repeat.loop_congr_on headerSpec {} 0 .nil phaseBody stateBody
    countingInteraction start
    (fun index state phase => state = .cons (some index) .nil ∧ phase = index)
    start count (.cons (some start) .nil) ⟨rfl, rfl⟩
  · intro index _ _ state phase valid
    rcases valid with ⟨rfl, rfl⟩
    rfl
  · intro index _ _ state phase valid
    rcases valid with ⟨rfl, rfl⟩
    intro reply
    exact ⟨rfl, rfl⟩

/-- Preservation of this invariant would be false at an unrelated phase, even
though the very same callback preserves it at the valid reached phase. -/
theorem phase_preservation_requires_valid_phase (index : Nat) :
    ¬ PIR.Boundary.Returns countingInteraction
      (fun result phase => result = .cons (some (index + 1)) .nil ∧ phase = index + 1)
      (phaseBody (.cons (some index) (.cons (some index) .nil))) (index + 1) := by
  intro preserved
  have wrong : index + 1 + 1 = index + 1 := (preserved ()).2
  omega

private def immediateStop {A : Type} : PIR.Process signals A → Option PIR.Stop
  | .halt reason => some reason
  | _ => none

/-- Runtime controls complement kernel equations, especially the guard that
must reject huge Nats before allocating their range. -/
def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let checked ← IO.mkRef 0
  let test := fun (name : String) (passed : Bool) => do
    checked.modify (· + 1)
    if !passed then failures.modify (name :: ·)
  test "huge-count-before-range" (decide (immediateStop
    (denoteRepeat emptySpec {} 0 (some (2^128)) .nil (.cons none .nil) alwaysStop) = some .refused))
  test "maximum-plus-one" (decide (immediateStop
    (denoteRepeat emptySpec {} 0 (some 5) .nil (.cons none .nil) alwaysStop) = some .refused))
  test "missing-active-count" (decide (immediateStop
    (denoteRepeat emptySpec {} 0 none .nil (.cons none .nil) alwaysStop) = some .incomplete))
  test "outside-huge-count" (match denoteRepeat emptySpec {} 1 (some (2^128)) .nil
    (.cons none .nil) alwaysStop with | .done _ => true | _ => false)
  test "zero-does-not-demand-capture" (match denoteRepeat emptySpec {} 0 (some 0) .nil
    (.cons none .nil) strictCapture with | .done _ => true | _ => false)
  test "positive-unused-capture" (match denoteRepeat emptySpec {} 0 (some 2) .nil
    (.cons none .nil) unusedCapture with | .done _ => true | _ => false)
  test "positive-demanded-capture" (decide (immediateStop
    (denoteRepeat emptySpec {} 0 (some 1) .nil (.cons none .nil) strictCapture) = some .incomplete))
  let stopped := ((denoteRepeat emptySpec {} 0 (some 4) .nil (.cons none .nil) stopSecond).bind
    (fun _ => .call 99 (fun _ => .done ()))).run signalHandler 10
  test "first-stop-outcome" (decide (stopped.outcome = .stopped .reject))
  test "first-stop-residual-state" (stopped.state == 12)
  test "first-stop-ordered-events" (stopped.events == [0, 1])
  let errors ← failures.get
  if errors.isEmpty then IO.println s!"structured repeat semantics: {← checked.get} checks passed"
  else throw (IO.userError ("structured repeat semantics failed: " ++ String.intercalate ", " errors.reverse))

#eval run

end Tests.StructuredRepeatSemantics
