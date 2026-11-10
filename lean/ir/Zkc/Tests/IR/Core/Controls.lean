import Zkc.Tools.IR.Core.Import
import Zkc.IR.Core.Laws

/-! Semantic controls for sides with several roles, for applications and for stops.

- Participants of a `branch` or `repeat` in the side that hold different copies stop
  the side with `incomplete`, before a count is compared with the maximum; equal
  copies select the region or run the loop.
- A `draw` whose owner is outside the side announces the coin to each receiver in
  the side by a separate `receive`, with independent replies.
- An application follows the callee's actual definition: swapping two same-typed
  arguments swaps the result, and a different callee body gives a different caller
  meaning.
- An application with a role map that is not the identity runs the callee for the
  preimage side: the caller's role performs what the callee's formal role does.
- A stop by one role of a side ends the side's process.
- A partial row stops with an authored reason in every model: no model makes a side
  stop `incomplete`. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

namespace Zkc.Tests.Core.Controls

-- The definitions below name imported rows and programs, which are not compiled.
noncomputable section

/-! ## Agreement at `branch` and `repeat` -/

import_core agreement from r#"["zkc.core/0",
 [["original", [], [],
   [["law.uniform_below", [["nat", 256]], "sampling", [], ["index"]]],
   [["protocol", 0, 2,
     [["bool", 0], ["bool", 1], ["index", 0], ["index", 1]],
     [["index", 1]],
     [[0, [0, 1]], [0, [2, 3]]],
     [[["branch", [[0, 0], [1, 1]], [2, 3],
        [[["exchange", 0, 1, 0, 0]], [2]],
        [[], [1]]],
       ["repeat", [[0, 2], [1, 3]], 8, [4], [],
        [[["draw", 1, [0], 1, 0, []]], [1]]]],
      [5]]]]]],
 [], [], [],
 [["agreement"], [["prover", "verifier"]], [["forward", "challenge"]]]]"#

abbrev both : Side := Side.ofMask 0b11
abbrev verifier : Side := Side.ofMask 0b10
abbrev uniform : SamplingRow := .of agreement.row.«law.uniform_below(nat 256)»

variable (M : Model)

/-- Equal conditions and equal counts: the selected region, then the loop. -/
theorem agreeing :
    agreement.agreement.meaning M both (.cons true (.cons true (.cons (2 : Nat) (.cons (2 : Nat) .nil)))) =
      .call (.draw ⟨0, 1⟩ uniform .nil) fun _ =>
      .call (.draw ⟨0, 1⟩ uniform .nil) fun second =>
      .done (.cons second .nil) :=
  rfl

/-- Equal conditions selecting the other region. -/
theorem agreeing_otherwise :
    agreement.agreement.meaning M both (.cons false (.cons false (.cons (1 : Nat) (.cons (1 : Nat) .nil)))) =
      .call (.draw ⟨0, 1⟩ uniform .nil) fun first => .done (.cons first .nil) :=
  rfl

/-- Different conditions: the side stops `incomplete` before any effect. -/
theorem conditions_disagree (first second : Nat) :
    agreement.agreement.meaning M both
        (.cons true (.cons false (.cons first (.cons second .nil)))) = .halt .incomplete :=
  rfl

/-- Equal conditions, different counts: the side stops `incomplete` at the loop. -/
theorem counts_disagree :
    agreement.agreement.meaning M both (.cons true (.cons true (.cons (2 : Nat) (.cons (3 : Nat) .nil)))) =
      .halt .incomplete :=
  rfl

/-- Different counts of which one exceeds the maximum: `incomplete`, not `refused`.
The copies are compared before the count is compared with the maximum. -/
theorem counts_disagree_beyond_maximum :
    agreement.agreement.meaning M both (.cons true (.cons true (.cons (2 : Nat) (.cons (9 : Nat) .nil)))) =
      .halt .incomplete :=
  rfl

/-- Equal counts above the maximum: `refused`. -/
theorem counts_beyond_maximum :
    agreement.agreement.meaning M both (.cons true (.cons true (.cons (9 : Nat) (.cons (9 : Nat) .nil)))) =
      .halt .refused :=
  rfl

/-- One participant in the side: its own copies decide, with nothing to compare. The
loop is the bounded iteration of one draw. -/
theorem single_participant (count : Nat) :
    agreement.agreement.meaning M verifier (.cons () (.cons true (.cons () (.cons count .nil)))) =
      .call (.receive ⟨0, 0⟩ .index) fun forwarded =>
      (repeatProcess M 8
          (fun (_ : Values (SideValue M verifier) [⟨.index, 1⟩]) =>
            PIR.Process.call (.draw ⟨0, 1⟩ uniform .nil) fun challenge =>
              PIR.Process.done (Values.cons (Value := SideValue M verifier) (ty := ⟨.index, 1⟩)
                challenge .nil))
          count (.cons forwarded .nil)).bind fun final => .done (.cons (final.get .here) .nil) :=
  rfl

/-- The same by the general statement about distinct participants: the copy of the
one participant in the side decides, whatever the other copies are. -/
example (count : Nat) (others : Held Nat (verifier 0)) (onValue : Nat → Bool) :
    agreed Nat.beq verifier onValue false [0, 1] (.cons others (.cons count .nil)) (fun _ => false) =
      onValue count :=
  agreed_single Nat.beq verifier onValue false [0, 1] rfl _ _ (.there .here) rfl
    (by intro other member present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact Bool.noConfusion present
        · rfl)

/-- The agreement of the `branch` by its statement, for symbolic counts: the two
participants in the side hold the conditions `true` and `false`. -/
theorem conditions_disagree_stepwise (first second : Nat) :
    agreement.agreement.meaning M both
        (.cons true (.cons false (.cons first (.cons second .nil)))) = .halt .incomplete := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  exact (sideMeaning_step
    (branch_disagree .here (.there .here) rfl rfl (fun same => Bool.noConfusion same))).trans rfl

/-- Equal symbolic counts, by the statement for equal copies: the `repeat` is the
bounded iteration, whatever the count is. -/
theorem counts_agree_stepwise (count : Nat) :
    agreement.agreement.meaning M both
        (.cons false (.cons false (.cons count (.cons count .nil)))) =
      (repeatProcess M 8
          (fun (_ : Values (SideValue M both) [⟨.index, 1⟩]) =>
            PIR.Process.call (.draw ⟨0, 1⟩ uniform .nil) fun challenge =>
              PIR.Process.done (Values.cons (Value := SideValue M both) (ty := ⟨.index, 1⟩)
                challenge .nil))
          count (.cons count .nil)).bind fun final => .done (.cons (final.get .here) .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  -- the `branch`: both conditions are `false`, the second region returns role 1's count
  refine (sideMeaning_step (branch_agreed false ?_ rfl)).trans ?_
  · intro role position member
    cases position with
    | here => rfl
    | there position => cases position with
      | here => rfl
      | there position => nomatch position
  refine (bind_cond _ _ _ _).trans ?_
  refine (congrArg (fun process => PIR.Process.bind process _) sideMeaning_ret).trans ?_
  -- the `repeat`: both counts are `count`
  refine (sideMeaning_step (repeat_agreed count ?_ rfl)).trans ?_
  · intro role position member
    cases position with
    | here => rfl
    | there position => cases position with
      | here => rfl
      | there position => nomatch position
  refine congr (congrArg PIR.Process.bind (congrArg (fun step => repeatProcess M 8 step count _)
    (funext fun state => ?_))) (funext fun final => sideMeaning_ret)
  -- one iteration: the verifier draws, the prover's copy is the coin
  match state with
  | .cons _ .nil =>
    refine (sideMeaning_step_call (draw_owner rfl)).trans ?_
    exact congrArg (PIR.Process.call _) (funext fun _ => sideMeaning_ret)

/-- Different symbolic counts, by the statement for unequal copies: `incomplete`. -/
theorem counts_disagree_stepwise (first second : Nat) (differ : first ≠ second) :
    agreement.agreement.meaning M both
        (.cons false (.cons false (.cons first (.cons second .nil)))) = .halt .incomplete := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step (branch_agreed false ?_ rfl)).trans ?_
  · intro role position member
    cases position with
    | here => rfl
    | there position => cases position with
      | here => rfl
      | there position => nomatch position
  refine (bind_cond _ _ _ _).trans ?_
  refine (congrArg (fun process => PIR.Process.bind process _) sideMeaning_ret).trans ?_
  refine (sideMeaning_step (repeat_disagree .here (.there .here) rfl rfl ?_)).trans rfl
  exact differ

/-- No participant in the side: the `branch` and the `repeat` do nothing, and the
side holds no output. -/
theorem no_participant :
    agreement.agreement.meaning M (Side.ofMask 0b100) (.cons () (.cons () (.cons () (.cons () .nil)))) =
      .done (.cons () .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step branch_meaning).trans ?_
  refine (congrArg (fun process => PIR.Process.bind process _)
    ((agreed_absent rfl).trans ((agreed_absent rfl).trans agreed_nil))).trans ?_
  refine (sideMeaning_step repeat_meaning).trans ?_
  refine (congrArg (fun process => PIR.Process.bind process _)
    ((agreed_absent rfl).trans ((agreed_absent rfl).trans agreed_nil))).trans ?_
  exact sideMeaning_ret

/-! ## Announcements from outside the side -/

import_core announcement from r#"["zkc.core/0",
 [["original", [], [],
   [["law.uniform_below", [["nat", 256]], "sampling", [], ["index"]]],
   [["protocol", 0, 3, [], [["index", 1], ["index", 2]], [],
     [[["draw", 0, [1, 2], 0, 0, []]], [1, 2]]]]]],
 [], [], [],
 [["announcement"], [["owner", "first", "second"]], [["coin"]]]]"#

/-- The owner is outside the side and two receivers are inside: two `receive`s, each
receiver holding its own reply. No broadcast is assumed. -/
theorem two_receivers :
    announcement.announcement.meaning M (Side.ofMask 0b110) .nil =
      .call (.receive ⟨0, 0⟩ .index) fun first =>
      .call (.receive ⟨0, 0⟩ .index) fun second =>
      .done (.cons first (.cons second .nil)) :=
  rfl

/-- The same by walking the receivers: each receiver in the side performs its own
`receive`. -/
theorem two_receivers_stepwise :
    announcement.announcement.meaning M (Side.ofMask 0b110) .nil =
      .call (.receive ⟨0, 0⟩ .index) fun first =>
      .call (.receive ⟨0, 0⟩ .index) fun second =>
      .done (.cons first (.cons second .nil)) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step (draw_outside rfl)).trans ?_
  rw [receiverReplies_present M _ _ _ 1 [2] rfl, receiverReplies_present M _ _ _ 2 [] rfl,
    receiverReplies_nil]
  rfl

/-- One receiver in the side and one outside: one `receive`. -/
theorem one_receiver :
    announcement.announcement.meaning M (Side.ofMask 0b100) .nil =
      .call (.receive ⟨0, 0⟩ .index) fun second => .done (.cons () (.cons second .nil)) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step (draw_outside rfl)).trans ?_
  rw [receiverReplies_absent M _ _ _ 1 [2] rfl, receiverReplies_present M _ _ _ 2 [] rfl,
    receiverReplies_nil]
  rfl

/-- With the owner in the side, one draw and every copy is the coin. -/
theorem owner_inside :
    announcement.announcement.meaning M (Side.ofMask 0b111) .nil =
      .call (.draw ⟨0, 0⟩ (.of announcement.row.«law.uniform_below(nat 256)») .nil) fun coin =>
        .done (.cons coin (.cons coin .nil)) :=
  rfl

/-! ## Applications follow the callee -/

import_core first from r#"["zkc.core/0",
 [["original", [], [], [],
   [["protocol", 0, 1, [["index", 0], ["index", 0]], [["index", 0]], [], [[], [0]]],
    ["protocol", 0, 1, [["index", 0], ["index", 0]], [["index", 0], ["index", 0]], [],
     [[["apply", 0, [0], 0, [0, 1]], ["apply", 0, [0], 1, [1, 0]]], [2, 3]]]]]],
 [], [], [],
 [["pick", "caller"], [["role"], ["role"]], [[], ["straight", "swapped"]]]]"#

import_core second from r#"["zkc.core/0",
 [["original", [], [], [],
   [["protocol", 0, 1, [["index", 0], ["index", 0]], [["index", 0]], [], [[], [1]]],
    ["protocol", 0, 1, [["index", 0], ["index", 0]], [["index", 0], ["index", 0]], [],
     [[["apply", 0, [0], 0, [0, 1]], ["apply", 0, [0], 1, [1, 0]]], [2, 3]]]]]],
 [], [], [],
 [["pick", "caller"], [["role"], ["role"]], [[], ["straight", "swapped"]]]]"#

abbrev role : Side := Side.ofMask 0b1

/-- The callee returns its first argument: the two applications return `a` and `b`. -/
theorem swapped_first (a b : Nat) :
    first.caller.meaning M role (.cons a (.cons b .nil)) = .done (.cons a (.cons b .nil)) := rfl

/-- The same caller over a callee that returns its second argument: `b` and `a`. -/
theorem swapped_second (a b : Nat) :
    second.caller.meaning M role (.cons a (.cons b .nil)) = .done (.cons b (.cons a .nil)) := rfl

/-- Changing the callee's body changes the caller's meaning. -/
theorem callee_body_matters :
    first.caller.meaning M role (.cons (0 : Nat) (.cons (1 : Nat) .nil)) ≠
      second.caller.meaning M role (.cons (0 : Nat) (.cons (1 : Nat) .nil)) := by
  rw [swapped_first, swapped_second]
  intro same
  have first := congrArg (fun (process : PIR.Process (Effects M)
      (Values (SideValue M role) [⟨.index, 0⟩, ⟨.index, 0⟩])) =>
    show Nat from match process with
    | .done values => values.get .here
    | _ => (0 : Nat)) same
  exact Nat.zero_ne_one first

/-! ## A role map that is not the identity

`handoff` sends a number from its role 0 to its role 1. `relay` applies it with the
role map `[1, 0]`: its own role 1, the source, runs the sender, and its role 0, the
collector, the receiver. Each side of `relay` is derived by walking its body: the
`apply` runs the entry of `handoff` for the preimage side, the entry equation names
`handoff`'s own meaning, and the memberships of the preimage side hold by
evaluation. -/

import_core relayed from r#"["zkc.core/0",
 [["original", [], [], [],
   [["protocol", 0, 2, [["index", 0]], [["index", 1]], [], [[["exchange", 0, 1, 0, 0]], [1]]],
    ["protocol", 0, 2, [["index", 1]], [["index", 0]], [],
     [[["apply", 0, [1, 0], 0, [0]]], [1]]]]]],
 [], [], [],
 [["handoff", "relay"], [["sender", "receiver"], ["collector", "source"]],
  [["message"], ["handoff"]]]]"#

abbrev collector : Side := Side.ofMask 0b01
abbrev source : Side := Side.ofMask 0b10

/-- `handoff` for the preimage of the source's side: its sender is in the side. -/
theorem handoff_for_source (n : Nat) :
    relayed.handoff.meaning M (Side.preimage [1, 0] source) (.cons n .nil) =
      .call (.send ⟨0, 0⟩ .index n) fun _ => .done (.cons () .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step_call (exchange_send rfl rfl)).trans ?_
  exact congrArg (PIR.Process.call _) (funext fun _ => sideMeaning_ret)

/-- `handoff` for the preimage of the collector's side: its receiver is in the side. -/
theorem handoff_for_collector :
    relayed.handoff.meaning M (Side.preimage [1, 0] collector) (.cons () .nil) =
      .call (.receive ⟨0, 0⟩ .index) fun reply => .done (.cons reply .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  exact congrArg (PIR.Process.call _) (funext fun _ => sideMeaning_ret)

/-- The source, role 1 of `relay`, performs the send of `handoff`'s role 0. The site
of the effect is `handoff`'s. -/
theorem source_sends (n : Nat) :
    relayed.relay.meaning M source (.cons n .nil) =
      .call (.send ⟨0, 0⟩ .index n) fun _ => .done (.cons () .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step apply_meaning).trans ?_
  rw [relayed.relay.entry.handoff]
  refine (congrArg (fun process => PIR.Process.bind (PIR.Process.bind process _) _)
    (handoff_for_source M n)).trans ?_
  exact congrArg (PIR.Process.call _) (funext fun _ => sideMeaning_ret)

/-- The collector, role 0 of `relay`, performs the receive of `handoff`'s role 1. -/
theorem collector_receives :
    relayed.relay.meaning M collector (.cons () .nil) =
      .call (.receive ⟨0, 0⟩ .index) fun reply => .done (.cons reply .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step apply_meaning).trans ?_
  rw [relayed.relay.entry.handoff]
  refine (congrArg (fun process => PIR.Process.bind (PIR.Process.bind process _) _)
    (handoff_for_collector M)).trans ?_
  exact congrArg (PIR.Process.call _) (funext fun _ => sideMeaning_ret)

/-- Both roles: the handoff is internal. -/
theorem relay_internal (n : Nat) :
    relayed.relay.meaning M both (.cons n .nil) = .done (.cons n .nil) := rfl

/-! ## Stops

A stop by any role of a side ends the side's process: with the guarding role in the
side, a later send of another role of the side does not happen. -/

import_core stopping from r#"["zkc.core/0",
 [["original", [], [],
   [["index.checked_decrement", [], "partial", ["index"], ["index"]]],
   [["protocol", 0, 3, [["bool", 0], ["index", 1]], [], [],
     [[["at", 0, ["guard", "reject", 0]], ["exchange", 1, 2, 0, 1]], []]],
    ["protocol", 0, 1, [["index", 0]], [["index", 0]], [],
     [[["at", 0, ["op", 0, [0]]]], [1]]]]]],
 [], [], [],
 [["guarded", "decrement"], [["guard", "sender", "receiver"], ["role"]], [["message"], []]]]"#

/-- The guard's role and the sender together: the false condition stops the side. -/
theorem joint_side_stops (n : Nat) :
    stopping.guarded.meaning M (Side.ofMask 0b011) (.cons false (.cons n .nil)) = .halt .reject :=
  rfl

/-- The sender alone goes on and sends. -/
theorem sender_alone_sends (n : Nat) :
    stopping.guarded.meaning M (Side.ofMask 0b010) (.cons () (.cons n .nil)) =
      .call (.send ⟨0, 0⟩ .index n) fun _ => .done .nil :=
  rfl

/-- A partial row performed by the one role of a side: the model's result, or a stop
with the model's authored reason. -/
theorem decrement_side (n : Nat) :
    stopping.decrement.meaning M role (.cons n .nil) =
      (partialProcess M (M.partial (.of stopping.row.«index.checked_decrement») (.cons n .nil))).bind
        fun values => .done (.cons (values.get .here) .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step (at_partial rfl)).trans ?_
  rw [PIR.Process.bind_assoc]
  exact congrArg (PIR.Process.bind _) (funext fun _ => sideMeaning_ret)

/-- For every model, the side with the partial row never stops `incomplete`: a
partial row has no way to name that reason. -/
theorem decrement_never_incomplete (n : Nat) :
    NeverStops .incomplete (stopping.decrement.meaning M role (.cons n .nil)) := by
  rw [decrement_side]
  cases M.partial (.of stopping.row.«index.checked_decrement») (.cons n .nil) with
  | ok values => exact trivial
  | error reason => exact reason.stop_ne_incomplete

/-! ## Local regions

The body of a function is walked with the equations of the local regions: `if`,
`stop`, a partial row, `guard`, `call` and `loop`. -/

import_core locals from r#"["zkc.core/0",
 [["original", [], [],
   [["index.add", [], "pure", ["index", "index"], ["index"]],
    ["index.checked_decrement", [], "partial", ["index"], ["index"]]],
   [["function", 0, ["bool", "index"], ["index"],
     [[["if", 0, [1], [[["op", 1, [0]]], [1]], [[["stop", "abort"]], []]]], [2]]],
    ["function", 0, ["index", "index"], ["index"],
     [[["loop", 16, 0, [1], [], [[["op", 0, [1, 0]]], [2]]]], [2]]],
    ["function", 0, ["bool", "index"], ["index"],
     [[["guard", "reject", 0], ["call", 1, [1, 1]]], [2]]]]]],
 [], [], [],
 [["decrement_or_abort", "accumulate", "guarded_accumulate"], [[], [], []], [[], [], []]]]"#

/-- `index.add`, by the catalogue identity of its row. -/
def plus (a b : Nat) : Nat :=
  (M.pure (.of locals.row.«index.add») (.cons a (.cons b .nil))).get .here

/-- An `if` whose second region stops: the first region's partial row, or `abort`. -/
theorem decrement_or_abort_meaning (condition : Bool) (n : Nat) :
    locals.decrement_or_abort.meaning M (.cons condition (.cons n .nil)) =
      cond condition
        ((partialProcess M (M.partial (.of locals.row.«index.checked_decrement») (.cons n .nil))).bind
          fun values => .done (.cons (values.get .here) .nil))
        (.halt .abort) := by
  refine (Program.function_meaning M rfl _).trans ?_
  refine (localMeaning_step localOperation_conditional).trans ?_
  refine (bind_cond _ _ _ _).trans ?_
  refine congr (congrArg (cond condition) ?_) ?_
  · -- the first region: the partial row, then its result is the function's
    refine (congrArg (fun process => PIR.Process.bind process _)
      ((localMeaning_step localOperation_partial).trans
        (congrArg (PIR.Process.bind _) (funext fun _ => localMeaning_ret)))).trans ?_
    refine (PIR.Process.bind_assoc _ _ _).trans ?_
    exact congrArg (PIR.Process.bind _) (funext fun _ => localMeaning_ret)
  · -- the second region stops
    exact congrArg (fun process => PIR.Process.bind process _) localMeaning_stop

/-- One iteration of `accumulate`: the carried value plus the iteration number. -/
theorem accumulate_iteration (iteration total : Nat) :
    Region.denote (localMeaning M (Program.table M locals.decrement_or_abort))
        (dialect := LocalDialect locals.operations _ true)
        (.letOp (.op locals.row.«index.add» rfl) (.cons (.there .here) (.cons .here .nil)) .nil
          (.ret (.cons .here .nil)))
        (Values.cons (Value := M.Value) iteration (.cons total .nil)).get =
      .done (.cons (plus M total iteration) .nil) :=
  (localMeaning_step_done localOperation_pure).trans localMeaning_ret

/-- A `loop` is the bounded iteration of its region. -/
theorem accumulate_meaning (count start : Nat) :
    locals.accumulate.meaning M (.cons count (.cons start .nil)) =
      (loopProcess M 16 [.index] []
        (fun values => .done (.cons (plus M (values.tail.get .here) (values.get .here)) .nil))
        count (.cons start .nil) .nil).bind fun final => .done (.cons (final.get .here) .nil) := by
  refine (Program.function_meaning M rfl _).trans ?_
  refine (localMeaning_step localOperation_loop).trans ?_
  refine congr (congrArg PIR.Process.bind (congrArg (fun body =>
    loopProcess M 16 [.index] [] body count _ _) (funext fun values => ?_)))
    (funext fun _ => localMeaning_ret)
  match values with
  | .cons iteration (.cons total .nil) => exact accumulate_iteration M iteration total

/-- Within its maximum the loop is `PIR.repeatN` over the iteration number and the
carried value. -/
theorem accumulate_within (count start : Nat) (within : count ≤ 16) :
    locals.accumulate.meaning M (.cons count (.cons start .nil)) =
      ((PIR.repeatN count
          (fun (state : Nat × Values M.Value [.index]) =>
            PIR.Process.done (state.1 + 1, Values.cons (plus M (state.2.get .here) state.1) .nil))
          (0, .cons start .nil)).bind fun final => .done final.2).bind
        fun final => .done (.cons (final.get .here) .nil) := by
  rw [accumulate_meaning, loopProcess_within M within]
  refine congrArg (fun process => PIR.Process.bind (PIR.Process.bind process _) _)
    (congrArg (fun step => PIR.repeatN count step _) (funext fun state => ?_))
  match state with
  | (iteration, .cons total .nil) => rfl

/-- Above its maximum the loop stops `refused`. -/
theorem accumulate_refused (count start : Nat) (beyond : 16 < count) :
    locals.accumulate.meaning M (.cons count (.cons start .nil)) = .halt .refused := by
  rw [accumulate_meaning, loopProcess_beyond M beyond]
  rfl

/-- A `guard`, then a `call`: the entry equation names the callee's own meaning. -/
theorem guarded_accumulate_meaning (condition : Bool) (n : Nat) :
    locals.guarded_accumulate.meaning M (.cons condition (.cons n .nil)) =
      cond condition
        ((locals.accumulate.meaning M (.cons n (.cons n .nil))).bind fun values =>
          .done (.cons (values.get .here) .nil))
        (.halt .reject) := by
  refine (Program.function_meaning M rfl _).trans ?_
  refine (localMeaning_step localOperation_guard).trans ?_
  refine (bind_cond _ _ _ _).trans ?_
  refine guarded_congr ?_
  refine (localMeaning_step localOperation_call).trans ?_
  rw [locals.guarded_accumulate.entry.accumulate]
  exact congrArg (PIR.Process.bind _) (funext fun _ => localMeaning_ret)

end

end Zkc.Tests.Core.Controls

/-- info: 'Zkc.Tests.Core.Controls.source_sends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Core.Controls.source_sends

/-- info: 'Zkc.Tests.Core.Controls.decrement_never_incomplete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Core.Controls.decrement_never_incomplete

/-! ## Models exist

A model interprets every row, so a statement quantified over models is not vacuous only when a
model exists. The one-point model is one, and every carrier of a model has a value. -/

namespace Zkc.Tests.Core.Models

open Zkc.Core

example : Nonempty Model := ⟨Model.unit⟩

example (model : Model) (row : Nat) : Nonempty (model.Carrier row) := ⟨model.inhabitant row⟩

end Zkc.Tests.Core.Models
