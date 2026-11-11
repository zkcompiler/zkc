import Zkc.Tools.IR.Core.Import
import Zkc.IR.Core.Laws

/-! Sumcheck over a public table, as a `zkc.core/0` package.

The protocol `sumcheck` repeats the two-role protocol `round` as many times as the
round count says, through `apply`; a round calls the functions `half_sums` and
`fold_table`, which loop over the table, and the verifier guards the received sums
and draws the challenge. A final call of `final_check` decides. The embedded package
is the fixture `fixtures/core/sumcheck.json`.

Every side meaning below is derived by walking the body one operation at a time
with the equations of `Zkc.IR.Core.Laws`: a root step per operation, the operation's
equation with its memberships decided by evaluation, and the importer's entry
equations at each `call` and `apply`. No statement is closed by unfolding a whole
side.

For a symbolic round count the side meaning is the bounded iteration `repeatProcess`
of one round, so that a loop invariant applies to it. With both roles in the side,
the two copies of the count must agree; otherwise the side stops `incomplete`. -/

set_option autoImplicit false

open Zkc.Source Zkc.Core

import_core sumcheck from r#"["zkc.core/0",
 [["original",
   [["field", [["domain", "scalar"]]], ["vector", [["domain", "scalar"]]]],
   [],
   [["law.uniform", [["type", ["nominal", 0]]], "sampling", [], [["nominal", 0]]],
    ["vector.length", [["domain", "scalar"]], "pure", [["nominal", 1]], ["index"]],
    ["index.constant", [["nat", 1]], "pure", [], ["index"]],
    ["index.logical_shift_right", [], "pure", ["index", "index"], ["index"]],
    ["field.constant", [["domain", "scalar"], ["nat", 0]], "pure", [], [["nominal", 0]]],
    ["vector.get", [["domain", "scalar"]], "partial", [["nominal", 1], "index"], [["nominal", 0]]],
    ["index.add", [], "pure", ["index", "index"], ["index"]],
    ["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]],
    ["field.sub", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]],
    ["field.mul", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]],
    ["field.equal", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], ["bool"]],
    ["vector.empty", [["domain", "scalar"]], "pure", [], [["nominal", 1]]],
    ["vector.append", [["domain", "scalar"]], "pure", [["nominal", 1], ["nominal", 0]], [["nominal", 1]]],
    ["multilinear.restrict_prefix", [["domain", "scalar"]], "pure",
     [["nominal", 1], ["nominal", 1]], [["nominal", 1]]],
    ["vector.sum", [["domain", "scalar"]], "pure", [["nominal", 1]], [["nominal", 0]]]],
   [["function", 0, [["nominal", 1]], [["nominal", 0], ["nominal", 0]],
     [[["op", 1, [0]],
       ["op", 2, []],
       ["op", 3, [1, 2]],
       ["op", 4, []],
       ["loop", 1048576, 3, [4, 4], [0, 3],
        [[["op", 5, [3, 0]],
          ["op", 6, [0, 4]],
          ["op", 5, [3, 6]],
          ["op", 7, [1, 5]],
          ["op", 7, [2, 7]]],
         [8, 9]]]],
      [5, 6]]],
    ["function", 0, [["nominal", 1], ["nominal", 0]], [["nominal", 1]],
     [[["op", 1, [0]],
       ["op", 2, []],
       ["op", 3, [2, 3]],
       ["op", 11, []],
       ["loop", 1048576, 4, [5], [0, 1, 4],
        [[["op", 5, [2, 0]],
          ["op", 6, [0, 4]],
          ["op", 5, [2, 6]],
          ["op", 8, [7, 5]],
          ["op", 9, [3, 8]],
          ["op", 7, [5, 9]],
          ["op", 12, [1, 10]]],
         [11]]]],
      [6]]],
    ["protocol", 0, 2,
     [[["nominal", 1], 0], [["nominal", 0], 1], [["nominal", 1], 1]],
     [[["nominal", 1], 0], [["nominal", 0], 1], [["nominal", 1], 1]],
     [],
     [[["at", 0, ["call", 0, [0]]],
       ["exchange", 0, 1, 0, 3],
       ["exchange", 0, 1, 1, 4],
       ["at", 1, ["op", 7, [5, 6]]],
       ["at", 1, ["op", 10, [7, 1]]],
       ["at", 1, ["guard", "reject", 8]],
       ["draw", 1, [0], 2, 0, []],
       ["at", 0, ["call", 1, [0, 10]]],
       ["at", 1, ["op", 8, [6, 5]]],
       ["at", 1, ["op", 9, [9, 12]]],
       ["at", 1, ["op", 7, [5, 13]]],
       ["at", 1, ["op", 12, [2, 9]]]],
      [11, 14, 15]]],
    ["function", 0, [["nominal", 1], ["nominal", 1], ["nominal", 0]], ["bool"],
     [[["op", 13, [0, 1]],
       ["op", 14, [3]],
       ["op", 10, [4, 2]]],
      [5]]],
    ["protocol", 0, 2,
     [[["nominal", 1], 0], ["index", 0], [["nominal", 1], 1], [["nominal", 0], 1], ["index", 1]],
     [["bool", 1]],
     [[0, [0, 2]], [0, [1, 4]]],
     [[["at", 1, ["op", 11, []]],
       ["repeat", [[0, 1], [1, 4]], 64, [0, 3, 5], [],
        [[["apply", 2, [0, 1], 0, [0, 1, 2]]],
         [3, 4, 5]]],
       ["at", 1, ["call", 3, [2, 8, 7]]]],
      [9]]]]]],
 [], [], [],
 [["half_sums", "fold_table", "round", "final_check", "sumcheck"],
  [[], [], ["prover", "verifier"], [], ["prover", "verifier"]],
  [[], [], ["low_sum", "high_sum", "challenge"], [], ["round"]]]]"# fixture "fixtures/core/sumcheck.json"

namespace Zkc.Tests.Core.Sumcheck

-- The definitions below name imported rows and programs, which are not compiled.
noncomputable section

abbrev field : Ty := .nominal 0
abbrev vector : Ty := .nominal 1

/-- The uniform law over the field. -/
abbrev uniform : SamplingRow := .of sumcheck.row.«law.uniform(type field(domain scalar))»

abbrev verifier : Side := Side.ofMask 0b10
abbrev both : Side := Side.ofMask 0b11

variable (M : Model)

/-! The model's operations, by the catalogue identity of their rows. -/

def add (a b : M.Value field) : M.Value field :=
  (M.pure (.of sumcheck.row.«field.add(domain scalar)») (.cons a (.cons b .nil))).get .here
def sub (a b : M.Value field) : M.Value field :=
  (M.pure (.of sumcheck.row.«field.sub(domain scalar)») (.cons a (.cons b .nil))).get .here
def mul (a b : M.Value field) : M.Value field :=
  (M.pure (.of sumcheck.row.«field.mul(domain scalar)») (.cons a (.cons b .nil))).get .here
def equal (a b : M.Value field) : Bool :=
  (M.pure (.of sumcheck.row.«field.equal(domain scalar)») (.cons a (.cons b .nil))).get .here
def empty : M.Value vector :=
  (M.pure (.of sumcheck.row.«vector.empty(domain scalar)») .nil).get .here
def append (v : M.Value vector) (a : M.Value field) : M.Value vector :=
  (M.pure (.of sumcheck.row.«vector.append(domain scalar)») (.cons v (.cons a .nil))).get .here

/-- A local computation of role `role`, for a side that contains it: the computation,
then its results held by `role`. -/
def performed (side : Side) (role : Nat) {types : List Ty}
    (computation :
      PIR.Process (Effects M) (Values (fun type => Held (M.Value type) (side role)) types)) :
    PIR.Process (Effects M) (Values (SideValue M side) (Located.atRole role types)) :=
  computation.bind fun values =>
    .done (remapValues (F := SideValue M side) (fun type => ⟨type, role⟩) types values)

/-! ## One round -/

/-- The round protocol for the verifier: receive the two sums, check them against
the running claim, draw the challenge, and extend the point. -/
theorem round_verifier (claim : M.Value field) (point : M.Value vector) :
    sumcheck.round.meaning M verifier (.cons () (.cons claim (.cons point .nil))) =
      .call (.receive ⟨2, 0⟩ field) fun low =>
      .call (.receive ⟨2, 1⟩ field) fun high =>
      cond (equal M (add M low high) claim)
        (.call (.draw ⟨2, 2⟩ uniform .nil) fun challenge =>
          .done (.cons () (.cons (add M low (mul M challenge (sub M high low)))
            (.cons (append M point challenge) .nil))))
        (.halt .reject) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  -- the prover computes the two sums: nothing for the verifier
  refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  -- the sums arrive
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun low => ?_)
  refine (sideMeaning_step_call (exchange_receive rfl rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun high => ?_)
  -- the verifier adds them, compares the sum with the claim, and guards
  refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step_guarded (at_guard rfl)).trans ?_
  refine guarded_congr ?_
  -- the verifier draws the challenge; the prover folds its table
  refine (sideMeaning_step_call (draw_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun challenge => ?_)
  refine (sideMeaning_step_done (at_absent rfl)).trans ?_
  -- the verifier's next claim and point
  iterate 4 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  exact sideMeaning_ret

/-- The round protocol for both roles: the prover's two functions, the verifier's
check and the challenge; the exchanged sums are internal. The entry equations turn
the two calls into the functions' own meanings. -/
theorem round_both (table : M.Value vector) (claim : M.Value field) (point : M.Value vector) :
    sumcheck.round.meaning M both (.cons table (.cons claim (.cons point .nil))) =
      (performed M both 0 (sumcheck.half_sums.meaning M (.cons table .nil))).bind fun sums =>
      cond (equal M (add M (sums.get .here) (sums.tail.get .here)) claim)
        (.call (.draw ⟨2, 2⟩ uniform .nil) fun challenge =>
          (performed M both 0
            (sumcheck.fold_table.meaning M (.cons table (.cons challenge .nil)))).bind fun folded =>
          .done (.cons (folded.get .here)
            (.cons (add M (sums.get .here)
              (mul M challenge (sub M (sums.tail.get .here) (sums.get .here))))
            (.cons (append M point challenge) .nil))))
        (.halt .reject) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step (at_call rfl)).trans ?_
  rw [sumcheck.round.entry.half_sums]
  refine congrArg (PIR.Process.bind _) (funext fun sums => ?_)
  iterate 2 refine (sideMeaning_step_done (exchange_internal rfl rfl)).trans ?_
  iterate 2 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step_guarded (at_guard rfl)).trans ?_
  refine guarded_congr ?_
  refine (sideMeaning_step_call (draw_owner rfl)).trans ?_
  refine congrArg (PIR.Process.call _) (funext fun challenge => ?_)
  refine (sideMeaning_step (at_call rfl)).trans ?_
  rw [sumcheck.round.entry.fold_table]
  refine congrArg (PIR.Process.bind _) (funext fun folded => ?_)
  iterate 4 refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  exact sideMeaning_ret

/-! ## The repeated round -/

/-- The carried values of the repeat: the prover's table, the verifier's running
claim and the verifier's point. -/
abbrev carried : List Located := [⟨vector, 0⟩, ⟨field, 1⟩, ⟨vector, 1⟩]

/-- One round as the repeat of `sumcheck` runs it for a side: the round protocol for
the preimage side under the role map `[0, 1]`. -/
def round (side : Side) (state : Values (SideValue M side) carried) :
    PIR.Process (Effects M) (Values (SideValue M side) carried) :=
  (sumcheck.round.meaning M (Side.preimage [0, 1] side)
      (unmapValues (F := SideValue M side) (Located.rename [0, 1]) carried state)).bind
    fun values => .done (remapValues (F := SideValue M side) (Located.rename [0, 1]) carried values)

theorem values_eta {F : Located → Type} {a b c : Located} (values : Values F [a, b, c]) :
    Values.cons (values.get .here) (.cons (values.tail.get .here)
      (.cons (values.tail.tail.get .here) .nil)) = values := by
  match values with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-- Returning a round's results one by one is the round. -/
theorem round_returned (side : Side) (state : Values (SideValue M side) carried) :
    ((round M side state).bind fun (results : Values (SideValue M side) carried) =>
      PIR.Process.done (Values.cons (results.get .here) (Values.cons (results.tail.get .here)
        (Values.cons (results.tail.tail.get .here) Values.nil)))) = round M side state := by
  simp only [values_eta, PIR.Process.bind_done]

/-- One iteration of the repeat is one round, for the side at hand: the `apply` names
the table entry of `round`, which the entry equation turns into the round protocol's
own meaning. -/
local macro "repeated_round" : tactic => `(tactic|
  (refine congrArg (fun step => repeatProcess _ 64 step _ _) (funext fun state => ?_)
   match state with
   | .cons _ (.cons _ (.cons _ .nil)) =>
     refine (sideMeaning_step apply_meaning).trans ?_
     rw [sumcheck.sumcheck.entry.round]
     exact (congrArg (PIR.Process.bind _) (funext fun _ => sideMeaning_ret)).trans
       (round_returned _ _ _)))

/-! ## The protocol -/

/-- For a symbolic round count, the verifier's side of `sumcheck` is the bounded
iteration of one round, followed by the final check. The agreement is walked one
participant at a time: the prover is outside the side, the verifier is the first
participant inside, and no later one remains. -/
theorem sumcheck_verifier (values : M.Value vector) (claim : M.Value field) (rounds : Nat) :
    sumcheck.sumcheck.meaning M verifier
        (.cons () (.cons () (.cons values (.cons claim (.cons rounds .nil))))) =
      (repeatProcess M 64 (round M verifier) rounds
          (.cons () (.cons claim (.cons (empty M) .nil)))).bind fun final =>
        (performed M verifier 1 (sumcheck.final_check.meaning M
          (.cons values (.cons (final.tail.tail.get .here) (.cons (final.tail.get .here) .nil))))).bind
          fun decision => .done (.cons (decision.get .here) .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step repeat_meaning).trans ?_
  refine congr (congrArg PIR.Process.bind ?_) (funext fun final => ?_)
  · refine (agreed_absent rfl).trans ?_
    refine (agreed_present rfl).trans ?_
    refine agreeWith_nil.trans ?_
    repeated_round
  · refine (sideMeaning_step (at_call rfl)).trans ?_
    rw [sumcheck.sumcheck.entry.final_check]
    exact congrArg (PIR.Process.bind _) (funext fun decision => sideMeaning_ret)

/-- Both roles together: the two copies of the round count are compared; when they
are equal, the side is the bounded iteration of one round of both roles. -/
theorem sumcheck_both (values : M.Value vector) (rounds : Nat) (values' : M.Value vector)
    (claim : M.Value field) (rounds' : Nat) :
    sumcheck.sumcheck.meaning M both
        (.cons values (.cons rounds (.cons values' (.cons claim (.cons rounds' .nil))))) =
      (cond (Nat.beq rounds rounds')
          (repeatProcess M 64 (round M both) rounds
            (.cons values (.cons claim (.cons (empty M) .nil))))
          (.halt .incomplete)).bind fun final =>
        (performed M both 1 (sumcheck.final_check.meaning M
          (.cons values' (.cons (final.tail.tail.get .here) (.cons (final.tail.get .here) .nil))))).bind
          fun decision => .done (.cons (decision.get .here) .nil) := by
  refine (Program.protocol_meaning M rfl _ _).trans ?_
  refine (sideMeaning_step_done (at_pure rfl)).trans ?_
  refine (sideMeaning_step repeat_meaning).trans ?_
  refine congr (congrArg PIR.Process.bind ?_) (funext fun final => ?_)
  · refine (agreed_present rfl).trans ?_
    refine (agreeWith_present rfl).trans ?_
    refine congrArg (fun process => cond (Nat.beq rounds rounds') process _) ?_
    refine agreeWith_nil.trans ?_
    repeated_round
  · refine (sideMeaning_step (at_call rfl)).trans ?_
    rw [sumcheck.sumcheck.entry.final_check]
    exact congrArg (PIR.Process.bind _) (funext fun decision => sideMeaning_ret)

/-- Equal counts: both roles iterate one round. -/
theorem sumcheck_both_agreeing (values : M.Value vector) (rounds : Nat) (values' : M.Value vector)
    (claim : M.Value field) :
    sumcheck.sumcheck.meaning M both
        (.cons values (.cons rounds (.cons values' (.cons claim (.cons rounds .nil))))) =
      (repeatProcess M 64 (round M both) rounds
          (.cons values (.cons claim (.cons (empty M) .nil)))).bind fun final =>
        (performed M both 1 (sumcheck.final_check.meaning M
          (.cons values' (.cons (final.tail.tail.get .here) (.cons (final.tail.get .here) .nil))))).bind
          fun decision => .done (.cons (decision.get .here) .nil) := by
  rw [sumcheck_both, Nat.beq_refl, Bool.cond_true]

/-- Different counts: the side stops `incomplete`. -/
theorem sumcheck_both_disagreeing (values : M.Value vector) (rounds : Nat) (values' : M.Value vector)
    (claim : M.Value field) (rounds' : Nat) (differ : rounds ≠ rounds') :
    sumcheck.sumcheck.meaning M both
        (.cons values (.cons rounds (.cons values' (.cons claim (.cons rounds' .nil))))) =
      .halt .incomplete := by
  have unequal : Nat.beq rounds rounds' = false := by
    cases equal : Nat.beq rounds rounds' with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true equal) differ
  rw [sumcheck_both, unequal, Bool.cond_false]
  rfl

/-- A round count within the maximum: `PIR.repeatN` of one round. -/
theorem sumcheck_verifier_within (values : M.Value vector) (claim : M.Value field) (rounds : Nat)
    (within : rounds ≤ 64) :
    sumcheck.sumcheck.meaning M verifier
        (.cons () (.cons () (.cons values (.cons claim (.cons rounds .nil))))) =
      (PIR.repeatN rounds (round M verifier)
          (.cons () (.cons claim (.cons (empty M) .nil)))).bind fun final =>
        (performed M verifier 1 (sumcheck.final_check.meaning M
          (.cons values (.cons (final.tail.tail.get .here) (.cons (final.tail.get .here) .nil))))).bind
          fun decision => .done (.cons (decision.get .here) .nil) := by
  rw [sumcheck_verifier, repeatProcess_within M within]

/-- The verifier's round count above the maximum: the side stops `refused`. -/
theorem sumcheck_verifier_refused (values : M.Value vector) (claim : M.Value field) (rounds : Nat)
    (beyond : 64 < rounds) :
    sumcheck.sumcheck.meaning M verifier
        (.cons () (.cons () (.cons values (.cons claim (.cons rounds .nil))))) =
      .halt .refused := by
  rw [sumcheck_verifier, repeatProcess_beyond M beyond]
  rfl

end

end Zkc.Tests.Core.Sumcheck

/-- info: 'Zkc.Tests.Core.Sumcheck.sumcheck_verifier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Core.Sumcheck.sumcheck_verifier

/-- info: 'Zkc.Tests.Core.Sumcheck.round_both' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Zkc.Tests.Core.Sumcheck.round_both
