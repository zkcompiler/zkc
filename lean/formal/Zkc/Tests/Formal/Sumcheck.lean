import Zkc.Tests.Core.Printed
import Zkc.Tests.Core.Check
import Zkc.Formal.Bls12381.Relation
import Zkc.Formal.Steps
import Zkc.Tools.Formal.Evaluate

/-! Ten rounds of Sumcheck keep the claim: a statement over one piece of the body per round.

The subject is a package of `Sumcheck<Fr, 10>` of the worked program `sumcheck_example`:
`fixtures/sumcheck-ten-rounds.json` is the package of the root `Sumcheck<Fr, 10>` that an
earlier state of the frontend's tool wrote for `examples/sumcheck_example.zkc` of the repository
(`zkc-check types … --packages <directory>`); the present frontend emits a different package for
that root. The loop of `Reduce` is written out: its body is the ten rounds one after another,
each of nine operations, and the library functions `sums`, `low`, `high` and `fix_first` are in
it once per size of the table. The package is linked here with its body in pieces of nine
operations, so that a piece is a round.

1. **The mathematics** (`sum_halves`, `sum_line`, `evaluate_fixFirst`). In any arithmetic: the
   sum of a table is the sum of the sums of its halves; and the line through those two sums, at
   a challenge, is the sum of the table with its first variable fixed at the challenge. Each is
   proved once, for every size.
2. **The laws of the library functions, at the sizes that the rounds use** (`sums0` …
   `bind9`, `boundary`, `evaluate`). Each function of the package is what the mathematics says:
   `sums` gives the sums of the halves, `fix_first` the table with its first variable fixed.
   A law is proved from the body of the function, with the laws of the functions it calls as
   hypotheses: `message` calls `sums`, `fix_first` calls `low` and `high`, `bind` calls
   `fix_first`. One statement per function of the library is instantiated at the ten sizes.
3. **A round** (`round0` … `round9`). The statement of a round is about its piece of the body
   followed by any region: when the two claims are the sum of the table, the verifier's check
   passes and the two claims of the next round are the sum of the next table. It uses the laws
   of the four functions that the round calls, as hypotheses about the table of functions; the
   law of `evaluate` is used at two calls, the prover's and the verifier's.
4. **Ten rounds** (`rounds_keep`, `reduce_keeps`). The ten statements compose one after
   another, and the laws hold of the functions of the package. So for the protocol `Reduce` of
   the package, in the model of any arithmetic: when the claims at the start are the sum of the
   table, every run reaches the instructions after the tenth round with claims that are the
   sum of the remaining table of one entry.

What is not here: the instructions after the tenth round, which collect the challenges, and the
final check of `Sumcheck`, which compares the last claim with the evaluation of the table at
the challenges. They need what each round leaves of the earlier rounds, which the statement of
a round does not keep. Nothing here is about the model that runs: the relation theorem does not
cover the operations that the core owns, which the library functions use.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core

printed_package Rounds from file "fixtures/sumcheck-ten-rounds.json" in pieces of 9

namespace Zkc.Formal.Sumcheck

typed_literal binding := Bls12381.bindingOf Rounds.raw

/-- One operation of a protocol of the package that returns, for both roles together, with the
equation of what it returns. -/
macro "step " equation:term : tactic =>
  `(tactic| (
    refine EveryRun.step
      (meaning := sideMeaning (provider _ binding) _ _ 0 [] (fun _ => true)) ?values ?computes ?next
    case computes => exact $equation))

/-- A draw of a protocol of the package, for both roles together. -/
macro "draw_step" : tactic =>
  `(tactic| (
    refine EveryRun.draw (site := ?site) (law := ?law) (inputs := ?inputs)
      (meaning := sideMeaning (provider _ binding) _ _ 0 [] (fun _ => true)) ?results ?draws ?next
    case draws => exact rfl))

/-- One operation of a function of the package that returns, with the equation of what it
returns. -/
macro "local_step " equation:term : tactic =>
  `(tactic| (
    refine (denote_step (meaning := localMeaning (provider _ binding) _) ?values ?computes).trans ?next
    case computes => exact $equation
    evaluate_bound))

/-- An operation of a function of the package that takes a part of a sized collection. Its
conditions are closed equations, which the kernel evaluates. -/
macro "slice_step" : tactic =>
  `(tactic| (
    refine (denote_step (meaning := localMeaning (provider _ binding) _) ?values ?computes).trans ?next
    case computes => exact slice_computes_of_checks _ _ _ kernel_rfl% kernel_rfl% kernel_rfl%
    evaluate_bound))

section Mathematics

variable (A : Arithmetic)

/-- Both roles. -/
abbrev both : Side := fun _ => true

/-- A table of a size. -/
abbrev Table (size : Nat) : Type := { items : List A.Scalar // items.length = size }

/-- The message of a round: the sums of the two halves of a table. -/
def halves (half : Nat) (table : List A.Scalar) : A.Scalar × A.Scalar × PUnit :=
  (A.sum (table.take half), A.sum (table.drop half), ())

/-- The first variable fixed: each entry of the first half, plus the challenge times its
difference to the entry of the second half. -/
def fixFirst (half : Nat) (table : List A.Scalar) (challenge : A.Scalar) : List A.Scalar :=
  List.zipWith (fun low high => low + (high - low) * challenge) (table.take half) (table.drop half)

theorem length_fixFirst {half : Nat} (table : Table A (half + half)) (challenge : A.Scalar) :
    (fixFirst A half table.val challenge).length = half := by
  simp [fixFirst, table.property]

/-- The sum of a table is the sum of the sums of its halves. -/
theorem sum_halves (half : Nat) (table : List A.Scalar) :
    A.sum table = (halves A half table).1 + (halves A half table).2.1 := by
  show A.sum table = A.sum (table.take half) + A.sum (table.drop half)
  rw [← A.sum_append, List.take_append_drop]

/-- The sum of two lists of one length combined at a challenge is the line through their sums
at the challenge. -/
theorem sum_line (challenge : A.Scalar) :
    ∀ (low high : List A.Scalar), low.length = high.length →
      (1 - challenge) * A.sum low + challenge * A.sum high =
        A.sum (List.zipWith (fun low high => low + (high - low) * challenge) low high)
  | [], [], _ => by
    show (1 - challenge) * A.sum [] + challenge * A.sum [] = A.sum []
    rw [A.sum_nil]
    grind
  | first :: low, second :: high, same => by
    have rest := sum_line challenge low high (Nat.succ.inj same)
    show (1 - challenge) * A.sum (first :: low) + challenge * A.sum (second :: high) =
      A.sum ((first + (second - first) * challenge) ::
        List.zipWith (fun low high => low + (high - low) * challenge) low high)
    rw [A.sum_cons, A.sum_cons, A.sum_cons, ← rest]
    grind
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same

/-- The claim of the next round: the line through the sums of the halves, at the challenge, is
the sum of the table with its first variable fixed. -/
theorem evaluate_fixFirst {half : Nat} (table : Table A (half + half)) (challenge : A.Scalar) :
    (1 - challenge) * (halves A half table.val).1 + challenge * (halves A half table.val).2.1 =
      A.sum (fixFirst A half table.val challenge) :=
  sum_line A challenge _ _ (by simp [table.property])

/-- What a round keeps: the verifier's running claim is the sum of the prover's table, and
the prover's running claim is the verifier's. -/
def Holds {size : Nat} (table : Table A size) (proverClaim verifierClaim : A.Scalar) : Prop :=
  verifierClaim = A.sum table.val ∧ proverClaim = verifierClaim

/-! ## The rounds -/

/-- The laws of the four functions that a round calls, of a table of functions: the message of
the round is the sums of the halves of the table; `boundary` adds the two parts of a message;
`bind` fixes the first variable of the table at a challenge; `evaluate` is the line through
the two parts of a message at a challenge. -/
structure RoundLaws (functions : FunctionTable (provider A binding) Rounds.functionHeaders63)
    (half : Nat)
    (message : Var Rounds.functionHeaders63
      ⟨[.seq (.nominal 0) (some (half + half))], [.tuple [.nominal 0, .nominal 0]], false⟩)
    (bind : Var Rounds.functionHeaders63
      ⟨[.seq (.nominal 0) (some (half + half)), .nominal 0], [.seq (.nominal 0) (some half)], false⟩) :
    Prop where
  message : ∀ table : Table A (half + half),
    functions.get message (.cons table .nil) = .done (.cons (halves A half table.val) .nil)
  boundary : ∀ sums : A.Scalar × A.Scalar × PUnit,
    functions.get (⟨60, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.tuple [.nominal 0, .nominal 0]], [.nominal 0], false⟩)
      (.cons sums .nil) = .done (.cons (ty := Ty.nominal 0) (sums.1 + sums.2.1) .nil)
  bind : ∀ (table : Table A (half + half)) (challenge : A.Scalar),
    functions.get bind (.cons table (.cons (ty := Ty.nominal 0) challenge .nil)) =
      .done (.cons (ty := Ty.seq (.nominal 0) (some half))
        ⟨fixFirst A half table.val challenge, length_fixFirst A table challenge⟩ .nil)
  evaluate : ∀ (sums : A.Scalar × A.Scalar × PUnit) (challenge : A.Scalar),
    functions.get (⟨55, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.tuple [.nominal 0, .nominal 0], .nominal 0], [.nominal 0], false⟩)
      (.cons sums (.cons (ty := Ty.nominal 0) challenge .nil)) =
        .done (.cons (ty := Ty.nominal 0)
          ((1 - challenge) * sums.1 + challenge * sums.2.1) .nil)

/-- The statement of one round, at its piece of the protocol's body: when the table and the
two claims that the piece reads satisfy what a round keeps, every run of the piece followed by
any region returns, provided every run of that region does on a table and two claims that
satisfy it again. The verifier's check passes by the law of the sums; the claim of the next
round is the sum of the next table by the law of the line. -/
macro "round_block " name:ident " : " piece:ident " from " before:term " to " after:term
    " at " size:num " = " half:num " + " _again:num " calling " message:num ", " bind:num
    " reading " state:num : command =>
  `(theorem $name
      (functions : FunctionTable (provider A binding) Rounds.functionHeaders63)
      (protocols : ProtocolTable (provider A binding) Rounds.protocolHeaders0)
      (rest : Region (ProtocolDialect Rounds.signatures Rounds.functionHeaders63
        Rounds.protocolHeaders0 (!Rounds.ph0.specificationOnly)) $after Rounds.ph0.outputs)
      (env : Environment (SideValue (provider A binding) both) $before)
      (post : Values (SideValue (provider A binding) both) Rounds.ph0.outputs → Prop)
      (laws : RoundLaws A functions $half ⟨$message, kernel_rfl%⟩ ⟨$bind, kernel_rfl%⟩)
      (holds : Holds A (size := $size)
        (env (⟨$state, kernel_rfl%⟩ : Var $before ⟨.seq (.nominal 0) (some $size), 0⟩))
        (env (⟨1, kernel_rfl%⟩ : Var $before ⟨.nominal 0, 0⟩))
        (env (⟨0, kernel_rfl%⟩ : Var $before ⟨.nominal 0, 1⟩)))
      (continues : ∀ next : Environment (SideValue (provider A binding) both) $after,
        Holds A (size := $half)
          (next (⟨2, kernel_rfl%⟩ : Var $after ⟨.seq (.nominal 0) (some $half), 0⟩))
          (next (⟨1, kernel_rfl%⟩ : Var $after ⟨.nominal 0, 0⟩))
          (next (⟨0, kernel_rfl%⟩ : Var $after ⟨.nominal 0, 1⟩)) →
        EveryRun post (rest.denote
          (sideMeaning (provider A binding) functions protocols 0 [] both) next)) :
      EveryRun post (($piece).typed rest |>.denote
        (sideMeaning (provider A binding) functions protocols 0 [] both) env) := by
    delta $piece
    dsimp only
    step returns_of_eq (laws.message _) _
    step rfl
    step returns_of_eq (laws.boundary _) _
    step rfl
    step guard_passes (decide_holds (holds.1.trans (sum_halves A $half _))) _ _ _
    draw_step
    intro (challenge : A.Scalar)
    step returns_of_eq (laws.bind _ _) _
    step returns_of_eq (laws.evaluate _ _) _
    step returns_of_eq (laws.evaluate _ _) _
    refine continues _ ?_
    show Holds A (size := $half)
      ⟨fixFirst A $half
          (env (⟨$state, kernel_rfl%⟩ : Var $before ⟨.seq (.nominal 0) (some $size), 0⟩) :
            Table A ($half + $half)).val challenge, _⟩
      ((1 - challenge) *
          (halves A $half (env (⟨$state, kernel_rfl%⟩ :
            Var $before ⟨.seq (.nominal 0) (some $size), 0⟩) : Table A ($half + $half)).val).1 +
        challenge *
          (halves A $half (env (⟨$state, kernel_rfl%⟩ :
            Var $before ⟨.seq (.nominal 0) (some $size), 0⟩) : Table A ($half + $half)).val).2.1)
      ((1 - challenge) *
          (halves A $half (env (⟨$state, kernel_rfl%⟩ :
            Var $before ⟨.seq (.nominal 0) (some $size), 0⟩) : Table A ($half + $half)).val).1 +
        challenge *
          (halves A $half (env (⟨$state, kernel_rfl%⟩ :
            Var $before ⟨.seq (.nominal 0) (some $size), 0⟩) : Table A ($half + $half)).val).2.1)
    exact ⟨evaluate_fixFirst A _ challenge, rfl⟩)

round_block round0 : Rounds.p0_body_piece0 from (bindAll [] Rounds.ph0.inputs) to
  Rounds.p0_body_context1 at 1024 = 512 + 512 calling 61, 56 reading 4

round_block round1 : Rounds.p0_body_piece1 from Rounds.p0_body_context1 to
  Rounds.p0_body_context2 at 512 = 256 + 256 calling 53, 49 reading 2

round_block round2 : Rounds.p0_body_piece2 from Rounds.p0_body_context2 to
  Rounds.p0_body_context3 at 256 = 128 + 128 calling 47, 43 reading 2

round_block round3 : Rounds.p0_body_piece3 from Rounds.p0_body_context3 to
  Rounds.p0_body_context4 at 128 = 64 + 64 calling 41, 37 reading 2

round_block round4 : Rounds.p0_body_piece4 from Rounds.p0_body_context4 to
  Rounds.p0_body_context5 at 64 = 32 + 32 calling 35, 31 reading 2

round_block round5 : Rounds.p0_body_piece5 from Rounds.p0_body_context5 to
  Rounds.p0_body_context6 at 32 = 16 + 16 calling 29, 25 reading 2

round_block round6 : Rounds.p0_body_piece6 from Rounds.p0_body_context6 to
  Rounds.p0_body_context7 at 16 = 8 + 8 calling 23, 19 reading 2

round_block round7 : Rounds.p0_body_piece7 from Rounds.p0_body_context7 to
  Rounds.p0_body_context8 at 8 = 4 + 4 calling 17, 13 reading 2

round_block round8 : Rounds.p0_body_piece8 from Rounds.p0_body_context8 to
  Rounds.p0_body_context9 at 4 = 2 + 2 calling 11, 7 reading 2

round_block round9 : Rounds.p0_body_piece9 from Rounds.p0_body_context9 to
  Rounds.p0_body_context10 at 2 = 1 + 1 calling 5, 1 reading 2

/-- The laws of the functions that the ten rounds call. -/
structure Laws (functions : FunctionTable (provider A binding) Rounds.functionHeaders63) :
    Prop where
  round0 : RoundLaws A functions 512 ⟨61, kernel_rfl%⟩ ⟨56, kernel_rfl%⟩
  round1 : RoundLaws A functions 256 ⟨53, kernel_rfl%⟩ ⟨49, kernel_rfl%⟩
  round2 : RoundLaws A functions 128 ⟨47, kernel_rfl%⟩ ⟨43, kernel_rfl%⟩
  round3 : RoundLaws A functions 64 ⟨41, kernel_rfl%⟩ ⟨37, kernel_rfl%⟩
  round4 : RoundLaws A functions 32 ⟨35, kernel_rfl%⟩ ⟨31, kernel_rfl%⟩
  round5 : RoundLaws A functions 16 ⟨29, kernel_rfl%⟩ ⟨25, kernel_rfl%⟩
  round6 : RoundLaws A functions 8 ⟨23, kernel_rfl%⟩ ⟨19, kernel_rfl%⟩
  round7 : RoundLaws A functions 4 ⟨17, kernel_rfl%⟩ ⟨13, kernel_rfl%⟩
  round8 : RoundLaws A functions 2 ⟨11, kernel_rfl%⟩ ⟨7, kernel_rfl%⟩
  round9 : RoundLaws A functions 1 ⟨5, kernel_rfl%⟩ ⟨1, kernel_rfl%⟩

/-- Ten rounds keep the claim. When the two claims at the start are the sum of the table, every
run of the body of `Reduce` returns, provided every run of the instructions after the tenth
round does on a table of one entry and two claims that are its sum. Each round is its own
statement, and the ten compose one after another. -/
theorem rounds_keep (functions : FunctionTable (provider A binding) Rounds.functionHeaders63)
    (protocols : ProtocolTable (provider A binding) Rounds.protocolHeaders0) (laws : Laws A functions)
    (env : Environment (SideValue (provider A binding) both) (bindAll [] Rounds.ph0.inputs))
    (post : Values (SideValue (provider A binding) both) Rounds.ph0.outputs → Prop)
    (holds : Holds A (size := 1024)
      (env (⟨4, kernel_rfl%⟩ : Var (bindAll [] Rounds.ph0.inputs) ⟨.seq (.nominal 0) (some 1024), 0⟩))
      (env (⟨1, kernel_rfl%⟩ : Var (bindAll [] Rounds.ph0.inputs) ⟨.nominal 0, 0⟩))
      (env (⟨0, kernel_rfl%⟩ : Var (bindAll [] Rounds.ph0.inputs) ⟨.nominal 0, 1⟩)))
    (continues : ∀ last : Environment (SideValue (provider A binding) both) Rounds.p0_body_context10,
      Holds A (size := 1)
        (last (⟨2, kernel_rfl%⟩ : Var Rounds.p0_body_context10 ⟨.seq (.nominal 0) (some 1), 0⟩))
        (last (⟨1, kernel_rfl%⟩ : Var Rounds.p0_body_context10 ⟨.nominal 0, 0⟩))
        (last (⟨0, kernel_rfl%⟩ : Var Rounds.p0_body_context10 ⟨.nominal 0, 1⟩)) →
      EveryRun post (Rounds.p0_body_rest10.typed.denote
        (sideMeaning (provider A binding) functions protocols 0 [] both) last)) :
    EveryRun post (Rounds.p0.definition.body.denote
      (sideMeaning (provider A binding) functions protocols 0 [] both) env) :=
  round0 A functions protocols _ env post laws.round0 holds fun _ holds =>
  round1 A functions protocols _ _ post laws.round1 holds fun _ holds =>
  round2 A functions protocols _ _ post laws.round2 holds fun _ holds =>
  round3 A functions protocols _ _ post laws.round3 holds fun _ holds =>
  round4 A functions protocols _ _ post laws.round4 holds fun _ holds =>
  round5 A functions protocols _ _ post laws.round5 holds fun _ holds =>
  round6 A functions protocols _ _ post laws.round6 holds fun _ holds =>
  round7 A functions protocols _ _ post laws.round7 holds fun _ holds =>
  round8 A functions protocols _ _ post laws.round8 holds fun _ holds =>
  round9 A functions protocols _ _ post laws.round9 holds continues

/-! ## The laws of the library functions -/

theorem length_take_half {half : Nat} (table : Table A (half + half)) :
    (table.val.take half).length = half := by
  rw [List.length_take, table.property]
  omega

theorem length_drop_half {half : Nat} (table : Table A (half + half)) :
    (table.val.drop half).length = half := by
  rw [List.length_drop, table.property]
  omega

/-- Two processes that return sized collections with the same elements are the same. -/
theorem done_sized {size : Nat} {first second : List A.Scalar} (same : first = second)
    (firstSized : first.length = size) (secondSized : second.length = size)
    {model : Model} :
    (PIR.Process.done (Values.cons (Value := Ty.Value (Carrier A binding))
        (ty := Ty.seq (.nominal 0) (some size)) ⟨first, firstSized⟩ Values.nil) :
      PIR.Process (Effects model) _) =
      .done (Values.cons (ty := Ty.seq (.nominal 0) (some size)) ⟨second, secondSized⟩ Values.nil) := by
  subst same
  rfl

/-- The first variable fixed, as the rows of sized collections compute it: the difference of
the halves, times the challenge, added to the first half. -/
theorem zipWith_line (challenge : A.Scalar) :
    ∀ low high : List A.Scalar,
      List.zipWith (fun x1 x2 => x1 + x2) low
          ((List.zipWith (fun x1 x2 => x1 - x2) high low).map fun value => value * challenge) =
        List.zipWith (fun low high => low + (high - low) * challenge) low high
  | [], _ => rfl
  | _ :: _, [] => rfl
  | first :: low, second :: high => by
    show (first + (second - first) * challenge) :: _ = (first + (second - first) * challenge) :: _
    rw [zipWith_line challenge low high]

theorem fixed_sized {half : Nat} (table : Table A (half + half)) (challenge fallback : A.Scalar) :
    sized fallback half (List.zipWith (fun x1 x2 => x1 + x2) (table.val.take half)
        (sized fallback half
          ((sized fallback half
            (List.zipWith (fun x1 x2 => x1 - x2) (table.val.drop half) (table.val.take half))).val.map
              fun value => value * challenge)).val) =
      ⟨fixFirst A half table.val challenge, length_fixFirst A table challenge⟩ := by
  have low := length_take_half A table
  have high := length_drop_half A table
  apply Subtype.ext
  have inner : (sized fallback half
      (List.zipWith (fun x1 x2 => x1 - x2) (table.val.drop half) (table.val.take half))).val =
        List.zipWith (fun x1 x2 => x1 - x2) (table.val.drop half) (table.val.take half) :=
    sized_val fallback (by rw [List.length_zipWith, high, low, Nat.min_self])
  rw [inner]
  have middle : (sized fallback half
      ((List.zipWith (fun x1 x2 => x1 - x2) (table.val.drop half) (table.val.take half)).map
        fun value => value * challenge)).val =
        (List.zipWith (fun x1 x2 => x1 - x2) (table.val.drop half) (table.val.take half)).map
          fun value => value * challenge :=
    sized_val fallback (by rw [List.length_map, List.length_zipWith, high, low, Nat.min_self])
  rw [middle]
  rw [sized_val fallback (by
    rw [List.length_zipWith, low, List.length_map, List.length_zipWith, high, low, Nat.min_self,
      Nat.min_self])]
  exact zipWith_line A challenge _ _

/-- The law of `sums` at a size: the sums of the two halves of the table. -/
macro "sums_law " name:ident " : " function:ident ", " rest:ident " over " headers:ident
    " at " half:num : command =>
  `(theorem $name (callees : FunctionTable (provider A binding) $headers)
      (table : Table A ($half + $half)) :
      ($function).definition.meaning (provider A binding) callees (.cons table .nil) =
        .done (.cons (halves A $half table.val) .nil) := by
    delta $function
    dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    slice_step
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    delta $rest
    dsimp only
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    slice_step
    local_step rfl
    local_step rfl
    have second : (table.val.drop $half).take $half = table.val.drop $half :=
      List.take_of_length_le (Nat.le_of_eq (length_drop_half A table))
    show PIR.Process.done
      (Values.cons (Value := Ty.Value (Carrier A binding)) (ty := Ty.tuple [.nominal 0, .nominal 0])
        (A.sum (table.val.take $half), A.sum ((table.val.drop $half).take $half), PUnit.unit)
        Values.nil) = _
    rw [second]
    rfl)

/-- The law of the message of a round at a size, from the law of `sums`, which it calls. -/
macro "message_law " name:ident " : " function:ident " over " headers:ident
    " at " half:num : command =>
  `(theorem $name (callees : FunctionTable (provider A binding) $headers)
      (sums : ∀ table : Table A ($half + $half),
        callees.get (⟨0, kernel_rfl%⟩ : Var $headers
            ⟨[.seq (.nominal 0) (some ($half + $half))], [.tuple [.nominal 0, .nominal 0]], false⟩)
          (.cons table .nil) = .done (.cons (halves A $half table.val) .nil))
      (table : Table A ($half + $half)) :
      ($function).definition.meaning (provider A binding) callees (.cons table .nil) =
        .done (.cons (halves A $half table.val) .nil) := by
    delta $function
    dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
    local_step sums _
    rfl)

/-- The law of `low` at a size: the first half of the table. -/
macro "low_law " name:ident " : " function:ident " over " headers:ident
    " at " half:num : command =>
  `(theorem $name (callees : FunctionTable (provider A binding) $headers)
      (table : Table A ($half + $half)) :
      ($function).definition.meaning (provider A binding) callees (.cons table .nil) =
        .done (.cons (ty := Ty.seq (.nominal 0) (some $half))
          ⟨table.val.take $half, length_take_half A table⟩ .nil) := by
    delta $function
    dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    slice_step
    rfl)

/-- The law of `high` at a size: the second half of the table. -/
macro "high_law " name:ident " : " function:ident " over " headers:ident
    " at " half:num : command =>
  `(theorem $name (callees : FunctionTable (provider A binding) $headers)
      (table : Table A ($half + $half)) :
      ($function).definition.meaning (provider A binding) callees (.cons table .nil) =
        .done (.cons (ty := Ty.seq (.nominal 0) (some $half))
          ⟨table.val.drop $half, length_drop_half A table⟩ .nil) := by
    delta $function
    dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    local_step rfl
    slice_step
    have second : (table.val.drop $half).take $half = table.val.drop $half :=
      List.take_of_length_le (Nat.le_of_eq (length_drop_half A table))
    show PIR.Process.done (Values.cons (Value := Ty.Value (Carrier A binding))
      (ty := Ty.seq (.nominal 0) (some $half))
      (⟨(table.val.drop $half).take $half,
          (congrArg List.length second).trans (length_drop_half A table)⟩ : Table A $half)
      Values.nil) = _
    exact done_sized A second _ _)

/-- The law of `fix_first` at a size, from the laws of `low` and `high`, which it calls: the
table with its first variable fixed at the challenge. -/
macro "fix_law " name:ident " : " function:ident " over " headers:ident
    " at " half:num : command =>
  `(theorem $name (callees : FunctionTable (provider A binding) $headers)
      (low : ∀ table : Table A ($half + $half),
        callees.get (⟨1, kernel_rfl%⟩ : Var $headers
            ⟨[.seq (.nominal 0) (some ($half + $half))], [.seq (.nominal 0) (some $half)], false⟩)
          (.cons table .nil) = .done (.cons (ty := Ty.seq (.nominal 0) (some $half))
            ⟨table.val.take $half, length_take_half A table⟩ .nil))
      (high : ∀ table : Table A ($half + $half),
        callees.get (⟨0, kernel_rfl%⟩ : Var $headers
            ⟨[.seq (.nominal 0) (some ($half + $half))], [.seq (.nominal 0) (some $half)], false⟩)
          (.cons table .nil) = .done (.cons (ty := Ty.seq (.nominal 0) (some $half))
            ⟨table.val.drop $half, length_drop_half A table⟩ .nil))
      (table : Table A ($half + $half)) (challenge : A.Scalar) :
      ($function).definition.meaning (provider A binding) callees
          (.cons table (.cons (ty := Ty.nominal 0) challenge .nil)) =
        .done (.cons (ty := Ty.seq (.nominal 0) (some $half))
          ⟨fixFirst A $half table.val challenge, length_fixFirst A table challenge⟩ .nil) := by
    delta $function
    dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
    local_step low _
    local_step high _
    local_step low _
    local_step rfl
    local_step rfl
    local_step rfl
    exact congrArg
      (fun items => PIR.Process.done (Values.cons (Value := Ty.Value (Carrier A binding))
        (ty := Ty.seq (.nominal 0) (some $half)) items Values.nil))
      (fixed_sized A table challenge 0))

/-- The law of `bind` of a round at a size, from the law of `fix_first`, which it calls. -/
macro "bind_law " name:ident " : " function:ident " over " headers:ident
    " at " half:num : command =>
  `(theorem $name (callees : FunctionTable (provider A binding) $headers)
      (fixes : ∀ (table : Table A ($half + $half)) (challenge : A.Scalar),
        callees.get (⟨0, kernel_rfl%⟩ : Var $headers
            ⟨[.seq (.nominal 0) (some ($half + $half)), .nominal 0],
              [.seq (.nominal 0) (some $half)], false⟩)
          (.cons table (.cons (ty := Ty.nominal 0) challenge .nil)) =
            .done (.cons (ty := Ty.seq (.nominal 0) (some $half))
              ⟨fixFirst A $half table.val challenge, length_fixFirst A table challenge⟩ .nil))
      (table : Table A ($half + $half)) (challenge : A.Scalar) :
      ($function).definition.meaning (provider A binding) callees
          (.cons table (.cons (ty := Ty.nominal 0) challenge .nil)) =
        .done (.cons (ty := Ty.seq (.nominal 0) (some $half))
          ⟨fixFirst A $half table.val challenge, length_fixFirst A table challenge⟩ .nil) := by
    delta $function
    dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
    local_step fixes _ _
    rfl)

/-- `boundary`: the sum of the two parts of a message. -/
theorem boundary (callees : FunctionTable (provider A binding) Rounds.functionHeaders2)
    (sums : A.Scalar × A.Scalar × PUnit) :
    Rounds.f2.definition.meaning (provider A binding) callees
        (.cons (ty := Ty.tuple [.nominal 0, .nominal 0]) sums .nil) =
      .done (.cons (ty := Ty.nominal 0) (sums.1 + sums.2.1) .nil) := by
  delta Rounds.f2
  dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
  local_step rfl
  local_step rfl
  local_step rfl
  rfl

/-- `evaluate`: the line through the two parts of a message, at a challenge. -/
theorem evaluate (callees : FunctionTable (provider A binding) Rounds.functionHeaders7)
    (sums : A.Scalar × A.Scalar × PUnit) (challenge : A.Scalar) :
    Rounds.f7.definition.meaning (provider A binding) callees
        (.cons (ty := Ty.tuple [.nominal 0, .nominal 0]) sums
          (.cons (ty := Ty.nominal 0) challenge .nil)) =
      .done (.cons (ty := Ty.nominal 0)
        ((1 - challenge) * sums.1 + challenge * sums.2.1) .nil) := by
  delta Rounds.f7
  dsimp only [FunctionDefinition.meaning, FunctionLink.ofBody]
  local_step rfl
  local_step rfl
  local_step rfl
  local_step rfl
  local_step rfl
  local_step rfl
  local_step rfl
  rfl

sums_law sums0 : Rounds.f0, Rounds.f0_body_rest1 over Rounds.functionHeaders0 at 512
message_law message0 : Rounds.f1 over Rounds.functionHeaders1 at 512
low_law low0 : Rounds.f3 over Rounds.functionHeaders3 at 512
high_law high0 : Rounds.f4 over Rounds.functionHeaders4 at 512
fix_law fixFirst0 : Rounds.f5 over Rounds.functionHeaders5 at 512
bind_law bind0 : Rounds.f6 over Rounds.functionHeaders6 at 512

sums_law sums1 : Rounds.f8, Rounds.f8_body_rest1 over Rounds.functionHeaders8 at 256
message_law message1 : Rounds.f9 over Rounds.functionHeaders9 at 256
low_law low1 : Rounds.f10 over Rounds.functionHeaders10 at 256
high_law high1 : Rounds.f11 over Rounds.functionHeaders11 at 256
fix_law fixFirst1 : Rounds.f12 over Rounds.functionHeaders12 at 256
bind_law bind1 : Rounds.f13 over Rounds.functionHeaders13 at 256

sums_law sums2 : Rounds.f14, Rounds.f14_body_rest1 over Rounds.functionHeaders14 at 128
message_law message2 : Rounds.f15 over Rounds.functionHeaders15 at 128
low_law low2 : Rounds.f16 over Rounds.functionHeaders16 at 128
high_law high2 : Rounds.f17 over Rounds.functionHeaders17 at 128
fix_law fixFirst2 : Rounds.f18 over Rounds.functionHeaders18 at 128
bind_law bind2 : Rounds.f19 over Rounds.functionHeaders19 at 128

sums_law sums3 : Rounds.f20, Rounds.f20_body_rest1 over Rounds.functionHeaders20 at 64
message_law message3 : Rounds.f21 over Rounds.functionHeaders21 at 64
low_law low3 : Rounds.f22 over Rounds.functionHeaders22 at 64
high_law high3 : Rounds.f23 over Rounds.functionHeaders23 at 64
fix_law fixFirst3 : Rounds.f24 over Rounds.functionHeaders24 at 64
bind_law bind3 : Rounds.f25 over Rounds.functionHeaders25 at 64

sums_law sums4 : Rounds.f26, Rounds.f26_body_rest1 over Rounds.functionHeaders26 at 32
message_law message4 : Rounds.f27 over Rounds.functionHeaders27 at 32
low_law low4 : Rounds.f28 over Rounds.functionHeaders28 at 32
high_law high4 : Rounds.f29 over Rounds.functionHeaders29 at 32
fix_law fixFirst4 : Rounds.f30 over Rounds.functionHeaders30 at 32
bind_law bind4 : Rounds.f31 over Rounds.functionHeaders31 at 32

sums_law sums5 : Rounds.f32, Rounds.f32_body_rest1 over Rounds.functionHeaders32 at 16
message_law message5 : Rounds.f33 over Rounds.functionHeaders33 at 16
low_law low5 : Rounds.f34 over Rounds.functionHeaders34 at 16
high_law high5 : Rounds.f35 over Rounds.functionHeaders35 at 16
fix_law fixFirst5 : Rounds.f36 over Rounds.functionHeaders36 at 16
bind_law bind5 : Rounds.f37 over Rounds.functionHeaders37 at 16

sums_law sums6 : Rounds.f38, Rounds.f38_body_rest1 over Rounds.functionHeaders38 at 8
message_law message6 : Rounds.f39 over Rounds.functionHeaders39 at 8
low_law low6 : Rounds.f40 over Rounds.functionHeaders40 at 8
high_law high6 : Rounds.f41 over Rounds.functionHeaders41 at 8
fix_law fixFirst6 : Rounds.f42 over Rounds.functionHeaders42 at 8
bind_law bind6 : Rounds.f43 over Rounds.functionHeaders43 at 8

sums_law sums7 : Rounds.f44, Rounds.f44_body_rest1 over Rounds.functionHeaders44 at 4
message_law message7 : Rounds.f45 over Rounds.functionHeaders45 at 4
low_law low7 : Rounds.f46 over Rounds.functionHeaders46 at 4
high_law high7 : Rounds.f47 over Rounds.functionHeaders47 at 4
fix_law fixFirst7 : Rounds.f48 over Rounds.functionHeaders48 at 4
bind_law bind7 : Rounds.f49 over Rounds.functionHeaders49 at 4

sums_law sums8 : Rounds.f50, Rounds.f50_body_rest1 over Rounds.functionHeaders50 at 2
message_law message8 : Rounds.f51 over Rounds.functionHeaders51 at 2
low_law low8 : Rounds.f52 over Rounds.functionHeaders52 at 2
high_law high8 : Rounds.f53 over Rounds.functionHeaders53 at 2
fix_law fixFirst8 : Rounds.f54 over Rounds.functionHeaders54 at 2
bind_law bind8 : Rounds.f55 over Rounds.functionHeaders55 at 2

sums_law sums9 : Rounds.f56, Rounds.f56_body_rest1 over Rounds.functionHeaders56 at 1
message_law message9 : Rounds.f57 over Rounds.functionHeaders57 at 1
low_law low9 : Rounds.f58 over Rounds.functionHeaders58 at 1
high_law high9 : Rounds.f59 over Rounds.functionHeaders59 at 1
fix_law fixFirst9 : Rounds.f60 over Rounds.functionHeaders60 at 1
bind_law bind9 : Rounds.f61 over Rounds.functionHeaders61 at 1

/-! ## The functions of the package -/

/-- The functions of the package, in the model of an arithmetic. A statement about them reads
them by the equations below, and never by their bodies. -/
@[irreducible] noncomputable def functions : FunctionTable (provider A binding) Rounds.functionHeaders63 :=
  Rounds.functions63.typed.table (provider A binding)

-- A function of the package, by its position in the table of the package's functions, is its
-- definition over the functions before it. The kernel evaluates each equation.
theorem boundary_at :
    (functions A).get (⟨60, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.tuple [.nominal 0, .nominal 0]], [.nominal 0], false⟩) =
      Rounds.f2.definition.meaning (provider A binding) (Rounds.functions2.typed.table (provider A binding)) :=
  kernel_rfl%

theorem evaluate_at :
    (functions A).get (⟨55, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.tuple [.nominal 0, .nominal 0], .nominal 0], [.nominal 0], false⟩) =
      Rounds.f7.definition.meaning (provider A binding) (Rounds.functions7.typed.table (provider A binding)) :=
  kernel_rfl%

theorem message_at0 :
    (functions A).get (⟨61, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (512 + 512))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f1.definition.meaning (provider A binding) (Rounds.functions1.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at0 :
    (functions A).get (⟨56, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (512 + 512)), .nominal 0], [.seq (.nominal 0) (some 512)],
          false⟩) =
      Rounds.f6.definition.meaning (provider A binding) (Rounds.functions6.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws0 : RoundLaws A (functions A) 512 ⟨61, kernel_rfl%⟩ ⟨56, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at0 A) _).trans
        (message0 A (Rounds.functions1.typed.table (provider A binding)) (fun table => sums0 A (Rounds.functions0.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at0 A) _).trans
        (bind0 A (Rounds.functions6.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst0 A (Rounds.functions5.typed.table (provider A binding)) (fun table => low0 A (Rounds.functions3.typed.table (provider A binding)) table)
              (fun table => high0 A (Rounds.functions4.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at1 :
    (functions A).get (⟨53, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (256 + 256))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f9.definition.meaning (provider A binding) (Rounds.functions9.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at1 :
    (functions A).get (⟨49, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (256 + 256)), .nominal 0], [.seq (.nominal 0) (some 256)],
          false⟩) =
      Rounds.f13.definition.meaning (provider A binding) (Rounds.functions13.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws1 : RoundLaws A (functions A) 256 ⟨53, kernel_rfl%⟩ ⟨49, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at1 A) _).trans
        (message1 A (Rounds.functions9.typed.table (provider A binding)) (fun table => sums1 A (Rounds.functions8.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at1 A) _).trans
        (bind1 A (Rounds.functions13.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst1 A (Rounds.functions12.typed.table (provider A binding)) (fun table => low1 A (Rounds.functions10.typed.table (provider A binding)) table)
              (fun table => high1 A (Rounds.functions11.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at2 :
    (functions A).get (⟨47, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (128 + 128))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f15.definition.meaning (provider A binding) (Rounds.functions15.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at2 :
    (functions A).get (⟨43, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (128 + 128)), .nominal 0], [.seq (.nominal 0) (some 128)],
          false⟩) =
      Rounds.f19.definition.meaning (provider A binding) (Rounds.functions19.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws2 : RoundLaws A (functions A) 128 ⟨47, kernel_rfl%⟩ ⟨43, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at2 A) _).trans
        (message2 A (Rounds.functions15.typed.table (provider A binding)) (fun table => sums2 A (Rounds.functions14.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at2 A) _).trans
        (bind2 A (Rounds.functions19.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst2 A (Rounds.functions18.typed.table (provider A binding)) (fun table => low2 A (Rounds.functions16.typed.table (provider A binding)) table)
              (fun table => high2 A (Rounds.functions17.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at3 :
    (functions A).get (⟨41, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (64 + 64))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f21.definition.meaning (provider A binding) (Rounds.functions21.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at3 :
    (functions A).get (⟨37, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (64 + 64)), .nominal 0], [.seq (.nominal 0) (some 64)],
          false⟩) =
      Rounds.f25.definition.meaning (provider A binding) (Rounds.functions25.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws3 : RoundLaws A (functions A) 64 ⟨41, kernel_rfl%⟩ ⟨37, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at3 A) _).trans
        (message3 A (Rounds.functions21.typed.table (provider A binding)) (fun table => sums3 A (Rounds.functions20.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at3 A) _).trans
        (bind3 A (Rounds.functions25.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst3 A (Rounds.functions24.typed.table (provider A binding)) (fun table => low3 A (Rounds.functions22.typed.table (provider A binding)) table)
              (fun table => high3 A (Rounds.functions23.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at4 :
    (functions A).get (⟨35, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (32 + 32))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f27.definition.meaning (provider A binding) (Rounds.functions27.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at4 :
    (functions A).get (⟨31, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (32 + 32)), .nominal 0], [.seq (.nominal 0) (some 32)],
          false⟩) =
      Rounds.f31.definition.meaning (provider A binding) (Rounds.functions31.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws4 : RoundLaws A (functions A) 32 ⟨35, kernel_rfl%⟩ ⟨31, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at4 A) _).trans
        (message4 A (Rounds.functions27.typed.table (provider A binding)) (fun table => sums4 A (Rounds.functions26.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at4 A) _).trans
        (bind4 A (Rounds.functions31.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst4 A (Rounds.functions30.typed.table (provider A binding)) (fun table => low4 A (Rounds.functions28.typed.table (provider A binding)) table)
              (fun table => high4 A (Rounds.functions29.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at5 :
    (functions A).get (⟨29, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (16 + 16))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f33.definition.meaning (provider A binding) (Rounds.functions33.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at5 :
    (functions A).get (⟨25, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (16 + 16)), .nominal 0], [.seq (.nominal 0) (some 16)],
          false⟩) =
      Rounds.f37.definition.meaning (provider A binding) (Rounds.functions37.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws5 : RoundLaws A (functions A) 16 ⟨29, kernel_rfl%⟩ ⟨25, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at5 A) _).trans
        (message5 A (Rounds.functions33.typed.table (provider A binding)) (fun table => sums5 A (Rounds.functions32.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at5 A) _).trans
        (bind5 A (Rounds.functions37.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst5 A (Rounds.functions36.typed.table (provider A binding)) (fun table => low5 A (Rounds.functions34.typed.table (provider A binding)) table)
              (fun table => high5 A (Rounds.functions35.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at6 :
    (functions A).get (⟨23, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (8 + 8))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f39.definition.meaning (provider A binding) (Rounds.functions39.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at6 :
    (functions A).get (⟨19, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (8 + 8)), .nominal 0], [.seq (.nominal 0) (some 8)],
          false⟩) =
      Rounds.f43.definition.meaning (provider A binding) (Rounds.functions43.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws6 : RoundLaws A (functions A) 8 ⟨23, kernel_rfl%⟩ ⟨19, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at6 A) _).trans
        (message6 A (Rounds.functions39.typed.table (provider A binding)) (fun table => sums6 A (Rounds.functions38.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at6 A) _).trans
        (bind6 A (Rounds.functions43.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst6 A (Rounds.functions42.typed.table (provider A binding)) (fun table => low6 A (Rounds.functions40.typed.table (provider A binding)) table)
              (fun table => high6 A (Rounds.functions41.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at7 :
    (functions A).get (⟨17, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (4 + 4))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f45.definition.meaning (provider A binding) (Rounds.functions45.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at7 :
    (functions A).get (⟨13, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (4 + 4)), .nominal 0], [.seq (.nominal 0) (some 4)],
          false⟩) =
      Rounds.f49.definition.meaning (provider A binding) (Rounds.functions49.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws7 : RoundLaws A (functions A) 4 ⟨17, kernel_rfl%⟩ ⟨13, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at7 A) _).trans
        (message7 A (Rounds.functions45.typed.table (provider A binding)) (fun table => sums7 A (Rounds.functions44.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at7 A) _).trans
        (bind7 A (Rounds.functions49.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst7 A (Rounds.functions48.typed.table (provider A binding)) (fun table => low7 A (Rounds.functions46.typed.table (provider A binding)) table)
              (fun table => high7 A (Rounds.functions47.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at8 :
    (functions A).get (⟨11, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (2 + 2))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f51.definition.meaning (provider A binding) (Rounds.functions51.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at8 :
    (functions A).get (⟨7, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (2 + 2)), .nominal 0], [.seq (.nominal 0) (some 2)],
          false⟩) =
      Rounds.f55.definition.meaning (provider A binding) (Rounds.functions55.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws8 : RoundLaws A (functions A) 2 ⟨11, kernel_rfl%⟩ ⟨7, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at8 A) _).trans
        (message8 A (Rounds.functions51.typed.table (provider A binding)) (fun table => sums8 A (Rounds.functions50.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at8 A) _).trans
        (bind8 A (Rounds.functions55.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst8 A (Rounds.functions54.typed.table (provider A binding)) (fun table => low8 A (Rounds.functions52.typed.table (provider A binding)) table)
              (fun table => high8 A (Rounds.functions53.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

theorem message_at9 :
    (functions A).get (⟨5, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (1 + 1))], [.tuple [.nominal 0, .nominal 0]], false⟩) =
      Rounds.f57.definition.meaning (provider A binding) (Rounds.functions57.typed.table (provider A binding)) :=
  kernel_rfl%

theorem bind_at9 :
    (functions A).get (⟨1, kernel_rfl%⟩ : Var Rounds.functionHeaders63
        ⟨[.seq (.nominal 0) (some (1 + 1)), .nominal 0], [.seq (.nominal 0) (some 1)],
          false⟩) =
      Rounds.f61.definition.meaning (provider A binding) (Rounds.functions61.typed.table (provider A binding)) :=
  kernel_rfl%

theorem laws9 : RoundLaws A (functions A) 1 ⟨5, kernel_rfl%⟩ ⟨1, kernel_rfl%⟩ :=
  ⟨fun table =>
      (congrFun (message_at9 A) _).trans
        (message9 A (Rounds.functions57.typed.table (provider A binding)) (fun table => sums9 A (Rounds.functions56.typed.table (provider A binding)) table) table),
    fun sums => (congrFun (boundary_at A) _).trans (boundary A (Rounds.functions2.typed.table (provider A binding)) sums),
    fun table challenge =>
      (congrFun (bind_at9 A) _).trans
        (bind9 A (Rounds.functions61.typed.table (provider A binding))
          (fun table challenge =>
            fixFirst9 A (Rounds.functions60.typed.table (provider A binding)) (fun table => low9 A (Rounds.functions58.typed.table (provider A binding)) table)
              (fun table => high9 A (Rounds.functions59.typed.table (provider A binding)) table) table challenge)
          table challenge),
    fun sums challenge => (congrFun (evaluate_at A) _).trans (evaluate A (Rounds.functions7.typed.table (provider A binding)) sums challenge)⟩

/-- The laws of the functions that the ten rounds call hold of the functions of the package. -/
theorem laws : Laws A (functions A) :=
  ⟨laws0 A, laws1 A, laws2 A, laws3 A, laws4 A, laws5 A, laws6 A, laws7 A, laws8 A, laws9 A⟩

/-- Ten rounds of the protocol `Reduce` of the package keep the claim, in the model of any
arithmetic. When the two claims that the protocol is given are the sum of the table, every run
of the prover and the verifier together returns, provided every run of the instructions after
the tenth round does on a table of one entry and two claims that are its sum. So in every run
the verifier's ten checks pass, whatever the ten challenges. -/
theorem reduce_keeps (protocols : ProtocolTable (provider A binding) Rounds.protocolHeaders0)
    (inputs : Values (SideValue (provider A binding) both) Rounds.ph0.inputs)
    (post : Values (SideValue (provider A binding) both) Rounds.ph0.outputs → Prop)
    (holds : Holds A (size := 1024)
      (Environment.ofValues inputs
        (⟨4, kernel_rfl%⟩ : Var (bindAll [] Rounds.ph0.inputs) ⟨.seq (.nominal 0) (some 1024), 0⟩))
      (Environment.ofValues inputs
        (⟨1, kernel_rfl%⟩ : Var (bindAll [] Rounds.ph0.inputs) ⟨.nominal 0, 0⟩))
      (Environment.ofValues inputs
        (⟨0, kernel_rfl%⟩ : Var (bindAll [] Rounds.ph0.inputs) ⟨.nominal 0, 1⟩)))
    (continues : ∀ last : Environment (SideValue (provider A binding) both) Rounds.p0_body_context10,
      Holds A (size := 1)
        (last (⟨2, kernel_rfl%⟩ : Var Rounds.p0_body_context10 ⟨.seq (.nominal 0) (some 1), 0⟩))
        (last (⟨1, kernel_rfl%⟩ : Var Rounds.p0_body_context10 ⟨.nominal 0, 0⟩))
        (last (⟨0, kernel_rfl%⟩ : Var Rounds.p0_body_context10 ⟨.nominal 0, 1⟩)) →
      EveryRun post (Rounds.p0_body_rest10.typed.denote
        (sideMeaning (provider A binding) (functions A) protocols 0 [] both) last)) :
    EveryRun post (Rounds.p0.definition.meaning (provider A binding) (functions A) protocols 0 []
      both inputs) := by
  unfold ProtocolDefinition.meaning
  exact rounds_keep A (functions A) protocols (laws A) (Environment.ofValues inputs) post holds
    continues

end Mathematics

/-! ## Checks -/

#print axioms sum_halves
#print axioms evaluate_fixFirst
#print axioms sums0
#print axioms fixFirst0
#print axioms round0
#print axioms rounds_keep
#print axioms laws
#print axioms reduce_keeps

end Zkc.Formal.Sumcheck
