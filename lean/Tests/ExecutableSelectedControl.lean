import Zkc.Executable.Cleanup
import Zkc.Executable.Installed
import Zkc.Executable.Reading
import Zkc.Executable.ProgramAdmission
import Zkc.Construction.Encoding
import Zkc.Construction.SourceOccurrences
import Mathlib.Algebra.Field.ZMod

/-! Controls for participant capture rows and selected control in the
executable meaning and the lowering rule.

A small validator over Booleans runs on a concrete instance. The controls fix
which arm runs, the frames it enters and leaves, the instructions it charges,
and what it binds: only the selected arm runs (a dormant arm may even hold an
unsupported instruction), capture rows bind formals to parents row by row (two
rows may share a copyable parent, and swapping rows swaps the bindings), a
body's names are not visible after it, and a stop inside an arm leaves every
frame innermost first. Branches in loops and loops in branches run zero or
more times. The lowering rule refuses participant branches by name, binds loop
capture formals, and refuses a loop capture of the transcript or of a custody
permission. Whole-program admission applies the lexical body rule: nested bodies
see their formals only and may reuse outer names, sites stay unique in the
participant, and capture rows share only copyable parents. A branch origin step
keeps its arm's alternative in a four-field canonical tree, adds no dynamic
coordinate, and is outside the occurrence rules' application and repeat
profile. -/

namespace Tests.ExecutableSelectedControl
open Zkc.Construction Zkc.Executable

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev F := ZMod 5
abbrev G := ZMod 5

def boolean : PhysicalType := ⟨.data .boolean, "native.bool/0"⟩
def index : PhysicalType := ⟨.data .index, "native.index/0"⟩
def transcript : PhysicalType := ⟨.transcript nativeSuite, "host.resource/0"⟩
def slot : String := "zkl_resource_0123456789abcdef"
def unit : PhysicalType := ⟨.data (.resourceUnit slot), "logical.resource_unit/0"⟩

/-- Boolean negation and conjunction, and a function that stops with `reject`. -/
def functions : List Function := [
  ⟨"negate", [("x", boolean)], [boolean], [.operation "negate_op" "not" [] ["x"] ["y"], .ret ["y"]]⟩,
  ⟨"conjoin", [("x", boolean), ("y", boolean)], [boolean],
    [.operation "conjoin_op" "and" [] ["x", "y"] ["z"], .ret ["z"]]⟩,
  ⟨"refuse", [("x", boolean)], [boolean], [.stop "refuse_stop" "reject"]⟩]

def bindings : List Binding :=
  [⟨"not", "bool.not", [], "arkworks/bool.not", []⟩, ⟨"and", "bool.and", [], "arkworks/bool.and", []⟩]

def validator (body : List Action) (inputs : List (String × PhysicalType) :=
    [("flag", boolean), ("value", boolean), ("rounds", index), ("state", transcript)]) : Validator :=
  ⟨"main", "V", "validator", inputs, [boolean, transcript], body, functions, bindings⟩

def context : Context := .plain "main" ["P", "V"] 0 1

def challenge (_ : History F G) : Id F := 0

def decode (_ : PhysicalType) (_ : List UInt8) : Option (Payload F G) := none

def runOn (body : List Action) (flag value : Bool) (rounds : Nat) (budget : Nat := 100) : Run F G :=
  Id.run (execute installed (validator body) context challenge decode budget
    [.data (.boolean flag), .data (.boolean value), .index rounds] [] [])

/-- The returned Boolean of a normal return. -/
def returned (run : Run F G) : Option Bool :=
  match run.result with
  | .returned (.data (.boolean value) :: _) => some value
  | _ => none

/-- The cause and site of a stop. -/
def stopped (run : Run F G) : Option (Cause × Option String) :=
  match run.result with
  | .stopped cause site _ => some (cause, site)
  | .returned _ => none

/-- The frames a run entered, in order. -/
def entered (run : Run F G) : List FrameId :=
  run.events.filterMap fun event => match event with
    | .enter frame => some frame
    | .leave _ _ => none

/-! ## Only the selected arm runs -/

/-- The true arm yields its capture; the false arm negates it. -/
def selected : List Action := [
  .cond "choose" "flag" [⟨"v", "value"⟩]
    [.yield ["v"]]
    [.call "negate_call" "negate" ["v"] ["w"], .yield ["w"]]
    ["out"],
  .ret ["out", "state"]]

theorem selected_then :
    returned (runOn selected true true 0) = some true ∧ (runOn selected true true 0).used = 3 ∧
      (runOn selected true true 0).events =
        [.enter .participant, .enter (.branch "choose" "then"),
          .leave (.branch "choose" "then") .returned, .leave .participant .returned] := by
  decide +kernel

theorem selected_else :
    returned (runOn selected false true 0) = some false ∧ (runOn selected false true 0).used = 6 ∧
      (runOn selected false true 0).events =
        [.enter .participant, .enter (.branch "choose" "else"), .enter (.call "negate_call" "negate"),
          .leave (.call "negate_call" "negate") .returned, .leave (.branch "choose" "else") .returned,
          .leave .participant .returned] := by
  decide +kernel

/-- An empty, event-free arm only yields: the false arm here yields the capture. -/
def eventFree : List Action := [
  .cond "choose" "flag" [⟨"v", "value"⟩] [.call "negate_call" "negate" ["v"] ["w"], .yield ["w"]]
    [.yield ["v"]] ["out"],
  .ret ["out", "state"]]

theorem eventFree_returns :
    returned (runOn eventFree false false 0) = some false ∧
      entered (runOn eventFree false false 0) = [.participant, .branch "choose" "else"] := by
  decide +kernel

/-- A dormant arm is not executed: the static inventory may hold a call that
stops and an instruction outside the profile. -/
def dormant : List Action := [
  .cond "choose" "flag" [⟨"v", "value"⟩]
    [.yield ["v"]]
    [.call "refuse_call" "refuse" ["v"] ["w"], .unsupported "send", .yield ["w"]]
    ["out"],
  .ret ["out", "state"]]

theorem dormant_not_executed : returned (runOn dormant true false 0) = some false := by
  decide +kernel

/-- Early completion inside the selected arm: the stop is reported at its own
site, and the call, the arm and the participant frames are left innermost
first. -/
theorem stop_inside_arm :
    stopped (runOn dormant false false 0) = some (.explicit .reject, some "refuse_stop") ∧
      (runOn dormant false false 0).events.drop 3 =
        [.leave (.call "refuse_call" "refuse") .stopped, .leave (.branch "choose" "else") .stopped,
          .leave .participant .stopped] ∧
      decide (runOn dormant false false 0).Cleaned = true := by
  decide +kernel

/-! ## Capture rows -/

/-- Two rows share one copyable parent: two formals, one value. -/
def aliased : List Action := [
  .cond "choose" "flag" [⟨"a", "value"⟩, ⟨"b", "value"⟩]
    [.call "conjoin_call" "conjoin" ["a", "b"] ["c"], .yield ["c"]]
    [.yield ["b"]]
    ["out"],
  .ret ["out", "state"]]

theorem aliased_rows : returned (runOn aliased true true 0) = some true ∧
    returned (runOn aliased true false 0) = some false := by
  decide +kernel

/-- Rows bind formals to parents row by row: swapping the parents swaps what
the arm yields. -/
def rows (first second : String) : List Action := [
  .cond "choose" "flag" [⟨"a", first⟩, ⟨"b", second⟩] [.yield ["a"]] [.yield ["b"]] ["out"],
  .ret ["out", "state"]]

theorem swapped_captures :
    returned (runOn (rows "flag" "value") true false 0) = some true ∧
      returned (runOn (rows "value" "flag") true false 0) = some false := by
  decide +kernel

/-- Swapped successors: the outputs bind what the arm yields, in order. -/
def successors (swap : Bool) : List Action := [
  .cond "choose" "flag" [⟨"a", "flag"⟩, ⟨"b", "value"⟩]
    [.yield (if swap then ["b", "a"] else ["a", "b"])] [.yield ["a", "b"]] ["first", "second"],
  .ret ["first", "state"]]

theorem swapped_successors :
    returned (runOn (successors false) true false 0) = some true ∧
      returned (runOn (successors true) true false 0) = some false := by
  decide +kernel

/-! ## Lexical bodies -/

/-- A name bound in an arm is not visible after the branch. -/
def leak : List Action := [
  .cond "choose" "flag" [⟨"v", "value"⟩] [.call "negate_call" "negate" ["v"] ["w"], .yield ["v"]]
    [.yield ["v"]] ["out"],
  .ret ["w", "state"]]

theorem arm_names_do_not_leak : stopped (runOn leak true true 0) = some (.contract, none) := by
  decide +kernel

/-- An arm sees only its formals: an uncaptured outer name is not visible. -/
def uncaptured : List Action := [
  .cond "choose" "flag" [] [.yield ["value"]] [.yield ["value"]] ["out"],
  .ret ["out", "state"]]

theorem arm_sees_only_formals : stopped (runOn uncaptured true true 0) = some (.contract, none) := by
  decide +kernel

/-- Sequential branches reuse the same formal names, each in its own arm. -/
def sequential : List Action := [
  .cond "first" "flag" [⟨"v", "value"⟩] [.yield ["v"]] [.call "n1" "negate" ["v"] ["w"], .yield ["w"]] ["x"],
  .cond "second" "flag" [⟨"v", "x"⟩] [.call "n2" "negate" ["v"] ["w"], .yield ["w"]] [.yield ["v"]] ["y"],
  .ret ["y", "state"]]

theorem sequential_branches :
    returned (runOn sequential true true 0) = some false ∧
      returned (runOn sequential false true 0) = some false ∧
      entered (runOn sequential false true 0) =
        [.participant, .branch "first" "else", .call "n1" "negate", .branch "second" "else"] := by
  decide +kernel

/-! ## Branches and loops -/

/-- A branch in a loop: the loop captures the selector, and each iteration
negates the carried value when it is true. -/
def branchInLoop : List Action := [
  .loop "rounds_loop" "rounds" 4 "i" [("acc", "value")] [⟨"f", "flag"⟩]
    [.cond "inner" "f" [⟨"v", "acc"⟩] [.call "neg" "negate" ["v"] ["w"], .yield ["w"]] [.yield ["v"]] ["next"],
     .yield ["next"]]
    ["out"],
  .ret ["out", "state"]]

theorem branch_in_loop :
    returned (runOn branchInLoop true true 0) = some true ∧
      entered (runOn branchInLoop true true 0) = [.participant] ∧
      returned (runOn branchInLoop true true 3) = some false ∧
      returned (runOn branchInLoop false true 3) = some true ∧
      entered (runOn branchInLoop true true 1) =
        [.participant, .loop "rounds_loop" 0, .branch "inner" "then", .call "neg" "negate"] := by
  decide +kernel

/-- A loop in an arm, counted by a captured index. -/
def loopInBranch : List Action := [
  .cond "outer" "flag" [⟨"v", "value"⟩, ⟨"n", "rounds"⟩]
    [.loop "inner_loop" "n" 4 "i" [("acc", "v")] [] [.call "neg" "negate" ["acc"] ["w"], .yield ["w"]] ["r"],
     .yield ["r"]]
    [.yield ["v"]]
    ["out"],
  .ret ["out", "state"]]

theorem loop_in_branch :
    returned (runOn loopInBranch true true 0) = some true ∧
      entered (runOn loopInBranch true true 0) = [.participant, .branch "outer" "then"] ∧
      returned (runOn loopInBranch true true 1) = some false ∧
      returned (runOn loopInBranch true true 2) = some true ∧
      returned (runOn loopInBranch false true 2) = some true := by
  decide +kernel

/-! ## Charges and selectors -/

/-- The branch is charged before its arm: at budget 0 it stops at its site, and
at budget 2 the true arm's yield and the return fit but nothing more. -/
theorem branch_budget :
    stopped (runOn selected true true 0 0) = some (.limit, some "choose") ∧
      stopped (runOn selected true true 0 2) = some (.limit, none) ∧
      returned (runOn selected true true 0 3) = some true := by
  decide +kernel

/-- A selector that is not a Boolean stops at the branch site uncharged. -/
def wrongSelector : List Action := [
  .cond "choose" "rounds" [] [.yield ["rounds"]] [.yield ["rounds"]] ["out"],
  .ret ["out", "state"]]

theorem wrong_selector :
    stopped (runOn wrongSelector true true 0) = some (.contract, some "choose") ∧
      (runOn wrongSelector true true 0).used = 0 := by
  decide +kernel

/-- The value model has no variant values: a match is outside the profile and
refuses explicitly as unsupported, uncharged, rather than failing as a
contract. -/
def matched : List Action := [
  .select "match" "flag" [] [("then", [], [.yield ["flag"]]), ("else", [], [.yield ["flag"]])] ["out"],
  .ret ["out", "state"]]

theorem match_unsupported :
    stopped (runOn matched true true 0) = some (.unsupported "participant-match", some "match") ∧
      (runOn matched true true 0).used = 0 := by
  decide +kernel

/-- An instruction kept as unsupported refuses explicitly when an arm reaches
it, and only then. -/
def unsupportedArm : List Action := [
  .cond "choose" "flag" [] [.unsupported "send", .yield []] [.yield []] [],
  .ret ["value", "state"]]

theorem unsupported_reached :
    stopped (runOn unsupportedArm true true 0) = some (.unsupported "send", none) ∧
      returned (runOn unsupportedArm false true 0) = some true := by
  decide +kernel

/-! ## The lowering rule -/

def refusal : Except Refusal Lowered → Option Refusal
  | .error refusal => some refusal
  | .ok _ => none

/-- The constructed instructions have no participant branch. -/
theorem branch_not_lowered :
    refusal ((validator selected).read installed []) = some (.unsupported "participant-branch") ∧
      refusal ((validator matched).read installed []) = some (.unsupported "participant-branch") := by
  decide +kernel

/-- A loop whose body uses its capture formal is read; using the parent name
instead refuses, because the body sees only its formals. -/
def captured (name : String) : List Action := [
  .loop "rounds_loop" "rounds" 4 "i" [("acc", "value")] [⟨"f", "flag"⟩]
    [.call "and_call" "conjoin" ["acc", name] ["next"], .yield ["next"]]
    ["out"],
  .ret ["out", "state"]]

theorem loop_capture_formal :
    refusal ((validator (captured "f")).read installed []) = none ∧
      refusal ((validator (captured "flag")).read installed []) = some (.operand "flag") := by
  decide +kernel

/-- A loop body reads its captures in every iteration: the transcript and a
custody permission are not copyable and refuse. -/
def capturing (parent : String) : List Action := [
  .loop "rounds_loop" "rounds" 4 "i" [("acc", "value")] [⟨"c", parent⟩] [.yield ["acc"]] ["out"],
  .ret ["out", "state"]]

def withUnit : List (String × PhysicalType) :=
  [("flag", boolean), ("value", boolean), ("rounds", index), ("held", unit), ("state", transcript)]

theorem affine_loop_capture :
    refusal ((validator (capturing "flag")).read installed []) = none ∧
      refusal ((validator (capturing "state")).read installed []) = some (.loop "rounds_loop") ∧
      refusal ((validator (capturing "held") withUnit).read installed []) = some (.loop "rounds_loop") := by
  decide +kernel

/-! ## Whole-program admission -/

def admission (body : List Action) (services : List ParticipantService := []) : Option AdmissionClass :=
  match ProgramArtifact.admit ⟨bindings, functions,
      [⟨"validator", "main", "V", (validator body).inputs, [boolean, transcript], body, services⟩],
      [⟨"main", [("V", "validator")]⟩]⟩ with
  | .ok () => none
  | .error refusal => some refusal.kind

-- The controls above admit as whole programs, except a match: no physical type
-- of this vocabulary is a variant.
#guard [selected, eventFree, aliased, rows "flag" "value", sequential, branchInLoop, loopInBranch].all
  (admission · == none)
#guard admission dormant == some .outside
#guard admission matched == some .types
-- A name bound in an arm is not visible after it; an arm sees only its formals.
#guard admission leak == some .namesAndSsa
#guard admission uncaptured == some .namesAndSsa

/-- Sibling arms and a later body may reuse a name; one body may not bind it twice. -/
def reuse (twice : Bool) : List Action := [
  .cond "choose" "flag" [⟨"v", "value"⟩]
    ([.call "n1" "negate" ["v"] ["w"]] ++ (if twice then [.call "n2" "negate" ["v"] ["w"]] else []) ++ [.yield ["w"]])
    [.call "n3" "negate" ["v"] ["w"], .yield ["w"]] ["w"],
  .ret ["w", "state"]]

#guard admission (reuse false) == none
#guard admission (reuse true) == some .namesAndSsa

/-- Sites are participant-wide: sibling arms cannot reuse one. -/
def siblingSites : List Action := [
  .cond "choose" "flag" [⟨"v", "value"⟩] [.call "same" "negate" ["v"] ["w"], .yield ["w"]]
    [.call "same" "negate" ["v"] ["w"], .yield ["w"]] ["w"],
  .ret ["w", "state"]]

#guard admission siblingSites == some .namesAndSsa

/-- Capture rows: a copyable parent may be shared; the transcript may be moved
into an arm once, never shared and never captured by a loop. -/
def sharing (parent : String) : List Action := [
  .cond "choose" "flag" [⟨"a", parent⟩, ⟨"b", parent⟩] [.yield ["a"]] [.yield ["b"]] ["out"],
  .ret ["out", "state"]]

def movedState : List Action := [
  .cond "choose" "flag" [⟨"s", "state"⟩] [.yield ["s"]] [.yield ["s"]] ["after"],
  .ret ["value", "after"]]

#guard admission (sharing "value") == none
#guard admission (sharing "state") == some .affineUse
#guard admission movedState == none
#guard admission (capturing "flag") == none
#guard admission (capturing "state") == some .affineUse
-- A formal may not bind a service port, which stays participant-wide.
#guard admission selected [⟨"v", "random.bls12-381.fr/0", 4⟩] == some .namesAndSsa
#guard admission selected [⟨"challenges", "random.bls12-381.fr/0", 4⟩] == none

/-! ## Branch origin steps -/

def branchTemplate : Template :=
  ⟨"main", [.apply "main" "call", .branch "child" "choose" "then", .repeat "child" "rounds"],
    ["message", "child", "site", "site", "P", "V"]⟩

-- A branch adds no dynamic coordinate and does not qualify sites.
#guard branchTemplate.repeats == 1
#guard branchTemplate.applicationPrefix == some "call"
#guard branchTemplate.steps.map Step.kind == ["apply", "branch", "repeat"]
-- The canonical tree keeps the alternative as a fourth field.
#guard (templateTree branchTemplate).encode == (Tree.list [.text "zkc.native-origin-template/0", .text "main",
    .list [.list [.text "apply", .text "main", .text "call"],
      .list [.text "branch", .text "child", .text "choose", .text "then"],
      .list [.text "repeat", .text "child", .text "rounds"]],
    .list [], .list (["message", "child", "site", "site", "P", "V"].map .text)]).encode
-- Distinct alternatives are distinct occurrences.
#guard (stepTree (.branch "child" "choose" "then")).encode != (stepTree (.branch "child" "choose" "else")).encode
-- The occurrence rules admit application and repeat paths only.
#guard !branchTemplate.steps.all (fun step => step.kind == "apply" || step.kind == "repeat")

end Tests.ExecutableSelectedControl
