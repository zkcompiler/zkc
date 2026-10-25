import Zkc.Source.RegionInterpretation
import Zkc.Source.ScalarRegion
import Zkc.Source.Mathematical.Projection

/-! Kernel-checked consumers of explicit region compatibility and component
projection. These tests concern independent Lean models, not native execution
or security. Higher-order compatibility is proved for the local operations.
-/

set_option autoImplicit false

namespace Tests.RegionCompatibility
open Zkc.Source PIR

local macro "vals[" xs:term,* "]" : term => do
  let mut result ← `(Values.nil)
  for x in xs.getElems.reverse do
    result ← `(Values.cons $x $result)
  return result

abbrev value (_ : Unit) := Nat
abbrev calls : Signature := ⟨Nat, fun _ => Nat⟩

namespace Translation

inductive Operation where
  | ask | pair | scope
  | branch (selected : Bool)

abbrev dialect : Dialect where
  Ty := Unit
  Op := Operation
  arguments
    | .pair => [(), ()]
    | _ => [()]
  results
    | .ask => [()]
    | _ => [(), ()]
  regions
    | .scope => [([()], [(), ()])]
    | .branch _ => [([()], [(), ()]), ([()], [(), ()])]
    | _ => []

abbrev source : RegionMeaning dialect calls where
  Value := value
  operation
    | .ask, .cons request .nil, .nil =>
        .call request fun reply => .done vals[reply]
    | .pair, args, .nil => .done args
    | .scope, args, .cons body .nil => body args
    | .branch selected, args, .cons yes (.cons no .nil) =>
        if selected then yes args else no args

/-- Change both the request and its reply while retaining an open interaction. -/
def lower : OperationInterpretation calls calls := fun request =>
  .call (request + 100) fun reply => .done (reply + 1)

abbrev target : RegionMeaning dialect calls where
  Value := value
  operation
    | .ask, .cons request .nil, .nil =>
        .call (request + 100) fun reply => .done vals[reply + 1]
    | .pair, args, .nil => .done args
    | .scope, args, .cons body .nil => body args
    | .branch selected, args, .cons yes (.cons no .nil) =>
        if selected then yes args else no args

/-- The callback law holds for arbitrary processes for these specific operations. -/
def compatibility : source.Translation lower where
  operation := target.operation
  commutes := by
    intro op args bodies
    cases op with
    | ask =>
      cases args with
      | cons request rest =>
        cases rest
        cases bodies
        rfl
    | pair => cases bodies; rfl
    | scope =>
      cases bodies with
      | cons body rest => cases rest; rfl
    | branch selected =>
      cases bodies with
      | cons yes rest => cases rest with
        | cons no rest => cases rest; cases selected <;> rfl

/-- Every callback receives only its declared input. The second request depends
on the first actual reply. The final bind reverses the two ordered results. -/
def nested (selected : Bool) : Region dialect [()] [(), ()] :=
  .bind
    (.letOp .scope vals[.here]
      (.cons
        (.letOp .ask vals[.here] .nil
          (.letOp (.branch selected) vals[.here]
            (.cons
              (.letOp .scope vals[.here]
                (.cons
                  (.letOp .ask vals[.here] .nil
                    (.letOp .pair vals[.there .here, .here] .nil
                      (.ret vals[.here, .there .here]))) .nil)
                (.ret vals[.here, .there .here]))
              (.cons (.stop .reject) .nil))
            (.ret vals[.here, .there .here]))) .nil)
      (.ret vals[.here, .there .here]))
    (.letOp .pair vals[.there .here, .here] .nil
      (.ret vals[.here, .there .here]))

theorem nested_translation (selected : Bool) (env : Environment value [()]) :
    (nested selected).denote target env =
      ((nested selected).denote source env).interpret lower :=
  Region.denote_translate source lower compatibility (nested selected) env

theorem source_open_replies (seed : Nat) :
    (nested true).denote source (vals[seed] : Values value [()]).get =
      .call seed (fun first => .call first (fun second => .done vals[second, first])) := rfl

-- This expected process is independent of the recursive translation definition.
theorem translated_open_replies (seed : Nat) :
    (nested true).denote target (vals[seed] : Values value [()]).get =
      .call (seed + 100) (fun first =>
        .call (first + 1 + 100) (fun second => .done vals[second + 1, first + 1])) := by
  rw [nested_translation, source_open_replies]
  rfl

theorem translated_callback_stop (seed : Nat) :
    (nested false).denote target (vals[seed] : Values value [()]).get =
      .call (seed + 100) (fun _ => .halt .reject) := by
  rw [nested_translation]
  rfl

theorem callback_stop_prevents_suffix (seed : Nat) :
    (Region.bind (nested false) (.stop .abort : Region dialect [(), (), ()] [(), ()])).denote
      target (vals[seed] : Values value [()]).get =
      .call (seed + 100) (fun _ => .halt .reject) := by
  change ((nested false).denote target _).bind _ = _
  rw [translated_callback_stop]
  rfl

/-- A reply tape records actual requests, replies, missing input and residual state. -/
def handler : Handler calls (List Nat) (Nat × Option Nat)
  | request, [] => ⟨.stopped .incomplete, [], [(request, none)]⟩
  | request, reply :: rest => ⟨.returned reply, rest, [(request, some reply)]⟩

def execute (selected : Bool) (replies : List Nat) :=
  ((nested selected).denote target (vals[7] : Values value [()]).get).run handler replies

theorem ordered_results_and_residual_state : execute true [4, 9, 88] =
    ⟨.returned vals[10, 5], [88], [(107, some 4), (105, some 9)]⟩ := rfl

theorem first_reply_changes_request_and_result : execute true [6, 9, 88] =
    ⟨.returned vals[10, 7], [88], [(107, some 6), (107, some 9)]⟩ := rfl

theorem second_reply_changes_its_own_result : execute true [4, 12, 88] =
    ⟨.returned vals[13, 5], [88], [(107, some 4), (105, some 12)]⟩ := rfl

theorem callback_stop_retains_prefix : execute false [4, 9, 88] =
    ⟨.stopped .reject, [9, 88], [(107, some 4)]⟩ := rfl

theorem missing_reply_retains_prefix : execute true [4] =
    ⟨.stopped .incomplete, [], [(107, some 4), (105, none)]⟩ := rfl

end Translation

namespace Scalar

abbrev language : Language where
  Ty := Unit
  Op := Unit
  arguments _ := [()]
  result _ := ()
  condition := ()

abbrev meaning : Interpretation language calls where
  Value := value
  condition n := n != 0
  operation
    | (), .cons request .nil => .call request .done

/-- Lowered iteration contains a closed branch callback and an effectful arm. -/
def repeated : Program language [()] () :=
  .iterate 2 .here
    (.branch .here
      (.letOp () vals[.here] (.ret .here))
      (.stop .refused))
    (.ret .here)

theorem lowered_translation (env : Environment value [()]) :
    repeated.toRegion.denote (meaning.translate Translation.lower).regionMeaning env =
      (repeated.toRegion.denote meaning.regionMeaning env).interpret Translation.lower :=
  Program.translate_toRegion meaning Translation.lower repeated env

theorem lowered_ordered_calls :
    (repeated.toRegion.denote (meaning.translate Translation.lower).regionMeaning
      (vals[7] : Values value [()]).get).run Translation.handler [4, 9, 88] =
        ⟨.returned vals[10], [88], [(107, some 4), (105, some 9)]⟩ := by
  rw [lowered_translation]
  rfl

theorem lowered_callback_stop :
    repeated.toRegion.denote (meaning.translate Translation.lower).regionMeaning
      (vals[0] : Values value [()]).get = .halt .refused := by
  rw [lowered_translation]
  rfl

end Scalar

namespace Projection
open Mathematical

inductive Role where
  | alice | bob | missing | excluded

inductive Operation where
  | first | add

abbrev language : Language where
  Ty := Unit
  Op := Operation
  arguments _ := [(), ()]
  result _ := ()
  condition := ()

abbrev meaning : Meaning language where
  Value := value
  operation
    | .first, .cons first (.cons _ .nil) => first
    | .add, .cons first (.cons second .nil) => first + second

def inputs : Values (fun _ : Unit => RoleFamily.Family Role Nat) [(), ()] :=
  vals[(fun role => some (match role with
      | .alice => 2 | .bob => 7 | .missing => 11 | .excluded => 17)),
    (fun role => match role with
      | .alice => some 3 | .bob => some 5 | .missing => none | .excluded => some 13)]

def selected : Role → Bool
  | .excluded => false
  | _ => true

def first : Block Role language [(), ()] () :=
  .letOp .first vals[.here, .there .here] (.ret .here)

/-- The inner bind doubles the restricted result. The outer suffix reads the
original second input, beyond the single exported result, yielding 2*x + y. -/
def nested : Block Role language [(), ()] () :=
  .bind
    (.letOp .first vals[.here, .there .here]
      (.bind
        (.restrict selected .here (.ret .here))
        (.letOp .add vals[.here, .there .here] (.ret .here))))
    (.letOp .add vals[.here, .there (.there .here)] (.ret .here))

def projected (block : Block Role language [(), ()] ())
    (condition : Option Nat → Bool) (role : Role) : Process calls (Values (fun _ : Unit => Option Nat) [()]) :=
  (block.project role).denote (meaning.projected condition) (RoleFamily.project inputs.get role)

-- All assertions compare the complete canonical process and singleton tuple.
-- The condition policy is arbitrary; projection neither branches nor calls it.
theorem disagreeing_alice (condition : Option Nat → Bool) :
    projected first condition .alice = .done vals[some 2] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem disagreeing_bob (condition : Option Nat → Bool) :
    projected first condition .bob = .done vals[some 7] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem ignored_argument_absence (condition : Option Nat → Bool) :
    projected first condition .missing = .done vals[none] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem present_before_restriction (condition : Option Nat → Bool) :
    projected first condition .excluded = .done vals[some 17] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem nested_alice (condition : Option Nat → Bool) :
    projected nested condition .alice = .done vals[some 7] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem nested_bob (condition : Option Nat → Bool) :
    projected nested condition .bob = .done vals[some 19] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem restriction_cannot_fill_absence (condition : Option Nat → Bool) :
    projected nested condition .missing = .done vals[none] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem restriction_removes_present_component (condition : Option Nat → Bool) :
    projected nested condition .excluded = .done vals[none] := by
  unfold projected
  rw [Block.denote_project]
  rfl

/-- An unused absent intermediate result cannot stop a later available return. -/
def discard : Block Role language [(), ()] () :=
  .bind nested (.ret (.there .here))

theorem absent_intermediate_keeps_suffix (condition : Option Nat → Bool) :
    projected discard condition .missing = .done vals[some 11] := by
  unfold projected
  rw [Block.denote_project]
  rfl

theorem restricted_intermediate_keeps_suffix (condition : Option Nat → Bool) :
    projected discard condition .excluded = .done vals[some 17] := by
  unfold projected
  rw [Block.denote_project]
  rfl

end Projection
end Tests.RegionCompatibility
