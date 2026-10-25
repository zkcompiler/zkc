import Zkc.Source.Structured.Occurrence

/-! Control-flow controls for original-source iteration observations. These
check actual traces, not just instances of the generic erasure theorem. -/
set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured
namespace Tests.SourceIterationObservations

abbrev carriers := uniformCarriers Nat Unit
abbrev signature := Occurrence.signature carriers

inductive Trace where
  | entered (site : String) (index : Nat)
  | left (site : String) (index : Nat)
  | queried (field : String)
  deriving DecidableEq, Repr

def handler : PIR.Handler signature Unit Trace
  | .enter frame, state => ⟨.returned (), state, [.entered frame.site frame.index]⟩
  | .leave frame, state => ⟨.returned (), state, [.left frame.site frame.index]⟩
  | .action (.query _ field _), state => ⟨.returned (7 : Nat), state, [.queried field]⟩
  | .action _, state => ⟨.stopped .refused, state, []⟩

def spec : RepeatSpec := ⟨[], [], [0], [], 2⟩

def query (field : String) : PIR.Process signature Unit :=
  .call (.action (.query "challenge" field (.cons 0 .nil))) fun _ => .done ()

def body : RegionFunction (Component carriers.Value) signature ([.index], []) :=
  fun _ => (query "base").bind fun _ => .done .nil

def repeated (count : Option Nat) :=
  denoteRepeatOn spec {} 0 count Values.nil Values.nil body Occurrence.iterations "round"

example : ((repeated (some 2)).run handler ()).events =
    [.entered "round" 0, .queried "base", .left "round" 0,
     .entered "round" 1, .queried "base", .left "round" 1] := by decide +kernel

example : ((repeated (some 0)).run handler ()).events = [] := by decide +kernel
example : ((repeated (some 3)).run handler ()).outcome = .stopped .refused := rfl
example : ((repeated none).run handler ()).outcome = .stopped .incomplete := rfl

/-- A failed callback never closes its frame or starts a subsequent iteration. -/
def stopped :=
  denoteRepeatOn (carriers := carriers) spec {} 0 (some 2) Values.nil Values.nil
    (fun _ => (query "extension").bind fun _ => .halt .abort)
    Occurrence.iterations "round"

example : (stopped.run handler ()).events = [.entered "round" 0, .queried "extension"] := by
  decide +kernel
example : (stopped.run handler ()).outcome = .stopped .abort := rfl

/-- A nested repeat restarts its own index, preserving both boundaries. -/
def nested :=
  denoteRepeatOn (carriers := carriers) spec {} 0 (some 2) Values.nil Values.nil
    (fun _ => repeated (some 1)) Occurrence.iterations "outer"

example : (nested.run handler ()).events =
    [.entered "outer" 0, .entered "round" 0, .queried "base", .left "round" 0, .left "outer" 0,
     .entered "outer" 1, .entered "round" 0, .queried "base", .left "round" 0, .left "outer" 1] := by
  decide +kernel

/-- The actual call context qualifies the repeat site at the source boundary. -/
def called :=
  denoteRepeatOn spec (({} : ProtocolContext).enter "left" [0]) 0 (some 1)
    Values.nil Values.nil body Occurrence.iterations "round"

example : (called.run handler ()).events =
    [.entered "apply_4_left_round" 0, .queried "base", .left "apply_4_left_round" 0] := by
  decide +kernel

#print axioms Occurrence.participant_erase
end Tests.SourceIterationObservations
