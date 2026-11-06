module

public import Zkc.Source.Structured.OracleLoopPresentation
public import Zkc.Source.Structured.OracleReferenceLaws
meta import Zkc.Source.Structured.OracleProtocol

@[expose] public section

set_option autoImplicit false
namespace Tests.OracleLoopPresentation
open Zkc.Source Zkc.Source.Structured

abbrev model : DomainModel := ringModel Int Int
abbrev spec : RepeatSpec := ⟨[], [], [0], [], 3⟩
def algebra := OracleProtocol.algebra model 0 ⟨[], []⟩ []

def reference (_ : Unit) (index : Nat) : PIR.Process (OracleProtocol.Interface model) Unit :=
  if index = 1 then .halt .abort else .done ()

def callback : RegionFunction (Component (ProtocolValue model.toCarriers))
    (OracleProtocol.Interface model) ([.index], []) := fun args ↦
  match (args.get .here).bind ProtocolValue.toConcrete with
  | none => .halt .incomplete
  | some index => (reference () index).bind (fun _ ↦ .done .nil)

/-- An effectful loop whose second callback stops. The library preserves its exact
boundary process; the companion only supplies the one-step mathematical equation. -/
theorem stopping_presentation (count : Nat) (bounded : count ≤ 3) :
    algebra.repeatProcess spec {} 0 "round"
      (some (ProtocolValue.ofConcrete .index count)) .nil .nil callback =
      (Finite.fold (fun value index ↦
        (OracleProtocol.iterationObservations model).within "round" index
          (reference value index)) (List.range' 0 count) ()).bind (fun _ ↦ .done .nil) := by
  apply ProtocolLoopPresentation.present algebra spec {} 0 "round"
    (OracleProtocol.iterationObservations model)
    (OracleProtocol.iteration_eq model 0 ⟨[], []⟩ [] {} "round")
    (by decide) .nil callback (fun _ _ ↦ .nil) (fun _ _ ↦ True)
    (fun _ _ ↦ rfl) reference count
  · intro index value _ _
    cases value
    change callback (.cons (some (ProtocolValue.ofConcrete .index index)) .nil) =
      (reference () index).bind (fun _ ↦ .done .nil)
    simp only [callback, Values.get, Option.bind_some, ProtocolValue.toConcrete_ofConcrete]
  · intro index value _ _
    dsimp only [reference]
    split <;> trivial
  · change (some (ProtocolValue.ofConcrete .index count)).bind ProtocolValue.toConcrete = some count
    simp only [Option.bind_some, ProtocolValue.toConcrete_ofConcrete]
  · exact bounded
  · rfl
  · trivial

def provider : PIR.Handler (OracleProtocol.Interface model) Nat String := fun action state ↦
  match action with
  | .iteration site index => ⟨.returned (), state + 1, [site ++ ":" ++ toString index]⟩
  | .leave => ⟨.returned (), state + 1, ["leave"]⟩
  | _ => ⟨.stopped .refused, state, ["unexpected"]⟩

def observe (self : Nat) (count : Option Nat) : String × Nat × List String := Id.run do
  let result := (algebra.repeatProcess spec {} self "round"
    (count.map (ProtocolValue.ofConcrete .index)) .nil .nil callback).run provider 0
  let outcome := match result.outcome with
    | .returned _ => "returned"
    | .stopped .abort => "abort"
    | .stopped .refused => "refused"
    | .stopped .incomplete => "incomplete"
    | .stopped _ => "other"
  return (outcome, result.state, result.events)

#eval show IO Unit from do
  let cases : List (String × (String × Nat × List String) × (String × Nat × List String)) := [
    ("stopped second body", observe 0 (some 3), ("abort", 3, ["round:0", "leave", "round:1"])),
    ("bounded before effects", observe 0 (some 4), ("refused", 0, [])),
    ("missing count", observe 0 none, ("incomplete", 0, [])),
    ("unselected role", observe 1 none, ("returned", 0, [])),
    ("empty loop", observe 0 (some 0), ("returned", 0, []))]
  for (name, actual, expected) in cases do
    if actual != expected then throw (IO.userError (name ++ ": " ++ reprStr actual))
  IO.println "loop presentation: five outcome/state/boundary controls passed"

#print axioms stopping_presentation
#print axioms ProtocolLoopPresentation.present
#print axioms OracleProtocol.iteration_eq
#print axioms ReferenceLaw.invokeOracleConcrete
end Tests.OracleLoopPresentation
