import Zkc.Core.Admission.Theorems
import Zkc.Frontend.Written.Charge
import Zkc.Tests.Frontend.SyntaxHarness

open Zkc.Frontend Zkc.Frontend.Written

private def assemblyOf (src : String) : Assembly :=
  Id.run <| assemble #[⟨"count.zkc", Syntax.parseString "count.zkc" src⟩] fun _ => pure none

private theorem bindings_eq {a b : Zkc.Vocabulary.Project.Bindings} (rows : a.rows = b.rows) : a = b := by
  cases a
  cases b
  congr

private def sameProgram (a b : AdmittedRoot) : Bool := Id.run do
  if rows : a.emission.bindings.rows = b.emission.bindings.rows then
    have same := bindings_eq rows
    let expected := cast (congrArg (fun v : Zkc.Vocabulary.Project.Bindings => Zkc.Core.Typed v.vocabulary) same.symm)
      b.evidence.admitted.program
    return (Zkc.Core.identifyAdmitted a.evidence.accepted expected).decide
  return false

private def checkAmount (c : AdmittedRoot) (goal : String) (path : List Zkc.Core.Key)
    (expected : Nat × Nat) : IO Unit := do
  let charge ← IO.ofExcept (goalDrawCharge c goal path "z")
  unless (charge.numerator, charge.denominator) == expected && charge.draws.length == 1 do
    throw (IO.userError s!"{goal}: expected {expected} at one admitted draw, got {repr charge}")

private def refused {α} (attempt : Except String α) (rule : String) : IO Unit := do
  let .error why := attempt | throw (IO.userError s!"expected refusal {rule}")
  unless why.contains rule do throw (IO.userError s!"expected {rule}, got {why}")

#eval show IO Unit from do
  let blocks := Zkc.Tests.Frontend.readBlocks (← IO.FS.readFile "../../language/conformance/layer-b.txt")
  let some direct := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing Count<8> goal fixture")
  let assembly := assemblyOf direct
  let count ← IO.ofExcept (admitSoundnessGoal assembly "loose")
  let strict ← IO.ofExcept (admitSoundnessGoal assembly "strict")
  unless count.id == strict.id && sameProgram count strict do throw (IO.userError "goal changed deployed program")
  -- Both requests select the very same admission and the same draw occurrence.
  checkAmount count "loose" [] (3, 8)
  checkAmount count "strict" [] (3, 4)
  let selectGoal (text : String) := admitSoundnessGoal (assemblyOf text) "loose"
  for replacement in ["", ", spec e = 4, spec e = 1", ", spec unknown = 4"] do
    refused (selectGoal (direct.replace ", spec e = 4" replacement)) "SP11"
  refused (selectGoal (direct.replace "spec e: nat>:" "spec e: nat> where (e <= n):" |>.replace
    "spec e = 4" "spec e = 9")) "SP4"
  let wrapper := "protocol Caller<spec tolerance: nat> roles(P, V)(xs: [F; 8] @(P, V)):\n" ++
    "    first <- Count<8, spec e = tolerance>(xs)\n" ++
    "    second <- Count<8, spec e = 1>(xs)\n"
  let wrapped := ((direct.replace "scheme Checked = Count<8>:" (wrapper ++ "scheme Checked = Caller:")).replace
    "Checked, spec e" "Checked, spec tolerance")
  let caller ← IO.ofExcept (selectGoal wrapped)
  let #[origin] := caller.emission.origins.filter (·.definition.number == caller.id)
    | throw (IO.userError "missing caller origin")
  let #[first, second] := origin.specification | throw (IO.userError "expected two applications")
  unless first.callee == second.callee && first.instruction != second.instruction do
    throw (IO.userError "expected distinct uses of one deployed Count<8>")
  checkAmount caller "loose" [first.instruction] (3, 8)
  checkAmount caller "strict" [first.instruction] (3, 4)
  checkAmount caller "loose" [second.instruction] (3, 4)
  let observers ← IO.ofExcept (selectGoal (wrapped.replace "nat> roles(P, V)" "nat> roles(P, V, Observer)"))
  let (fields, _) ← IO.ofExcept (evaluate observers.state default
    (Static.protocolViewFields observers.id (.received "Observer") default))
  unless fields.isEmpty do throw (IO.userError "a proof argument changed the uninvolved role's view")
  refused (goalDrawCharge caller "loose" [⟨1000⟩] "z") "expected an application"
  for args in ["8", "8, spec other = 1", "8, spec e = 1, spec e = 2"] do
    refused (selectGoal (wrapped.replace "8, spec e = tolerance" args)) "SP11"
  let limited := wrapped.replace "spec e: nat>:" "spec e: nat> where (e <= n):"
  refused (selectGoal (limited.replace "spec e = 1>" "spec e = 9>")) "SP4"
  let large ← IO.ofExcept (selectGoal (limited.replace "spec tolerance = 4" "spec tolerance = 9"))
  refused (goalDrawCharge large "loose" [first.instruction] "z") "SP4"
  -- A condition at the head of the relation is a condition of the clause that applies it, at
  -- the values of each use: those of the goal, and those of an application on the path.
  let relationHead := "relation NearZero(xs: [F; n]):"
  let conditioned (text : String) (bound : Nat) :=
    text.replace relationHead s!"relation NearZero(xs: [F; n]) where (e <= {bound}):"
  unless (direct.splitOn relationHead).length == 2 && (wrapped.splitOn relationHead).length == 2 do
    throw (IO.userError "the fixture does not have the relation head that the controls change")
  refused (selectGoal (conditioned direct 3)) "SP4"
  let some reference := (blocks.find? (·.id == "N-GL2d")).bind (·.files[0]?)
    | throw (IO.userError "missing the reference case of a relation's condition at a goal")
  refused (selectGoal reference) "SP4"
  let within ← IO.ofExcept (selectGoal (conditioned direct 4))
  checkAmount within "loose" [] (3, 8)
  let conditionedCaller ← IO.ofExcept (selectGoal (conditioned wrapped 3))
  refused (goalDrawCharge conditionedCaller "loose" [first.instruction] "z") "SP4"
  checkAmount conditionedCaller "loose" [second.instruction] (3, 4)
  refused (selectGoal ((conditioned wrapped 3).replace "spec e = 1>" "spec e = 4>")) "SP4"
  let localArg := (wrapped.replace "    first <-" "    offset = 1\n    first <-").replace
    "spec e = tolerance>" "spec e = tolerance + offset>"
  let localCaller ← IO.ofExcept (selectGoal localArg)
  checkAmount localCaller "strict" [first.instruction] (5, 8)
  let shared := direct.replace "scheme Checked = Count<8>:" (
    "    protocol Relay roles(P, V)(xs: [F; n] @(P, V)):\n        child <- Count(xs)\n" ++
    "scheme Checked = Relay<8>:")
  let sharedCaller ← IO.ofExcept (selectGoal shared)
  let #[origin] := sharedCaller.emission.origins.filter (·.definition.number == sharedCaller.id)
    | throw (IO.userError "missing relay")
  let #[call] := origin.specification | throw (IO.userError "missing inherited application")
  checkAmount sharedCaller "loose" [call.instruction] (3, 8)
  refused (selectGoal (shared.replace "child <- Count(xs)" "child <- Count<spec e = 1>(xs)")) "SP11"
  -- The body of a relation that a clause applies is typed at the values of each use. `ZeroAt`
  -- reads the table at a proof argument: at 7 of 8 it is typed, and at 8 the goal is refused; a
  -- caller that gives the value is refused where it writes it, and where a goal gives it to the
  -- caller, on the path to the application.
  let placed (id : String) : IO String :=
    match (blocks.find? (·.id == id)).bind (·.files[0]?) with
    | some text => pure text
    | none => throw (IO.userError s!"missing the reference case {id}")
  let inside ← placed "N-GL2e"
  let outside ← placed "N-GL2f"
  let selectPlaced (text : String) := admitSoundnessGoal (assemblyOf text) "placed"
  let reads ← IO.ofExcept (selectPlaced inside)
  let charge ← IO.ofExcept (goalDrawCharge reads "placed" [] "z")
  unless (charge.numerator, charge.denominator) == (7, 8) do
    throw (IO.userError s!"the charge of the relation that reads at a proof argument: {repr charge}")
  refused (selectPlaced outside) "TY7"
  let relay (argument goal : String) :=
    (inside.replace "scheme Checked = Count<8>:" (
      "protocol Relay<spec place: nat> roles(P, V)(xs: [F; 8] @(P, V)):\n" ++
      s!"    child <- Count<8, spec e = {argument}>(xs)\n" ++ "scheme Checked = Relay:")).replace
      "Checked, spec e = 7" s!"Checked, spec place = {goal}"
  let relayed ← IO.ofExcept (selectPlaced (relay "place" "7"))
  let #[relayOrigin] := relayed.emission.origins.filter (·.definition.number == relayed.id)
    | throw (IO.userError "missing the relay")
  let #[child] := relayOrigin.specification | throw (IO.userError "missing the relay's application")
  let through ← IO.ofExcept (goalDrawCharge relayed "placed" [child.instruction] "z")
  unless (through.numerator, through.denominator) == (7, 8) do
    throw (IO.userError s!"the charge through the relay: {repr through}")
  refused (selectPlaced (relay "8" "7")) "TY7"
  let beyond ← IO.ofExcept (selectPlaced (relay "place" "8"))
  refused (goalDrawCharge beyond "placed" [child.instruction] "z") "TY7"
  -- A relation that the relation of the clause applies is typed at the same values: where it
  -- shares the scope of the parameter, and where it is given the value in a specification
  -- argument. A relation that leaves the argument out is refused where the protocol is typed.
  discard <| IO.ofExcept (selectPlaced (← placed "N-GL2g"))
  refused (selectPlaced (← placed "N-GL2h")) "TY7"
  let given ← placed "N-GL2i"
  refused (selectPlaced given) "TY7"
  discard <| IO.ofExcept (selectPlaced (given.replace "spec e = 8" "spec e = 7"))
  refused (selectPlaced (← placed "N-GL2j")) "SP11"
  IO.println "Count<8> selected two exact ceilings on one admitted verifier, directly and through shared callees."
