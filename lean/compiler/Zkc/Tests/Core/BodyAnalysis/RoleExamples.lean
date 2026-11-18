import Zkc.Core.Facts.Body.RoleChecking
import Zkc.Tests.Core.Shapes

namespace Zkc.Core.BodyAnalysis.RoleExamples
open Shapes

private def catalog := (FunctionContracts.check ([] : List (FnHeader plain))).toOption.get (by decide)

private def relayAccepted (r : Role) :=
  (RoleContracts.checkRole catalog r relayHeader (inputs := Names.counting 0 _) (project r relay)).isOk

example : [0, 1, 2].all relayAccepted := by decide +kernel

private def selfComparison (r : Role) :=
  (RoleContracts.compareRoles catalog r roundsHeader (inputs := Names.counting 0 _)
    (otherInputs := Names.counting 0 _) (project r rounds) (project r rounds)).isOk

example : [0, 1].all selfComparison := by decide +kernel

/-- The same ports and operand names as the relay, with a different second event. -/
private def changedRelay : Term (protocolDialect plain Shapes.none) (Ctx.positional [nat [0]]) [nat [0,1,2]] :=
  .op ⟨1⟩ (.flow .message 0 [1] (by decide) (by decide)) (.cons (var 0) .nil) (.cons 1 .nil) <|
  .op ⟨2⟩ (.flow .opening 1 [2] (by decide) (by decide)) (.cons (var 1) .nil) (.cons 2 .nil) <|
  .ret (.cons (var 2) .nil)

private def changedPlaces (r : Role) : Option (List Place) :=
  match RoleContracts.compareRoles catalog r relayHeader (inputs := Names.counting 0 _)
      (otherInputs := Names.counting 0 _) (project r relay) (project r changedRelay) with
  | .error (.body [] differences) => some differences
  | _ => Option.none

example : changedPlaces 1 = some [⟨relayHeader.key, [], some ⟨2⟩, some 1⟩] := by decide +kernel
example : changedPlaces 2 = some [⟨relayHeader.key, [], some ⟨2⟩, some 2⟩] := by decide +kernel
example : (RoleContracts.compareRoles catalog 0 relayHeader (inputs := Names.counting 0 _)
    (otherInputs := Names.counting 0 _) (project 0 relay) (project 0 changedRelay)).isOk := by decide +kernel

end Zkc.Core.BodyAnalysis.RoleExamples
