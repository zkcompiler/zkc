import Zkc.Core.Transform.FunctionChecking
import Zkc.Tests.Core.Summaries

namespace Zkc.Core.BodyAnalysis.FunctionExamples
open FactsTests

/-! The shared body fixtures have full public verdicts in FactsTests and SummariesTests.
These cases cover bounded requirements, header type errors and numbered differences. -/

private def header (ins outs : List field.Ty) (pre post : List (Requirement Empty)) : FnHeader field :=
  ⟨⟨2⟩,ins,outs,false,none,⟨pre,post⟩⟩

example : verdict [] (header [.nat] [.nat] [] [.bounded (.arg 1)]) (.mk [0] [] [0]) =
    some (.inl [⟨.guarantee, ⟨⟨2⟩, [], none, none⟩, .unestablished (.bounded (.arg 1)) [anyNat]⟩]) := by decide +kernel
example : verdict [] (header [] [.nat] [] [.bounded (.arg 0)])
    (.mk [] [.op ⟨1⟩ [10] (natural 0) []] [10]) = accepted := by decide +kernel

private def boundedCallee : FnHeader field := ⟨⟨1⟩,[.nat],[.nat],false,none,⟨[.bounded (.arg 0)],[]⟩⟩
example : verdict [boundedCallee] (header [.nat] [.nat] [] [])
    (.mk [0] [.op ⟨1⟩ [10] (.call ⟨1⟩) [0]] [10]) =
    some (.inl [SummariesTests.unjustifiedAt 2 1 (.call ⟨1⟩) (.bounded (.arg 0)) [anyNat]]) := by decide +kernel
example : verdict [boundedCallee] (header [] [.nat] [] [])
    (.mk [] [.op ⟨1⟩ [0] (natural 0) [], .op ⟨2⟩ [10] (.call ⟨1⟩) [0]] [10]) = accepted := by decide +kernel

private def twoLoops : Region (LocalRaw field) Unit := .mk [0,1] [
  .op ⟨1⟩ [10] (toNat 4) [0], .op ⟨2⟩ [11] (toNat 8) [1],
  .loop ⟨3⟩ () (.count 10) [] [] (.mk [20] [] []),
  .loop ⟨4⟩ () (.count 11) [] [] (.mk [21] [] [])] []
private def loopBounds : List (Place × Nat) := [(⟨⟨2⟩,[],some ⟨3⟩,none⟩,3),(⟨⟨2⟩,[],some ⟨4⟩,none⟩,7)]
example : verdict [] (header [.fin 4,.fin 8] [] [] []) twoLoops = some (.inr loopBounds) := by decide +kernel

example : verdict [] (header [.nat] [.nat] [] [.difference (.arg 1) (.arg 0) 0])
    (.mk [0] [.op ⟨1⟩ [1] (natural 0) [], .op ⟨2⟩ [2] plus [0,1]] [2]) = accepted := by decide +kernel
example : verdict [] (header [sizedElements 8,.fin 8] [sizedElements 0] [] [])
    (.mk [0,1] [.op ⟨1⟩ [10] (toNat 8) [1], .op ⟨2⟩ [11] (natural 0) [],
      .op ⟨3⟩ [12] plus [11,10], .op ⟨4⟩ [13] (slice (sizedElements 8) (sizedElements 0)) [0,10,12]] [13])
      = accepted := by decide +kernel

/-- The current header is checked even when its body returns immediately. -/
example : verdict [] (header [.bool] [] [.below (.arg 0) 4] []) (.mk [0] [] []) =
    some (.inl [refuseWhole ⟨2⟩ .summary (.requirement (.below (.arg 0) 4))]) := by decide +kernel

/-- Even a caller with an empty body must validate the catalog it was given. -/
example : verdict [header [.nat] [] [.holds (.arg 0)] []] (header [] [] [] []) (.mk [] [] []) =
    some (.inl [refuseWhole ⟨2⟩ .summary (.requirement (.holds (.arg 0)))]) := by decide +kernel

/-- An unused invalid callee is reported at the callee, with its original clause. -/
example : verdict [{ header [.nat] [] [.holds (.arg 0)] [] with key := ⟨7⟩ }]
    (header [] [] [] []) (.mk [] [] []) =
    some (.inl [refuseWhole ⟨7⟩ .summary (.requirement (.holds (.arg 0)))]) := by decide +kernel

/-- Two copies of the same guard occupy different numbered instances of a block. -/
private def repeatedGuards (first second : Reason) : Region (LocalRaw field) Unit :=
  .mk [0] [.block ⟨7⟩ 0 [] (.mk [] [.guard ⟨2⟩ () 0 first] []),
    .block ⟨7⟩ 1 [] (.mk [] [.guard ⟨2⟩ () 0 second] [])] []

private def guardDifferences : Option (List Place) := do
  let hdr := header [.bool] [] [] []
  let stopping := { hdr with canStop := true }
  let catalog ← (FunctionContracts.check ([] : List (FnHeader field))).toOption
  let source ← (typeFn [] stopping (repeatedGuards .reject .reject)).toOption
  let candidate ← (typeFn [] stopping (repeatedGuards .abort .abort)).toOption
  match catalog.compareFunctions source candidate with
  | .error (.comparison (.body [] places)) => some places
  | _ => none

example : guardDifferences = some [⟨⟨2⟩, [(⟨7⟩,0)], some ⟨2⟩, none⟩,
    ⟨⟨2⟩, [(⟨7⟩,1)], some ⟨2⟩, none⟩] := by decide +kernel

end Zkc.Core.BodyAnalysis.FunctionExamples
