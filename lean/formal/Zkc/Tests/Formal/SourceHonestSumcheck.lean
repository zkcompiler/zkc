import Zkc.Tools.Formal.SumcheckCaller
import Zkc.Tests.Formal.SourceProtocolRoots
import Zkc.Formal.Interactive.SourceCompleteness

namespace Zkc.Tests.Formal.SourceHonestSumcheck
open Zkc.Core Zkc.Frontend
open Zkc.Formal.Interactive.Sumcheck
open SourceProtocolRoots (sourceEvents vectorRows)
open SourcePairMembers (sourceRows)

abbrev sumRow := Zkc.Formal.Written.SumcheckRows.sumRow

abbrev callKeys := Zkc.Tools.Formal.sumcheckCallKeys

def certificate (e : Emit.RootEmission) (evidence : (e.package ⟨[],[],[],[],[]⟩).Admission)
    (root : Key) (n : Nat) (variant : SourcePairReadback.Variant) :
    Option (SourceCompleteness.Certificate (sourceRows e.bindings) (sumRow e.bindings)
      (vectorRows e.bindings) (sourceEvents e.bindings) evidence.admitted.program root n) := do
  let ⟨_,callee,eval⟩ ← callKeys e root
  let b := e.bindings
  let rows := sourceRows b
  SourceCompleteness.certify rows (sumRow b) (vectorRows b) (sourceEvents b)
    evidence.admitted.program root n callee eval
    (if variant == .affine then rows.affineReadback else rows.evaluationReadback)

/-- The external extension must receive the actual first input of the Sumcheck caller. -/
abbrev hasSourceExtension := Zkc.Tools.Formal.hasSourceExtension

/-- Joint completeness at the admitted entry together with its external source association. -/
structure AtSource (c : SourceProtocolRoots.CheckedRoot) (n : Nat) where
  extension : hasSourceExtension c = true
  joint : SourceCompleteness.Certificate (sourceRows c.emission.bindings) (sumRow c.emission.bindings)
    (vectorRows c.emission.bindings) (sourceEvents c.emission.bindings) c.evidence.admitted.program ⟨c.id⟩ n

def atSource (c : SourceProtocolRoots.CheckedRoot) (n : Nat) (variant : SourcePairReadback.Variant) :
    Option (AtSource c n) := do
  if attached : hasSourceExtension c = true then
    return ⟨attached, ← certificate c.emission c.evidence ⟨c.id⟩ n variant⟩
  else none

/-- The two private-function controls also exercise the previously certified open verifier. -/
def openVerifier (e : Emit.RootEmission) (evidence : (e.package ⟨[],[],[],[],[]⟩).Admission)
    (root : Key) (n : Nat) : Option Bool := do
  let ⟨_,red,eval⟩ ← callKeys e root
  let b := e.bindings
  let rows := sourceRows b
  return (TableVerifier.certify rows (vectorRows b) evidence.admitted.program
    root red eval n (sourceEvents b) rows.evaluationReadback).isSome

section
open Zkc.Formal.Interactive

private def sig : Sig := ⟨Unit,fun _ => Bool⟩
private def ask : Process sig Unit Unit := .call () fun _ => .done ()
private def replies : Experiment sig Unit := ⟨fun _ s => FiniteLaw.certain (true,s)⟩
private def silentService : Experiment sig Unit := ⟨fun _ _ => ⟨[],Mass.zero_le _⟩⟩

example : replies.probability ask () (fun _ _ => true) = 1 := by decide +kernel
example : silentService.probability ask () (fun _ _ => true) = 0 := by decide +kernel
example : ¬ silentService.TotalOn ask () := fun h => (by decide : (0 : Mass) ≠ 1) h.1
example : silentService.TotalOn (Process.done (H := Unit) ()) () := trivial
end

end Zkc.Tests.Formal.SourceHonestSumcheck
