import Zkc.Tests.Formal.SourceProtocolRoots
import Zkc.Formal.Interactive.SourceCompleteness

namespace Zkc.Tests.Formal.SourceHonestSumcheck
open Zkc.Core Zkc.Frontend
open Zkc.Formal.Interactive.Sumcheck
open SourceProtocolRoots (sourceEvents vectorRows)
open SourcePairMembers (sourceRows)

def sumRow (b : Emit.Bindings) (n : Nat) : HonestPairs.SumRow (sourceRows b) n :=
  ⟨.inl (.seq .sum (.atom (.field .bls12381Fr)) (some (2^n))),rfl⟩

/-- Identify the callees by the instructions of the emitted caller. -/
def callKeys (e : Emit.RootEmission) (root : Key) : Option (Key × Key) := do
  let .protocol _ _ _ _ (.mk _ [_,.op _ _ (.apply red [0,1]) _,.op _ _ (.compute [1] (.call eval)) _,_,_] _) ←
    e.named.definitions.find? (·.key == root) | none
  return (red,eval)

def certificate (e : Emit.RootEmission) (evidence : (e.package ⟨[],[],[],[],[]⟩).Admission)
    (root : Key) (n : Nat) (variant : SourcePairReadback.Variant) :
    Option (SourceCompleteness.Certificate (sourceRows e.bindings) (sumRow e.bindings)
      (vectorRows e.bindings) (sourceEvents e.bindings) evidence.admitted.program root n) := do
  let (callee,eval) ← callKeys e root
  let b := e.bindings
  let rows := sourceRows b
  SourceCompleteness.certify rows (sumRow b) (vectorRows b) (sourceEvents b)
    evidence.admitted.program root n callee eval
    (if variant == .affine then rows.affineReadback else rows.evaluationReadback)

/-- The two private-function controls also exercise the previously certified open verifier. -/
def openVerifier (e : Emit.RootEmission) (evidence : (e.package ⟨[],[],[],[],[]⟩).Admission)
    (root : Key) (n : Nat) : Option Bool := do
  let (red,eval) ← callKeys e root
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
