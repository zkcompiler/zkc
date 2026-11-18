import Zkc.Tests.Formal.SourceProtocolRoots
import Zkc.Formal.Interactive.SourceCompleteness

namespace Zkc.Tests.Formal.SourceHonestSumcheck
open Zkc.Core Zkc.Frontend
open Zkc.Formal.Interactive.Sumcheck
open SourceProtocolRoots (sourceEvents vectorRows)
open SourcePairMembers (sourceRows)

def sumRow (b : Emit.Bindings) (n : Nat) : HonestPairs.SumRow (sourceRows b) n :=
  ⟨.inl (.seq .sum (.atom (.field .bls12381Fr)) (some (2^n))),rfl⟩

structure CallerKeys where
  site : Key
  reduction : Key
  evaluator : Key

/-- Read the application site and both callees from the emitted caller. -/
def callKeys (e : Emit.RootEmission) (root : Key) : Option CallerKeys := do
  let .protocol _ _ _ _ (.mk _ [_,.op site _ (.apply red [0,1]) _,.op _ _ (.compute [1] (.call eval)) _,_,_] _) ←
    e.named.definitions.find? (·.key == root) | none
  return ⟨site,red,eval⟩

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
def hasSourceExtension (c : SourceProtocolRoots.CheckedRoot) : Bool := Id.run do
  let key : Key := ⟨c.id⟩
  let some keys := callKeys c.emission key | return false
  let some caller := c.state.results.checked? c.id | return false
  let .protocol body := caller.definition.body | return false
  let #[values, _] := body.ports | return false
  let some claim := c.emission.externalApplicationAt? c.state key keys.site keys.reduction [0,1]
    "p" "Zkc.Polynomial.extension" | return false
  return claim.operands == [.binder values.binder.id]

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
