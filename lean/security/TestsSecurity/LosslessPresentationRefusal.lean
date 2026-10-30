module

import ZkcSecurity.Bindings.Transcript.LosslessPresentation

set_option autoImplicit false
namespace TestsSecurity.LosslessPresentationRefusal
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.Original

abbrev carriers := Structured.uniformCarriers Bool Unit
def origin : Origin := .query "lossless" "draw" "random" "uniform" "validator" (.draw "field")

abbrev collapsedSignature : PIR.Signature := ⟨Unit, fun _ => Unit⟩
def collapsed : Interface collapsedSignature (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw :=
  fun _ => .query (.challenge origin) (fun _ => some ())

/-- A lossy actual query reply map cannot be certified as lossless. -/
theorem collapsed_refused : ¬ LosslessInterface collapsed := by
  intro lossless
  have injective := (lossless.query () origin (fun _ => ()) rfl).injective
  have impossible : (false : Bool) = true := injective rfl
  cases impossible

abbrev extraReplySignature : PIR.Signature := ⟨Unit, fun _ => Bool⟩
def extraReply : Interface extraReplySignature (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw :=
  fun _ => .send (.challenge origin) false

/-- The law refuses an unused second send reply before lifting is attempted. -/
theorem extraReply_refused : ¬ LosslessInterface extraReply := by
  intro lossless
  have impossible := lossless.send () (.challenge origin) false rfl true
  cases impossible

#print axioms collapsed_refused
#print axioms extraReply_refused

end TestsSecurity.LosslessPresentationRefusal
