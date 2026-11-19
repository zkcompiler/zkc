module

public import Zkc.Core.Program.EraseProgram

@[expose] public section

/-!
A typed program that is written one definition at a time, with its program by names beside it.

What elaboration decides about the body of a definition is one check of the body
(`Fn.checks`, `Prot.checks`); a body that passes has the conditions of a definition
(`FnConditions.of_checks`, `ProtocolConditions.of_checks`), and two decisions of the protocol
dialect that are functions and not instances give their propositions (`Fits.of_decision`,
`GivenKind.Typed.of_decision`). The erasure of a program is the
erasure of the definitions before its last one, followed by the last one's
(`Defs.erase_fn`, `Defs.erase_protocol`), so that a program by names is compared with a typed
program one definition at a time.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-! ## The conditions of a body, as one check -/

/-- Whether the body of a function has what elaboration decides about it. -/
def Fn.checks {fns : List (FnHeader V)} {hdr : FnHeader V} {inputs : Names hdr.ins}
    (body : Fn V fns hdr inputs) : Bool :=
  body.repeatedAddress.isNone &&
    (body.misuse (fun τ : V.Ty => Ty.isLinear V τ) inputs).isNone &&
    (hdr.canStop == body.canStop) &&
    body.armed &&
    (body.rebound inputs.toList).isNone &&
    (hdr.summary.misplaced hdr.ins.length hdr.outs.length).isNone

/-- A function's body that passes the check has the conditions of a definition. -/
theorem FnConditions.of_checks {fns : List (FnHeader V)} {hdr : FnHeader V}
    {inputs : Names hdr.ins} {body : Fn V fns hdr inputs} (passed : body.checks = true) :
    FnConditions body := by
  simp only [Fn.checks, Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at passed
  obtain ⟨⟨⟨⟨⟨distinct, linear⟩, stops⟩, armed⟩, once⟩, summary⟩ := passed
  exact {
    distinct := (Term.repeatedAddress_eq_none body).mp distinct
    linear := linear
    stops := stops
    armed := armed
    once := (Term.rebound_eq_none inputs.toList body).mp once
    summary := summary }

/-- Whether the body of a protocol has what elaboration decides about it, apart from the shape
in its header. -/
def Prot.checks {hs : Headers V} {hdr : ProtocolHeader V} {inputs : Names hdr.ins}
    (body : Prot V hs hdr inputs) : Bool :=
  @decide (Within (List.range hdr.roles) body) (decideWithin (List.range hdr.roles) body) &&
    decide (∀ a, a ∈ hdr.ins ++ hdr.outs → ∀ r, r ∈ a.holders → r < hdr.roles) &&
    @decide (Enclosed body) (decideEnclosed body) &&
    body.repeatedAddress.isNone &&
    (body.misuse (fun a : LTy V => Ty.isLinear V a.ty) inputs).isNone &&
    body.armed &&
    (body.rebound inputs.toList).isNone

/-- A protocol's body that passes the check, under a header with the shape of the body, has
the conditions of a definition. -/
theorem ProtocolConditions.of_checks {hs : Headers V} {hdr : ProtocolHeader V}
    {inputs : Names hdr.ins} {body : Prot V hs hdr inputs} (shaped : hdr.shape = shapeOf body)
    (passed : body.checks = true) : ProtocolConditions hdr body := by
  simp only [Prot.checks, Bool.and_eq_true, Option.isNone_iff_eq_none] at passed
  obtain ⟨⟨⟨⟨⟨⟨within, located⟩, enclosed⟩, distinct⟩, linear⟩, armed⟩, once⟩ := passed
  exact {
    within := @of_decide_eq_true _ (decideWithin (List.range hdr.roles) body) within
    located := of_decide_eq_true located
    enclosed := @of_decide_eq_true _ (decideEnclosed body) enclosed
    distinct := (Term.repeatedAddress_eq_none body).mp distinct
    shaped := shaped
    linear := linear
    armed := armed
    once := (Term.rebound_eq_none inputs.toList body).mp once }

/-- Operands that are decided to fit their ports fit them. -/
theorem Fits.of_decision {actual expected : List (LTy V)}
    (decided : @decide (Fits actual expected) (decideFits actual expected) = true) :
    Fits actual expected :=
  @of_decide_eq_true _ (decideFits actual expected) decided

/-- What the world gives that is decided to have the types of its kind has them. -/
theorem GivenKind.Typed.of_decision {kind : GivenKind V} {ins : List V.Ty} {out : V.Ty}
    (decided : @decide (kind.Typed ins out) (decideGiven kind ins out) = true) :
    kind.Typed ins out :=
  @of_decide_eq_true _ (decideGiven kind ins out) decided

/-! ## Erasure, one definition at a time -/

/-- The erasure of definitions that end with a function: the erasure of those before it, then
the function by names. -/
theorem Defs.erase_fn {hs : Headers V} {hdr : FnHeader V} {inputs : Names hdr.ins}
    {body : Fn V hs.fns hdr inputs} {ok : FnConditions body} {rest : Defs V hs}
    {notes : BodyAnalysis.Annotations (LocalRaw V)} {before : List (Definition V)}
    {stored : Definition V} (earlier : rest.erase = before)
    (same : Definition.fn hdr.key hdr.ins hdr.outs hdr.canStop hdr.kernel hdr.summary
      (eraseFn inputs body) notes = stored) :
    (Defs.fn hdr inputs body ok rest notes).erase = before ++ [stored] := by
  subst earlier
  subst same
  rfl

/-- The erasure of definitions that end with a protocol: the erasure of those before it, then
the protocol by names. -/
theorem Defs.erase_protocol {hs : Headers V} {hdr : ProtocolHeader V} {inputs : Names hdr.ins}
    {body : Prot V hs hdr inputs} {ok : ProtocolConditions hdr body} {rest : Defs V hs}
    {before : List (Definition V)} {stored : Definition V} (earlier : rest.erase = before)
    (same : Definition.protocol hdr.key hdr.roles hdr.ins hdr.outs (eraseProtocol inputs body) =
      stored) :
    (Defs.protocol hdr inputs body ok rest).erase = before ++ [stored] := by
  subst earlier
  subst same
  rfl

end

end Zkc.Core
