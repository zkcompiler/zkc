module

public import ZkcExamples.Structured.SumcheckVerifierProcess
public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import Zkc.Source.Structured.RepeatLaws
public import Zkc.Source.DenotationLaws
public import ZkcExamples.Structured.SumcheckRoundNormalForms

@[expose] public section

/-! The plain verifier process of the entire retained callback. The normal form
below is derived from that body, including its calculated guard, append and
interpolation. Its action replies are arbitrary; no provider law is assumed. -/
namespace ZkcExamples.Structured.SumcheckVerifierLaws
open Zkc.Source Zkc.Source.Structured
open SumcheckVerifierBodies SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The two optional verifier components occupy the actual last two slots. -/
def embedV (pc : Option (List F) × Option F) :
    Values (Component (assignment F G)) repeatState :=
  .cons none (.cons none (.cons none (.cons none (.cons pc.1 (.cons pc.2 .nil)))))

def cap (service : Option Nat) :
    Values (Component (assignment F G)) [.service "random.bls12-381.fr/0"] :=
  .cons service .nil

/-- The existing Region interpreter, using this unit's own complete tables. -/
def bodyFn (U : UnitPayload) (ctx : ProtocolContext) (self : Nat) :
    RegionFunction (Component (assignment F G)) (participantInterface F G)
      (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"]), repeatState) :=
  fun args => roundBody.denote
    (participantMeaningWith (.silent _) (participantActions F G)
      (plainHelpers U) self (U.plainProtocolTable F G) ctx) args.get

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem mask_embedV (ctx : ProtocolContext) (self : Nat)
    (verifier : self = ctx.roles 1) (maximum : Nat) (pc : Option (List F) × Option F) :
    maskValues self (ctx.mapScopes (repeatSpec maximum).stateScopes) (embedV (G := G) pc) =
      embedV pc :=
  SumcheckRoundNormalForms.verifierState_masked ctx self verifier pc.1 pc.2

/-- The callback at the verifier, for every presence of its carried state and
service: the generated normal form of the literal body. -/
theorem round_body_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (index : Nat) (service : Option Nat)
    (pc : Option (List F) × Option F) :
    bodyFn U ctx self (.cons (some index) ((embedV (G := G) pc).append (cap service))) =
      (roundPlain ctx service pc).bind (fun result => .done (embedV result)) :=
  SumcheckRoundNormalForms.verifier_process U bodies ctx self verifier separate index service pc.1 pc.2

/-- Each iteration uses the same immutable context and service capture. -/
theorem round_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (maximum index : Nat) (service : Option Nat)
    (pc : Option (List F) × Option F) :
    Repeat.step (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self)
      (embedV (G := G) pc) index =
      (roundPlain ctx service pc).bind (fun result => .done (embedV result)) := by
  unfold Repeat.step
  rw [mask_embedV ctx self verifier maximum pc]
  rw [round_body_optional U bodies ctx self verifier separate]
  simp only [PIR.Proc.bind_assoc, PIR.Proc.bind, mask_embedV ctx self verifier maximum]

/-- Arbitrary finite residual count and starting index, without re-admission. -/
theorem loop_optional (U : UnitPayload) (bodies : Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (verifier : self = ctx.roles 1)
    (separate : ctx.roles 0 ≠ self) (start count maximum : Nat) (service : Option Nat)
    (pc : Option (List F) × Option F) :
    Repeat.loop (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self)
      start count (embedV (G := G) pc) =
      (PIR.repeatN count (roundPlain ctx service) pc).bind
        (fun result => .done (embedV result)) := by
  refine (Repeat.loop_embed (F := F) (G := G) (repeatSpec maximum) ctx self
    (cap service) (bodyFn U ctx self) (embedV (F := F) (G := G))
    (fun value _ => roundPlain ctx service value) start count pc
    (fun value index => round_optional U bodies ctx self verifier separate maximum index service value)).trans ?_
  rw [Finite.fold_range_repeatN]



end ZkcExamples.Structured.SumcheckVerifierLaws
