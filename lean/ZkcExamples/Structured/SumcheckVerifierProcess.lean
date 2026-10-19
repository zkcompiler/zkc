module

public import Zkc.Source.Structured.Participant
public import Zkc.Semantics.Boundary

@[expose] public section

/-! The single plain process contract shared by the complete-source verifier
proofs and independent consumers. Replies and service behavior are unrestricted.
Literal source association is proved separately in SumcheckVerifierLaws. -/
namespace ZkcExamples.Structured.SumcheckVerifierLaws
open Zkc.Source Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The qualified source action routes, shared by the process and its consumers. -/
abbrev lowSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_0"

abbrev highSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_726f756e64_1"

abbrev challengeSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_6368616c6c656e6765"

abbrev deliverySite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix "label_64656c6976657279_0"

/-- Exact expansion target: LOW, HIGH, calculated guard, captured-service query,
delivery, actual append, then calculated interpolation. -/
def roundPlain (ctx : ProtocolContext) (service : Option Nat)
    (pc : Option (List F) × Option F) :
    PIR.Proc (participantInterface F G) (Option (List F) × Option F) :=
  .call (.receive (.field "bls12-381.fr")
    (lowSite ctx) (ctx.roles 0)) fun (lo : F) =>
  .call (.receive (.field "bls12-381.fr")
    (highSite ctx) (ctx.roles 0)) fun (hi : F) =>
  match pc.2 with
  | none => .halt .incomplete
  | some claim =>
    if claim = lo + hi then
      match service with
      | none => .halt .incomplete
      | some handle =>
        .call (.query (challengeSite ctx)
          "bls12-381.fr" (.cons handle .nil)) fun (cv : F) =>
        .call (.send (ty := .field "bls12-381.fr")
          (deliverySite ctx)
          (ctx.roles 0) cv) fun _ =>
        match pc.1 with
        | none => .halt .incomplete
        | some point => .done (some (point ++ [cv]), some ((1 - cv) * lo + cv * hi))
    else .halt .reject

/-- A present-state view of the same four calls and calculated values. -/
def roundPresent (ctx : ProtocolContext) (handle : Nat) (pc : List F × F) :
    PIR.Proc (participantInterface F G) (List F × F) :=
  .call (.receive (.field "bls12-381.fr")
    (lowSite ctx) (ctx.roles 0)) fun (lo : F) =>
  .call (.receive (.field "bls12-381.fr")
    (highSite ctx) (ctx.roles 0)) fun (hi : F) =>
  if pc.2 = lo + hi then
    .call (.query (challengeSite ctx)
      "bls12-381.fr" (.cons handle .nil)) fun (cv : F) =>
    .call (.send (ty := .field "bls12-381.fr")
      (deliverySite ctx)
      (ctx.roles 0) cv) fun _ =>
    .done (pc.1 ++ [cv], (1 - cv) * lo + cv * hi)
  else .halt .reject

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem round_present (ctx : ProtocolContext) (handle : Nat) (pc : List F × F) :
    roundPlain (G := G) ctx (some handle) (some pc.1, some pc.2) =
      (roundPresent ctx handle pc).bind (fun result => .done (some result.1, some result.2)) := by
  simp only [roundPlain, roundPresent, PIR.Proc.bind]
  congr 1
  funext lo
  congr 1
  funext hi
  split <;> rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Arbitrary-count iteration of the same source process on present state.
Every call and stop is retained; this is a process equality, not a provider law. -/
theorem repeat_present (ctx : ProtocolContext) (handle count : Nat) (pc : List F × F) :
    PIR.repeatN count (roundPlain (G := G) ctx (some handle)) (some pc.1, some pc.2) =
      (PIR.repeatN count (roundPresent ctx handle) pc).bind
        (fun result => .done (some result.1, some result.2)) := by
  induction count generalizing pc with
  | zero => rfl
  | succ count ih =>
    simp only [PIR.repeatN, round_present, PIR.Proc.bind_assoc, PIR.Proc.bind]
    congr 1
    funext result
    exact ih result

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- A successful source round appends one actual query reply and returns both
verifier values present, for every interface-typed reply and every phase. -/
theorem round_returns (P : PIR.Interaction (participantInterface F G))
    (ctx : ProtocolContext) (service : Option Nat) (point : List F) (claim : Option F)
    (phase : P.Phase) :
    PIR.Boundary.Returns P (fun result _ =>
      ∃ next value, result = (some next, some value) ∧ next.length = point.length + 1)
      (roundPlain ctx service (some point, claim)) phase := by
  simp only [roundPlain, PIR.Boundary.Returns]
  intro lo hi
  cases claim with
  | none => trivial
  | some value =>
    dsimp only
    split
    · cases service with
      | none => trivial
      | some handle =>
        refine fun (cv : F) (_ : Unit) => ?_
        exact ⟨point ++ [cv], (1 - cv) * lo + cv * hi, rfl, by simp⟩
    · trivial

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Successful finite iteration preserves point presence and counts actual
appends. Zero retains the optional claim; a positive return has a claim. -/
theorem repeat_returns (P : PIR.Interaction (participantInterface F G))
    (ctx : ProtocolContext) (service : Option Nat) (count : Nat)
    (point : List F) (claim : Option F) (phase : P.Phase) :
    PIR.Boundary.Returns P (fun result _ =>
      ∃ next, result.1 = some next ∧ next.length = point.length + count ∧
        (count = 0 → result.2 = claim) ∧ (0 < count → result.2.isSome = true))
      (PIR.repeatN count (roundPlain ctx service) (some point, claim)) phase := by
  induction count generalizing point claim phase with
  | zero => exact ⟨point, rfl, by omega, fun _ => rfl, by omega⟩
  | succ count ih =>
    apply PIR.Boundary.returns_bind P _ _
      (fun result _ => ∃ next value,
        result = (some next, some value) ∧ next.length = point.length + 1)
    · exact round_returns P ctx service point claim phase
    · intro result nextPhase returned
      obtain ⟨next, value, rfl, length⟩ := returned
      apply PIR.Boundary.returns_mono P _ _ _ _ (ih next (some value) nextPhase)
      intro result finalPhase returned
      obtain ⟨last, present, lastLength, zeroClaim, positiveClaim⟩ := returned
      refine ⟨last, present, by omega, by omega, ?_⟩
      intro _
      cases count with
      | zero => simp only [zeroClaim rfl, Option.isSome_some]
      | succ count => exact positiveClaim (Nat.zero_lt_succ _)


end ZkcExamples.Structured.SumcheckVerifierLaws
