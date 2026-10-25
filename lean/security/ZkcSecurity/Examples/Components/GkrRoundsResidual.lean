module

public import ZkcSecurity.Examples.Components.GkrRoundsBindingInvocation

@[expose] public section
noncomputable section

/-! Charged residual falsehood for the actual Rounds verifier. The only local
probability premise is a collision bound for the actual conditional query.
An anchored prefix trace and all four factor representations survive return. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsResidual
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open OracleComp OracleSpec
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
open GkrRoundsBinding GkrRoundsRealization GkrRoundsGateRealization

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- A trace begins at the fixed caller's four factors and restricts each factor
separately under every received challenge. Coefficients are unrestricted. -/
inductive Prefix {dimension : Nat} (root : GkrRoundsBinding.State F dimension) :
    {n : Nat} → GkrRoundsBinding.State F n → Prop
  | initial : Prefix root root
  | step {n : Nat} (s : GkrRoundsBinding.State F (n + 1)) (m : F × F × F) (r : F) :
      Prefix root s → Prefix root (advance s m r)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem prefix_representation {dimension n : Nat} (root : GkrRoundsBinding.State F dimension)
    (s : GkrRoundsBinding.State F n) (represented : Represents root.raw root.reference)
    (reachedPrefix : Prefix root s) : Represents s.raw s.reference := by
  induction reachedPrefix with
  | initial => exact represented
  | step s m r _ ih => exact restriction_represents s.raw s.reference ih r

/-- The same full actual round_message/fix_gates laws apply at every verifier prefix.
Role 1 retains the separate mathematical factors while role 0 executes these
helpers. No equality with an adversarially received triple is assumed. -/
theorem prefix_helpers {dimension n : Nat} (root : GkrRoundsBinding.State F dimension)
    (s : GkrRoundsBinding.State F (n + 1)) (represented : Represents root.raw root.reference)
    (reachedPrefix : Prefix root s) (r : F) :
    invoke (GkrRoundsHelpers.table (G := G))
        GkrRoundsHelpers.roundMessageHelper s.raw.values =
      .done (.cons (GkrRoundsReference.message s.reference).constant
        (.cons (GkrRoundsReference.message s.reference).linear
          (.cons (GkrRoundsReference.message s.reference).quadratic .nil))) ∧
    invoke (GkrRoundsHelpers.table (G := G))
        GkrRoundsHelpers.gateRestrictionHelper
        (s.raw.values.append (.cons r .nil)) = .done (s.raw.restrict r).values ∧
    Represents (s.raw.restrict r) (GkrRoundsReference.restrict s.reference r) ∧
    ((GkrRoundsReference.data F).polynomial s.reference).natDegree ≤ 2 ∧
    ZkcSecurity.Families.Sumcheck.boundaryPoly ((GkrRoundsReference.data F).polynomial s.reference) =
      GkrRoundsReference.total s.reference ∧
    ((GkrRoundsReference.data F).polynomial s.reference).eval r =
      GkrRoundsReference.total (GkrRoundsReference.restrict s.reference r) :=
  helper_realization s.raw s.reference (prefix_representation root s represented reachedPrefix) r

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Residual dimension and exact point length account for every executed round. -/
theorem prefix_length {dimension n : Nat} (root : GkrRoundsBinding.State F dimension)
    (s : GkrRoundsBinding.State F n) (reachedPrefix : Prefix root s) :
    s.point.length + n = root.point.length + dimension := by
  induction reachedPrefix with
  | initial => rfl
  | @step n s m r _ ih =>
    simp only [advance, List.length_append, List.length_singleton]
    omega

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- All typed returns retain their actual restriction trace. This fact has no
sampling, boundary-success or honest-message hypothesis. -/
theorem returns_prefix (service : Nat) (ctx : ProtocolContext)
    (interaction : PIR.Interaction (participantInterface F G))
    {dimension n : Nat} (root : GkrRoundsBinding.State F dimension)
    (count : Nat) (s : GkrRoundsBinding.State F (n + count))
    (reachedPrefix : Prefix root s) (phase : interaction.Phase) :
    PIR.Boundary.Returns interaction (fun result _ => Prefix root result)
      ((program service).remaining count ctx s) phase :=
  Program.returns (program service) interaction (fun current => Prefix root current)
    (fun _ current currentPrefix m r => .step current m r currentPrefix)
    count ctx s phase reachedPrefix

/-- Residual relation on the complete returned ABI, anchored to the caller.
Private runtime outputs remain absent; their ghost factors cannot be chosen
anew after a query because Prefix starts at the fixed original state. -/
def NoReturn {dimension n : Nat} (service : Nat)
    (root : GkrRoundsBinding.State F dimension)
    (output : Values (Component (assignment F G)) spec.state) : Prop :=
  ∃ final : GkrRoundsBinding.State F n,
    Prefix root final ∧ Represents final.raw final.reference ∧
    (representation (G := G) service).No final ∧ carried (G := G) final = output

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The return relation exposes exactly the executed source count and masks,
even when the call leaves a nonzero mathematical residual dimension. -/
theorem noReturn_exact_point {n count : Nat} (service : Nat) (raw : RawState F)
    (reference : GkrRoundsReference.State F (n + count)) (claim : F)
    (output : Values (Component (assignment F G)) spec.state)
    (residual : NoReturn (n := n) service (initial raw reference claim) output) :
    ∃ point scalar, output = runtime (G := G) point scalar ∧ point.length = count := by
  rcases residual with ⟨final, reachedPrefix, _, _, carriedEq⟩
  refine ⟨final.point, final.claim, carriedEq.symm, ?_⟩
  have length := prefix_length (initial raw reference claim) final reachedPrefix
  simp only [initial, List.length_nil, zero_add] at length
  omega

def interaction : PIR.Interaction (participantInterface F G) where
  Role := Unit
  Phase := Unit
  owner _ := ()
  enabled _ _ := True
  advance _ _ _ := ()

variable {E P : Type} {Raw : E → Type}
  [∀ event, SampleableType (Raw event)]
  {absorb : Interface (participantInterface F G) E P Raw}
  {charge : List E → E → ENNReal}

/-- Substantive residual derivation: arbitrary adversarial triples, the proved
whole imported Process equation, degree-two reference laws, and a checked
actual-query collision bound. No target-truth or honest-receive premise. -/
def verifier_residual (service count : Nat) (bounded : count ≤ 4)
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F))
    {n : Nat} (raw : RawState F) (reference : GkrRoundsReference.State F (n + count))
    (claim : F) (represented : Represents raw reference)
    (wrong : claim ≠ GkrRoundsReference.total reference)
    (queries : QueryInterface (program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (representation service) 2 2 charge)
    (history : List E) :
    Derivation absorb (boundedEscape charge)
      (fun _ output => NoReturn (n := n) service (initial raw reference claim) output)
      history (protocol0Role1Process (F := F) (G := G) ctx a m l r
        (some claim) (some count) (some service)) := by
  let root := initial raw reference claim
  have no : (representation (G := G) service).No root := ⟨represented.2.1, wrong⟩
  have base := Consumers.residual (representation (G := G) service)
    Message.coefficientTriples_laws GkrRoundsReference.laws queries sampling count ctx root history no
  have framed := base.frameReturns (interaction (F := F) (G := G))
    (fun final => Prefix root final) ()
    (returns_prefix service ctx (interaction (F := F) (G := G)) root count root .initial ())
  have projected : Derivation absorb (boundedEscape charge)
      (fun _ output => NoReturn (n := n) service root output) history
      (((program service).remaining count ctx root).bind (fun final => .done (carried (G := G) final))) :=
    framed.bind (fun final => .done (carried (G := G) final))
    (fun reached final holds => .done
      ⟨final, holds.2, prefix_representation root final represented holds.2, holds.1, rfl⟩)
  exact projected.transport (verifier_binding ctx distinct a m l r claim service count bounded raw reference)

theorem verifier_doomed (service count : Nat) (bounded : count ≤ 4)
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F))
    {n : Nat} (raw : RawState F) (reference : GkrRoundsReference.State F (n + count))
    (claim : F) (represented : Represents raw reference)
    (wrong : claim ≠ GkrRoundsReference.total reference)
    (queries : QueryInterface (program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (representation service) 2 2 charge)
    (history : List E) :
    (reduction absorb
      (fun _ output => NoReturn (n := n) service (initial raw reference claim) output) charge).doomed
      history (protocol0Role1Process (F := F) (G := G) ctx a m l r
        (some claim) (some count) (some service)) :=
  derived_doomed (verifier_residual service count bounded ctx distinct a m l r raw reference claim
    represented wrong queries sampling history)

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Uniform specialization is a theorem only after the actual raw sampler's
pushforward law is checked. The charged step is exactly 2 / |F|. -/
theorem conditional_uniform [Fintype F] [SampleableType F]
    (service : Nat) (queries : QueryInterface (program (F := F) (G := G) service) absorb)
    (uniform : ∀ {k} (ctx : ProtocolContext) (s : GkrRoundsBinding.State F (k + 1)) m (predicate : F → Prop),
      Pr{let raw ← $ᵗ (Raw (queries.event ctx s m))}[
        predicate (queries.challenge ctx s m raw)] =
      Pr{let r ← $ᵗ F}[predicate r]) :
    queries.ConditionalBound (representation service) 2 2
      (fun _ _ => 2 / (Fintype.card F : ENNReal)) := by
  intro k ctx s allowed m history p q different left right
  simpa only [max_self, Nat.cast_ofNat] using
    queries.conditional_of_uniform (representation service) 2 2 uniform ctx s allowed m history p q
      different left right

/-- The same actual verifier derivation at the uniform degree-two charge.
Only the raw query's pushforward law is specialized; no honest coefficient
policy or circuit terminal predicate is introduced. -/
def verifier_uniform_residual [Fintype F] [SampleableType F]
    (service count : Nat) (bounded : count ≤ 4)
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F))
    {n : Nat} (raw : RawState F) (reference : GkrRoundsReference.State F (n + count))
    (claim : F) (represented : Represents raw reference)
    (wrong : claim ≠ GkrRoundsReference.total reference)
    (queries : QueryInterface (program (F := F) (G := G) service) absorb)
    (uniform : ∀ {k} (ctx : ProtocolContext) (s : GkrRoundsBinding.State F (k + 1)) m (predicate : F → Prop),
      Pr{let raw ← $ᵗ (Raw (queries.event ctx s m))}[
        predicate (queries.challenge ctx s m raw)] = Pr{let r ← $ᵗ F}[predicate r])
    (history : List E) :
    Derivation absorb (boundedEscape (fun _ _ => 2 / (Fintype.card F : ENNReal)))
      (fun _ output => NoReturn (n := n) service (initial raw reference claim) output)
      history (protocol0Role1Process (F := F) (G := G) ctx a m l r
        (some claim) (some count) (some service)) :=
  verifier_residual service count bounded ctx distinct a m l r raw reference claim represented wrong queries
    (conditional_uniform service queries uniform) history

end ZkcSecurity.Examples.Components.GkrRoundsResidual
