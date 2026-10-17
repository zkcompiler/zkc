module

public import Zkc.Source.Structured.LogicalFrames
public import ZkcExamples.Structured.SumcheckProverRoots
public import Zkc.Protocols.Sumcheck.Multilinear.Fold

@[expose] public section

/-! The prover's per-round fold invariant on the imported Reduce callback.

The original table is one port-independent logical binder of a library sort.
The prover's current table, its remaining dimension, width and received point
are carried slots of the Reduce repeat, observed in loop frames at the prover.
At every frame the loop reaches, the carried point is exactly the challenges
received so far, the carried entries represent the partial evaluation of the
original table at that point, and their two half sums are the endpoints of the
correct round polynomial. The step obligation is discharged on `bodyFn`, the
typed callback whose erasure is each unit's checked Reduce body (`reduce_raw`,
`reduce_raw_shared`); the round messages are the prover's actual sends. The
binder is the decoding of the prover's own input table: this agreement is an
explicit premise, never inferred from a port. -/
namespace ZkcExamples.Structured.SumcheckFoldInvariant
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical PrimitiveLibrary
open SumcheckVerifierBodies SumcheckVerifierHelpers SumcheckVerifierLaws SumcheckProverLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear (PartialEvaluation roundEndpoint)

-- Interpretation meanings compute dependent sort and value types.
set_option backward.isDefEq.respectTransparency false

/-- Library sorts: multilinear tables over the scalar domain, by arity. -/
inductive FoldSort where
  | table (dimension : Nat)
  deriving DecidableEq

inductive FoldPredicate where
  | partialEvaluation (dimension : Nat)
  | remaining (dimension : Nat)
  | unitWidth
  | roundMessage (dimension : Nat)
  deriving DecidableEq

/-- Identities carry every static argument; the table sort, the partial
evaluation and the round message also carry the scalar domain. There are no views. -/
def vocabulary : Vocabulary where
  Sorts := FoldSort
  Predicates := FoldPredicate
  Views := Empty
  sortIdentity
    | .table dimension => ⟨"zkc::multilinear::logic::Polynomial", [.domain "bls12-381.fr", .nat dimension]⟩
  predicateIdentity
    | .partialEvaluation dimension =>
      ⟨"zkc::multilinear::logic::PartialEvaluation", [.domain "bls12-381.fr", .nat dimension]⟩
    | .remaining dimension => ⟨"zkc::multilinear::logic::Remaining", [.nat dimension]⟩
    | .unitWidth => ⟨"zkc::multilinear::logic::UnitWidth", []⟩
    | .roundMessage dimension =>
      ⟨"sumcheck::logic::RoundMessage", [.domain "bls12-381.fr", .nat dimension]⟩
  viewIdentity view := nomatch view
  arguments
    | .partialEvaluation dimension => [.sort (.table dimension), .native vector, .native vector]
    | .remaining _ => [.native vector, .native .index]
    | .unitWidth => [.native .index]
    | .roundMessage dimension => [.sort (.table dimension), .native vector, .native vector]
  viewInput view := nomatch view
  viewOutput view := nomatch view

variable {F G : Type} [CommRing F]

/-- `partialEvaluation` is the represented partial evaluation; `roundMessage`
says that the two ordered half sums of the entries are the endpoints of the
correct round polynomial whenever a round remains. -/
def interpretation (F G : Type) [CommRing F] : Interpretation vocabulary (assignment F G) where
  sorts
    | .table dimension => Table F dimension
  holds
    | .partialEvaluation _, .cons table (.cons point (.cons entries .nil)) =>
      PartialEvaluation table point entries
    | .remaining count, .cons point (.cons dimension .nil) =>
      point.length ≤ count ∧ dimension = count - point.length
    | .unitWidth, .cons width .nil => width = (1 : Nat)
    | .roundMessage count, .cons table (.cons point (.cons entries .nil)) =>
      point.length < count →
        (entries.take (entries.length / 2)).sum = roundEndpoint table point 0 ∧
          (entries.drop (entries.length / 2)).sum = roundEndpoint table point 1
  view v := nomatch v

/-- One table binder, the original table. -/
abbrev tableContext (dimension : Nat) : List (LogicalType vocabulary.Sorts) :=
  [.sort (.table dimension)]

abbrev original (dimension : Nat) : Var (tableContext dimension) (.sort (.table dimension)) := .here

/-- The prover's carried slots of the Reduce repeat. -/
abbrev entriesSlot : Var repeatState (.vector "bls12-381.fr") := .here
abbrev dimensionSlot : Var repeatState .index := .there .here
abbrev widthSlot : Var repeatState .index := .there (.there .here)
abbrev pointSlot : Var repeatState (.vector "bls12-381.fr") := .there (.there (.there .here))

/-- The fold invariant: four atoms over the original table and carried slots. -/
def proverInvariant (count : Nat) :
    FrameInvariant vocabulary (assignment F G) repeatState (tableContext count) :=
  [⟨.partialEvaluation count, .cons (.binder (original count))
      (.cons (.carried pointSlot) (.cons (.carried entriesSlot) .nil))⟩,
   ⟨.remaining count, .cons (.carried pointSlot) (.cons (.carried dimensionSlot) .nil)⟩,
   ⟨.unitWidth, .cons (.carried widthSlot) .nil⟩,
   ⟨.roundMessage count, .cons (.binder (original count))
      (.cons (.carried pointSlot) (.cons (.carried entriesSlot) .nil))⟩]

/-- The index slot of `assignment` is a natural number. -/
abbrev indexValue : Nat → assignment F G .index := id

/-- The owner's binder values: only the original table. -/
def tableBinders (count : Nat) (table : Table F count) :
    Values (interpretation F G).Denote (tableContext count) :=
  .cons (show (interpretation F G).Denote (.sort (.table count)) from table) .nil

/-- The invariant at one frame, for the original table `table`. -/
abbrev Holds (count : Nat) (table : Table F count) (index : Nat)
    (state : Values (Component (assignment F G)) repeatState) : Prop :=
  (proverInvariant (F := F) (G := G) count).Holds (interpretation F G) indexValue
    (tableBinders count table) ⟨index, state⟩

variable [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Every honest state whose point fits the dimension satisfies the invariant. -/
theorem holds_honest (raw : List F) (count : Nat) (table : Table F count)
    (decoded : ofList? count raw = some table) (point : List F) (fits : point.length ≤ count) :
    Holds count table point.length (embedP (G := G) (honestState raw count point)) := by
  have represents := Zkc.Protocols.Sumcheck.Multilinear.partialEvaluation_restrict raw table decoded
    point fits
  intro atom member
  simp only [proverInvariant, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, represents⟩
  · refine ⟨_, rfl, ?_⟩
    show point.length ≤ count ∧ count - point.length = count - point.length
    exact ⟨fits, rfl⟩
  · refine ⟨_, rfl, ?_⟩
    show (1 : Nat) = 1
    rfl
  · refine ⟨_, rfl, ?_⟩
    exact fun remaining =>
      Zkc.Protocols.Sumcheck.Multilinear.partialEvaluation_endpoints table point _ represents remaining

/-- The phase records, in order, the challenges the prover has received at the
delivery site of `ctx`. Sends and other actions leave it unchanged. -/
def receivedChallenges (ctx : ProtocolContext) : PIR.Interaction (participantInterface F G) where
  Role := Unit
  Phase := List F
  owner _ := ()
  enabled _ _ := True
  advance phase action reply :=
    match action, reply with
    | .receive (.field _) site _, (challenge : F) =>
      if site = deliverySite ctx then phase ++ [challenge] else phase
    | _, _ => phase

/-- The frame reached after `index` iterations is the honest state of exactly
the challenges received so far. -/
def HonestFrame (raw : List F) (count index : Nat) (received : List F)
    (state : Values (Component (assignment F G)) repeatState) : Prop :=
  received.length = index ∧ index ≤ count ∧ state = embedP (honestState raw count received)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- One honest round either stops or returns the received point extended by the
challenge it receives, still within the dimension. -/
theorem roundHonest_received (ctx : ProtocolContext) (raw : List F) (count : Nat) (point : List F) :
    PIR.Boundary.Returns (receivedChallenges (G := G) ctx)
      (fun result received => result = received ∧ result.length = point.length + 1 ∧
        result.length ≤ count)
      (roundHonest ctx raw count point) point := by
  unfold roundHonest
  by_cases remaining : point.length < count
  · simp only [remaining, ↓reduceIte, SumcheckProverLaws.roundPresent, PIR.Proc.bind,
      PIR.Boundary.Returns]
    intro _ _ cp
    simp only [receivedChallenges, ↓reduceIte, honestState, List.length_append,
      List.length_singleton]
    exact ⟨trivial, trivial, remaining⟩
  · simp only [remaining, ↓reduceIte, PIR.Boundary.Returns]

/-- The fold invariant on the imported Reduce callback at the prover: after
any number of iterations, the frame the loop reaches is the honest state of
exactly the challenges it received, and it satisfies every atom. Starting from no received challenge, the phase is the received point.
The binder is the decoding of the prover's own input table. -/
theorem prover_frames (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self) (maximum : Nat) (service : Option Nat)
    (raw : List F) (count : Nat) (shape : HasShape raw count 1) (bound : raw.length < indexLimit)
    (table : Table F count) (decoded : ofList? count raw = some table) (iterations : Nat) :
    PIR.Boundary.Returns (receivedChallenges (G := G) ctx)
      (fun state received => HonestFrame raw count iterations received state ∧
        Holds count table iterations state)
      (Repeat.loop (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self) 0 iterations
        (embedP (G := G) (honestState raw count []))) [] := by
  have exact := Repeat.loop_frames (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self)
    (receivedChallenges (F := F) (G := G) ctx)
    (fun index state (received : List F) => HonestFrame raw count index received state)
    (by
      intro index state received valid
      obtain ⟨length, _, rfl⟩ := valid
      rw [step_honest U bodies ctx self prover separate maximum service raw count shape bound
        received index]
      apply PIR.Boundary.returns_bind (receivedChallenges (F := F) (G := G) ctx) _ _
        (fun result next => result = next ∧ result.length = received.length + 1 ∧
          result.length ≤ count)
      · exact roundHonest_received ctx raw count received
      · intro result next ⟨same, extended, fits⟩
        subst next
        exact ⟨by omega, by omega, rfl⟩)
    0 iterations (embedP (honestState raw count [])) [] ⟨rfl, Nat.zero_le _, rfl⟩
  apply PIR.Boundary.returns_mono (receivedChallenges (F := F) (G := G) ctx) _ _ _ _ exact
  intro state received valid
  rw [Nat.zero_add] at valid
  refine ⟨valid, ?_⟩
  obtain ⟨length, fits, rfl⟩ := valid
  rw [← length]
  exact holds_honest raw count table decoded received (by omega)

/-- The round messages on the actual callback: from a frame in the honest form
with a round remaining, the prover's two actual sends are the endpoints of the
correct round polynomial, and the delivered challenge yields the next honest
frame. -/
theorem prover_messages (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
    (ctx : ProtocolContext) (self : Nat) (prover : self = ctx.roles 0)
    (separate : ctx.roles 1 ≠ self) (maximum : Nat) (service : Option Nat)
    (raw : List F) (count : Nat) (shape : HasShape raw count 1) (bound : raw.length < indexLimit)
    (table : Table F count) (decoded : ofList? count raw = some table)
    (point : List F) (remaining : point.length < count) (index : Nat) :
    Repeat.step (repeatSpec maximum) ctx self (cap service) (bodyFn U ctx self)
      (embedP (G := G) (honestState raw count point)) index =
      .call (.send (ty := .field "bls12-381.fr") (lowSite ctx) (ctx.roles 1)
        (roundEndpoint table point 0)) fun _ =>
      .call (.send (ty := .field "bls12-381.fr") (highSite ctx) (ctx.roles 1)
        (roundEndpoint table point 1)) fun _ =>
      .call (.receive (.field "bls12-381.fr") (deliverySite ctx) (ctx.roles 1)) fun (cp : F) =>
      .done (embedP (honestState raw count (point ++ [cp]))) := by
  have endpoints := Zkc.Protocols.Sumcheck.Multilinear.partialEvaluation_endpoints table point _
    (Zkc.Protocols.Sumcheck.Multilinear.partialEvaluation_restrict raw table decoded point
      (Nat.le_of_lt remaining)) remaining
  rw [step_honest U bodies ctx self prover separate maximum service raw count shape bound point index]
  simp only [roundHonest, remaining, ↓reduceIte, SumcheckProverLaws.roundPresent, PIR.Proc.bind,
    honestState]
  rw [← endpoints.1, ← endpoints.2]

/-! ### The two complete units -/

/-- The fold invariant at the prover of the complete Source unit's Reduce. -/
theorem source_frames (raw : List F) (count : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (table : Table F count) (decoded : ofList? count raw = some table)
    (iterations : Nat) :
    PIR.Boundary.Returns (receivedChallenges (G := G) SumcheckSourceVerifier.childContext)
      (fun state received => HonestFrame raw count iterations received state ∧
        Holds count table iterations state)
      (Repeat.loop (repeatSpec 2) SumcheckSourceVerifier.childContext 0 (cap none)
        (bodyFn SumcheckSourceViews.unit SumcheckSourceVerifier.childContext 0) 0 iterations
        (embedP (G := G) (honestState raw count []))) [] :=
  prover_frames SumcheckSourceViews.unit SumcheckSourceContracts.bodies
    SumcheckSourceVerifier.childContext 0 rfl (by decide) 2 none raw count shape bound table decoded
    iterations

/-- The fold invariant at the prover of the complete Reduction unit's Reduce. -/
theorem reduction_frames (raw : List F) (count : Nat) (shape : HasShape raw count 1)
    (bound : raw.length < indexLimit) (table : Table F count) (decoded : ofList? count raw = some table)
    (iterations : Nat) :
    PIR.Boundary.Returns (receivedChallenges (G := G) (ProtocolContext.enter {} "s3" [0, 1]))
      (fun state received => HonestFrame raw count iterations received state ∧
        Holds count table iterations state)
      (Repeat.loop (repeatSpec 4) (ProtocolContext.enter {} "s3" [0, 1]) 0 (cap none)
        (bodyFn SumcheckReduceViews.unit (ProtocolContext.enter {} "s3" [0, 1]) 0) 0 iterations
        (embedP (G := G) (honestState raw count []))) [] :=
  prover_frames SumcheckReduceViews.unit SumcheckReduceContracts.bodies
    (ProtocolContext.enter {} "s3" [0, 1]) 0 rfl (by decide) 4 none raw count shape bound table
    decoded iterations

/-! ### Exported frame metadata -/

instance : DecidableEq vocabulary.Sorts := inferInstanceAs (DecidableEq FoldSort)

def partialIdentity (dimension : Nat) : Identity :=
  ⟨"zkc::multilinear::logic::PartialEvaluation", [.domain "bls12-381.fr", .nat dimension]⟩
def remainingIdentity (dimension : Nat) : Identity :=
  ⟨"zkc::multilinear::logic::Remaining", [.nat dimension]⟩
def widthIdentity : Identity := ⟨"zkc::multilinear::logic::UnitWidth", []⟩
def roundIdentity (dimension : Nat) : Identity :=
  ⟨"sumcheck::logic::RoundMessage", [.domain "bls12-381.fr", .nat dimension]⟩

def sortCandidate (identity : Identity) : Option FoldSort :=
  match identity.statics with
  | [_, .nat dimension] => some (.table dimension)
  | _ => none

def predicateCandidate (identity : Identity) : Option FoldPredicate :=
  match identity.declaration, identity.statics with
  | "zkc::multilinear::logic::PartialEvaluation", [_, .nat dimension] =>
    some (.partialEvaluation dimension)
  | "sumcheck::logic::RoundMessage", [_, .nat dimension] => some (.roundMessage dimension)
  | _, [.nat dimension] => some (.remaining dimension)
  | _, [] => some .unitWidth
  | _, _ => none

/-- Candidates are accepted only when their full identity matches. -/
def resolution : Resolution vocabulary :=
  .ofCandidates vocabulary sortCandidate predicateCandidate

/-- The fold invariant in the proposed export form, written in Lean: the Reduce
repeat at site `s15`, observed at local role 0 (the prover), with carried slots
named by position. No compiler exporter produces it yet. -/
def frameExport (count : Nat) : RawFrame where
  site := "s15"
  role := 0
  atoms := [⟨partialIdentity count, [.binder 0, .carried 3, .carried 0]⟩,
    ⟨remainingIdentity count, [.carried 3, .carried 1]⟩,
    ⟨widthIdentity, [.carried 2]⟩,
    ⟨roundIdentity count, [.binder 0, .carried 3, .carried 0]⟩]

/-- The Reduction unit's actual Reduce body has its repeat at site `s15`, with
maximum four; the Source unit's has maximum two. -/
theorem reduction_repeat :
    repeatAt SumcheckReduceViews.reduceDefinition.raw.operations "s15" = some (repeatSpec 4) := by
  decide +kernel

theorem source_repeat :
    repeatAt SumcheckSourceViews.reduceDefinition.raw.operations "s15" = some (repeatSpec 2) := by
  decide +kernel

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- For every dimension, the exported frame checks against the actual Reduction
body's own repeat occurrence to exactly the invariant proved on its callback. -/
theorem frame_export_checks (count : Nat) :
    checkFrame (Value := assignment F G) resolution
      (repeatAt SumcheckReduceViews.reduceDefinition.raw.operations) (tableContext count)
      (frameExport count) = .ok ⟨repeatSpec 4, proverInvariant count⟩ := by
  simp only [checkFrame]
  simp [checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, frameExport,
    partialIdentity, remainingIdentity, widthIdentity, roundIdentity, vocabulary,
    decode_first_binder, bind, Except.bind, pure, Except.pure]
  rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The same export checks against the actual Source body's repeat occurrence. -/
theorem source_frame_export_checks (count : Nat) :
    checkFrame (Value := assignment F G) resolution
      (repeatAt SumcheckSourceViews.reduceDefinition.raw.operations) (tableContext count)
      (frameExport count) = .ok ⟨repeatSpec 2, proverInvariant count⟩ := by
  simp only [checkFrame]
  simp [checkFrameAtoms, checkFrameAtom, checkFrameTerms, checkFrameTerm, resolution,
    Resolution.ofCandidates, sortCandidate, predicateCandidate, frameExport,
    partialIdentity, remainingIdentity, widthIdentity, roundIdentity, vocabulary,
    decode_first_binder, bind, Except.bind, pure, Except.pure]
  rfl

end ZkcExamples.Structured.SumcheckFoldInvariant
