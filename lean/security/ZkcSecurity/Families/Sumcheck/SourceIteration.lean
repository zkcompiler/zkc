module

public import ZkcSecurity.Families.Sumcheck.SourceRound
public import ZkcSecurity.Families.Sumcheck.TableComponentNominal
public import ZkcSecurity.Obligations.RepeatedComponent

@[expose] public section

/-! Mathematical contracts for symbolic repetition of the actual typed callback.
The carried object retains every source slot, the reached index and arbitrary
caller-frame data. The representation is the existing prefix-table family;
its existence never implies scalar truth. No compiled execution is defined here.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ZkcSecurity.Families.Sumcheck.SourceIteration
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation
open TableComponent
open OracleComp OracleSpec

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField

structure Runtime (Frame : Type) where
  index : Nat
  slots : Values (Component model.Value) SumcheckVerifierBodies.repeatState
  callerFrame : Frame

variable {Frame E P : Type} {Raw : E → Type}

/-- Readback keeps the full runtime; the original table is mathematical data. -/
def encode {n : Nat} (index : Nat) (reference : PrefixState (model.Field field) Frame n) :
    Runtime model Frame :=
  ⟨index, state model (some reference.point) (some reference.scalar), reference.frame⟩

abbrev layout := TableComponent.Nominal.layout (F := model.Field field) (Frame := Frame) field

/-- Exact source callback with its own input index and unchanged callerFrame suffix. -/
def roundStep (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (handle : Nat) (runtime : Runtime model Frame) :
    PIR.Process (Occurrence.signature model.toCarriers) (Runtime model Frame) :=
  (SumcheckVerifierBodies.roundBody.denote
    (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
      (ctx.roles 1) protocols ctx Occurrence.iterations)
    (Values.cons (some runtime.index) (runtime.slots.append (.cons (some handle) .nil))).get).bind
      fun returned => .done ⟨runtime.index + 1, returned, runtime.callerFrame⟩

def repeatSite (ctx : ProtocolContext) : String :=
  qualifyProtocolSite ctx.applicationPrefix SumcheckVerifierBodies.repeatSite

def step (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (handle : Nat) (runtime : Runtime model Frame) :
    PIR.Process (Occurrence.signature model.toCarriers) (Runtime model Frame) :=
  Occurrence.iterations.within (repeatSite ctx) runtime.index
    (roundStep model definitions protocols ctx handle runtime)

/-- Iteration boundaries are read explicitly, including the reached index. -/
structure Boundaries (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (ctx : ProtocolContext) where
  enter : Nat → E
  leave : Nat → E
  entered : ∀ index, absorb (.enter ⟨repeatSite ctx, index⟩) = .send (enter index) ()
  left : ∀ index, absorb (.leave ⟨repeatSite ctx, index⟩) = .send (leave index) ()

/-- This relation is fixed mathematics; the component has no logical evaluator. -/
def sumRelation : ClaimRelation (List (model.Field field) × model.Field field) Unit :=
  ClaimRelation.exact (fun statement _ => statement.2 = statement.1.sum)

def view (original : List (model.Field field)) (runtime : Runtime model Frame) :
    Option (List (model.Field field) × model.Field field) := do
  let point ← runtime.slots.get (.there (.there (.there (.there .here))))
  let scalar ← runtime.slots.get (.there (.there (.there (.there (.there .here)))))
  pure (Zkc.Polynomial.Multilinear.restrictPrefixValues original point, scalar)

def component (definitions : List CheckedDefinition)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (handle : Nat) :
    ComponentInterface (Occurrence.signature model.toCarriers) E (Runtime model Frame) (Runtime model Frame) where
  Parameters := List (model.Field field)
  Input := List (model.Field field) × model.Field field
  InputWitness := Unit
  Output := List (model.Field field) × model.Field field
  OutputWitness := Unit
  input := sumRelation model
  output := sumRelation model
  body := step model definitions protocols ctx handle
  Scope _ _ _ := True
  inputView := fun original runtime _ => view model original runtime
  outputView := fun original _ _ runtime => view model original runtime

/-- Full shape and arbitrary callerFrame suffix, independent of Yes and No. -/
def represented (original : List (model.Field field)) (callerFrame : Frame)
    (n : Nat) (runtime : Runtime model Frame) : Prop :=
  ∃ reference : PrefixState (model.Field field) Frame n,
    reference.original = original ∧ reference.frame = callerFrame ∧
      runtime = encode model runtime.index reference

def no (original : List (model.Field field)) (callerFrame : Frame)
    (_history : List E) (n : Nat) (runtime : Runtime model Frame) : Prop :=
  ∃ reference : PrefixState (model.Field field) Frame n,
    reference.original = original ∧ reference.frame = callerFrame ∧
      runtime = encode model runtime.index reference ∧ (layout model).representation.No reference

variable (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
  (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
  (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
  (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2) (handle : Nat)

include linked bodies distinct

/-- The only source/reference equation is derived from the installed exact body
and normal form. Both consumers below use this same theorem. -/
theorem round_reference {n : Nat} (index : Nat)
    (reference : PrefixState (model.Field field) Frame (n+1)) :
    roundStep model definitions protocols ctx handle (encode model index reference) =
      (SumcheckReferenceInstallation.reference model ctx (some handle)
        (some reference.point) (some reference.scalar)).bind fun returned =>
          .done ⟨index+1, returned, reference.frame⟩ := by
  unfold roundStep
  have source := body_reference model definitions linked bodies protocols ctx distinct index
    (some reference.point) (some reference.scalar) (some handle)
  exact congrArg (fun process => process.bind fun returned =>
    .done (Runtime.mk (index+1) returned reference.frame)) source

/-- Every typed reply preserves the original table, shape and complete frame.
A failing boundary halts; no honest-message hypothesis is used. -/
theorem frame_contract (original : List (model.Field field)) (callerFrame : Frame) :
    RepeatedComponent.FrameContract
      (component (E := E) model definitions protocols ctx handle)
      (represented model original callerFrame) := by
  intro n runtime valid
  obtain ⟨reference, same, retained, encoded⟩ := valid
  rw [encoded]
  change PIR.Yields _ (step model definitions protocols ctx handle (encode model runtime.index reference))
  simp only [step, Occurrence.iterations, IterationObservations.within, PIR.Process.bind]
  rw [round_reference model definitions linked bodies protocols ctx distinct handle]
  change ∀ (_ : Unit) (lo hi : model.Field field), PIR.Yields _ _
  intro _ lo hi
  by_cases checked : reference.scalar = lo+hi
  · simp only [SumcheckReferenceInstallation.reference, checked, ↓reduceIte, PIR.Process.bind,
      PIR.Yields]
    intro r _ _
    refine ⟨reference.advance (lo,hi) r, same, retained, ?_⟩
    rfl
  · simp [SumcheckReferenceInstallation.reference, checked, PIR.Process.bind, PIR.Yields]

/-- Conditional collision bounds are required at every reached history. They
are independent mathematical assumptions, not discoveries from source metadata. -/
def no_contract (original : List (model.Field field)) (callerFrame : Frame)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw) (cuts : SourceRound.Cuts model absorb ctx handle)
    (boundaries : Boundaries model absorb ctx)
    (bounded : ∀ reached {n : Nat} (reference : PrefixState (model.Field field) Frame (n+1)),
      (layout model).representation.No reference →
      ∀ packetLo lo, cuts.recoverLow (cuts.low packetLo) = some lo →
      ∀ packetHi hi, cuts.recoverHigh (cuts.high packetHi) = some hi → reference.scalar = lo+hi →
      escape (reached ++ [cuts.low packetLo] ++ [cuts.high packetHi]) cuts.query
        (fun raw => ∃ r, cuts.decode raw = some r ∧
          ((Message.endpoints (model.Field field)).polynomial (lo,hi)).eval r =
            ((TableReference.data (model.Field field)).polynomial
              ((layout model).representation.state reference)).eval r)) :
    RepeatedComponent.NoContract (component model definitions protocols ctx handle)
      absorb escape (no model original callerFrame) := by
  intro history n runtime valid
  let reference := Classical.choose valid
  obtain ⟨same, retained, encoded, wrong⟩ := Classical.choose_spec valid
  rw [encoded]
  change Derivation _ _ _ _ (step model definitions protocols ctx handle (encode model runtime.index reference))
  simp only [step, Occurrence.iterations, IterationObservations.within, PIR.Process.bind]
  rw [round_reference model definitions linked bodies protocols ctx distinct handle]
  refine .send (boundaries.entered runtime.index) ?_
  have derived := SourceRound.adversarial model absorb escape ctx handle cuts
    ((layout model).representation.state reference) reference.point reference.scalar reference.frame
    (history ++ [boundaries.enter runtime.index]) wrong.2
    (bounded (history ++ [boundaries.enter runtime.index]) reference wrong)
  have mapped := derived.bind (Final := fun reached => no model original callerFrame reached n) (fun out => .call (.leave ⟨repeatSite ctx, runtime.index⟩) fun _ =>
      .done (Runtime.mk (runtime.index+1) out.1 out.2)) (by
    intro reached out residual
    refine .send (boundaries.left runtime.index) (.done ?_)
    obtain ⟨lo, hi, r, output, different⟩ := residual
    refine ⟨reference.advance (lo,hi) r, same, retained, ?_, ?_⟩
    · rw [output]
      rfl
    · change True ∧ _
      refine ⟨trivial, ?_⟩
      have restrict : (layout model).table (reference.advance (lo,hi) r) =
          (TableReference.data (model.Field field)).restrict ((layout model).table reference) r := by
        apply Option.some.inj
        rw [← (layout model).decoded]
        change Zkc.Polynomial.Multilinear.ofList? n (reference.advance (lo,hi) r).entries = _
        rw [PrefixState.advance_entries]
        exact Zkc.Polynomial.Multilinear.ofList?_restrictValues _ _ r ((layout model).decoded reference)
      change (1-r)*lo+r*hi ≠ (TableReference.data (model.Field field)).total
        ((layout model).table (reference.advance (lo,hi) r))
      rw [restrict]
      exact different)
  simpa only [PIR.Process.bind_assoc, PIR.Process.bind, encode] using mapped

/-- Independent all-replies frames and No steps compose over symbolic counts. -/
def no_repeat (original : List (model.Field field)) (callerFrame : Frame)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw)
    (steps : RepeatedComponent.NoContract (component model definitions protocols ctx handle)
      absorb escape (no model original callerFrame))
    (count : Nat) (history : List E) (runtime : Runtime model Frame)
    (initial : no model original callerFrame history count runtime) :
    Derivation absorb escape (fun reached => no model original callerFrame reached 0) history
      (PIR.repeatN count (step model definitions protocols ctx handle) runtime) :=
  RepeatedComponent.no_repeatN _ steps count history runtime initial

/-- Sampling is required at each actual reached raw-query cut, after both
attacker messages and the iteration entry have already been fixed. -/
def sampled_contract (original : List (model.Field field)) (callerFrame : Frame)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (charge : List E → E → ENNReal) (cuts : SourceRound.Cuts model absorb ctx handle)
    (boundaries : Boundaries model absorb ctx)
    [∀ event, SampleableType (Raw event)]
    (sampling : ∀ reached (p q : Polynomial (model.Field field)), p ≠ q →
      p.natDegree ≤ 1 → q.natDegree ≤ 1 →
      Pr{let raw ← $ᵗ (Raw cuts.query)}[∃ r, cuts.decode raw = some r ∧ p.eval r = q.eval r] ≤ charge reached cuts.query) :
    RepeatedComponent.NoContract (component model definitions protocols ctx handle)
      absorb (ZkcSecurity.Obligations.boundedEscape charge) (no model original callerFrame) := by
  apply no_contract model definitions linked bodies protocols ctx distinct handle original callerFrame
    absorb (ZkcSecurity.Obligations.boundedEscape charge) cuts boundaries
  intro reached n reference wrong packetLo lo recoveredLo packetHi hi recoveredHi checked
  exact sampling _ _ _
    (checked_polynomial_ne TableReference.laws Message.endpoints_laws
      ((layout model).representation.state reference) trivial reference.scalar wrong.2 (lo,hi) checked.symm)
    (Message.endpoints_laws.degree_le (lo,hi)) (TableReference.laws.degree_le _ trivial)

/-- A concrete ENNReal budget for the same actual loop. The price is bounded at
all reached histories; this does not infer a sampling law or independence. -/
theorem cost_contract (original : List (model.Field field)) (callerFrame : Frame)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (charge : List E → E → ENNReal) (cuts : SourceRound.Cuts model absorb ctx handle)
    (boundaries : Boundaries model absorb ctx) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error) :
    ZkcSecurity.Obligations.RepeatedComponent.CostContract
      (component model definitions protocols ctx handle) absorb charge
      (represented model original callerFrame) (fun count _ _ => count • error) := by
  intro n history runtime valid
  obtain ⟨reference, same, retained, encoded⟩ := valid
  rw [encoded]
  change ZkcSecurity.Obligations.WeakestPrecondition.costWP _ _
    (step model definitions protocols ctx handle (encode model runtime.index reference)) _ _ _ _
  simp only [step, Occurrence.iterations, IterationObservations.within, PIR.Process.bind]
  rw [round_reference model definitions linked bodies protocols ctx distinct handle]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, encode,
    SumcheckReferenceInstallation.reference, ZkcSecurity.Obligations.WeakestPrecondition.costWP,
    PIR.Process.foldReplies, ZkcSecurity.Obligations.WeakestPrecondition.costNode,
    boundaries.entered, cuts.receiveLow, cuts.receiveHigh]
  intro packetLo lo recoveredLo packetHi hi recoveredHi
  by_cases checked : reference.scalar = lo+hi
  · simp only [checked, ↓reduceIte, PIR.Process.bind, PIR.Process.foldReplies,
      ZkcSecurity.Obligations.WeakestPrecondition.costNode, cuts.draw]
    refine ⟨n • error, ?_, ?_⟩
    · calc
        _ ≤ error + n • error := add_le_add (price _) (le_refl (n • error))
        _ = (n+1) • error := by rw [succ_nsmul]; ac_rfl
    · intro r
      have sent := cuts.send r
      dsimp only [SourceRound.deliveryOp] at sent
      simp only [PIR.Process.bind, PIR.Process.foldReplies, ZkcSecurity.Obligations.WeakestPrecondition.costNode,
        sent, boundaries.left, le_refl]
  · simp [checked, PIR.Process.bind, PIR.Process.foldReplies]

theorem cost_repeat (original : List (model.Field field)) (callerFrame : Frame)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (charge : List E → E → ENNReal) (cuts : SourceRound.Cuts model absorb ctx handle)
    (boundaries : Boundaries model absorb ctx) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error)
    (count : Nat) (history : List E) (runtime : Runtime model Frame)
    (initial : represented model original callerFrame count runtime) :
    ZkcSecurity.FiatShamir.Typed.ChargedCostBound absorb charge
      (PIR.repeatN count (step model definitions protocols ctx handle) runtime) history (count • error) :=
  ZkcSecurity.Obligations.RepeatedComponent.cost_repeatN _ _ _
    (frame_contract model definitions linked bodies protocols ctx distinct handle original callerFrame)
    (cost_contract model definitions linked bodies protocols ctx distinct handle original callerFrame
      absorb charge cuts boundaries error price) count history runtime initial

end ZkcSecurity.Families.Sumcheck.SourceIteration
