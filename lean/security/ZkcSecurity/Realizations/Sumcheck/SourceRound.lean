module

public import ZkcExamples.Structured.SumcheckReferenceInstallation
public import ZkcSecurity.Families.Sumcheck.TableComponent
public import ZkcSecurity.Families.Sumcheck.Round
public import Zkc.Obligations.NormalizedComponent
public import ZkcSecurity.Obligations.Derivation
public import ZkcSecurity.Tools.ComponentDerivation

@[expose] public section

/-! Honest return and adversarial escape for the same actual typed Sumcheck
round and occurrence normal form. Reference state is supplied independently of
scalar truth. Challenge fixation is explicit: both messages and the current
history are arguments of the query-cut obligation, before its raw reply. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceRound
open ZkcSecurity.Families.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured
open SumcheckReferenceInstallation
open Zkc.Polynomial.Multilinear
open OracleComp OracleSpec

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField

abbrev lowOp (ctx : ProtocolContext) : (Occurrence.signature model.toCarriers).Op :=
  .action (.receive (.field field) (SumcheckRoundNormalForms.round0Site ctx) (ctx.roles 0))
abbrev highOp (ctx : ProtocolContext) : (Occurrence.signature model.toCarriers).Op :=
  .action (.receive (.field field) (SumcheckRoundNormalForms.round1Site ctx) (ctx.roles 0))
abbrev queryOp (ctx : ProtocolContext) (handle : Nat) : (Occurrence.signature model.toCarriers).Op :=
  .action (.query (SumcheckRoundNormalForms.challengeSite ctx) field (.cons handle .nil))
abbrev deliveryOp (ctx : ProtocolContext) (r : model.Field field) : (Occurrence.signature model.toCarriers).Op :=
  .action (.send (ty := .field field) (SumcheckRoundNormalForms.deliverySite ctx) (ctx.roles 0) r)

variable {E P : Type} {Raw : E → Type}

/-- Exact cuts of the existing source interface. No sampler, recovery,
independence or target interpretation is inferred from a source name. -/
structure Cuts (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (ctx : ProtocolContext) (handle : Nat) where
  low : P → E
  recoverLow : E → Option (model.Field field)
  receiveLow : absorb (lowOp model ctx) = .receive low recoverLow
  high : P → E
  recoverHigh : E → Option (model.Field field)
  receiveHigh : absorb (highOp model ctx) = .receive high recoverHigh
  query : E
  decode : Raw query → Option (model.Field field)
  draw : absorb (queryOp model ctx handle) = .query query decode
  delivery : model.Field field → E
  send : ∀ r, absorb (deliveryOp model ctx r) = .send (delivery r) ()

/-- The postcondition includes the entire source return and arbitrary private
caller frame. The existential is the actual challenge/update, not a witness
for a newly invented target relation. -/
def residual {Frame : Type} {n : Nat} (table : Table (model.Field field) (n+1))
    (point : List (model.Field field)) (frame : Frame)
    (out : Values (Component model.Value) SumcheckVerifierBodies.repeatState × Frame) : Prop :=
  ∃ lo hi r : model.Field field,
    out = (state model (some (point ++ [r])) (some ((1-r)*lo+r*hi)), frame) ∧
    ((1-r)*lo+r*hi) ≠ (TableReference.data (model.Field field)).total
      ((TableReference.data (model.Field field)).restrict table r)

/-- Every recovered attacker endpoint pair is retained. Failed guards stop.
The only discarded query replies are exactly the explicitly bounded collision
set; complete returned tuples and private frames survive the derivation. -/
def adversarial {Frame : Type} {n : Nat}
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw) (ctx : ProtocolContext) (handle : Nat)
    (cuts : Cuts model absorb ctx handle)
    (table : Table (model.Field field) (n+1)) (point : List (model.Field field))
    (scalar : model.Field field) (frame : Frame) (history : List E)
    (_wrong : scalar ≠ (TableReference.data (model.Field field)).total table)
    (bounded : ∀ packetLo lo, cuts.recoverLow (cuts.low packetLo) = some lo →
      ∀ packetHi hi, cuts.recoverHigh (cuts.high packetHi) = some hi → scalar = lo+hi →
      escape (history ++ [cuts.low packetLo] ++ [cuts.high packetHi]) cuts.query
        (fun raw => ∃ r, cuts.decode raw = some r ∧
          ((Message.endpoints (model.Field field)).polynomial (lo,hi)).eval r =
            ((TableReference.data (model.Field field)).polynomial table).eval r)) :
    Derivation absorb escape (fun _ => residual model table point frame) history
      ((reference model ctx (some handle) (some point) (some scalar)).bind
        fun values => .done (values, frame)) := by
  change Derivation _ _ _ _ (.call (lowOp model ctx) _)
  refine .receive cuts.receiveLow fun packetLo lo recoveredLo => ?_
  refine .receive cuts.receiveHigh fun packetHi hi recoveredHi => ?_
  by_cases checked : scalar = lo+hi
  · simp only [checked, ↓reduceIte, PIR.Process.bind]
    refine .query cuts.draw _ (bounded packetLo lo recoveredLo packetHi hi recoveredHi checked)
      fun raw (r : model.Field field) decoded outside => ?_
    refine .send (cuts.send r) (.done ?_)
    refine ⟨lo, hi, r, rfl, ?_⟩
    have unequal : ((Message.endpoints (model.Field field)).polynomial (lo,hi)).eval r ≠
        ((TableReference.data (model.Field field)).polynomial table).eval r :=
      fun collision => outside ⟨r, decoded, collision⟩
    exact (false_round TableReference.laws Message.endpoints_laws table trivial (lo,hi) r unequal).1
  · simp only [checked, ↓reduceIte, PIR.Process.bind]
    exact .halt .reject

/-- The actual conditional distribution remains an ordinary mathematical
premise. Degree and unequal-polynomial facts are supplied by the family laws,
not by honest-message equality. State and endpoints are fixed before `challenge`. -/
theorem conditional_escape {n : Nat}
    (table : Table (model.Field field) (n+1)) (scalar lo hi : model.Field field)
    (wrong : scalar ≠ (TableReference.data (model.Field field)).total table)
    (checked : scalar = lo+hi) (challenge : ProbComp (model.Field field)) (error : ENNReal)
    (sampling : ∀ p q : Polynomial (model.Field field), p ≠ q → p.natDegree ≤ 1 →
      q.natDegree ≤ 1 →
      Pr{let r ← challenge}[p.eval r = q.eval r] ≤ error) :
    Pr{let r ← challenge}[(Message.endpoints (model.Field field)).evaluate (lo,hi) r =
      (TableReference.data (model.Field field)).total
        ((TableReference.data (model.Field field)).restrict table r)] ≤ error := by
  exact escape_actual_le TableReference.laws Message.endpoints_laws table trivial scalar wrong
    (lo,hi) checked.symm challenge error sampling

/-- Honest return has separate successful handler laws at all four reached
operations. A rejecting guard cannot satisfy this theorem's returned outcome.
The event list and final handler state are exact, not erased observations. -/
theorem honest_reference {H O : Type} {n : Nat}
    (ctx : ProtocolContext) (handle : Nat) (point : List (model.Field field))
    (table : Table (model.Field field) (n+1)) (scalar : model.Field field)
    (yes : scalar = (TableReference.data (model.Field field)).total table)
    (lo hi r : model.Field field)
    (delivered : (Message.endpoints (model.Field field)).polynomial (lo,hi) =
      (TableReference.data (model.Field field)).polynomial table)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H O)
    (h0 h1 h2 h3 h4 : H) (e0 e1 e2 e3 : List O)
    (low : handler (lowOp model ctx) h0 = ⟨.returned lo, h1, e0⟩)
    (high : handler (highOp model ctx) h1 = ⟨.returned hi, h2, e1⟩)
    (query : handler (queryOp model ctx handle) h2 = ⟨.returned r, h3, e2⟩)
    (sent : handler (deliveryOp model ctx r) h3 = ⟨.returned (), h4, e3⟩) :
    (reference model ctx (some handle) (some point) (some scalar)).run handler h0 =
      ⟨.returned (state model (some (point ++ [r]))
        (some ((TableReference.data (model.Field field)).total
          ((TableReference.data (model.Field field)).restrict table r)))),
        h4, e0 ++ (e1 ++ (e2 ++ e3))⟩ := by
  obtain ⟨boundary, evaluation, _⟩ := honest_round TableReference.laws Message.endpoints_laws
    table trivial (lo,hi) delivered r r rfl
  have checked : scalar = lo+hi := yes.trans boundary.symm
  change ((PIR.Process.call (lowOp model ctx) _) : PIR.Process _ _).run handler h0 = _
  simp only [PIR.Process.run, low, high, query, sent, PIR.Execution.follow,
    checked, ↓reduceIte, List.append_nil]
  change ((1-r)*lo+r*hi) = booleanSum (fixFirst table r) at evaluation
  rw [evaluation]

/-- Both consumers use this exact source binding. Root call/repeat installation
is separate and does not supply a per-instance whole-source equation here. -/
def source_adversarial {Frame : Type} {n : Nat}
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2)
    (index handle : Nat)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw) (cuts : Cuts model absorb ctx handle)
    (table : Table (model.Field field) (n+1)) (point : List (model.Field field))
    (scalar : model.Field field) (frame : Frame) (history : List E)
    (wrong : scalar ≠ (TableReference.data (model.Field field)).total table)
    (bounded : ∀ packetLo lo, cuts.recoverLow (cuts.low packetLo) = some lo →
      ∀ packetHi hi, cuts.recoverHigh (cuts.high packetHi) = some hi → scalar = lo+hi →
      escape (history ++ [cuts.low packetLo] ++ [cuts.high packetHi]) cuts.query
        (fun raw => ∃ r, cuts.decode raw = some r ∧
          ((Message.endpoints (model.Field field)).polynomial (lo,hi)).eval r =
            ((TableReference.data (model.Field field)).polynomial table).eval r)) :
    Derivation absorb escape (fun _ => residual model table point frame) history
      ((SumcheckVerifierBodies.roundBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
          (ctx.roles 1) protocols ctx Occurrence.iterations)
        (Syntax.pattern.environment model (inputs model index (some point) (some scalar) (some handle))).get).bind
        fun values => .done (values, frame)) := by
  rw [body_reference model definitions linked bodies protocols ctx distinct index]
  assemble_component_property
    [adversarial model absorb escape ctx handle cuts table point scalar frame history wrong]
    unfolding [] repeating [] reporting "actual Sumcheck round No and full private residual"
    from (Syntax.form, ctx, inputs model index (some point) (some scalar) (some handle))

theorem source_honest {H O : Type} {n : Nat}
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (index : Nat) (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2) (handle : Nat) (point : List (model.Field field))
    (table : Table (model.Field field) (n+1)) (scalar : model.Field field)
    (yes : scalar = (TableReference.data (model.Field field)).total table)
    (lo hi r : model.Field field)
    (delivered : (Message.endpoints (model.Field field)).polynomial (lo,hi) =
      (TableReference.data (model.Field field)).polynomial table)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H O)
    (h0 h1 h2 h3 h4 : H) (e0 e1 e2 e3 : List O)
    (low : handler (lowOp model ctx) h0 = ⟨.returned lo, h1, e0⟩)
    (high : handler (highOp model ctx) h1 = ⟨.returned hi, h2, e1⟩)
    (query : handler (queryOp model ctx handle) h2 = ⟨.returned r, h3, e2⟩)
    (sent : handler (deliveryOp model ctx r) h3 = ⟨.returned (), h4, e3⟩) :
    (SumcheckVerifierBodies.roundBody.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
        (ctx.roles 1) protocols ctx Occurrence.iterations)
      (Syntax.pattern.environment model (inputs model index (some point) (some scalar) (some handle))).get).run handler h0 =
      ⟨.returned (state model (some (point ++ [r]))
        (some ((TableReference.data (model.Field field)).total
          ((TableReference.data (model.Field field)).restrict table r)))),
        h4, e0 ++ (e1 ++ (e2 ++ e3))⟩ := by
  rw [body_reference model definitions linked bodies protocols ctx distinct index]
  exact honest_reference model ctx handle point table scalar yes lo hi r delivered
    handler h0 h1 h2 h3 h4 e0 e1 e2 e3 low high query sent

/-- Root counting is connected to the actual decoded raw query cut. The
sampling law is quantified at each reached history and for any unequal degree
one polynomials; source lookup and honest delivery do not supply it. -/
def source_sampled {Frame : Type} {n : Nat}
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2)
    (index handle : Nat)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (charge : List E → E → ENNReal) (cuts : Cuts model absorb ctx handle)
    (table : Table (model.Field field) (n+1)) (point : List (model.Field field))
    (scalar : model.Field field) (frame : Frame) (history : List E)
    (wrong : scalar ≠ (TableReference.data (model.Field field)).total table)
    [∀ event, SampleableType (Raw event)]
    (sampling : ∀ reached (p q : Polynomial (model.Field field)), p ≠ q →
      p.natDegree ≤ 1 → q.natDegree ≤ 1 →
      Pr{let raw ← $ᵗ (Raw cuts.query)}[∃ r, cuts.decode raw = some r ∧ p.eval r = q.eval r] ≤
        charge reached cuts.query) :
    Derivation absorb (ZkcSecurity.Obligations.boundedEscape charge) (fun _ => residual model table point frame) history
      ((SumcheckVerifierBodies.roundBody.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
          (ctx.roles 1) protocols ctx Occurrence.iterations)
        (Syntax.pattern.environment model (inputs model index (some point) (some scalar) (some handle))).get).bind
        fun values => .done (values, frame)) := by
  apply source_adversarial model definitions linked bodies protocols ctx distinct index handle
    absorb (ZkcSecurity.Obligations.boundedEscape charge) cuts table point scalar frame history wrong
  intro packetLo lo recoveredLo packetHi hi recoveredHi checked
  exact sampling _ _ _
    (checked_polynomial_ne TableReference.laws Message.endpoints_laws table trivial scalar wrong
      (lo,hi) checked.symm)
    (Message.endpoints_laws.degree_le (lo,hi)) (TableReference.laws.degree_le table trivial)

/-- The installed half-sum producer has the polynomial meaning of the same
representation used by the No consumer, independently of scalar truth. -/
theorem producer_polynomial {I : PIR.Signature} {Context : Type} {State : Nat → Type}
    {program : Program I Context State (Message.endpoints (model.Field field))}
    (layout : TableComponent.Layout program) {n : Nat} (state : State (n+1)) :
    (Message.endpoints (model.Field field)).polynomial
        (((layout.entries state).take ((layout.entries state).length/2)).sum,
          ((layout.entries state).drop ((layout.entries state).length/2)).sum) =
      (TableReference.data (model.Field field)).polynomial (layout.representation.state state) := by
  rw [layout.honest_endpoints]
  rfl

/-- The returned inequality is the existing family Representation.No for the
same update, with the entire source result and private frame still present. -/
theorem residual_no {I : PIR.Signature} {Context Frame : Type} {State : Nat → Type}
    {program : Program I Context State (Message.endpoints (model.Field field))}
    (layout : TableComponent.Layout program) {n : Nat} (context : Context) (original : State (n+1))
    (point : List (model.Field field)) (frame : Frame)
    (out : Values (Component model.Value) SumcheckVerifierBodies.repeatState × Frame)
    (post : residual model (layout.representation.state original) point frame out) :
    ∃ (message : model.Field field × model.Field field) (r : model.Field field),
      out = (state model (some (point ++ [r]))
        (some ((Message.endpoints (model.Field field)).evaluate message r)), frame) ∧
      layout.representation.No (program.advance context original message r) := by
  obtain ⟨lo, hi, r, same, wrong⟩ := post
  refine ⟨(lo,hi), r, same, ?_⟩
  change True ∧ program.claim (program.advance context original (lo,hi) r) ≠
    (TableReference.data (model.Field field)).total
      (layout.representation.state (program.advance context original (lo,hi) r))
  rw [layout.representation.advance, layout.representation.claim]
  exact ⟨trivial, wrong⟩

/-- Existing table representation supplies the polynomial delivery law for the
actual installed half-sum producer. Handler success remains explicit. -/
theorem source_honest_represented {I : PIR.Signature} {Context H O : Type} {State : Nat → Type}
    {program : Program I Context State (Message.endpoints (model.Field field))}
    (layout : TableComponent.Layout program) {n : Nat} (original : State (n+1))
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (bodies : Bodies definitions MultilinearSourceBindings.sumcheck)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (index : Nat) (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx 1 2)
    (handle : Nat) (point : List (model.Field field))
    (scalar : model.Field field) (yes : scalar = program.claim original)
    (honest : layout.representation.Yes original) (r : model.Field field)
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H O)
    (h0 h1 h2 h3 h4 : H) (e0 e1 e2 e3 : List O)
    (low : handler (lowOp model ctx) h0 =
      ⟨.returned ((layout.entries original).take ((layout.entries original).length/2)).sum, h1, e0⟩)
    (high : handler (highOp model ctx) h1 =
      ⟨.returned ((layout.entries original).drop ((layout.entries original).length/2)).sum, h2, e1⟩)
    (query : handler (queryOp model ctx handle) h2 = ⟨.returned r, h3, e2⟩)
    (sent : handler (deliveryOp model ctx r) h3 = ⟨.returned (), h4, e3⟩) :
    (SumcheckVerifierBodies.roundBody.denote
      (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
        (ctx.roles 1) protocols ctx Occurrence.iterations)
      (Syntax.pattern.environment model (inputs model index (some point) (some scalar) (some handle))).get).run handler h0 =
      ⟨.returned (state model (some (point ++ [r]))
        (some ((TableReference.data (model.Field field)).total
          ((TableReference.data (model.Field field)).restrict (layout.representation.state original) r)))),
        h4, e0 ++ (e1 ++ (e2 ++ e3))⟩ :=
  source_honest model definitions linked bodies protocols index ctx distinct handle point
    (layout.representation.state original) scalar (yes.trans honest.2) _ _ r
    (producer_polynomial model layout original) handler h0 h1 h2 h3 h4 e0 e1 e2 e3 low high query sent

end ZkcSecurity.Realizations.Sumcheck.SourceRound
