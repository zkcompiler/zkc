module

public import Zkc.Source.Constructed
public import Zkc.Protocols.Sumcheck.Common.Program

@[expose] public section

/-! Fixed scalar/full-prefix interpretation of actual constructed Sumcheck leaves.
This explicitly selected ideal model is not a semantics theorem about Merlin.
-/
set_option autoImplicit false
namespace Zkc.Protocols.Sumcheck.NativeConstruction
open Zkc.Source
open Zkc.Protocols.AlgebraicRounds (Message)

/-- Exact native occurrences. These descriptors are public domain separation,
not functions supplying arbitrary meanings to an operation. -/
structure Schedule where
  receives : List Constructed.Primitive
  observations : List Constructed.Primitive
  challenges : List Constructed.Primitive
  deriving DecidableEq

structure Binding (Context F : Type) where
  source : String
  construction : String
  context : Context
  schedule : Schedule
  coefficients : Common.Coefficients F
  claim : F

/-- The second query retains the actual first challenge, including its delivery. -/
abbrev QueryKey (Context F : Type) :=
  (Binding Context F × Message F) ⊕ (Binding Context F × Message F × F × Message F)

abbrev oracleSignature (Context F : Type) : PIR.Signature where
  Op := QueryKey Context F
  Reply := fun _ => F

/-- `values` is the ordered typed field observation prefix. The exact occurrence
metadata lives in `binding.schedule`. Pending challenges must be delivered next. -/
structure Transcript (Context F : Type) where
  binding : Binding Context F
  values : List F := []
  pending : Option F := none

abbrev Value (Context F : Type) : String → Type
  | "i1" => Bool
  | "!algebra.field<\"bls12-381.fr\">" => F
  | "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">" => Transcript Context F
  | "!algebra.indices" => List Nat
  | _ => Empty

variable {Context F : Type} [Field F] [DecidableEq F]

/-- Proof coordinates are selected by exact receive descriptors, not instruction
position, a value in an unrelated input, or an assumed honest prover. -/
def receiveValue (schedule : Schedule) (proof : Message F × Message F)
    (op : Constructed.Primitive) : Option F :=
  if schedule.receives[0]? = some op then some proof.1.constant else
  if schedule.receives[1]? = some op then some proof.1.linear else
  if schedule.receives[2]? = some op then some proof.1.quadratic else
  if schedule.receives[3]? = some op then some proof.2.constant else
  if schedule.receives[4]? = some op then some proof.2.linear else
  if schedule.receives[5]? = some op then some proof.2.quadratic else none

def observe (op : Constructed.Primitive) (state : Transcript Context F) (value : F)
    (indices : List Nat) : PIR.Proc (oracleSignature Context F) (Transcript Context F) :=
  if indices.isEmpty && state.binding.schedule.observations[state.values.length]? == some op then
    match state.values.length, state.pending with
    | 0, none | 1, none | 2, none | 4, none | 5, none | 6, none =>
      .done { state with values := state.values ++ [value] }
    | 3, some challenge | 7, some challenge =>
      if value = challenge then
        .done { state with values := state.values ++ [value], pending := none }
      else .halt .refused
    | _, _ => .halt .refused
  else .halt .refused

def challenge (op : Constructed.Primitive) (state : Transcript Context F)
    (indices : List Nat) : PIR.Proc (oracleSignature Context F) (F × Transcript Context F) :=
  if indices.isEmpty && state.pending.isNone then
    match state.values with
    | [a, b, c] =>
      if state.binding.schedule.challenges[0]? == some op then
        .call (.inl (state.binding, ⟨a,b,c⟩)) fun value =>
          .done (value, { state with pending := some value })
      else .halt .refused
    | [a, b, c, first, d, e, f] =>
      if state.binding.schedule.challenges[1]? == some op then
        .call (.inr (state.binding, ⟨a,b,c⟩, first, ⟨d,e,f⟩)) fun value =>
          .done (value, { state with pending := some value })
      else .halt .refused
    | _ => .halt .refused
  else .halt .refused

/-- Names and nominal signatures select fixed arithmetic; attributes on pure
arithmetic must be empty. Unknown leaves and malformed transcript states refuse. -/
def primitive (schedule : Schedule) (proof : Message F × Message F)
    (op : Constructed.Primitive) : Values (Value Context F) op.arguments →
      PIR.Proc (oracleSignature Context F) (Values (Value Context F) op.results) :=
  match op with
  | ⟨"protocol.receive", _, _, _, [], ["!algebra.field<\"bls12-381.fr\">"]⟩ =>
    fun .nil => match receiveValue schedule proof op with
      | some value => .done (.cons value .nil)
      | none => .halt .refused
  | ⟨"algebra.exec.indices_empty", _, _, _, [], ["!algebra.indices"]⟩ =>
    fun .nil => .done (.cons [] .nil)
  | ⟨"crypto.exec.indexed_transcript_observe_data", _, _, _,
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">",
       "!algebra.field<\"bls12-381.fr\">", "!algebra.indices"],
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]⟩ =>
    fun (.cons state (.cons value (.cons indices .nil))) =>
      (observe op state value indices).bind fun next => .done (.cons next .nil)
  | ⟨"crypto.exec.indexed_transcript_challenge", _, _, _,
      ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">", "!algebra.indices"],
      ["!algebra.field<\"bls12-381.fr\">",
       "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]⟩ =>
    fun (.cons state (.cons indices .nil)) =>
      (challenge op state indices).bind fun (value, next) =>
        .done (.cons value (.cons next .nil))
  | ⟨"algebra.field_add", "{}", "", _,
      ["!algebra.field<\"bls12-381.fr\">", "!algebra.field<\"bls12-381.fr\">"],
      ["!algebra.field<\"bls12-381.fr\">"]⟩ =>
    fun (.cons x (.cons y .nil)) => .done (.cons (@HAdd.hAdd F F F inferInstance x y) .nil)
  | ⟨"algebra.field_subtract", "{}", "", _,
      ["!algebra.field<\"bls12-381.fr\">", "!algebra.field<\"bls12-381.fr\">"],
      ["!algebra.field<\"bls12-381.fr\">"]⟩ =>
    fun (.cons x (.cons y .nil)) => .done (.cons (@HSub.hSub F F F inferInstance x y) .nil)
  | ⟨"algebra.field_multiply", "{}", "", _,
      ["!algebra.field<\"bls12-381.fr\">", "!algebra.field<\"bls12-381.fr\">"],
      ["!algebra.field<\"bls12-381.fr\">"]⟩ =>
    fun (.cons x (.cons y .nil)) => .done (.cons (@HMul.hMul F F F inferInstance x y) .nil)
  | ⟨"algebra.field_equal", "{}", "", _,
      ["!algebra.field<\"bls12-381.fr\">", "!algebra.field<\"bls12-381.fr\">"], ["i1"]⟩ =>
    fun (.cons x (.cons y .nil)) => .done (.cons (decide ((x : F) = y)) .nil)
  | _ => fun _ => .halt .refused

def meaning (schedule : Schedule) (proof : Message F × Message F) :
    Constructed.Meaning (oracleSignature Context F) where
  Value := Value Context F
  condition := id
  primitive := primitive schedule proof

def inputTypes : List String :=
  List.replicate 10 "!algebra.field<\"bls12-381.fr\">" ++
    ["!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]

def outputTypes : List String :=
  ["i1", "!local.capability<\"transcript:merlin3.bls12-381.fr64be/0\">"]

def inputs (binding : Binding Context F) :
    Values (Values (Value Context F)) (inputTypes.map Constructed.scalar) :=
  let p := binding.coefficients
  .cons (.cons p.constant.constant .nil) (.cons (.cons p.constant.linear .nil)
  (.cons (.cons p.constant.quadratic .nil) (.cons (.cons p.linear.constant .nil)
  (.cons (.cons p.linear.linear .nil) (.cons (.cons p.linear.quadratic .nil)
  (.cons (.cons p.quadratic.constant .nil) (.cons (.cons p.quadratic.linear .nil)
  (.cons (.cons p.quadratic.quadratic .nil) (.cons (.cons binding.claim .nil)
  (.cons (.cons (⟨binding, [], none⟩ : Transcript Context F) .nil) .nil))))))))))

/-- Complete reference process, including guards, both oracle calls, both
challenge deliveries and the returned transcript. No completion after rejection. -/
def experiment (binding : Binding Context F) (proof : Message F × Message F) :
    PIR.Proc (oracleSignature Context F) (Values (Value Context F) outputTypes) :=
  if decide (Common.wireBoundary proof.1 = binding.claim) then
    .call (.inl (binding, proof.1)) fun first =>
    if decide (Common.wireBoundary proof.2 = Common.wireEvaluate proof.1 first) then
      .call (.inr (binding, proof.1, first, proof.2)) fun second =>
      .done (.cons (decide (Common.wireEvaluate proof.2 second =
        Common.evaluate binding.coefficients first second))
        (.cons (⟨binding, [proof.1.constant, proof.1.linear, proof.1.quadratic, first,
          proof.2.constant, proof.2.linear, proof.2.quadratic, second], none⟩ :
          Transcript Context F) .nil))
    else .halt .reject
  else .halt .reject

def result (reply : Values (Value Context F) outputTypes) : Option Bool :=
  match reply with | .cons accepted (.cons _ .nil) => some accepted

omit [DecidableEq F] in
/-- Fixed polynomial identity used to normalize authored Horner arithmetic. -/
theorem horner_evaluate (a b c x : F) :
    a + x * (b + x * c) = a + x * b + (x * x) * c := by ring

omit [DecidableEq F] in
/-- Reordered coefficient sums have the same Boolean boundary. -/
theorem reordered_boundary (a b c : F) :
    c + b + (a + a) = a + a + b + c := by ring

/-- Deterministic table observation; cache sampling is supplied by the optional
security experiment. This handler logs every entered query without resets. -/
def tableHandler (table : QueryKey Context F → F) :
    PIR.Handler (oracleSignature Context F) Unit (QueryKey Context F) :=
  fun key state => ⟨.returned (table key), state, [key]⟩

/-- Acceptance at a fixed total table preserves both early rejection checks.
The challenges are looked up using the actual messages and previous reply. -/
theorem experiment_accepted_iff (binding : Binding Context F) (proof : Message F × Message F)
    (table : QueryKey Context F → F) :
    (((experiment binding proof).bind fun reply => .done (result reply)).run
      (tableHandler table) ()).outcome = .returned (some true) ↔
    let first := table (.inl (binding, proof.1))
    let second := table (.inr (binding, proof.1, first, proof.2))
    Common.wireBoundary proof.1 = binding.claim ∧
    Common.wireBoundary proof.2 = Common.wireEvaluate proof.1 first ∧
    Common.wireEvaluate proof.2 second = Common.evaluate binding.coefficients first second := by
  by_cases first : Common.wireBoundary proof.1 = binding.claim
  all_goals by_cases second : Common.wireBoundary proof.2 =
    Common.wireEvaluate proof.1 (table (.inl (binding, proof.1)))
  all_goals simp [experiment, first, second, PIR.Proc.bind, PIR.Proc.run,
    PIR.Execution.follow, tableHandler, result]

/-- One-shot rejection can consume zero, one, or two queries. Completing the
verifier unconditionally would not preserve this event trace. -/
theorem experiment_events (binding : Binding Context F) (proof : Message F × Message F)
    (table : QueryKey Context F → F) :
    ((experiment binding proof).run (tableHandler table) ()).events =
    if Common.wireBoundary proof.1 = binding.claim then
      let first := table (.inl (binding, proof.1))
      if Common.wireBoundary proof.2 = Common.wireEvaluate proof.1 first then
        [.inl (binding, proof.1), .inr (binding, proof.1, first, proof.2)]
      else [.inl (binding, proof.1)]
    else [] := by
  by_cases first : Common.wireBoundary proof.1 = binding.claim
  all_goals by_cases second : Common.wireBoundary proof.2 =
    Common.wireEvaluate proof.1 (table (.inl (binding, proof.1)))
  all_goals simp [experiment, first, second, PIR.Proc.run,
    PIR.Execution.follow, tableHandler]

omit [Field F] [DecidableEq F] in
/-- Omitting the current message cannot produce an ideal challenge. -/
theorem challenge_empty (op : Constructed.Primitive) (binding : Binding Context F)
    (indices : List Nat) :
    challenge op ⟨binding, [], none⟩ indices = .halt .refused := by
  simp [challenge]

omit [Field F] [DecidableEq F] in
/-- A pending challenge cannot be overwritten by another query. -/
theorem challenge_pending (op : Constructed.Primitive) (binding : Binding Context F)
    (values : List F) (value : F) (indices : List Nat) :
    challenge op ⟨binding, values, some value⟩ indices = .halt .refused := by
  simp [challenge]

omit [Field F] in
/-- The exact delivered challenge is required; a same-typed replacement refuses. -/
theorem observe_wrong_delivery (op : Constructed.Primitive) (binding : Binding Context F)
    (a b c sampled supplied : F) (different : supplied ≠ sampled) :
    observe op ⟨binding, [a,b,c], some sampled⟩ supplied [] = .halt .refused := by
  simp [observe, different]

end Zkc.Protocols.Sumcheck.NativeConstruction
