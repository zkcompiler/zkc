module

public import ZkcSecurity.Families.Sumcheck.CompiledRound
public import ZkcSecurity.Families.Sumcheck.TableComponentPrimeField
public import ZkcSecurity.Families.Sumcheck.TableComponentNominalCost

@[expose] public section

/-! Complete constructed scalar loops. The source connection retains the full
round SSA frame until its actual yield map is checked. Mathematical consumers
use the existing table reference; arbitrary raw tables remain runtime inputs.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
namespace ZkcSecurity.Families.Sumcheck.CompiledValidator
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.DomainReduction
open TableComponent

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

structure State (F G : Type) where
  point : List F
  scalar : F
  history : Domain.History (uniformCarriers F G)

def carried (field suite : String) (state : State F G) : Domain.Environment (uniformCarriers F G) :=
  [.data (.vector field state.point), .data (.field field state.scalar), .transcript suite state.history]

def advance (field : String) (sites : Nominal.Schedule field) (index : Nat)
    (state : State F G) (low high challenge : F) : State F G :=
  ⟨state.point ++ [challenge], (1 - challenge) * low + challenge * high,
    CompiledRound.finalHistory field (sites.low index) (sites.high index)
      (sites.query index) (sites.delivery index) state.history low high challenge⟩

noncomputable def run (field : String) (sites : Nominal.Schedule field) :
    List Nat → State F G → PIR.Process (Nominal.signature F field) (State F G)
  | [], state => .done state
  | index :: rest, state =>
      .call (.receive (sites.low index)) fun low =>
      .call (.receive (sites.high index)) fun high =>
      if state.scalar = low + high then
        .call (.query (sites.query index) (sites.request index)) fun challenge =>
        .call (.deliver (sites.delivery index) challenge) fun _ =>
          run field sites rest (advance field sites index state low high challenge)
      else .halt .reject

/-- A checked connection to the exact source block, independent of its caller's
raw table, retained captures, scalar, prefix, and every malicious endpoint. -/
structure RoundConnection (field : String) (program : Structured.Program) (context : Context)
    (plan : CompiledRound.Plan) (sites : Nominal.Schedule field) : Prop where
  lowFound : ∀ index, Domain.templateOrigin context plan.lowTemplate [index] = some (sites.low index)
  highFound : ∀ index, Domain.templateOrigin context plan.highTemplate [index] = some (sites.high index)
  queryFound : ∀ index, Domain.queryOrigin context context.suite field plan.queryTemplate [index] = some (sites.query index)
  deliveryFound : ∀ index, Domain.templateOrigin context plan.deliveryTemplate [index] = some (sites.delivery index)
  lowMessage : ∀ index, (sites.low index).request = none
  highMessage : ∀ index, (sites.high index).request = none
  deliveryMessage : ∀ index, (sites.delivery index).request = none
  append : ∀ point challenge,
    Domain.callHelper (ringModel F G) program plan.appendHelper [.data (.vector field)]
      [.data (.vector field point), .data (.field field challenge)] =
        .returned [.data (.vector field (point ++ [challenge]))]

variable {field : String} {program : Structured.Program} {context : Context}
  {plan : CompiledRound.Plan} {sites : Nominal.Schedule field}

/-- The entire output witnesses its exact reached history. -/
def RoundPost (captured : Domain.Environment (uniformCarriers F G)) (index : Nat)
    (state : State F G) (reached : Domain.History (uniformCarriers F G))
    (output : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ low high challenge, reached = (advance field sites index state low high challenge).history ∧
    output = CompiledRound.output field context.suite captured index state.point state.scalar state.history
      (sites.low index) (sites.high index) (sites.query index) (sites.delivery index) low high challenge

 theorem round_reading (connection : RoundConnection (F := F) (G := G) field program context plan sites)
    (captured : Domain.Environment (uniformCarriers F G)) (index : Nat) (state : State F G) :
    ReadingTo (Nominal.interface (G := G) field) (RoundPost (context := context) (sites := sites) captured index state)
      state.history
      (CompiledRound.block plan program context field captured.length
        (CompiledRound.input field context.suite captured index state.point state.scalar state.history))
      (CompiledRound.presented field context.suite captured index state.point state.scalar state.history
        (sites.low index) (sites.high index) (sites.query index) (sites.delivery index) (sites.request index)) := by
  apply CompiledRound.reading plan program context field captured index state.point state.scalar state.history
    (sites.low index) (sites.high index) (sites.query index) (sites.delivery index)
    (connection.lowFound index) (connection.highFound index) (connection.queryFound index)
    (connection.deliveryFound index) (connection.lowMessage index) (connection.highMessage index)
    (connection.deliveryMessage index) (sites.request index) connection.append
  intro low high challenge _
  exact ⟨low, high, challenge, rfl, rfl⟩

 theorem round_coherent (connection : RoundConnection (F := F) (G := G) field program context plan sites)
    (captured : Domain.Environment (uniformCarriers F G)) (index : Nat) (state : State F G) :
    CoherentTo (RoundPost (context := context) (sites := sites) captured index state) state.history
      (CompiledRound.block plan program context field captured.length
        (CompiledRound.input field context.suite captured index state.point state.scalar state.history)) := by
  apply CompiledRound.coherent plan program context field captured index state.point state.scalar state.history
    (sites.low index) (sites.high index) (sites.query index) (sites.delivery index)
    (connection.lowFound index) (connection.highFound index) (connection.queryFound index)
    (connection.deliveryFound index) (connection.lowMessage index) (connection.highMessage index)
    (connection.deliveryMessage index) (sites.request index) connection.append
  intro low high challenge _
  exact ⟨low, high, challenge, rfl, rfl⟩

/-- Successful loop output has the precise returned prefix, scalar and history. -/
def LoopPost (initialLength count : Nat) (reached : Domain.History (uniformCarriers F G))
    (output : Domain.Environment (uniformCarriers F G)) : Prop :=
  ∃ state : State F G, state.history = reached ∧ state.point.length = initialLength + count ∧
    output = carried field context.suite state

def decode (values : Domain.Environment (uniformCarriers F G)) : Option (State F G) :=
  match values with
  | [.data (.vector _ point), .data (.field _ scalar), .transcript _ history] =>
      some ⟨point, scalar, history⟩
  | _ => none

noncomputable def continueLoop (field suite : String) (sites : Nominal.Schedule field)
    (offset : Nat) (rest : List Nat) (output : Domain.Environment (uniformCarriers F G)) :
    PIR.Process (Nominal.signature F field) (Domain.Environment (uniformCarriers F G)) :=
  match Domain.read output [offset + 21, offset + 26, offset + 20] >>= decode with
  | none => .halt .refused
  | some next => (run field sites rest next).bind (fun final => .done (carried field suite final))

 theorem loop_reading (connection : RoundConnection (F := F) (G := G) field program context plan sites)
    (captured : Domain.Environment (uniformCarriers F G)) (indices : List Nat) (state : State F G) :
    ReadingTo (Nominal.interface (G := G) field)
      (LoopPost (field := field) (context := context) state.point.length indices.length) state.history
      (Domain.iterate (CompiledRound.block plan program context field captured.length) captured
        [captured.length + 21, captured.length + 26, captured.length + 20]
        [.data (.vector field), .data (.field field), .transcript context.suite]
        indices (carried field context.suite state))
      ((run field sites indices state).bind (fun final => .done (carried field context.suite final))) := by
  induction indices generalizing state with
  | nil => exact .done _ _ ⟨state, rfl, by simp, rfl⟩
  | cons index rest ih =>
    change ReadingTo _ _ _ ((CompiledRound.block plan program context field captured.length
      (CompiledRound.input field context.suite captured index state.point state.scalar state.history)).bind _) _
    have rightEq :
        (CompiledRound.presented field context.suite captured index state.point state.scalar state.history
          (sites.low index) (sites.high index) (sites.query index) (sites.delivery index) (sites.request index)).bind
            (continueLoop field context.suite sites captured.length rest) =
        (run field sites (index :: rest) state).bind (fun final => .done (carried field context.suite final)) := by
      simp only [CompiledRound.presented, run, PIR.Process.bind]
      congr 1
      funext low
      congr 1
      funext high
      split
      · simp only [PIR.Process.bind]
        congr 1
        funext challenge
        congr 1
        funext delivered
        simp only [continueLoop, CompiledRound.output_yielded, Option.bind_some, decode, PIR.Process.bind]
        rfl
      · rfl
    rw [← rightEq]
    apply (round_reading connection captured index state).bind
    intro reached output post
    obtain ⟨low, high, challenge, reachedEq, rfl⟩ := post
    subst reached
    rw [CompiledRound.output_yielded]
    simp only [Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, List.map_cons,
      List.map_nil, beq_self_eq_true, ite_true]
    simp only [continueLoop, CompiledRound.output_yielded, Option.bind_some, decode]
    apply (ih (advance field sites index state low high challenge)).weaken
    intro reached final holds
    obtain ⟨next, historyEq, lengthEq, outputEq⟩ := holds
    exact ⟨next, historyEq, by simpa [advance, List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using lengthEq, outputEq⟩

 theorem loop_coherent (connection : RoundConnection (F := F) (G := G) field program context plan sites)
    (captured : Domain.Environment (uniformCarriers F G)) (indices : List Nat) (state : State F G) :
    CoherentTo (LoopPost (field := field) (context := context) state.point.length indices.length) state.history
      (Domain.iterate (CompiledRound.block plan program context field captured.length) captured
        [captured.length + 21, captured.length + 26, captured.length + 20]
        [.data (.vector field), .data (.field field), .transcript context.suite]
        indices (carried field context.suite state)) := by
  induction indices generalizing state with
  | nil => exact .done _ _ ⟨state, rfl, by simp, rfl⟩
  | cons index rest ih =>
    change CoherentTo _ _ ((CompiledRound.block plan program context field captured.length
      (CompiledRound.input field context.suite captured index state.point state.scalar state.history)).bind _)
    apply (round_coherent connection captured index state).bind
    intro reached output post
    obtain ⟨low, high, challenge, reachedEq, rfl⟩ := post
    subst reached
    rw [CompiledRound.output_yielded]
    simp only [Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, List.map_cons,
      List.map_nil, beq_self_eq_true, ite_true]
    apply (ih (advance field sites index state low high challenge)).weaken
    intro reached final holds
    obtain ⟨next, historyEq, lengthEq, outputEq⟩ := holds
    exact ⟨next, historyEq, by simpa [advance, List.length_append, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using lengthEq, outputEq⟩

 theorem loop_bridge (connection : RoundConnection (F := F) (G := G) field program context plan sites)
    (captured : Domain.Environment (uniformCarriers F G)) (indices : List Nat) (state : State F G) :
    Bridge (Nominal.interface (G := G) field)
      (LoopPost (field := field) (context := context) state.point.length indices.length) state.history
      (Domain.iterate (CompiledRound.block plan program context field captured.length) captured
        [captured.length + 21, captured.length + 26, captured.length + 20]
        [.data (.vector field), .data (.field field), .transcript context.suite]
        indices (carried field context.suite state))
      ((run field sites indices state).bind (fun final => .done (carried field context.suite final))) :=
  ⟨loop_reading connection captured indices state, loop_coherent connection captured indices state⟩

end ZkcSecurity.Families.Sumcheck.CompiledValidator
