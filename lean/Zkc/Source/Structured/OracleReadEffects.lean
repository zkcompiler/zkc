module

public import Zkc.Source.DerivationLaws
public import Zkc.Source.Structured.OracleLocalAction
public import Zkc.Semantics.CallRestriction

@[expose] public section

/-! The source read handler may coexist with arbitrary prover and sampler
effects. Expanding even a nested virtual read can only ask the base provider.
Deterministic word reads therefore lift into any lawful experiment intact. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProcess
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {S E A B : Type}

private def baseOnly : (Interface model S E).Op → Prop
  | (.inl _, _) => False
  | (.inr _, _) => True

private theorem mapWithin {I : PIR.Signature} {allowed : I.Op → Prop} {p : PIR.Process I A}
    (ok : p.CallsWithin allowed) (change : A → B) : (mapResult change p).CallsWithin allowed :=
  ok.bind p _ fun _ ↦ trivial

private theorem presentWithin {I J : PIR.Signature} {T F : Type} {allowed : J.Op → Prop}
    (actions : (op : I.Op) → T → PIR.Process J (PIR.Execution T F (I.Reply op)))
    (localCalls : ∀ op state, (actions op state).CallsWithin allowed) (p : PIR.Process I A) (s : T) :
    (present actions p s).CallsWithin allowed := by
  induction p generalizing s with
  | done _ | halt _ => trivial
  | call op next ih =>
    apply (localCalls op s).bind
    intro result
    rcases result with ⟨outcome, post, events⟩
    cases outcome with
    | stopped why => trivial
    | returned reply => exact mapWithin (ih reply post) _

private theorem answerWithin (self : Nat) (entries : OracleEntries model snapshot domains math)
    (request : OracleRead) (state : S × Nat) :
    (answer (E := E) model self entries request state).CallsWithin baseOnly := by
  induction entries generalizing request state with
  | nil => trivial
  | cons entry older ih =>
    rcases entry with ⟨ty, table⟩
    simp only [answer]
    split
    · split
      · split
        · trivial
        · cases table.payload with
          | base data => exact mapWithin (show (baseCall (E := E) request state.1).CallsWithin baseOnly from
              ⟨trivial, fun _ ↦ trivial⟩) _
          | virtual checked type captures =>
            dsimp only
            split
            · apply mapWithin
              exact presentWithin _ (fun child current ↦ ih _ current) _ _
            · trivial
      · exact ih request state
    · exact ih request state

private theorem queryWithin (location : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (kind : OracleKind) (owner : Nat)
    (handle : Component (ProtocolValue model.toCarriers) (.oracle kind))
    (position : Component (ProtocolValue model.toCarriers) kind.query)
    (state : OracleRuntimeState model snapshot domains math S) :
    (query (E := E) model location self roles kind owner handle position state).CallsWithin baseOnly := by
  unfold query
  split
  · trivial
  · split
    · trivial
    · split
      · apply mapWithin
        exact mapWithin (answerWithin _ _ _ _) _
      · trivial

set_option smartUnfolding false in
private theorem operationWithin (oracles : List (CheckedOracle snapshot domains math))
    (location : OracleLocation) (self : Nat) (roles : Nat → Nat) (op : OracleOp)
    (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (state : OracleRuntimeState model snapshot domains math S) :
    (operation (E := E) model oracles location self roles op args state).CallsWithin baseOnly := by
  cases op <;> try trivial
  case query kind owner =>
    cases owner with
    | none => trivial
    | some owner => exact queryWithin _ _ _ _ _ _ _ _

/-- All logical actions before publication are independent of the ordinary
handler. This includes cursor refusal, role absence and failed expansions. -/
theorem logicalWithPureReads {m : Type → Type} [Monad m] [LawfulMonad m]
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E) (req : OracleRequest model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math S) :
    actionM model oracles ordinary (fun child s ↦ pure (base child s)) (.oracle req) state =
      pure (OracleProtocol.handler model oracles refusingOrdinary base (.oracle req) state) := by
  have onlyBase : (action (E := E) model oracles (.oracle req) state).CallsWithin baseOnly := by
    simp only [action]
    split
    · trivial
    · exact mapWithin (operationWithin _ _ _ _ _ _ _) _
  let stored := externalHandler (model := model) refusingOrdinary base
  refine Eq.trans ?_ (executeM_pure stored _ state _ (action_represents model oracles refusingOrdinary base _ state))
  unfold actionM executeM
  rw [onlyBase.runM_congr _ _ (handlerM (m := m) (fun op s ↦ pure (stored op s))) (by
    rintro ⟨op, supplied⟩ allowed current
    cases op with
    | inl ordinary => cases allowed
    | inr child => simp [handlerM, externalHandlerM, stored, externalHandler])]

end Zkc.Source.Structured.OracleProcess

namespace Zkc.Source.Structured.OracleProtocol

/-- The action of a source query with concrete receiver operands. The executed
frame supplies the invocation when the cursor admits this occurrence. -/
def tableQuery (model : DomainModel) (row : Ty) (fixed : Option Nat) (source : OracleAnchor)
    (position self owner : Nat) (roles : Nat → Nat) (site : OracleLocation) :
    OracleProtocolAction model.toCarriers :=
  let kind := OracleKind.table row fixed
  .oracle ⟨.query kind (some owner), site, self, roles,
    .cons (some (ProtocolValue.ofConcrete (.oracle kind) source))
      (.cons (some (ProtocolValue.ofConcrete .index position)) .nil)⟩

/-- The checked protocol algebra sends precisely this action to the handler. -/
theorem tableQueryStep (model : DomainModel) (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (Interface model))
    (table : ProtocolTable (ProtocolValue model.toCarriers) (Interface model))
    (context : ProtocolContext) (row : Ty) (fixed : Option Nat) (source : OracleAnchor)
    (position owner : Nat) (site : OracleLocation) :
    ((algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun op ↦ .call op .done) (.oracle (.query (.table row fixed) (some owner)) site)
      (.cons (some (ProtocolValue.ofConcrete (.oracle (.table row fixed)) source))
        (.cons (some (ProtocolValue.ofConcrete .index position)) .nil)) .nil
      (.call (tableQuery model row fixed source position self owner context.roles site) .done) :=
  RegionMeaning.OperationLaw.identity _ _ _ rfl

end Zkc.Source.Structured.OracleProtocol

namespace Zkc.Source.Structured.OraclePublication
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} {S E : Type}

/-- A logical query is read-only also at the publication boundary. -/
theorem queryWithPureReads {m : Type → Type} [Monad m] [LawfulMonad m]
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E)
    (kind : OracleKind) (owner : Nat) (site : OracleLocation) (self : Nat) (roles : Nat → Nat)
    (args : Values (Component (ProtocolValue model.toCarriers)) (.query kind (some owner) : OracleOp).arguments)
    (state : OracleProtocol.State model snapshot domains math S) :
    let op : OracleProtocolAction model.toCarriers := .oracle ⟨.query kind (some owner), site, self, roles, args⟩
    actionM model oracles ordinary (fun child s ↦ pure (base child s)) publish op state =
      pure (OracleProtocol.handler model oracles OracleProcess.refusingOrdinary base op state) := by
  dsimp only
  let op : OracleProtocolAction model.toCarriers := .oracle ⟨.query kind (some owner), site, self, roles, args⟩
  have none (result : PIR.Execution _ (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply op)) :
      request? op state result = none := by cases result; rfl
  change actionM model oracles ordinary _ publish op state = _
  rw [actionM, OracleProcess.logicalWithPureReads, pure_bind, afterM, none]
  simp only [pure_bind]

/-- The installed source query selects the actual invocation and row from its
cursor. A successful registry read returns its typed cell and the complete
provider state, count and ordered log. -/
theorem returnsCell {m : Type → Type} [Monad m] [LawfulMonad m]
    (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : PIR.MonadHandler m (participantInterfaceOn model.toCarriers) S E)
    (base : PIR.Handler (oracleReadInterface model.toCarriers) S E)
    (publish : PIR.MonadHandler m (Interface model) S E)
    (row : Ty) (fixed : Option Nat) (source : OracleAnchor) (position : Nat)
    (owner : Nat) (roles : Nat → Nat) (site : OracleLocation)
    (state : OracleProtocol.State model snapshot domains math S)
    (atDef : site.definition = state.frame.definition) (atRow : site.row = state.frame.row)
    (active : roles owner = state.oracle.self) (value : model.Value row) (final : S × Nat)
    (trace : List (OracleEvent E))
    (read : OracleStore.answer model base state.oracle.self state.oracle.entries
      ⟨.table row fixed, source, position, {site with invocation := state.frame.invocation}, []⟩
      (state.oracle.provider, state.oracle.queries) = ⟨.returned value, final, trace⟩) :
    actionM model oracles ordinary (fun child s ↦ pure (base child s)) publish
      (OracleProtocol.tableQuery model row fixed source position state.oracle.self owner roles site) state =
      pure ⟨.returned (.cons (some (ProtocolValue.ofConcrete row value)) .nil),
        {state with oracle := {state.oracle with provider := final.1, queries := final.2}},
        trace.map OracleProtocol.Event.logical⟩ := by
  dsimp only
  refine (queryWithPureReads oracles ordinary base publish (.table row fixed) owner site
    state.oracle.self roles _ state).trans ?_
  let location : OracleLocation := ⟨state.frame.invocation, state.frame.definition, state.frame.row⟩
  have siteEq : {site with invocation := state.frame.invocation} = location := by
    cases site
    simp_all [location]
  rw [siteEq] at read
  have meaning := OracleProcess.query_meaning model oracles base location state.oracle.self roles
    (.table row fixed) owner (some (ProtocolValue.ofConcrete (.oracle (.table row fixed)) source))
    (some (ProtocolValue.ofConcrete .index position)) state.oracle
  simp [active, Option.bind, OracleStore.read] at meaning
  have coordinate : @ProtocolValue.toConcrete model.toCarriers (.table row fixed : OracleKind).query
      (ProtocolValue.ofConcrete .index position) = some position :=
    ProtocolValue.toConcrete_ofConcrete .index position
  rw [coordinate] at meaning
  simp only [read] at meaning
  simp [OracleProtocol.handler, atDef, atRow]
  rw [meaning]
  rfl

end Zkc.Source.Structured.OraclePublication
