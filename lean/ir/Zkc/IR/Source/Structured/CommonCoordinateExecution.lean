module

public import Zkc.IR.Source.Structured.CommonCoordinateInvariant
public import Zkc.IR.Source.Structured.CommonCoordinateReport

@[expose] public section

/-! Source-prefix readback uses successful replies of the actual operation process.
A stopped process has no successful continuation. The relation permits every external
reply; it does not assume honest delivery or a common provider. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

inductive Returned {I : PIR.Signature} {A : Type} : PIR.Process I A → A → Prop where
  | done (value : A) : Returned (.done value) value
  | call {op next value} (reply : I.Reply op) (tail : Returned (next reply) value) :
      Returned (.call op next) value

theorem Returned.of_run {I : PIR.Signature} {A S E : Type}
    (process : PIR.Process I A) (handler : PIR.Handler I S E) (state : S) (value : A)
    (success : (process.run handler state).outcome = .returned value) : Returned process value := by
  induction process generalizing state with
  | done result => cases success; exact .done _
  | halt reason => cases success
  | call op next ih =>
    cases result : handler op state with
    | mk outcome final events =>
      cases outcome with
      | stopped reason => simp [PIR.Process.run, result, PIR.Execution.follow] at success
      | returned reply =>
        exact .call reply (ih reply final (by
          simpa only [PIR.Process.run, result, PIR.Execution.follow] using success))

theorem Returned.done_eq {I : PIR.Signature} {A : Type} {left right : A}
    (returned : Returned (I := I) (.done left) right) : right = left := by
  cases returned
  rfl

variable {model : DomainModel} {scope : Scope}

def Pair.includes (pair : Pair) (self : Nat) : Prop := self = pair.left ∨ self = pair.right

theorem Pair.selected_self {pair : Pair} {self : Nat} (member : pair.includes self)
    (roles : Nat → Nat) (selected : List Nat) (active : pair.selected roles selected = true) :
    (selected.map roles).contains self = true := by
  simp only [Pair.selected, Bool.and_eq_true] at active
  rcases member with rfl | rfl
  · exact active.1
  · exact active.2

theorem matches_mask {types : List Ty} (pair : Pair) (self : Nat)
    (member : pair.includes self) (context : ProtocolContext) (scopes : List (List Nat))
    (symbols : Symbols scope types) (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) types)
    (matched : Matches symbols observations values) :
    Matches (maskSymbols pair context.roles scopes symbols) observations
      (maskValues self (context.mapScopes scopes) values) := by
  induction symbols generalizing scopes with
  | nil => cases values; intro ty position; cases position
  | cons symbol symbols ih =>
    cases values with | cons value values =>
      intro ty position term known
      cases position with
      | here =>
        change (if pair.selected context.roles (scopes.headD []) then symbol else none) =
          some term at known
        split at known
        · rename_i selected
          have active := pair.selected_self member context.roles (scopes.headD []) selected
          have mapped : (context.mapScopes scopes).headD [] =
              (scopes.headD []).map context.roles := by cases scopes <;> rfl
          change (Participant.restrict _ value).bind ProtocolValue.toConcrete = _
          rw [mapped, active, Participant.restrict]
          exact matched .here term known
        · contradiction
      | there position =>
        cases scopes <;> exact ih _ values
          (fun position term known ↦ matched (.there position) term known) position term known

theorem matches_split_right {left right : List Ty} (symbols : Symbols scope (left ++ right))
    (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) (left ++ right))
    (matched : Matches symbols observations values) :
    Matches (symbols.split left).2 observations (values.split left).2 := by
  induction left with
  | nil => exact matched
  | cons ty left ih =>
    cases symbols with | cons symbol symbols =>
      cases values with | cons value values =>
        exact ih symbols values (fun position term known ↦ matched (.there position) term known)

theorem matches_hide {types : List Ty} (pair : Pair) (roles : Nat → Nat)
    (scopes : List (List Nat)) (symbols : Symbols scope types)
    (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) types)
    (matched : Matches symbols observations values) :
    Matches (maskSymbols pair roles scopes symbols) observations values := by
  induction symbols generalizing scopes with
  | nil => cases values; intro ty position; cases position
  | cons symbol symbols ih =>
    cases values with | cons value values =>
      intro ty position term known
      cases position with
      | here =>
        change (if pair.selected roles (scopes.headD []) then symbol else none) = some term at known
        split at known
        · exact matched .here term known
        · contradiction
      | there position =>
        exact ih (scopes.drop 1) values
          (fun position term known ↦ matched (.there position) term known) position term known

/-- Repeat state is deliberately unconstrained. Only the actual counter and the actual
ordered captures enter the callback environment. This is independent of peer loop counts. -/
theorem matches_callback (pair : Pair) (roles : Nat → Nat) (spec : RepeatSpec)
    (symbols : Symbols scope (.index :: (spec.state ++ spec.captures)))
    (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers))
      (.index :: (spec.state ++ spec.captures)))
    (matched : Matches symbols observations values) (index : Nat)
    (state : Values (Component (ProtocolValue model.toCarriers)) spec.state) :
    Matches (callbackSymbols pair roles spec symbols) (.cons (some index) observations)
      (.cons (some (ProtocolValue.ofConcrete .index index))
        (state.append ((laterEntries values).split spec.state).2)) := by
  cases symbols with | cons symbol symbols =>
    cases values with | cons value values =>
      have captures : Matches (symbols.split spec.state).2 observations
          (values.split spec.state).2 := matches_split_right symbols observations values
        (fun position term known ↦ matched (.there position) term known)
      have hidden : Matches (maskSymbols pair roles
          (List.replicate spec.captures.length spec.roles) (symbols.split spec.state).2)
          observations (values.split spec.state).2 :=
        matches_hide pair roles _ _ observations _ captures
      have weakened : Matches (weakenSymbols (maskSymbols pair roles
          (List.replicate spec.captures.length spec.roles) (symbols.split spec.state).2))
          (.cons (some index) observations) (values.split spec.state).2 :=
        matches_weaken _ observations (some index) _ hidden
      have rest : Matches _ _ (state.append (values.split spec.state).2) := matches_append (unknown (.value .index :: scope) spec.state) _
        (.cons (some index) observations) state _ (matches_unknown _ _) weakened
      intro ty position term known
      cases position with
      | here =>
        have same : term = .var .here := (Option.some.inj known).symm
        subst term
        simp only [Values.get, ProtocolValue.toConcrete_ofConcrete, Option.bind_some, observe]
      | there position => exact rest position term known

theorem transfer_calculate (pair : Pair) (roles : Nat → Nat) (op : Op)
    (allowed : op.isCalculation = true) (symbols : Symbols scope op.arguments) :
    transfer pair roles (.calculate op allowed) symbols = calculation op symbols := rfl

/-- Every known transfer result is read back from the actual successful source action.
All other actions, including receives and service replies, produce no common symbol. -/
theorem transfer_sound (pair : Pair) (self : Nat) (member : pair.includes self)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model))
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (context : ProtocolContext) (op : ProtocolOp)
    (symbols : Symbols scope op.arguments) (observations : Observations model scope)
    (args : Values (Component (ProtocolValue model.toCarriers)) op.arguments)
    (matched : Matches symbols observations args)
    (callbacks : Values (RegionFunction (Component (ProtocolValue model.toCarriers))
      (OracleProtocol.Interface model)) op.regions)
    (results : Values (Component (ProtocolValue model.toCarriers)) op.results)
    (returned : Returned ((OracleProtocol.algebra model self ordinary helpers).operation
      protocols context self op args callbacks) results) :
    Matches (transfer pair context.roles op symbols) observations results := by
  cases op with
  | calculate op allowed =>
    change Symbols scope op.arguments at symbols
    change Matches (calculation op symbols) observations results
    unfold calculation
    split
    · rename_i supported
      cases found : collect symbols with
      | none =>
        simp only [Option.map_none, Option.getD_none]
        exact matches_unknown observations results
      | some terms =>
        simp only [Option.map_some, Option.getD_some]
        have equation := scalar_operation (OracleProtocol.demand model) self ordinary helpers
          op supported args
        change Returned (ProtocolCalculation.operation model (OracleProtocol.demand model)
          self ordinary helpers op args) results at returned
        rw [equation] at returned
        have same := returned.done_eq
        subst results
        intro ty position term known
        exact calculated_readback op supported terms observations args
          (collected_readback symbols observations args matched terms found) position term known
    · exact matches_unknown observations results
  | restrict ty selected =>
    cases symbols with | cons symbol tail =>
      cases tail
      cases args with | cons value tail =>
        cases tail
        have same := returned.done_eq
        subst results
        intro type position term known
        cases position with
        | here =>
          change (if pair.selected context.roles selected then symbol else none) = some term at known
          split at known
          · rename_i active
            have selectedSelf := pair.selected_self member context.roles selected active
            change (Participant.restrict _ value).bind ProtocolValue.toConcrete = _
            rw [selectedSelf, Participant.restrict]
            exact matched .here term known
          · contradiction
        | there position => cases position
  | _ => exact matches_unknown observations results

end Zkc.Source.Structured.CommonCoordinate
