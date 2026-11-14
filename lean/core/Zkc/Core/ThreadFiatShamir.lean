module

public import Zkc.Core.ThreadRules

public section

/-! The Fiat–Shamir rule is sound: what it emits runs as its meaning.

`Absorber.run` and `Deriver.run` are what one role does to absorb a value or derive a coin,
as a process over the role's membership in the side: the catalogue's row applied to the
state, the label and the value, or the source suite's function; nothing when the role is
outside the side. `fiatShamirMeaning` composes them as the rule does: an exchange is the
exchange followed by the prover's and the verifier's absorption; a draw is the verifier's
and the prover's derivation. `fiatShamirRule_sound` is `RuleSound` for the rule, for both
kinds of suite and every side.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Steps

variable {model : Model}

/-- A role's step that returns given values holds them when the role is in the side. -/
theorem performStep_const {inputs outputs : List Ty} (values : Values model.Value outputs) :
    ∀ (present : Bool) (arguments : Values (fun type => Held (model.Value type) present) inputs),
      performStep model (fun _ => PIR.Process.done values) present arguments =
        .done (holdValues present values)
  | true, _ => rfl
  | false, _ => rfl

end Steps

section Run

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- What a role does to absorb a value, for its membership in the side. -/
@[expose] def Absorber.run (functionTable : FunctionTable model functions) {state type : Ty}
    (absorber : Absorber operations functions state type) (present : Bool)
    (current : Held (model.Value state) present) (value : Held (model.Value type) present) :
    PIR.Process (Effects model) (Held (model.Value state) present) :=
  match absorber with
  | .row label name absorb applies =>
      (performStep model (rowProcess model (.of absorb) .pure applies) present
        (.cons current
          (.cons ((holdValues present (Values.cons (model.literal label name) .nil)).get .here)
            (.cons value .nil)))).bind fun absorbed => .done (absorbed.get .here)
  | .handler callee =>
      (performStep model (fun values => functionTable.get callee values) present
        (.cons current (.cons value .nil))).bind fun absorbed => .done (absorbed.get .here)

/-- What a role does to derive a coin: the coin and the next state. -/
@[expose] def Deriver.run (functionTable : FunctionTable model functions) {state output : Ty}
    (deriver : Deriver operations functions state output) (present : Bool)
    (current : Held (model.Value state) present) :
    PIR.Process (Effects model)
      (Held (model.Value output) present × Held (model.Value state) present) :=
  match deriver with
  | .row label name derive applies =>
      (performStep model (rowProcess model (.of derive) .pure applies) present
        (.cons current
          (.cons ((holdValues present (Values.cons (model.literal label name) .nil)).get .here)
            .nil))).bind fun derived => .done (derived.get .here, derived.tail.get .here)
  | .handler callee =>
      (performStep model (fun values => functionTable.get callee values) present
        (.cons current .nil)).bind fun derived => .done (derived.get .here, derived.tail.get .here)

variable {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {side : Side}

/-- What an absorber emits yields the role's absorption: after it the environment holds
the next state at the produced value. -/
theorem Absorber.emit_yields {state type : Ty} (absorber : Absorber operations functions state type)
    (role : Nat) {Δ : List Located} (current : Var Δ ⟨state, role⟩) (value : Var Δ ⟨type, role⟩) :
    ∃ later : Environment (SideValue model side) Δ → Held (model.Value state) (side role) →
        Environment (SideValue model side)
          (absorber.emit (protocols := protocols) (deployed := deployed) role current value).context,
      ∀ env : Environment (SideValue model side) Δ,
        (absorber.emit (protocols := protocols) (deployed := deployed) role current value).Yields
            (labelledMeaning model label functionTable table side) env
            (absorber.run functionTable (side role) (env current) (env value)) (later env) ∧
          ∀ result, later env result
            ((absorber.emit (protocols := protocols) (deployed := deployed) role current
              value).values.get .here) = result := by
  cases absorber with
  | row name literal absorb applies =>
      refine ⟨fun env result => Environment.bindAll
          (Environment.bindAll env
            (remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located))
              [.nominal name] (holdValues (side role) (Values.cons (model.literal name literal) .nil))))
          (Values.cons result .nil), fun env => ⟨?_, fun _ => rfl⟩⟩
      refine ((Emitted.operation_yields (labelledMeaning model label functionTable table side)
          (.at role (.literal (.nominal name literal)) .nil) .nil .nil env).andThen
        (fun named => Emitted.operation_yields (labelledMeaning model label functionTable table side)
          (.at role (.op absorb applies) .nil) _ .nil (Environment.bindAll env named)) _).reindex _
        (fun result : Held (model.Value state) (side role) =>
          (remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located))
            [.nominal name] (holdValues (side role) (Values.cons (model.literal name literal) .nil)),
            Values.cons result .nil)) ?_
      simp only [Absorber.run, labelledOperation, localOperation, performStep_const, Operands.eval,
        Emitted.operation_keeps, PIR.Process.bind_assoc]
      rfl
  | handler callee =>
      refine ⟨fun env result => Environment.bindAll env (Values.cons result .nil),
        fun env => ⟨?_, fun _ => rfl⟩⟩
      refine (Emitted.operation_yields (labelledMeaning model label functionTable table side)
          (.at role (.call callee (Bool.and_false _)) .nil) (.cons current (.cons value .nil)) .nil
          env).reindex _
        (fun result : Held (model.Value state) (side role) => Values.cons result .nil) ?_
      simp only [Absorber.run, labelledOperation, localOperation, Operands.eval,
        PIR.Process.bind_assoc]
      rfl

/-- What a deriver emits yields the role's derivation: after it the environment holds the
coin and the next state at the produced values. -/
theorem Deriver.emit_yields {state output : Ty} (deriver : Deriver operations functions state output)
    (role : Nat) {Δ : List Located} (current : Var Δ ⟨state, role⟩) :
    ∃ later : Environment (SideValue model side) Δ →
        Held (model.Value output) (side role) × Held (model.Value state) (side role) →
        Environment (SideValue model side)
          (deriver.emit (protocols := protocols) (deployed := deployed) role current).context,
      ∀ env : Environment (SideValue model side) Δ,
        (deriver.emit (protocols := protocols) (deployed := deployed) role current).Yields
            (labelledMeaning model label functionTable table side) env
            (deriver.run functionTable (side role) (env current)) (later env) ∧
          ∀ result,
            later env result ((deriver.emit (protocols := protocols) (deployed := deployed) role
              current).values.get .here) = result.1 ∧
            later env result ((deriver.emit (protocols := protocols) (deployed := deployed) role
              current).values.get (.there .here)) = result.2 := by
  cases deriver with
  | row name literal derive applies =>
      refine ⟨fun env result => Environment.bindAll
          (Environment.bindAll env
            (remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located))
              [.nominal name] (holdValues (side role) (Values.cons (model.literal name literal) .nil))))
          (Values.cons result.1 (Values.cons result.2 .nil)), fun env => ⟨?_, fun _ => ⟨rfl, rfl⟩⟩⟩
      refine ((Emitted.operation_yields (labelledMeaning model label functionTable table side)
          (.at role (.literal (.nominal name literal)) .nil) .nil .nil env).andThen
        (fun named => Emitted.operation_yields (labelledMeaning model label functionTable table side)
          (.at role (.op derive applies) .nil) _ .nil (Environment.bindAll env named)) _).reindex _
        (fun result : Held (model.Value output) (side role) × Held (model.Value state) (side role) =>
          (remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located))
            [.nominal name] (holdValues (side role) (Values.cons (model.literal name literal) .nil)),
            Values.cons result.1 (Values.cons result.2 .nil))) ?_
      simp only [Deriver.run, labelledOperation, localOperation, performStep_const, Operands.eval,
        Emitted.operation_keeps, PIR.Process.bind_assoc]
      rfl
  | handler callee =>
      refine ⟨fun env result => Environment.bindAll env
          (Values.cons result.1 (Values.cons result.2 .nil)),
        fun env => ⟨?_, fun _ => ⟨rfl, rfl⟩⟩⟩
      refine (Emitted.operation_yields (labelledMeaning model label functionTable table side)
          (.at role (.call callee (Bool.and_false _)) .nil) (.cons current .nil) .nil env).reindex _
        (fun result : Held (model.Value output) (side role) × Held (model.Value state) (side role) =>
          Values.cons result.1 (Values.cons result.2 .nil)) ?_
      simp only [Deriver.run, labelledOperation, localOperation, Operands.eval,
        PIR.Process.bind_assoc]
      rfl

end Run

section Rule

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- What the Fiat–Shamir rule does for a side. An exchange from the prover to the verifier
is the exchange, then the prover's absorption of its value and the verifier's absorption of
the value it received. A draw between the two is the verifier's derivation and the
prover's; no coin is drawn or announced. -/
@[expose] def fiatShamirMeaning (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) :
    RuleMeaning model ⟨suite.state, suite.state⟩ operations where
  exchange := fun prover verifier place site effects type value state =>
    match suite.absorb (place.label site) type with
    | some absorber =>
        (exchangeStep model effects type prover verifier
          value).bind fun received =>
          (absorber.run functionTable prover state.1 value).bind fun atProver =>
            (absorber.run functionTable verifier state.2 received).bind
              fun atVerifier => .done (received, (atProver, atVerifier))
    | none => .halt .refused
  draw := fun prover verifier place site _ inputs output law state =>
    if inputs.isEmpty then
      match suite.derive (place.label site) law.index output with
      | some deriver =>
          (deriver.run functionTable verifier state.2).bind fun atVerifier =>
            (deriver.run functionTable prover state.1).bind fun atProver =>
              .done ((atProver.1, atVerifier.1), (atProver.2, atVerifier.2))
      | none => .halt .refused
    else .halt .refused

/-- The Fiat–Shamir rule is sound. -/
theorem fiatShamirRule_sound (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) :
    RuleSound (fiatShamirRule suite) (fiatShamirMeaning suite functionTable) functionTable := by
  refine ⟨?_, ?_⟩
  · intro protocols deployed table label side place site type Δ value first second emitted emits env
    simp only [fiatShamirRule] at emits
    split at emits
    · cases emits
    · rename_i absorber hasAbsorber
      have same := Except.ok.inj emits
      subst same
      obtain ⟨laterProver, yieldsProver⟩ := absorber.emit_yields (model := model)
        (protocols := protocols) (deployed := deployed) (functionTable := functionTable)
        (table := table) (label := label) (side := side) place.roles.prover
        (first.extend (Emitted.operation
          (dialect := ProtocolDialect operations functions protocols deployed)
          (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil) .nil).grows)
        (value.extend (Emitted.operation
          (dialect := ProtocolDialect operations functions protocols deployed)
          (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil) .nil).grows)
      obtain ⟨laterVerifier, yieldsVerifier⟩ := absorber.emit_yields (model := model)
        (protocols := protocols) (deployed := deployed) (functionTable := functionTable)
        (table := table) (label := label) (side := side) place.roles.verifier
        ((second.extend (Emitted.operation
          (dialect := ProtocolDialect operations functions protocols deployed)
          (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil)
          .nil).grows).extend (absorber.emit (protocols := protocols) (deployed := deployed)
            place.roles.prover _ _).grows)
        (((Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
          (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil)
          .nil).values.get .here).extend (absorber.emit (protocols := protocols)
            (deployed := deployed) place.roles.prover _ _).grows)
      have keepsProver := fun middle result {ty : Located} reference =>
        (yieldsProver middle).1.keeps result (ty := ty) reference
      have keepsVerifier := fun middle result {ty : Located} reference =>
        (yieldsVerifier middle).1.keeps result (ty := ty) reference
      have key : ∀ (results : List Located) (values : Operands _ results),
          (Emitted.andThen (results := results)
            ((Emitted.operation (dialect := ProtocolDialect operations functions protocols deployed)
              (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil)
              .nil).andThen (absorber.emit place.roles.prover _ _) (absorber.emit
                place.roles.prover _ _).values)
            (absorber.emit place.roles.verifier _ _) values).Yields
            (labelledMeaning model label functionTable table side) env
            ((fiatShamirMeaning suite functionTable).exchange (side place.roles.prover) (side place.roles.verifier) place site (label site) type
              (env value) (env first, env second))
            (fun result => laterVerifier
              (laterProver (Environment.bindAll env (Values.cons result.1 .nil)) result.2.1)
              result.2.2) := by
        intro results values
        refine (((Emitted.operation_yields (labelledMeaning model label functionTable table side)
            (.exchange place.roles.prover place.roles.verifier site type) (.cons value .nil) .nil
            env).andThen (fun sent => (yieldsProver (Environment.bindAll env sent)).1) _).andThen
          (fun pair => (yieldsVerifier (laterProver (Environment.bindAll env pair.1) pair.2)).1)
          values).reindex _
          (fun (result : SideValue model side ⟨type, place.roles.verifier⟩ ×
              ThreadState model ⟨suite.state, suite.state⟩ (side place.roles.prover)
                (side place.roles.verifier)) =>
            ((Values.cons result.1 .nil, result.2.1), result.2.2)) ?_
        simp only [fiatShamirMeaning, hasAbsorber, labelledOperation, Operands.eval,
          PIR.Process.bind_assoc]
        refine bind_congr rfl fun received => ?_
        show (Absorber.run functionTable absorber (side place.roles.prover) _ _).bind _ =
          (Absorber.run functionTable absorber (side place.roles.prover) _ _).bind _
        refine bind_congr rfl fun atProver => ?_
        show (Absorber.run functionTable absorber (side place.roles.verifier) _ _).bind _ =
          (Absorber.run functionTable absorber (side place.roles.verifier) _ _).bind _
        exact bind_congr
          (congr (congrArg (Absorber.run functionTable absorber (side place.roles.verifier))
            (keepsProver _ _ _)) (keepsProver _ _ _)) fun atVerifier => rfl
      refine ⟨_, (key _ _).runs, fun result => ⟨?_, ?_, ?_, fun reference =>
        (key _ _).keeps result reference⟩⟩
      · exact (keepsVerifier _ _ _).trans (keepsProver _ _ _)
      · exact (keepsVerifier _ _ _).trans ((yieldsProver _).2 _)
      · exact (yieldsVerifier _).2 _
  · intro protocols deployed table label side place site inputs output law Δ first second emitted
      emits env
    simp only [fiatShamirRule] at emits
    split at emits
    · rename_i empty
      split at emits
      · cases emits
      · rename_i deriver hasDeriver
        have same := Except.ok.inj emits
        subst same
        obtain ⟨laterVerifier, yieldsVerifier⟩ := deriver.emit_yields (model := model)
          (protocols := protocols) (deployed := deployed) (functionTable := functionTable)
          (table := table) (label := label) (side := side) place.roles.verifier second
        obtain ⟨laterProver, yieldsProver⟩ := deriver.emit_yields (model := model)
          (protocols := protocols) (deployed := deployed) (functionTable := functionTable)
          (table := table) (label := label) (side := side) place.roles.prover
          (first.extend (deriver.emit (protocols := protocols) (deployed := deployed)
            place.roles.verifier second).grows)
        have keepsProver := fun middle result {ty : Located} reference =>
          (yieldsProver middle).1.keeps result (ty := ty) reference
        have key : ∀ (results : List Located) (values : Operands _ results),
            (Emitted.andThen (results := results) (deriver.emit place.roles.verifier second)
              (deriver.emit place.roles.prover _) values).Yields
              (labelledMeaning model label functionTable table side) env
              ((fiatShamirMeaning suite functionTable).draw (side place.roles.prover) (side place.roles.verifier) place site (label site) law
                (env first, env second))
              (fun result => laterProver (laterVerifier env (result.1.2, result.2.2))
                (result.1.1, result.2.1)) := by
          intro results values
          refine ((yieldsVerifier env).1.andThen
            (fun atVerifier => (yieldsProver (laterVerifier env atVerifier)).1) values).reindex _
            (fun (result : (SideValue model side ⟨output, place.roles.prover⟩ ×
                  SideValue model side ⟨output, place.roles.verifier⟩) ×
                ThreadState model ⟨suite.state, suite.state⟩ (side place.roles.prover)
                  (side place.roles.verifier)) =>
              ((result.1.2, result.2.2), (result.1.1, result.2.1))) ?_
          simp only [fiatShamirMeaning, empty, hasDeriver, ↓reduceIte, PIR.Process.bind_assoc]
          refine bind_congr rfl fun atVerifier => ?_
          exact bind_congr
            (congrArg (Deriver.run functionTable deriver (side place.roles.prover))
              ((yieldsVerifier env).1.keeps _ _)) fun atProver => rfl
        refine ⟨_, (key _ _).runs, fun result => ⟨?_, ?_, ?_, ?_, fun reference =>
          (key _ _).keeps result reference⟩⟩
        · exact ((yieldsProver _).2 _).1
        · exact (keepsProver _ _ _).trans ((yieldsVerifier env).2 _).1
        · exact ((yieldsProver _).2 _).2
        · exact (keepsProver _ _ _).trans ((yieldsVerifier env).2 _).2
    · cases emits

end Rule

end Zkc.Core
