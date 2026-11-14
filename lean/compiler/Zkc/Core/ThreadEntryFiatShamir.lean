module

public import Zkc.Core.ThreadEntry
public import Zkc.Core.ThreadEntryEmitted
public import Zkc.Core.ThreadFiatShamir

public section

/-! What the entry of the Fiat–Shamir rule does, and that it does it.

`Suite.startRun` is what one role does to make its state at the start of the entry, for
its membership in the side, by the recursion of `startState`: a catalogue suite applies its
start row to the identity literal and then absorbs the role's copies of the statement in
order, each with the label of its position (`Suite.statementRun`, by the recursion of
`absorbStatement`); a source suite calls its start function on the role's copies
(`statementValues`, by the recursion of `statementOperands`). Where the suite has no row,
the rule refuses and the process stops.

`Suite.startRun_gives`: what `startState` emits runs as `Suite.startRun` and leaves the
state at the produced value.

`fiatShamirEntry`: the entry keeps its ports; the prover and then the verifier make their
states; after the body the two final states are dropped. `fiatShamirEntry_sound`: the
region that the rule makes of a threaded body runs the start, the body and the finish in
this order, for both kinds of suite and every side; the start and the finish perform no
effect over functions that perform none.

The module reads the bodies of `Absorber.run` and `QuietTable`, which their modules do not
expose.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Start

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- A role's copies of the statement as a side holds them, as the arguments of a start
function. -/
@[expose] def statementValues (side : Side) (role : Nat) {ports : List Located}
    (values : Values (SideValue model side) ports) :
    (statement : List (Agreement ports)) →
      Option (Values (SideValue model side) (Located.atRole role (statement.map (·.type))))
  | [] => some .nil
  | agreement :: rest =>
      match agreement.copyOf role, statementValues side role values rest with
      | some port, some tail => some (.cons (values.get port) tail)
      | _, _ => none

/-- A role absorbs its copies of the statement into its state, each with the label of its
position. -/
@[expose] def Suite.statementRun (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) (side : Side) (role : Nat)
    {ports : List Located} (values : Values (SideValue model side) ports) :
    Nat → List (Agreement ports) → Held (model.Value suite.state) (side role) →
      PIR.Process (Effects model) (Held (model.Value suite.state) (side role))
  | _, [], current => .done current
  | position, agreement :: rest, current =>
      match agreement.copyOf role, suite.absorb (.statement position) agreement.type with
      | some port, some absorber =>
          (absorber.run functionTable (side role) current (values.get port)).bind fun next =>
            suite.statementRun functionTable side role values (position + 1) rest next
      | _, _ => .halt .refused

/-- A role's state at the start of the entry, for its membership in the side. -/
@[expose] def Suite.startRun (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) (side : Side) (role : Nat)
    {ports : List Located} (statement : List (Agreement ports))
    (values : Values (SideValue model side) ports) :
    PIR.Process (Effects model) (Held (model.Value suite.state) (side role)) :=
  match suite.start (statement.map (·.type)) with
  | none => .halt .refused
  | some (.separator label identity row applies) =>
      (performStep model (rowProcess model (.of row) .pure applies) (side role)
        (.cons ((holdValues (side role) (Values.cons (model.literal label identity) .nil)).get .here)
          .nil)).bind fun started =>
        suite.statementRun functionTable side role values 0 statement (started.get .here)
  | some (.handler callee) =>
      match statementValues side role values statement with
      | some arguments =>
          (performStep model (fun inputs => functionTable.get callee inputs) (side role)
            (unmapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located)) _
              arguments)).bind fun started => .done (started.get .here)
      | none => .halt .refused

/-- What the entry of the Fiat–Shamir rule does. -/
@[expose] def fiatShamirEntry (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) :
    EntryMeaning model ⟨suite.state, suite.state⟩ (fiatShamirRule suite) where
  arguments := fun _ _ _ values => values
  start := fun side roles header values =>
    (suite.startRun functionTable side roles.prover (statementOf roles header) values).bind
      fun atProver =>
        (suite.startRun functionTable side roles.verifier (statementOf roles header) values).bind
          fun atVerifier => .done (atProver, atVerifier)
  finish := fun _ _ _ result => .done result.1

/-! ## The start performs no effect -/

/-- A role's absorption performs no effect over functions that perform none. -/
theorem Absorber.run_quiet {functionTable : FunctionTable model functions}
    (quiet : QuietTable functionTable) {state type : Ty}
    (absorber : Absorber operations functions state type) (present : Bool)
    (current : Held (model.Value state) present) (value : Held (model.Value type) present) :
    (absorber.run functionTable present current value).Quiet := by
  cases absorber with
  | row label name absorb applies =>
      exact PIR.Process.Quiet.bind
        (performStep_quiet (fun values => rowProcess_quiet _ _ _ values) _ _)
        fun _ => PIR.Process.Quiet.done _
  | handler callee =>
      exact PIR.Process.Quiet.bind (performStep_quiet (fun values => quiet callee values) _ _)
        fun _ => PIR.Process.Quiet.done _

/-- The absorption of the statement performs no effect over functions that perform none. -/
theorem Suite.statementRun_quiet (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (quiet : QuietTable functionTable)
    (side : Side) (role : Nat) {ports : List Located}
    (values : Values (SideValue model side) ports) :
    ∀ (statement : List (Agreement ports)) (position : Nat)
      (current : Held (model.Value suite.state) (side role)),
      (suite.statementRun functionTable side role values position statement current).Quiet
  | [], _, _ => PIR.Process.Quiet.done _
  | agreement :: rest, position, current => by
      unfold Suite.statementRun
      split
      · exact PIR.Process.Quiet.bind (Absorber.run_quiet quiet _ _ _ _) fun next =>
          Suite.statementRun_quiet suite quiet side role values rest (position + 1) next
      · exact PIR.Process.Quiet.halt _

/-- A role's start performs no effect over functions that perform none. -/
theorem Suite.startRun_quiet (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (quiet : QuietTable functionTable)
    (side : Side) (role : Nat) {ports : List Located} (statement : List (Agreement ports))
    (values : Values (SideValue model side) ports) :
    (suite.startRun functionTable side role statement values).Quiet := by
  unfold Suite.startRun
  split
  · exact PIR.Process.Quiet.halt _
  · exact PIR.Process.Quiet.bind
      (performStep_quiet (fun values => rowProcess_quiet _ _ _ values) _ _) fun started =>
        Suite.statementRun_quiet suite quiet side role values statement 0 _
  · split
    · exact PIR.Process.Quiet.bind (performStep_quiet (fun values => quiet _ values) _ _)
        fun _ => PIR.Process.Quiet.done _
    · exact PIR.Process.Quiet.halt _

/-! ## What the start emits -/

variable {protocols : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}
  {label : Nat → Site} {side : Side}

local notation "𝒟" => ProtocolDialect operations functions protocols deployed

/-- A role's copies of the statement, read in an environment, are the copies of the values
of the ports. -/
theorem statementOperands_eval (role : Nat) {ports Δ : List Located} (operands : Operands Δ ports)
    (env : Environment (SideValue model side) Δ) :
    ∀ (statement : List (Agreement ports))
      (arguments : Operands Δ (Located.atRole role (statement.map (·.type)))),
      statementOperands role operands statement = some arguments →
        statementValues side role (Operands.eval env operands) statement =
          some (Operands.eval env arguments)
  | [], arguments, found => by
      cases Option.some.inj found
      rfl
  | agreement :: rest, arguments, found => by
      unfold statementOperands at found
      unfold statementValues
      split at found
      · rename_i port tail hasPort hasTail
        cases Option.some.inj found
        rw [hasPort, statementOperands_eval role operands env rest tail hasTail]
        exact congrArg some
          (congr (congrArg Values.cons (Operands.get_eval env operands port)) rfl)
      · cases found

/-- The absorption of a statement whose first part the role holds and the suite absorbs:
the first part, then the rest. -/
theorem Suite.statementRun_cons (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) (side : Side) (role : Nat)
    {ports : List Located} (values : Values (SideValue model side) ports) (position : Nat)
    (agreement : Agreement ports) (rest : List (Agreement ports))
    (current : Held (model.Value suite.state) (side role))
    {port : Var ports ⟨agreement.type, role⟩}
    {absorber : Absorber operations functions suite.state agreement.type}
    (hasPort : agreement.copyOf role = some port)
    (hasAbsorber : suite.absorb (.statement position) agreement.type = some absorber) :
    suite.statementRun functionTable side role values position (agreement :: rest) current =
      (absorber.run functionTable (side role) current (values.get port)).bind fun next =>
        suite.statementRun functionTable side role values (position + 1) rest next := by
  conv => lhs; unfold Suite.statementRun
  rw [hasPort, hasAbsorber]

/-- What `absorbStatement` emits after a sequence that gives a state gives the absorption
of the statement into that state. -/
theorem Suite.statementRun_gives (suite : Suite operations functions) (role : Nat)
    {ports Δ : List Located} (operands : Operands Δ ports)
    (env : Environment (SideValue model side) Δ) :
    ∀ (statement : List (Agreement ports)) (position : Nat)
      (sofar emitted : Emitted 𝒟 Δ [⟨suite.state, role⟩]),
      absorbStatement suite role operands position statement sofar = .ok emitted →
      ∀ (process : PIR.Process (Effects model) (Held (model.Value suite.state) (side role))),
        sofar.Gives (labelledMeaning model label functionTable table side) env process
          (fun later => later (sofar.values.get .here)) →
        emitted.Gives (labelledMeaning model label functionTable table side) env
          (process.bind fun current =>
            suite.statementRun functionTable side role (Operands.eval env operands) position
              statement current)
          (fun later => later (emitted.values.get .here))
  | [], position, sofar, emitted, made, process, gives => by
      cases Except.ok.inj made
      exact (PIR.Process.bind_done process).symm ▸ gives
  | agreement :: rest, position, sofar, emitted, made, process, gives => by
      unfold absorbStatement at made
      split at made
      · rename_i port absorber hasPort hasAbsorber
        obtain ⟨laterAbsorbed, absorbs⟩ := absorber.emit_yields (model := model)
          (protocols := protocols) (deployed := deployed) (functionTable := functionTable)
          (table := table) (label := label) (side := side) role (sofar.values.get .here)
          ((operands.get port).extend sofar.grows)
        have step : (sofar.andThen
              (absorber.emit (protocols := protocols) (deployed := deployed) role
                (sofar.values.get .here) ((operands.get port).extend sofar.grows))
              (absorber.emit (protocols := protocols) (deployed := deployed) role
                (sofar.values.get .here) ((operands.get port).extend sofar.grows)).values).Gives
            (labelledMeaning model label functionTable table side) env
            (process.bind fun current => absorber.run functionTable (side role) current
              ((Operands.eval env operands).get port))
            (fun later => later ((absorber.emit (protocols := protocols) (deployed := deployed)
              role (sofar.values.get .here)
              ((operands.get port).extend sofar.grows)).values.get .here)) :=
          gives.andThen
            (next := fun current => absorber.run functionTable (side role) current
              ((Operands.eval env operands).get port))
            (fullAfter := fun middle => absorber.run functionTable (side role)
              (middle (sofar.values.get .here)) (middle ((operands.get port).extend sofar.grows)))
            (laterAfter := laterAbsorbed)
            (fun middle => (absorbs middle).1)
            (fun middle keeps => by
              show _ = (absorber.run functionTable (side role) (middle (sofar.values.get .here))
                (middle ((operands.get port).extend sofar.grows))).bind _
              rw [keeps, ← Operands.get_eval env operands port]
              exact (PIR.Process.bind_done _).symm.trans (bind_congr rfl fun result =>
                congrArg PIR.Process.done ((absorbs middle).2 result).symm)) _
        have next := Suite.statementRun_gives suite role operands env rest (position + 1) _ emitted
          made _ step
        rw [PIR.Process.bind_assoc] at next
        have same : (fun current => suite.statementRun functionTable side role
            (Operands.eval env operands) position (agreement :: rest) current) =
            fun current => (absorber.run functionTable (side role) current
              ((Operands.eval env operands).get port)).bind fun next =>
                suite.statementRun functionTable side role (Operands.eval env operands)
                  (position + 1) rest next :=
          funext fun current => Suite.statementRun_cons suite functionTable side role _ position
            agreement rest current hasPort hasAbsorber
        rw [same]
        exact next
      · cases made

/-- What `startState` emits gives the role's start and leaves the state at the produced
value. -/
theorem Suite.startRun_gives (suite : Suite operations functions) (role : Nat)
    {ports Δ : List Located} (statement : List (Agreement ports)) (operands : Operands Δ ports)
    (emitted : Emitted 𝒟 Δ [⟨suite.state, role⟩])
    (made : startState suite role statement operands = .ok emitted)
    (env : Environment (SideValue model side) Δ) (values : Values (SideValue model side) ports)
    (reads : Operands.eval env operands = values) :
    emitted.Gives (labelledMeaning model label functionTable table side) env
      (suite.startRun functionTable side role statement values)
      (fun later => later (emitted.values.get .here)) := by
  subst reads
  unfold startState at made
  unfold Suite.startRun
  split at made
  · cases made
  · rename_i name identity row applies hasStart
    rw [hasStart]
    have starts := Suite.statementRun_gives (functionTable := functionTable) (table := table)
      (label := label) suite role operands env statement 0 _ emitted made
      ((performStep model (rowProcess model (.of row) .pure applies) (side role)
        (.cons ((holdValues (side role) (Values.cons (model.literal name identity) .nil)).get .here)
          .nil)).bind fun started => .done (started.get .here))
      (by
        refine ⟨_, _, _, ((Emitted.operation_yields
            (labelledMeaning model label functionTable table side)
            (.at role (.literal (.nominal name identity)) .nil) .nil .nil env).andThen
          (fun named => Emitted.operation_yields
            (labelledMeaning model label functionTable table side)
            (.at role (.op row applies) .nil) _ .nil (Environment.bindAll env named)) _).reindex
          ((performStep model (rowProcess model (.of row) .pure applies) (side role)
            (.cons ((holdValues (side role)
              (Values.cons (model.literal name identity) .nil)).get .here) .nil)).bind
            fun started => .done (started.get .here))
          (fun result : Held (model.Value suite.state) (side role) =>
            (remapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located))
              [.nominal name]
              (holdValues (side role) (Values.cons (model.literal name identity) .nil)),
              Values.cons result .nil)) ?_, ?_⟩
        · simp only [labelledOperation, localOperation, performStep_const, Operands.eval,
            Emitted.operation_keeps, PIR.Process.bind_assoc]
          rfl
        · exact (PIR.Process.bind_done _).symm)
    rw [PIR.Process.bind_assoc] at starts
    exact starts
  · rename_i callee hasStart
    rw [hasStart]
    split at made
    · rename_i arguments hasArguments
      cases Except.ok.inj made
      rw [statementOperands_eval role operands env statement arguments hasArguments]
      refine ⟨_, _, _, (Emitted.operation_yields
          (labelledMeaning model label functionTable table side)
          (.at role (.call callee (Bool.and_false _)) .nil) arguments .nil env).reindex
        ((performStep model (fun inputs => functionTable.get callee inputs) (side role)
          (unmapValues (F := SideValue model side) (fun type => (⟨type, role⟩ : Located)) _
            (Operands.eval env arguments))).bind fun started => .done (started.get .here))
        (fun result : Held (model.Value suite.state) (side role) => Values.cons result .nil)
        ?_, ?_⟩
      · simp only [labelledOperation, localOperation, Operands.eval, PIR.Process.bind_assoc]
        rfl
      · exact (PIR.Process.bind_done _).symm
    · cases made

end Start

section Entry

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- The entry of the Fiat–Shamir rule runs as its meaning says. -/
theorem fiatShamirEntry_sound (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) :
    EntrySound (fiatShamirRule suite) (fiatShamirEntry suite functionTable) functionTable := by
  refine ⟨?_, ?_, ?_⟩
  · intro protocols deployed table label side place header body region made inner bodyMeaning
      arguments
    simp only [fiatShamirRule] at made
    split at made
    · cases made
    · rename_i atProver startsProver
      split at made
      · cases made
      · rename_i atVerifier startsVerifier
        split at made
        · rename_i threaded threads
          cases Except.ok.inj made
          have givesProver := suite.startRun_gives (functionTable := functionTable)
            (table := table) (label := label) (side := side) place.roles.prover
            (statementOf place.roles header) (Operands.newest header.inputs) atProver startsProver
            (Environment.ofValues arguments) arguments
            (Operands.eval_inputs header.inputs arguments)
          refine Eq.trans ?_ (PIR.Process.bind_assoc _ _ _).symm
          refine givesProver.wrap_denote _ _ ?_
          intro middle keepsProver
          have givesVerifier := suite.startRun_gives (functionTable := functionTable)
            (table := table) (label := label) (side := side) place.roles.verifier
            (statementOf place.roles header)
            ((Operands.newest header.inputs).extend atProver.grows) atVerifier startsVerifier
            middle arguments
            ((Operands.eval_extend atProver.grows (Environment.ofValues arguments) middle
              keepsProver _).trans (Operands.eval_inputs header.inputs arguments))
          refine Eq.trans ?_ (PIR.Process.bind_assoc _ _ _).symm
          refine givesVerifier.wrap_denote _ _ ?_
          intro final keepsVerifier
          have agrees : Renaming.Agrees
              ((Renaming.identity header.inputs).extend (atProver.grows.trans atVerifier.grows))
              (Environment.ofValues arguments) final :=
            Renaming.Agrees.extend (Renaming.identity_agrees header.inputs arguments) _ final
              fun reference => (congrArg final
                (Var.extend_trans reference atProver.grows atVerifier.grows)).trans
                  ((keepsVerifier _).trans (keepsProver reference))
          refine bind_congr ((bodyMeaning _ _ _ threaded threads arguments final agrees).trans
            (congrArg (fun atProver => inner arguments (atProver, _)) (keepsVerifier _)))
            fun values => ?_
          match values with
          | .cons finalProver (.cons finalVerifier outputs) =>
            exact congrArg PIR.Process.done (Operands.eval_newest header.outputs _ outputs)
        · cases made
  · intro quiet side roles header arguments
    exact PIR.Process.Quiet.bind (suite.startRun_quiet quiet side _ _ _) fun _ =>
      PIR.Process.Quiet.bind (suite.startRun_quiet quiet side _ _ _) fun _ =>
        PIR.Process.Quiet.done _
  · intro quiet side roles header result
    exact PIR.Process.Quiet.done _

end Entry

end Zkc.Core
