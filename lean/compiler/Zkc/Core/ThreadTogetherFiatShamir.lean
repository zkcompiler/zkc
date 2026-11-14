module

public import Zkc.Core.ThreadTogetherProgram
public import Zkc.Core.ThreadEntryFiatShamir

public section

/-! The Fiat–Shamir image of an entry, for a side that holds both transcript roles.

`fiatShamir_together`: for the program that the Fiat–Shamir step makes of a program, a side
that holds the prover and the verifier, and inputs on which the two hold equal copies of the
statement, whenever every run of the declared entry returns outputs of which a condition
holds, every run of the newest protocol of the result returns such outputs. With
`groupedComplete_iff_everyRun` this is: the Fiat–Shamir image of an entry that is complete
for every sampler is complete for every sampler.

It is the generic refinement of a threading step (`stepProtocols_entry_together`) at the
Fiat–Shamir rule, with the invariant that the two transcript states are equal.

- `Suite.Returns`: every absorber, deriver and starter that the suite gives returns on every
  input. A row of the catalogue always does, because a pure row is a total function
  (`Suite.Rows.returns`, and `Suite.ofRaw_catalogue_rows` for the suite of a catalogue
  declaration); for a function of a source suite it is a premise, which holds when every
  function of the package returns (`FunctionsReturn.suite`).
- `fiatShamirRule_couples`: from equal states an exchange between the two roles performs no
  effect and both absorb the one value into equal states; a derived draw performs no effect
  and both derive one coin and equal states.
- `StatementCopiesEqual`: of every part of the statement, the prover's copy and the
  verifier's copy are equal. From it and from the fact that the rule made the entry, both
  roles' starts return one state (`Suite.startRun_together`), and the entry is its threaded
  body from that state (`fiatShamirEntry_couples_of_copies`). It is what the proof uses.
- `StatementAgrees`: the side's copies of every part of the statement are equal, also the
  copies of a role of the side that is neither the prover nor the verifier. It gives
  `StatementCopiesEqual` (`StatementAgrees.copiesEqual`), and the statements that take it
  (`fiatShamirEntry_couples`, `fiatShamir_entry_together`, `fiatShamir_complete`,
  `Program.fiatShamir_together`) follow from those that take `StatementCopiesEqual`.

**What is assumed.** `Suite.Returns`, the equation of the step, the position of the declared
protocol, that the side holds both transcript roles, and `StatementCopiesEqual` of the
inputs. Nothing is assumed of the functions of the program beyond `Suite.Returns`, and
nothing of the model.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Source

variable {dialect : Dialect} {I : PIR.Signature} {Δ : List dialect.Ty}

/-- An emitted sequence that gives a value without an effect leaves one environment, which
holds every earlier value where it was and in which the value is read; whatever follows the
sequence runs in that environment. -/
theorem Emitted.Gives.wrap_done {results : List dialect.Ty} {meaning : RegionMeaning dialect I}
    {emitted : Emitted dialect Δ results} {env : Environment meaning.Value Δ} {A : Type}
    {value : A} {read : Environment meaning.Value emitted.context → A}
    (gives : emitted.Gives meaning env (.done value) read) :
    ∃ later : Environment meaning.Value emitted.context,
      (∀ {ty : dialect.Ty} (reference : Var Δ ty),
        later (reference.extend emitted.grows) = env reference) ∧
      read later = value ∧
      ∀ {out : List dialect.Ty} (next : Region dialect emitted.context out),
        (emitted.wrap next).denote meaning env = next.denote meaning later := by
  obtain ⟨R, full, later, yields, same⟩ := gives
  cases full with
  | done result =>
      exact ⟨later result, fun reference => yields.keeps result reference,
        (PIR.Process.done.inj same).symm, fun next => yields.runs next⟩
  | halt reason => cases same
  | call op tail => cases same

end Zkc.Source

namespace Zkc.Core

open Zkc.Source

/-! ## A suite whose rows and functions return -/

section Returns

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- A role's absorption returns on every state and every value. -/
@[expose] def Absorber.Returns (functionTable : FunctionTable model functions) {state type : Ty}
    (absorber : Absorber operations functions state type) : Prop :=
  ∀ (current : model.Value state) (value : model.Value type),
    ∃ next : model.Value state, absorber.run functionTable true current value = .done next

/-- A role's derivation returns a coin and a state on every state. -/
@[expose] def Deriver.Returns (functionTable : FunctionTable model functions) {state output : Ty}
    (deriver : Deriver operations functions state output) : Prop :=
  ∀ current : model.Value state,
    ∃ (coin : model.Value output) (next : model.Value state),
      deriver.run functionTable true current = .done (coin, next)

/-- A role's start returns: the start row of a catalogue always does, and the start function
of a source suite returns a state on every statement. -/
@[expose] def Starter.Returns (functionTable : FunctionTable model functions) {state : Ty}
    {statement : List Ty} : Starter operations functions state statement → Prop
  | .separator .. => True
  | .handler callee =>
      ∀ inputs : Values model.Value statement,
        ∃ outputs, functionTable.get callee inputs = .done outputs

/-- Every absorber, deriver and starter that the suite gives returns on every input. -/
structure Suite.Returns (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) : Prop where
  absorbs : ∀ (label : Label) (type : Ty)
    (absorber : Absorber operations functions suite.state type),
    suite.absorb label type = some absorber → absorber.Returns functionTable
  derives : ∀ (label : Label) (law : Nat) (output : Ty)
    (deriver : Deriver operations functions suite.state output),
    suite.derive label law output = some deriver → deriver.Returns functionTable
  starts : ∀ (statement : List Ty) (starter : Starter operations functions suite.state statement),
    suite.start statement = some starter → starter.Returns functionTable

/-- An absorbing row of the catalogue returns: a pure row is a total function. -/
theorem Absorber.row_returns (functionTable : FunctionTable model functions) {state type : Ty}
    (label : Nat) (name : List Nat)
    (absorb : Var operations ⟨[state, .nominal label, type], [state], .pure⟩)
    (applies : OperationSignature.applies ⟨[state, .nominal label, type], [state], .pure⟩ = true) :
    (Absorber.row (functions := functions) label name absorb applies).Returns functionTable :=
  fun _ _ => ⟨_, rfl⟩

/-- A deriving row of the catalogue returns. -/
theorem Deriver.row_returns (functionTable : FunctionTable model functions) {state output : Ty}
    (label : Nat) (name : List Nat)
    (derive : Var operations ⟨[state, .nominal label], [output, state], .pure⟩)
    (applies : OperationSignature.applies ⟨[state, .nominal label], [output, state], .pure⟩ = true) :
    (Deriver.row (functions := functions) label name derive applies).Returns functionTable :=
  fun _ => ⟨_, _, rfl⟩

/-- Every entry of the suite is a row of the catalogue: no function of the package. -/
structure Suite.Rows (suite : Suite operations functions) : Prop where
  absorbs : ∀ (label : Label) (type : Ty)
    (absorber : Absorber operations functions suite.state type),
    suite.absorb label type = some absorber →
      ∃ row name absorb applies, absorber = .row row name absorb applies
  derives : ∀ (label : Label) (law : Nat) (output : Ty)
    (deriver : Deriver operations functions suite.state output),
    suite.derive label law output = some deriver →
      ∃ row name derive applies, deriver = .row row name derive applies
  starts : ∀ (statement : List Ty) (starter : Starter operations functions suite.state statement),
    suite.start statement = some starter →
      ∃ label identity row applies, starter = .separator label identity row applies

/-- A suite all of whose entries are rows returns, over every table of functions. -/
theorem Suite.Rows.returns {suite : Suite operations functions} (rows : suite.Rows)
    (functionTable : FunctionTable model functions) : suite.Returns functionTable := by
  refine ⟨?_, ?_, ?_⟩
  · intro label type absorber gives
    obtain ⟨row, name, absorb, applies, rfl⟩ := rows.absorbs label type absorber gives
    exact Absorber.row_returns functionTable row name absorb applies
  · intro label law output deriver gives
    obtain ⟨row, name, derive, applies, rfl⟩ := rows.derives label law output deriver gives
    exact Deriver.row_returns functionTable row name derive applies
  · intro statement starter gives
    obtain ⟨label, identity, row, applies, rfl⟩ := rows.starts statement starter gives
    exact trivial

/-- What a row lookup gives is made of a row that applies. -/
theorem appliedRow_some {signature : OperationSignature} {α : Type}
    {make : Var operations signature → signature.applies = true → α}
    {found : Option (Var operations signature)} {value : α}
    (applied : appliedRow make found = some value) :
    ∃ row applies, value = make row applies := by
  unfold appliedRow at applied
  split at applied
  · split at applied
    · exact ⟨_, _, (Option.some.inj applied).symm⟩
    · cases applied
  · cases applied

/-- The suite of a catalogue declaration has rows only. -/
theorem Suite.ofRaw_catalogue_rows (rows : Scope operations) (callees : Scope functions)
    (state : Ty) (label start : Nat) (absorbing : List Nat) (deriving_ : List (Nat × Nat))
    (identity : List Nat) :
    (Suite.ofRaw rows callees
      (.catalogue state label start absorbing deriving_ identity)).Rows := by
  refine ⟨?_, ?_, ?_⟩
  · intro name type absorber gives
    obtain ⟨row, applies, rfl⟩ := appliedRow_some gives
    exact ⟨_, _, row, applies, rfl⟩
  · intro name law output deriver gives
    obtain ⟨row, applies, rfl⟩ := appliedRow_some gives
    exact ⟨_, _, row, applies, rfl⟩
  · intro statement starter gives
    obtain ⟨row, applies, rfl⟩ := appliedRow_some gives
    exact ⟨_, _, row, applies, rfl⟩

/-- The suite of a catalogue declaration returns, over every table of functions. -/
theorem Suite.ofRaw_catalogue_returns (rows : Scope operations) (callees : Scope functions)
    (state : Ty) (label start : Nat) (absorbing : List Nat) (deriving_ : List (Nat × Nat))
    (identity : List Nat) (functionTable : FunctionTable model functions) :
    (Suite.ofRaw rows callees
      (.catalogue state label start absorbing deriving_ identity)).Returns functionTable :=
  (Suite.ofRaw_catalogue_rows rows callees state label start absorbing deriving_ identity).returns
    functionTable

/-- Every function of the table returns on every input. -/
@[expose] def FunctionsReturn (functionTable : FunctionTable model functions) : Prop :=
  ∀ {header : FunctionHeader} (callee : Var functions header)
    (inputs : Values model.Value header.inputs),
    ∃ outputs, functionTable.get callee inputs = .done outputs

/-- Over functions that all return, every suite returns: a row always does, and a function of
the suite is one of the functions. -/
theorem FunctionsReturn.suite {functionTable : FunctionTable model functions}
    (returns : FunctionsReturn functionTable) (suite : Suite operations functions) :
    suite.Returns functionTable := by
  refine ⟨?_, ?_, ?_⟩
  · intro label type absorber _
    cases absorber with
    | row row name absorb applies => exact Absorber.row_returns functionTable row name absorb applies
    | handler callee =>
        intro current value
        obtain ⟨outputs, calls⟩ := returns callee (.cons current (.cons value .nil))
        refine ⟨outputs.get .here, ?_⟩
        show (functionTable.get callee (Values.cons current (Values.cons value .nil))).bind _ = _
        rw [calls]
        rfl
  · intro label law output deriver _
    cases deriver with
    | row row name derive applies => exact Deriver.row_returns functionTable row name derive applies
    | handler callee =>
        intro current
        obtain ⟨outputs, calls⟩ := returns callee (.cons current .nil)
        refine ⟨outputs.get .here, outputs.tail.get .here, ?_⟩
        show (functionTable.get callee (Values.cons current .nil)).bind _ = _
        rw [calls]
        rfl
  · intro statement starter _
    cases starter with
    | separator label identity row applies => exact trivial
    | handler callee => exact fun inputs => returns callee inputs

/-- What a role in the side absorbs, from what it absorbs as a role that is present. -/
theorem Absorber.run_member (functionTable : FunctionTable model functions) {state type : Ty}
    (absorber : Absorber operations functions state type) {present : Bool}
    (member : present = true) (current : Held (model.Value state) present)
    (value : Held (model.Value type) present) {next : model.Value state}
    (returns : absorber.run functionTable true
      (Held.value (X := model.Value state) present member current)
      (Held.value (X := model.Value type) present member value) = .done next) :
    absorber.run functionTable present current value = .done (Held.of present next) := by
  subst member
  exact returns

end Returns

/-! ## The rule keeps equal states equal -/

section Rule

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- The Fiat–Shamir rule keeps the two transcript states of a side that holds both
transcript roles equal, without an effect, when the suite's rows and functions return. -/
theorem fiatShamirRule_couples (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) (returns : suite.Returns functionTable) :
    RuleCouples (fiatShamirRule suite) (fiatShamirMeaning suite functionTable)
      (fun atProver atVerifier : model.Value suite.state => atProver = atVerifier) := by
  refine ⟨?_, ?_⟩
  · intro protocols deployed place site type Δ value first second emitted emits effects sent
      atProver atVerifier same
    cases same
    simp only [fiatShamirRule] at emits
    split at emits
    · cases emits
    · rename_i absorber hasAbsorber
      obtain ⟨next, absorbs⟩ := returns.absorbs _ _ absorber hasAbsorber atProver sent
      refine ⟨next, next, ?_, rfl⟩
      simp only [fiatShamirMeaning, hasAbsorber]
      show (absorber.run functionTable true atProver sent).bind (fun nextProver =>
        (absorber.run functionTable true atProver sent).bind fun nextVerifier =>
          PIR.Process.done (sent, (nextProver, nextVerifier))) = _
      rw [absorbs]
      rfl
  · intro protocols deployed place site inputs output law Δ first second emitted emits effects
      atProver atVerifier same
    cases same
    simp only [fiatShamirRule] at emits
    split at emits
    · rename_i empty
      split at emits
      · cases emits
      · rename_i deriver hasDeriver
        obtain ⟨coin, next, derives⟩ := returns.derives _ _ _ deriver hasDeriver atProver
        refine ⟨coin, next, next, ?_, rfl⟩
        simp only [fiatShamirMeaning, empty, hasDeriver, ↓reduceIte]
        show (deriver.run functionTable true atProver).bind (fun derivedVerifier =>
          (deriver.run functionTable true atProver).bind fun derivedProver =>
            PIR.Process.done ((derivedProver.1, derivedVerifier.1),
              (derivedProver.2, derivedVerifier.2))) = _
        rw [derives]
        rfl
    · cases emits

end Rule

/-! ## The statement and the start of the two roles -/

section Statement

variable {model : Model}

/-- The copy of an agreed value that a role holds is one of the agreement's copies. -/
theorem Agreement.copyOf_some {ports : List Located} {agreement : Agreement ports} {role : Nat}
    {port : Var ports ⟨agreement.type, role⟩} (found : agreement.copyOf role = some port) :
    ∃ copy ∈ agreement.copies, ∃ same : copy.holder = role,
      port = copy.port.retype (by rw [same]) := by
  unfold Agreement.copyOf at found
  obtain ⟨copy, member, gives⟩ := List.exists_of_findSome?_eq_some found
  refine ⟨copy, member, ?_⟩
  split at gives
  · rename_i same
    exact ⟨same, (Option.some.inj gives).symm⟩
  · cases gives

/-- The prover's and the verifier's copies of an agreed value exist and are equal. -/
@[expose] def Agreement.CopiesEqual (side : Side) {prover verifier : Nat}
    (isProver : side prover = true) (isVerifier : side verifier = true) {ports : List Located}
    (values : Values (SideValue model side) ports) (agreement : Agreement ports) : Prop :=
  ∃ (atProver : Var ports ⟨agreement.type, prover⟩)
    (atVerifier : Var ports ⟨agreement.type, verifier⟩),
    agreement.copyOf prover = some atProver ∧ agreement.copyOf verifier = some atVerifier ∧
      Held.value (side prover) isProver (values.get atProver) =
        Held.value (side verifier) isVerifier (values.get atVerifier)

/-- An agreement that holds for a side gives two roles of the side equal copies. -/
theorem Agreement.Holds.copies {side : Side} {prover verifier : Nat}
    (isProver : side prover = true) (isVerifier : side verifier = true) {ports : List Located}
    {values : Values (SideValue model side) ports} {agreement : Agreement ports}
    (holds : agreement.Holds model side values) {atProver : Var ports ⟨agreement.type, prover⟩}
    {atVerifier : Var ports ⟨agreement.type, verifier⟩}
    (hasProver : agreement.copyOf prover = some atProver)
    (hasVerifier : agreement.copyOf verifier = some atVerifier) :
    Held.value (side prover) isProver (values.get atProver) =
      Held.value (side verifier) isVerifier (values.get atVerifier) := by
  obtain ⟨proverCopy, proverMember, proverSame, rfl⟩ := Agreement.copyOf_some hasProver
  obtain ⟨verifierCopy, verifierMember, verifierSame, rfl⟩ := Agreement.copyOf_some hasVerifier
  obtain ⟨proverHolder, proverPort⟩ := proverCopy
  obtain ⟨verifierHolder, verifierPort⟩ := verifierCopy
  cases proverSame
  cases verifierSame
  exact holds ⟨proverHolder, proverPort⟩ proverMember ⟨verifierHolder, verifierPort⟩ verifierMember
    isProver isVerifier

/-- The condition on the inputs of an entry: the side's copies of every part of the
statement are equal. Honest inputs satisfy it: the prover and the verifier start from the
same statement. -/
@[expose] def StatementAgrees (model : Model) (side : Side) (roles : TranscriptRoles)
    (header : ProtocolHeader) (arguments : Values (SideValue model side) header.inputs) : Prop :=
  ∀ agreement ∈ statementOf roles header, agreement.Holds model side arguments

/-- On inputs that agree on the statement, the prover and the verifier hold equal copies of
every part of the statement. -/
theorem StatementAgrees.copies {side : Side} {roles : TranscriptRoles} {header : ProtocolHeader}
    {arguments : Values (SideValue model side) header.inputs}
    (agrees : StatementAgrees model side roles header arguments)
    (isProver : side roles.prover = true) (isVerifier : side roles.verifier = true) :
    ∀ agreement ∈ statementOf roles header,
      agreement.CopiesEqual side isProver isVerifier arguments := by
  intro agreement member
  have both := (List.mem_filter.mp member).2
  rw [Bool.and_eq_true] at both
  obtain ⟨atProver, hasProver⟩ := Option.isSome_iff_exists.mp both.1
  obtain ⟨atVerifier, hasVerifier⟩ := Option.isSome_iff_exists.mp both.2
  exact ⟨atProver, atVerifier, hasProver, hasVerifier,
    (agrees agreement member).copies isProver isVerifier hasProver hasVerifier⟩

/-- The condition on the inputs of an entry that the Fiat–Shamir step uses: of every part of
the statement, the prover's copy and the verifier's copy are equal. It asks nothing of a
copy that another role of the side holds, and nothing of a second copy of the prover or of
the verifier. For a side that does not hold both roles it holds of every input. -/
@[expose] def StatementCopiesEqual (model : Model) (side : Side) (roles : TranscriptRoles)
    (header : ProtocolHeader) (arguments : Values (SideValue model side) header.inputs) : Prop :=
  ∀ (isProver : side roles.prover = true) (isVerifier : side roles.verifier = true),
    ∀ agreement ∈ statementOf roles header,
      agreement.CopiesEqual side isProver isVerifier arguments

/-- Inputs on which every copy of the statement that the side holds is equal give the prover
and the verifier equal copies. -/
theorem StatementAgrees.copiesEqual {side : Side} {roles : TranscriptRoles}
    {header : ProtocolHeader} {arguments : Values (SideValue model side) header.inputs}
    (agrees : StatementAgrees model side roles header arguments) :
    StatementCopiesEqual model side roles header arguments :=
  fun isProver isVerifier => agrees.copies isProver isVerifier

end Statement

section Start

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

local notation "𝒟" => ProtocolDialect operations functions protocols deployed

/-- Two roles of the side that hold equal copies of every part of a statement hold the same
arguments of a start function. -/
theorem statementValues_together (side : Side) {prover verifier : Nat}
    (isProver : side prover = true) (isVerifier : side verifier = true) {ports : List Located}
    (values : Values (SideValue model side) ports) :
    ∀ (statement : List (Agreement ports)),
      (∀ agreement ∈ statement, agreement.CopiesEqual side isProver isVerifier values) →
      ∃ (copies : Values model.Value (statement.map (·.type)))
        (atProver : Values (SideValue model side)
          (Located.atRole prover (statement.map (·.type))))
        (atVerifier : Values (SideValue model side)
          (Located.atRole verifier (statement.map (·.type)))),
        statementValues side prover values statement = some atProver ∧
        statementValues side verifier values statement = some atVerifier ∧
        presentValues (side prover) isProver
            (unmapValues (F := SideValue model side) (fun type => (⟨type, prover⟩ : Located)) _
              atProver) = copies ∧
        presentValues (side verifier) isVerifier
            (unmapValues (F := SideValue model side) (fun type => (⟨type, verifier⟩ : Located)) _
              atVerifier) = copies
  | [], _ => ⟨.nil, .nil, .nil, rfl, rfl, presentValues_nil _ _, presentValues_nil _ _⟩
  | agreement :: rest, agrees => by
      obtain ⟨proverPort, verifierPort, hasProver, hasVerifier, equal⟩ :=
        agrees agreement List.mem_cons_self
      obtain ⟨copies, proverTail, verifierTail, proverValues, verifierValues, proverPlain,
          verifierPlain⟩ :=
        statementValues_together side isProver isVerifier values rest fun other member =>
          agrees other (List.mem_cons_of_mem _ member)
      refine ⟨.cons (Held.value (side prover) isProver (values.get proverPort)) copies,
        .cons (values.get proverPort) proverTail, .cons (values.get verifierPort) verifierTail,
        ?_, ?_, ?_, ?_⟩
      · unfold statementValues
        rw [hasProver, proverValues]
      · unfold statementValues
        rw [hasVerifier, verifierValues]
      · exact (presentValues_cons (side prover) isProver (values.get proverPort) _).trans
          (cons_congr rfl proverPlain)
      · exact (presentValues_cons (side verifier) isVerifier (values.get verifierPort) _).trans
          (cons_congr equal.symm verifierPlain)

/-- When the prover's absorption of a statement was emitted, the prover and the verifier,
which hold equal copies of every part of it, absorb it from one state into one state without
an effect. -/
theorem Suite.statementRun_together (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (returns : suite.Returns functionTable)
    (side : Side) {prover verifier : Nat} (isProver : side prover = true)
    (isVerifier : side verifier = true) {ports Δ : List Located}
    (values : Values (SideValue model side) ports) (operands : Operands Δ ports) :
    ∀ (statement : List (Agreement ports)) (position : Nat)
      (sofar emitted : Emitted 𝒟 Δ [⟨suite.state, prover⟩]),
      absorbStatement suite prover operands position statement sofar = .ok emitted →
      (∀ agreement ∈ statement, agreement.CopiesEqual side isProver isVerifier values) →
      ∀ current : model.Value suite.state,
        ∃ final : model.Value suite.state,
          suite.statementRun functionTable side prover values position statement
              (Held.of (side prover) current) = .done (Held.of (side prover) final) ∧
            suite.statementRun functionTable side verifier values position statement
              (Held.of (side verifier) current) = .done (Held.of (side verifier) final)
  | [], _, _, _, _, _, current => ⟨current, rfl, rfl⟩
  | agreement :: rest, position, sofar, emitted, made, agrees, current => by
      unfold absorbStatement at made
      split at made
      · rename_i port absorber hasPort hasAbsorber
        obtain ⟨atProver, atVerifier, hasProver, hasVerifier, equal⟩ :=
          agrees agreement List.mem_cons_self
        obtain ⟨next, absorbs⟩ := returns.absorbs _ _ absorber hasAbsorber current
          (Held.value (side prover) isProver (values.get atProver))
        obtain ⟨final, runsProver, runsVerifier⟩ :=
          Suite.statementRun_together suite returns side isProver isVerifier values operands rest
            (position + 1) _ emitted made
            (fun other member => agrees other (List.mem_cons_of_mem _ member)) next
        refine ⟨final, ?_, ?_⟩
        · rw [Suite.statementRun_cons suite functionTable side prover values position agreement
              rest _ hasProver hasAbsorber,
            Absorber.run_member functionTable absorber isProver _ _
              (by rw [Held.value_of]; exact absorbs)]
          exact runsProver
        · rw [Suite.statementRun_cons suite functionTable side verifier values position agreement
              rest _ hasVerifier hasAbsorber,
            Absorber.run_member functionTable absorber isVerifier _ _
              (by rw [Held.value_of, ← equal]; exact absorbs)]
          exact runsVerifier
      · cases made

/-- The start row of a catalogue, applied by a role in the side to the identity literal:
what follows continues from the state that the row gives. -/
theorem separatorStart_member {state : Ty} {label : Nat}
    (row : Var operations ⟨[.nominal label], [state], .pure⟩)
    (applies : OperationSignature.applies ⟨[.nominal label], [state], .pure⟩ = true)
    (identity : List Nat) {present : Bool} (member : present = true) {α : Type}
    (next : Held (model.Value state) present → PIR.Process (Effects model) α) :
    (performStep model (rowProcess model (.of row) .pure applies) present
        (.cons ((holdValues present (Values.cons (model.literal label identity) .nil)).get .here)
          .nil)).bind (fun started => next (started.get .here)) =
      next (Held.of present
        ((model.pure (.of row) applies (.cons (model.literal label identity) .nil)).get .here)) := by
  subst member
  rfl

/-- The first of the values that a role in the side holds. -/
theorem holdValues_get_here {X : Ty → Type} {present : Bool} (member : present = true)
    {type : Ty} {types : List Ty} (values : Values X (type :: types)) :
    (holdValues present values).get .here = Held.of present (values.get .here) := by
  subst member
  rfl

/-- When the prover's start was emitted, the prover and the verifier of a side that holds
both, with equal copies of every part of the statement, start from one state without an
effect. -/
theorem Suite.startRun_together (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (returns : suite.Returns functionTable)
    (side : Side) {prover verifier : Nat} (isProver : side prover = true)
    (isVerifier : side verifier = true) {ports Δ : List Located}
    (statement : List (Agreement ports)) (values : Values (SideValue model side) ports)
    (operands : Operands Δ ports) (emitted : Emitted 𝒟 Δ [⟨suite.state, prover⟩])
    (made : startState suite prover statement operands = .ok emitted)
    (agrees : ∀ agreement ∈ statement, agreement.CopiesEqual side isProver isVerifier values) :
    ∃ state : model.Value suite.state,
      suite.startRun functionTable side prover statement values =
          .done (Held.of (side prover) state) ∧
        suite.startRun functionTable side verifier statement values =
          .done (Held.of (side verifier) state) := by
  unfold startState at made
  unfold Suite.startRun
  split at made
  · cases made
  · rename_i name identity row applies hasStart
    rw [hasStart]
    obtain ⟨final, runsProver, runsVerifier⟩ :=
      Suite.statementRun_together suite returns side isProver isVerifier values operands statement
        0 _ emitted made agrees
        ((model.pure (.of row) applies (.cons (model.literal name identity) .nil)).get .here)
    exact ⟨final,
      (separatorStart_member row applies identity isProver
        (fun current => suite.statementRun functionTable side prover values 0 statement
          current)).trans runsProver,
      (separatorStart_member row applies identity isVerifier
        (fun current => suite.statementRun functionTable side verifier values 0 statement
          current)).trans runsVerifier⟩
  · rename_i callee hasStart
    rw [hasStart]
    obtain ⟨copies, atProver, atVerifier, proverValues, verifierValues, proverPlain,
        verifierPlain⟩ := statementValues_together side isProver isVerifier values statement agrees
    obtain ⟨outputs, calls⟩ := returns.starts _ _ hasStart copies
    refine ⟨outputs.get .here, ?_, ?_⟩
    · show (match statementValues side prover values statement with
        | some arguments => _
        | none => _) = _
      rw [proverValues]
      show (performStep model (fun inputs => functionTable.get callee inputs) (side prover) _).bind
        _ = _
      rw [performStep_present model _ _ isProver, proverPlain, calls]
      exact congrArg PIR.Process.done (holdValues_get_here isProver outputs)
    · show (match statementValues side verifier values statement with
        | some arguments => _
        | none => _) = _
      rw [verifierValues]
      show (performStep model (fun inputs => functionTable.get callee inputs) (side verifier)
        _).bind _ = _
      rw [performStep_present model _ _ isVerifier, verifierPlain, calls]
      exact congrArg PIR.Process.done (holdValues_get_here isVerifier outputs)

end Start

/-! ## The entry -/

section Entry

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}

/-- The obligation on the entry of a rule, for inputs of a stronger condition. -/
theorem EntryCouples.of_stronger {t : Threads} {rule : Rule t operations functions}
    {entry : EntryMeaning model t rule} {functionTable : FunctionTable model functions}
    {coupled : model.Value t.prover → model.Value t.verifier → Prop}
    {admits stronger : (side : Side) → (roles : TranscriptRoles) → (header : ProtocolHeader) →
      Values (SideValue model side) (rule.entryPorts roles header).inputs → Prop}
    (couples : EntryCouples rule entry functionTable coupled admits)
    (weakens : ∀ side roles header arguments,
      stronger side roles header arguments → admits side roles header arguments) :
    EntryCouples rule entry functionTable coupled stronger :=
  ⟨fun table label side place header body region made isProver isVerifier arguments admitted =>
      couples.runs table label side place header body region made isProver isVerifier arguments
        (weakens side place.roles header arguments admitted),
    couples.finishes⟩

/-- The entry of the Fiat–Shamir rule starts the two transcript states equal, for a side
that holds both transcript roles and inputs on which the prover's and the verifier's copies
of the statement are equal, when the suite's rows and functions return; it drops the two
final states. -/
theorem fiatShamirEntry_couples_of_copies (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) (returns : suite.Returns functionTable) :
    EntryCouples (fiatShamirRule suite) (fiatShamirEntry suite functionTable) functionTable
      (fun atProver atVerifier : model.Value suite.state => atProver = atVerifier)
      (fun side roles header arguments =>
        StatementCopiesEqual model side roles header arguments) := by
  refine ⟨?_, ?_⟩
  · intro protocols deployed table label side place header body region made isProver isVerifier
      arguments admitted
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
          obtain ⟨state, proverStarts, verifierStarts⟩ :=
            suite.startRun_together returns side isProver isVerifier
              (statementOf place.roles header) arguments (Operands.newest header.inputs) atProver
              startsProver (admitted isProver isVerifier)
          have givesProver := suite.startRun_gives (functionTable := functionTable)
            (table := table) (label := label) (side := side) place.roles.prover
            (statementOf place.roles header) (Operands.newest header.inputs) atProver startsProver
            (Environment.ofValues arguments) arguments
            (Operands.eval_inputs header.inputs arguments)
          rw [proverStarts] at givesProver
          obtain ⟨middle, keepsProver, readsProver, runsProver⟩ := givesProver.wrap_done
          have givesVerifier := suite.startRun_gives (functionTable := functionTable)
            (table := table) (label := label) (side := side) place.roles.verifier
            (statementOf place.roles header)
            ((Operands.newest header.inputs).extend atProver.grows) atVerifier startsVerifier
            middle arguments
            ((Operands.eval_extend atProver.grows (Environment.ofValues arguments) middle
              keepsProver _).trans (Operands.eval_inputs header.inputs arguments))
          rw [verifierStarts] at givesVerifier
          obtain ⟨final, keepsVerifier, readsVerifier, runsVerifier⟩ := givesVerifier.wrap_done
          have agrees : Renaming.Agrees
              ((Renaming.identity header.inputs).extend (atProver.grows.trans atVerifier.grows))
              (Environment.ofValues arguments) final :=
            Renaming.Agrees.extend (Renaming.identity_agrees header.inputs arguments) _ final
              fun reference => (congrArg final
                (Var.extend_trans reference atProver.grows atVerifier.grows)).trans
                  ((keepsVerifier _).trans (keepsProver reference))
          have atFirst : final ((atProver.values.get .here).extend atVerifier.grows) =
              Held.of (side place.roles.prover) state :=
            (keepsVerifier _).trans readsProver
          refine ⟨_, _, _, _, threaded, final, threads, agrees, ?_, ?_, ?_⟩
          · show (suite.startRun functionTable side place.roles.prover
                (statementOf place.roles header) arguments).bind (fun startedProver =>
              (suite.startRun functionTable side place.roles.verifier
                (statementOf place.roles header) arguments).bind fun startedVerifier =>
                  PIR.Process.done (startedProver, startedVerifier)) = _
            rw [proverStarts, verifierStarts]
            exact congrArg PIR.Process.done (Prod.ext atFirst.symm readsVerifier.symm)
          · have started : CoupledState
                (fun atProver atVerifier : model.Value suite.state => atProver = atVerifier)
                isProver isVerifier
                ((Held.of (side place.roles.prover) state, Held.of (side place.roles.verifier) state) :
                  ThreadState model ⟨suite.state, suite.state⟩ (side place.roles.prover)
                    (side place.roles.verifier)) :=
              (Held.value_of _ isProver state).trans (Held.value_of _ isVerifier state).symm
            exact started.of_eq atFirst readsVerifier
          · refine (runsProver _).trans ((runsVerifier _).trans ?_)
            refine bind_congr rfl fun values => ?_
            match values with
            | .cons finalProver (.cons finalVerifier outputs) =>
              exact congrArg PIR.Process.done (Operands.eval_newest header.outputs _ outputs)
        · cases made
  · intro side roles header isProver isVerifier outputs final coupledFinal
    exact ⟨outputs, rfl⟩

/-- The entry of the Fiat–Shamir rule starts the two transcript states equal, for a side
that holds both transcript roles and inputs that agree on the statement, when the suite's
rows and functions return; it drops the two final states. -/
theorem fiatShamirEntry_couples (suite : Suite operations functions)
    (functionTable : FunctionTable model functions) (returns : suite.Returns functionTable) :
    EntryCouples (fiatShamirRule suite) (fiatShamirEntry suite functionTable) functionTable
      (fun atProver atVerifier : model.Value suite.state => atProver = atVerifier)
      (fun side roles header arguments => StatementAgrees model side roles header arguments) :=
  (fiatShamirEntry_couples_of_copies suite functionTable returns).of_stronger
    fun _ _ _ _ agrees => agrees.copiesEqual

end Entry

/-! ## The Fiat–Shamir image of an entry -/

section Together

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- The Fiat–Shamir image of an entry that the step rewrote, for a side that holds both
transcript roles: on inputs on which the prover's and the verifier's copies of the statement
are equal, whenever every run of the entry returns outputs of which a condition holds, every
run of the image returns such outputs. -/
theorem fiatShamir_entry_together_of_copies (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (returns : suite.Returns functionTable)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (steps : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles protocols = .ok once)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) (rewrote : once.rewroteEntry = true) :
    ∃ image : Var once.headers ((fiatShamirRule suite).entryHeader roles header),
      image.index = 0 ∧
      ∀ (path : List Nat) (side : Side), side roles.prover = true → side roles.verifier = true →
      ∀ (arguments : Values (SideValue model side) header.inputs),
        StatementCopiesEqual model side roles header arguments →
        ∀ holds : Values (SideValue model side) header.outputs → Prop,
          EveryRun holds
              ((protocols.table model functionTable identities).get declared path side arguments) →
            EveryRun holds
              ((once.protocols.table model functionTable once.identities).get image path side
                arguments) := by
  obtain ⟨image, newest, refines⟩ := stepProtocols_entry_together
    (fiatShamirRule_sound suite functionTable) (fiatShamirRule_couples suite functionTable returns)
    (fiatShamirEntry_couples_of_copies suite functionTable returns) identities number roles
    protocols once steps declared isEntry rewrote
  refine ⟨image, newest, fun path side isProver isVerifier arguments agrees holds every => ?_⟩
  exact EveryRun.mono
    (fun result ⟨outputs, holding, final, _, finishes⟩ => PIR.Process.done.inj finishes ▸ holding)
    (refines path side isProver isVerifier arguments agrees holds every)

/-- The Fiat–Shamir image of an entry that the step rewrote, for a side that holds both
transcript roles: on inputs that agree on the statement, whenever every run of the entry
returns outputs of which a condition holds, every run of the image returns such outputs. -/
theorem fiatShamir_entry_together (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (returns : suite.Returns functionTable)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (steps : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles protocols = .ok once)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) (rewrote : once.rewroteEntry = true) :
    ∃ image : Var once.headers ((fiatShamirRule suite).entryHeader roles header),
      image.index = 0 ∧
      ∀ (path : List Nat) (side : Side), side roles.prover = true → side roles.verifier = true →
      ∀ (arguments : Values (SideValue model side) header.inputs),
        StatementAgrees model side roles header arguments →
        ∀ holds : Values (SideValue model side) header.outputs → Prop,
          EveryRun holds
              ((protocols.table model functionTable identities).get declared path side arguments) →
            EveryRun holds
              ((once.protocols.table model functionTable once.identities).get image path side
                arguments) := by
  obtain ⟨image, newest, together⟩ := fiatShamir_entry_together_of_copies suite returns identities
    number roles protocols once steps declared isEntry rewrote
  exact ⟨image, newest, fun path side isProver isVerifier arguments agrees holds every =>
    together path side isProver isVerifier arguments agrees.copiesEqual holds every⟩

/-- The Fiat–Shamir image of an entry that the step copied has the entry's meaning, so every
run of it returns what every run of the entry returns, for every side and every input. -/
theorem fiatShamir_entry_copied_together (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (identities : Identities) (number : Nat)
    (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (steps : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles protocols = .ok once)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) (copied : once.rewroteEntry = false) :
    ∃ image : Var once.headers header, image.index = 0 ∧
      ∀ (path : List Nat) (side : Side) (arguments : Values (SideValue model side) header.inputs)
        (holds : Values (SideValue model side) header.outputs → Prop),
        EveryRun holds
            ((protocols.table model functionTable identities).get declared path side arguments) →
          EveryRun holds
            ((once.protocols.table model functionTable once.identities).get image path side
              arguments) := by
  obtain ⟨image, newest, same⟩ := stepProtocols_entry_copied (model := model)
    (functionTable := functionTable) identities number roles protocols once steps declared isEntry
    copied
  refine ⟨image, newest, fun path side arguments holds every => ?_⟩
  rw [same]
  exact every

/-- The Fiat–Shamir image of an entry, whether the step rewrote the entry or copied it: for
a side that holds both transcript roles and inputs on which the prover's and the verifier's
copies of the statement are equal, whenever every run of the entry returns outputs of which
a condition holds, every run of the newest protocol of the result returns such outputs. The
Fiat–Shamir entry keeps its ports, so the image takes the entry's inputs and returns its
outputs. -/
theorem fiatShamir_together (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (returns : suite.Returns functionTable)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (steps : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles protocols = .ok once)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ image : Var once.headers header, image.index = 0 ∧
      ∀ (path : List Nat) (side : Side), side roles.prover = true → side roles.verifier = true →
      ∀ (arguments : Values (SideValue model side) header.inputs),
        StatementCopiesEqual model side roles header arguments →
        ∀ holds : Values (SideValue model side) header.outputs → Prop,
          EveryRun holds
              ((protocols.table model functionTable identities).get declared path side arguments) →
            EveryRun holds
              ((once.protocols.table model functionTable once.identities).get image path side
                arguments) := by
  cases rewrote : once.rewroteEntry with
  | true =>
      exact fiatShamir_entry_together_of_copies suite returns identities number roles protocols
        once steps declared isEntry rewrote
  | false =>
      obtain ⟨image, newest, same⟩ := fiatShamir_entry_copied_together (model := model)
        (functionTable := functionTable) suite identities number roles protocols once steps
        declared isEntry rewrote
      exact ⟨image, newest, fun path side _ _ arguments _ holds every =>
        same path side arguments holds every⟩

/-- The Fiat–Shamir image of an entry that is complete for every sampler is complete for
every sampler, with the same accepted outputs: for a side that holds both transcript roles
and inputs that agree on the statement. -/
theorem fiatShamir_complete (suite : Suite operations functions)
    {functionTable : FunctionTable model functions} (returns : suite.Returns functionTable)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (once : Stepped typeTable operations functions)
    (steps : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles protocols = .ok once)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ image : Var once.headers header, image.index = 0 ∧
      ∀ (path : List Nat) (side : Side), side roles.prover = true → side roles.verifier = true →
      ∀ (arguments : Values (SideValue model side) header.inputs),
        StatementAgrees model side roles header arguments →
        ∀ accepted : Values (SideValue model side) header.outputs → Prop,
          GroupedComplete
              ((protocols.table model functionTable identities).get declared path side arguments)
              accepted →
            GroupedComplete
              ((once.protocols.table model functionTable once.identities).get image path side
                arguments)
              accepted := by
  obtain ⟨image, newest, together⟩ := fiatShamir_together suite returns identities number roles
    protocols once steps declared isEntry
  exact ⟨image, newest, fun path side isProver isVerifier arguments agrees accepted complete =>
    (together path side isProver isVerifier arguments agrees.copiesEqual accepted
      complete.everyRun).groupedComplete⟩

/-- The Fiat–Shamir image of the entry of a program, with the meanings of the program's own
functions. -/
theorem Program.fiatShamir_together (suite : Suite operations functions) {old : List ProtocolHeader}
    (program : Program typeTable operations functions old)
    (returns : suite.Returns (program.functionTable model)) (identities : Identities)
    (number : Nat) (roles : TranscriptRoles) (once : Stepped typeTable operations functions)
    (steps : stepProtocols ⟨suite.state, suite.state⟩ (fiatShamirRule suite) identities number
      roles program.protocols = .ok once)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ image : Var once.headers header, image.index = 0 ∧
      ∀ (path : List Nat) (side : Side), side roles.prover = true → side roles.verifier = true →
      ∀ (arguments : Values (SideValue model side) header.inputs),
        StatementAgrees model side roles header arguments →
        ∀ holds : Values (SideValue model side) header.outputs → Prop,
          EveryRun holds
              ((program.protocolTable model identities).get declared path side arguments) →
            EveryRun holds
              ((once.protocols.table model (program.functionTable model) once.identities).get image
                path side arguments) := by
  obtain ⟨image, newest, together⟩ := Zkc.Core.fiatShamir_together suite returns identities number
    roles program.protocols once steps declared isEntry
  exact ⟨image, newest, fun path side isProver isVerifier arguments agrees holds every =>
    together path side isProver isVerifier arguments agrees.copiesEqual holds every⟩

end Together

end Zkc.Core
