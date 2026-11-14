module

public import Zkc.Core.LegalThread
public import Zkc.Core.Serialize

public section

/-! The Fiat–Shamir rule and the serialize rule emit what the check of a definition accepts.

`Rule.Legal` (`Core/LegalThread.lean`) is the obligation of a rule. Both rules meet it over
tables whose types are types of the package:

- `RowsNamed`: the types of every row of the operation table are types of the package.
  The operation table of a typed package is such a table (`Typed.rowsNamed`), by the
  residual condition on its tables.
- `FunctionsNamed`: the types of the header of every function are types of the package.
  The functions of a typed package are such (`Typed.functionsNamed`), because each is
  well formed.

`fiatShamirRule_legal`: for every suite over such tables. A suite names its rows and its
functions by references into the tables, so the state type and the label type of a suite
that absorbs, derives or starts are types of the package: nothing is assumed of the suite.
`serializeRule_legal`: for every layout over such a table of rows; the writer, the reader
and the proof are types of the package because the layout has its four fixed rows.

Every suite and every layout that a declaration describes over the tables of a typed
package (`Suite.ofRaw`, `Layout.ofRaw`) is a suite and a layout over those tables, so both
theorems apply to it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-! ## Tables whose types are types of the package -/

/-- The types of every row of the operation table are types of the package. -/
@[expose] def RowsNamed (typeTable : TypeTable) (operations : List OperationSignature) : Prop :=
  ∀ {signature : OperationSignature}, Var operations signature →
    Ty.allNamed typeTable signature.inputs = true ∧ Ty.allNamed typeTable signature.outputs = true

/-- The types of the header of every function are types of the package. -/
@[expose] def FunctionsNamed (typeTable : TypeTable) (functions : List FunctionHeader) : Prop :=
  ∀ {header : FunctionHeader}, Var functions header →
    Ty.allNamed typeTable header.inputs = true ∧ Ty.allNamed typeTable header.outputs = true

/-- The rows of an operation table without a violation have types of the package. -/
theorem rowsNamed_of_tables {types : List CatalogueRow} {records : List RecordDeclaration}
    {variants : List VariantDeclaration} {table : List Operation}
    (formed : tablesViolation types records variants table = none) :
    RowsNamed (typeTableOf types records variants) (table.map (·.signature)) := by
  intro signature row
  have conditions := firstViolation_holds _ formed
  have operationsNamed : (table.all fun row =>
      staticsNamed (typeTableOf types records variants) row.identity.statics &&
        (Ty.allNamed (typeTableOf types records variants) row.signature.inputs &&
          Ty.allNamed (typeTableOf types records variants) row.signature.outputs)) = true :=
    conditions _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  rw [List.all_eq_true] at operationsNamed
  obtain ⟨operation, among, rfl⟩ := List.mem_map.mp (position_mem row)
  have named := operationsNamed operation among
  simp only [Bool.and_eq_true] at named
  exact named.2

/-- The headers of the functions of a program have types of the package. -/
theorem Functions.headersNamed {typeTable : TypeTable} {operations : List OperationSignature} :
    ∀ {functions : List FunctionHeader},
      Functions typeTable operations functions → FunctionsNamed typeTable functions
  | _, .nil => fun callee => callee.elimNil
  | _, .snoc (header := header) earlier definition wellFormed =>
      have named : Ty.allNamed typeTable header.inputs = true ∧
          Ty.allNamed typeTable header.outputs = true := by
        cases both : (Ty.allNamed typeTable header.inputs &&
            Ty.allNamed typeTable header.outputs) with
        | true => simpa only [Bool.and_eq_true] using both
        | false =>
            unfold FunctionDefinition.violation at wellFormed
            rw [both] at wellFormed
            cases wellFormed
      fun callee => by
        cases callee with
        | here => exact named
        | there callee => exact earlier.headersNamed callee
  | _, .opaque earlier header named =>
      have both : Ty.allNamed typeTable header.inputs = true ∧
          Ty.allNamed typeTable header.outputs = true := by
        simpa only [Bool.and_eq_true] using named
      fun callee => by
        cases callee with
        | here => exact both
        | there callee => exact earlier.headersNamed callee

/-- The rows of a typed package have types of the package. -/
theorem Typed.rowsNamed (typed : Typed) :
    RowsNamed typed.typeTable (typed.table.map (·.signature)) :=
  rowsNamed_of_tables typed.tablesFormed

/-- The functions of a typed package have headers of types of the package. -/
theorem Typed.functionsNamed (typed : Typed) : FunctionsNamed typed.typeTable typed.functions :=
  typed.program.functions.headersNamed

theorem Ty.allNamed_single {typeTable : TypeTable} {type : Ty}
    (named : Ty.named typeTable type = true) : Ty.allNamed typeTable [type] = true := by
  simp only [Ty.allNamed, named, Bool.and_true]

theorem Located.allNamed_single {typeTable : TypeTable} {located : Located}
    (named : Ty.named typeTable located.type = true) :
    Located.allNamed typeTable [located] = true := by
  simp only [Located.allNamed, named, Bool.and_true]

/-! ## The Fiat–Shamir rule -/

section FiatShamir

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} {typeTable : TypeTable} {roles : Nat}
  {enclosing : Option (List Nat)}

/-- The state type of a suite that absorbs is a type of the package. -/
theorem Absorber.state_named (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) {state type : Ty}
    (absorber : Absorber operations functions state type) : Ty.named typeTable state = true := by
  cases absorber with
  | row label name absorb applies => exact Ty.allNamed_head (rows absorb).2
  | handler callee => exact Ty.allNamed_head (callees callee).2

/-- What a role that may act emits to absorb a value passes the check, without a site. -/
theorem Absorber.emit_passes (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) {state type : Ty}
    (absorber : Absorber operations functions state type) {role : Nat}
    (acts : Acts roles enclosing role) {Δ : List Located} (current : Var Δ ⟨state, role⟩)
    (value : Var Δ ⟨type, role⟩) :
    Emitted.Passes typeTable roles enclosing
      (absorber.emit (protocols := protocols) (deployed := deployed) role current value) [] := by
  cases absorber with
  | row label name absorb applies =>
      have inputs := (rows absorb).1
      simp only [Ty.allNamed, Bool.and_eq_true] at inputs
      exact Emitted.Passes.andThen
        (Emitted.Passes.local (.literal (.nominal label name)) acts
          (Ty.allNamed_single inputs.2.1))
        (Emitted.Passes.local (.op absorb applies) acts (rows absorb).2)
  | handler callee =>
      exact Emitted.Passes.local (.call callee (Bool.and_false _)) acts (callees callee).2

/-- The state type of a suite that derives is a type of the package. -/
theorem Deriver.state_named (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) {state output : Ty}
    (deriver : Deriver operations functions state output) : Ty.named typeTable state = true := by
  cases deriver with
  | row label name derive applies => exact Ty.allNamed_head (rows derive).1
  | handler callee => exact Ty.allNamed_head (callees callee).1

/-- What a role that may act emits to derive a coin passes the check, without a site. -/
theorem Deriver.emit_passes (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) {state output : Ty}
    (deriver : Deriver operations functions state output) {role : Nat}
    (acts : Acts roles enclosing role) {Δ : List Located} (current : Var Δ ⟨state, role⟩) :
    Emitted.Passes typeTable roles enclosing
      (deriver.emit (protocols := protocols) (deployed := deployed) role current) [] := by
  cases deriver with
  | row label name derive applies =>
      have inputs := (rows derive).1
      simp only [Ty.allNamed, Bool.and_eq_true] at inputs
      exact Emitted.Passes.andThen
        (Emitted.Passes.local (.literal (.nominal label name)) acts
          (Ty.allNamed_single inputs.2.1))
        (Emitted.Passes.local (.op derive applies) acts (rows derive).2)
  | handler callee =>
      exact Emitted.Passes.local (.call callee (Bool.and_false _)) acts (callees callee).2

/-- What a role that may act emits to absorb its copies of the statement passes the check,
without a site, after operations that do. -/
theorem absorbStatement_passes (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) (suite : Suite operations functions)
    {role : Nat} (acts : Acts roles enclosing role) {ports Δ : List Located}
    (values : Operands Δ ports) :
    ∀ (statement : List (Agreement ports)) (position : Nat)
      (sofar emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
        [⟨suite.state, role⟩]),
      Emitted.Passes typeTable roles enclosing sofar [] →
      absorbStatement suite role values position statement sofar = .ok emitted →
      Emitted.Passes typeTable roles enclosing emitted []
  | [], _, sofar, emitted, passes, absorbed => by
      simp only [absorbStatement, Except.ok.injEq] at absorbed
      subst absorbed
      exact passes
  | agreement :: rest, position, sofar, emitted, passes, absorbed => by
      unfold absorbStatement at absorbed
      split at absorbed
      · rename_i port absorber atRole found
        exact absorbStatement_passes rows callees suite acts values rest _ _ emitted
          (Emitted.Passes.andThen passes (Absorber.emit_passes rows callees absorber acts _ _))
          absorbed
      · cases absorbed

/-- A role's start of the entry: the state type is a type of the package, and what a role
that may act emits passes the check, without a site. -/
theorem startState_passes (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) (suite : Suite operations functions)
    {role : Nat} {ports Δ : List Located} (statement : List (Agreement ports))
    (values : Operands Δ ports)
    {emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨suite.state, role⟩]}
    (started : startState suite role statement values = .ok emitted) :
    Ty.named typeTable suite.state = true ∧
      (Acts roles enclosing role → Emitted.Passes typeTable roles enclosing emitted []) := by
  unfold startState at started
  split at started
  · cases started
  · rename_i label identity row applies found
    refine ⟨Ty.allNamed_head (rows row).2, fun acts => ?_⟩
    exact absorbStatement_passes rows callees suite acts values statement 0 _ emitted
      (Emitted.Passes.andThen
        (Emitted.Passes.local (.literal (.nominal label identity)) acts (rows row).1)
        (Emitted.Passes.local (.op row applies) acts (rows row).2))
      started
  · rename_i callee found
    split at started
    · rename_i arguments operands
      simp only [Except.ok.injEq] at started
      subst started
      exact ⟨Ty.allNamed_head (callees callee).2, fun acts =>
        Emitted.Passes.local (.call callee (Bool.and_false _)) acts (callees callee).2⟩
    · cases started

/-- The Fiat–Shamir rule of a suite over tables whose types are types of the package emits
what the check of a definition accepts. -/
theorem fiatShamirRule_legal (rows : RowsNamed typeTable operations)
    (callees : FunctionsNamed typeTable functions) (suite : Suite operations functions) :
    (fiatShamirRule suite).Legal typeTable where
  exchange := by
    intro protocols deployed place site type Δ value first second emitted emits
    simp only [fiatShamirRule] at emits
    split at emits
    · cases emits
    · rename_i absorber found
      simp only [Except.ok.injEq] at emits
      subst emits
      refine ⟨⟨absorber.state_named rows callees, absorber.state_named rows callees⟩,
        fun roles enclosing clean typeNamed => ⟨[site], List.Sublist.refl _, ?_⟩⟩
      have acts := ProtocolOp.roles_act clean
      exact Emitted.Passes.andThen
        (Emitted.Passes.andThen
          (Emitted.Passes.operation clean (Located.allNamed_single typeNamed) Regions.Passes.nil)
          (Absorber.emit_passes rows callees absorber (acts _ List.mem_cons_self) _ _))
        (Absorber.emit_passes rows callees absorber
          (acts _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ _)
  draw := by
    intro protocols deployed place site inputs output law Δ first second emitted emits
    simp only [fiatShamirRule] at emits
    split at emits
    · split at emits
      · cases emits
      · rename_i deriver found
        simp only [Except.ok.injEq] at emits
        subst emits
        refine ⟨⟨deriver.state_named rows callees, deriver.state_named rows callees⟩,
          fun roles enclosing proverActs verifierActs outputNamed =>
            ⟨[], List.nil_sublist _, ?_⟩⟩
        exact Emitted.Passes.andThen (Deriver.emit_passes rows callees deriver verifierActs _)
          (Deriver.emit_passes rows callees deriver proverActs _)
    · cases emits
  entryPorts := fun roles header _ _ legal => legal
  entry := by
    intro protocols deployed place header body region entered
    simp only [fiatShamirRule] at entered
    split at entered
    · cases entered
    · rename_i atProver startsProver
      split at entered
      · cases entered
      · rename_i atVerifier startsVerifier
        split at entered
        · rename_i threaded threads
          have same := Except.ok.inj entered
          subst same
          obtain ⟨stateNamed, proverPasses⟩ := startState_passes (roles := header.roles)
            (enclosing := none) rows callees suite _ _ startsProver
          obtain ⟨_, verifierPasses⟩ := startState_passes (roles := header.roles)
            (enclosing := none) rows callees suite _ _ startsVerifier
          refine ⟨⟨stateNamed, stateNamed⟩, fun prover verifier outputsNamed =>
            ⟨_, _, _, _, threaded, threads, fun kept passes => ?_⟩⟩
          exact Emitted.Passes.wrap_nil (proverPasses ⟨prover, rfl⟩)
            (Emitted.Passes.wrap_nil (verifierPasses ⟨verifier, rfl⟩)
              (Region.Passes.bind
                (Threads.Named.states ⟨stateNamed, stateNamed⟩ place.roles outputsNamed) passes
                (Region.Passes.ret _)))
        · cases entered

end FiatShamir

/-! ## The serialize rule -/

section Serialize

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {typeTable : TypeTable}

/-- The writer, the reader and the proof of a layout over rows of types of the package are
types of the package: they are types of its fixed rows. -/
theorem Layout.named (rows : RowsNamed typeTable operations) (layout : Layout operations) :
    Ty.named typeTable layout.writer = true ∧ Ty.named typeTable layout.reader = true ∧
      Ty.named typeTable layout.proof = true :=
  ⟨Ty.allNamed_head (rows layout.start).2, Ty.allNamed_head (rows layout.read).2,
    Ty.allNamed_head (rows layout.close).2⟩

/-- The serialize rule of a layout over rows whose types are types of the package emits
what the check of a definition accepts. -/
theorem serializeRule_legal (rows : RowsNamed typeTable operations) (layout : Layout operations) :
    (serializeRule (functions := functions) layout).Legal typeTable where
  exchange := by
    intro protocols deployed place site type Δ value writer reader emitted emits
    simp only [serializeRule] at emits
    split at emits
    · rename_i populated
      split at emits
      · rename_i put take hasPut hasTake
        simp only [Except.ok.injEq] at emits
        subst emits
        refine ⟨⟨(layout.named rows).1, (layout.named rows).2.1⟩,
          fun roles enclosing clean typeNamed => ⟨[], List.nil_sublist _, ?_⟩⟩
        have acts := ProtocolOp.roles_act clean
        have prover := acts _ List.mem_cons_self
        have verifier := acts _ (List.mem_cons_of_mem _ List.mem_cons_self)
        exact Emitted.Passes.andThen
          (Emitted.Passes.local (.op put layout.writerPopulated) prover (rows put).2)
          (Emitted.Passes.andThen
            (Emitted.Passes.local (.op take populated) verifier (rows take).2)
            (Emitted.Passes.local (.guard .reject) verifier rfl))
      · cases emits
    · cases emits
  draw := by
    intro protocols deployed place site inputs output law Δ first second emitted emits
    simp only [serializeRule] at emits
    cases emits
  entryPorts := by
    intro roles header prover verifier legal
    rw [ProtocolHeader.signatureLegal_iff] at legal ⊢
    obtain ⟨⟨some, held, typed⟩, agreed⟩ := legal
    rw [Located.allNamed_append] at typed
    simp only [Bool.and_eq_true] at typed
    refine ⟨⟨some, ?_, ?_⟩, ?_⟩
    · intro port member
      change port ∈ (⟨layout.proof, roles.verifier⟩ :: header.inputs) ++
        (⟨layout.proof, roles.prover⟩ :: header.outputs) at member
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with (rfl | input) | (rfl | output)
      · exact verifier
      · exact held port (List.mem_append_left _ input)
      · exact prover
      · exact held port (List.mem_append_right _ output)
    · change Located.allNamed typeTable ((⟨layout.proof, roles.verifier⟩ :: header.inputs) ++
        (⟨layout.proof, roles.prover⟩ :: header.outputs)) = true
      rw [Located.allNamed_append]
      show ((Ty.named typeTable layout.proof && Located.allNamed typeTable header.inputs) &&
        (Ty.named typeTable layout.proof && Located.allNamed typeTable header.outputs)) = true
      rw [(layout.named rows).2.2, typed.1, typed.2]
      rfl
    · change firstViolation
        (agreementConditions (header.agreements.inputs.map fun agreement =>
            agreement.under ⟨layout.proof, roles.verifier⟩) ++
          agreementConditions (header.agreements.outputs.map fun agreement =>
            agreement.under ⟨layout.proof, roles.prover⟩)) = none
      rw [agreementConditions_under, agreementConditions_under]
      exact agreed
  entry := by
    intro protocols deployed place header body region entered
    simp only [serializeRule] at entered
    split at entered
    · rename_i threaded threads
      have same := Except.ok.inj entered
      subst same
      have named := layout.named rows
      refine ⟨⟨named.1, named.2.1⟩, fun prover verifier outputsNamed =>
        ⟨_, _, _, _, threaded, threads, fun kept passes => ?_⟩⟩
      have proverActs : Acts header.roles none place.roles.prover := ⟨prover, rfl⟩
      have verifierActs : Acts header.roles none place.roles.verifier := ⟨verifier, rfl⟩
      exact Emitted.Passes.wrap_nil
        (Emitted.Passes.local (.op layout.start layout.writerPopulated) proverActs
          (rows layout.start).2)
        (Emitted.Passes.wrap_nil
          (Emitted.Passes.local (.op layout.read layout.readerPopulated) verifierActs
            (rows layout.read).2)
          (Region.Passes.bind
            (Threads.Named.states ⟨named.1, named.2.1⟩ place.roles outputsNamed) passes
            (Emitted.Passes.wrap_nil
              (Emitted.Passes.local (.op layout.close layout.proofPopulated) proverActs
                (rows layout.close).2)
              (Emitted.Passes.wrap_nil
                (Emitted.Passes.local (.op layout.exhausted rfl) verifierActs
                  (rows layout.exhausted).2)
                (Emitted.Passes.wrap_nil
                  (Emitted.Passes.local (.guard .reject) verifierActs rfl)
                  (Region.Passes.ret _))))))
    · cases entered

end Serialize

end Zkc.Core
