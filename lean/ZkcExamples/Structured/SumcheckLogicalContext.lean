module

public import Zkc.Source.Structured.LogicalTranslation
public import Zkc.Source.Structured.LogicalTransport
public import ZkcExamples.Structured.SumcheckContractRequests
public import ZkcExamples.Structured.SumcheckRepackedVerifier

@[expose] public section

/-! The Sumcheck residual request as a port-independent logical context.

One logical table binder, of a library sort that has no port, is shared by the
initial sum and the residual evaluation. Only V's claim, point and value are
runtime observations. The same context and atoms are used for the retained
Reduction root and for its repacked export; only the port map changes. The
external request `wrapperTerminal`, which decodes a raw vector parameter in
Lean, is recovered under the explicit representation law `ofList? = some`. -/
namespace ZkcExamples.Structured.SumcheckLogicalContext
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Logical
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open SumcheckRelationContract SumcheckContractBindings SumcheckContractRequests

set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
set_option maxRecDepth 20000

/-- Library sorts: multilinear tables over the scalar domain, by arity. -/
inductive TableSort where
  | table (dimension : Nat)
  deriving DecidableEq

inductive TablePredicate where
  | sum (dimension : Nat)
  | residual (remaining count : Nat)
  deriving DecidableEq

inductive TableView where
  | decode (dimension : Nat)
  deriving DecidableEq

/-- Identities carry the domain and every static arity. -/
def vocabulary : Vocabulary where
  Sorts := TableSort
  Predicates := TablePredicate
  Views := TableView
  sortIdentity
    | .table dimension => ⟨"zkc::multilinear::logic::Polynomial", [.domain "bls12-381.fr", .nat dimension]⟩
  predicateIdentity
    | .sum dimension => ⟨"sumcheck::logic::Sum", [.domain "bls12-381.fr", .nat dimension]⟩
    | .residual remaining count =>
      ⟨"zkc::multilinear::logic::Evaluates", [.domain "bls12-381.fr", .nat remaining, .nat count]⟩
  viewIdentity
    | .decode dimension => ⟨"zkc::multilinear::logic::decode", [.domain "bls12-381.fr", .nat dimension, .nat 1]⟩
  arguments
    | .sum dimension => [.sort (.table dimension), .native scalar]
    | .residual remaining count => [.sort (.table (remaining + count)), .native vector, .native scalar]
  viewInput
    | .decode _ => .native vector
  viewOutput
    | .decode dimension => .sort (.table dimension)

variable {F G : Type} [CommRing F]

/-- The library meaning. `sum` is the Boolean-cube sum, `residual` the existing
residual relation, and `decode` the checked flat-table view. -/
def interpretation (F G : Type) [CommRing F] : Interpretation vocabulary (assignment F G) where
  sorts
    | .table dimension => Table F dimension
  holds
    | .sum _, .cons table (.cons claim .nil) => claim = booleanSum table
    | .residual remaining count, .cons table (.cons point (.cons value .nil)) =>
      Residual remaining count table point value
  view
    | .decode dimension, raw => ofList? dimension raw

/-- One table binder. -/
abbrev tableContext (dimension : Nat) : List (LogicalType vocabulary.Sorts) :=
  [.sort (.table dimension)]

abbrev polynomial (dimension : Nat) : Var (tableContext dimension) (.sort (.table dimension)) := .here

abbrev store {snapshot : Snapshot} {imported : Imported snapshot} {owner : ContractBinding imported}
    {invocation : InvocationCoordinate} {dimension : Nat} (table : Table F dimension) :
    Store (interpretation F G) owner invocation (tableContext dimension) :=
  Store.ofValues (.cons table .nil)

/-! ### Retained Reduction root -/

/-- V's claim at the retained root: input position two. -/
def rootClaim : BoundarySelector reductionRoot.protocol.signature scalar :=
  ⟨.input (.there (.there .here)), ⟨1, by decide⟩, by decide⟩

def initialAtom (dimension : Nat) :
    Atom vocabulary (assignment F G) reductionRoot.protocol.signature (tableContext dimension) :=
  ⟨.sum dimension, .cons (Term.binder (polynomial dimension)) (.cons (.observed rootClaim) .nil)⟩

def residualAtom (remaining count : Nat) :
    Atom vocabulary (assignment F G) reductionRoot.protocol.signature (tableContext (remaining + count)) :=
  ⟨.residual remaining count, .cons (Term.binder (polynomial (remaining + count)))
    (.cons (.observed residualRootPoint) (.cons (.observed residualRootValue) .nil))⟩

/-- A library sort is never a native port type. This is a constructor fact of the
carrier, true for every sort and signature; the root is shown for concreteness. -/
theorem table_sort_has_no_port (dimension : Nat) :
    (LogicalType.sort (TableSort.table dimension) : LogicalType vocabulary.Sorts) ∉
        reductionRoot.protocol.inputs.map LogicalType.native ∧
      (LogicalType.sort (TableSort.table dimension) : LogicalType vocabulary.Sorts) ∉
        reductionRoot.protocol.outputs.map LogicalType.native := by
  simp only [List.mem_map]
  constructor <;> rintro ⟨type, _, same⟩ <;> cases same

variable [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The initial atom reads V's actual claim input on every outcome. -/
theorem initial_iff (dimension : Nat) (table : Table F dimension)
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (count handle : Nat)
    (outcome : PIR.Outcome (Values (Component (assignment F G)) reductionRoot.protocol.outputs)) :
    (initialAtom dimension).Holds (interpretation F G) {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary outcome)
      (store (owner := reductionRoot) (invocation := rootInvocation) table) ↔
      claim = booleanSum table := by
  constructor
  · rintro ⟨arguments, read, holds⟩
    cases read
    exact holds
  · intro truth
    exact ⟨.cons table (.cons claim .nil), rfl, truth⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The residual atom reads only V's returned point and value; a stop has none. -/
theorem residual_iff (remaining count : Nat) (table : Table F (remaining + count))
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat)
    (outputs : Values (Component (assignment F G)) reductionRoot.protocol.outputs) :
    (residualAtom remaining count).Holds (interpretation F G) {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary (.returned outputs))
      (store (owner := reductionRoot) (invocation := rootInvocation) table) ↔
      match outputs.get (.there (.there .here)), outputs.get (.there (.there (.there .here))) with
      | some point, some value => Residual remaining count table point value
      | _, _ => False := by
  rcases outputs with _ | ⟨pointP, _ | ⟨valuesP, _ | ⟨point, _ | ⟨value, _ | ⟨⟩⟩⟩⟩⟩
  cases point <;> cases value
  · constructor
    · rintro ⟨_, read, _⟩
      cases read
    · intro impossible
      exact impossible.elim
  · constructor
    · rintro ⟨_, read, _⟩
      cases read
    · intro impossible
      exact impossible.elim
  · constructor
    · rintro ⟨_, read, _⟩
      cases read
    · intro impossible
      exact impossible.elim
  · constructor
    · rintro ⟨_, read, holds⟩
      cases read
      exact holds
    · intro holds
      exact ⟨_, rfl, holds⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem residual_stopped (remaining count : Nat) (table : Table F (remaining + count))
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat)
    (reason : PIR.Stop) :
    ¬ (residualAtom remaining count).Holds (interpretation F G) {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary (.stopped reason))
      (store (owner := reductionRoot) (invocation := rootInvocation) table) := by
  rintro ⟨arguments, read, _⟩
  cases read

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The Lean-authored external request is the logical residual atom whenever
its raw parameter represents the binder's table. Only the representation law
connects them; the residual relation itself is unchanged. -/
theorem wrapper_terminal_iff_atom (raw : List F) (remaining count : Nat)
    (table : Table F (remaining + count)) (represented : ofList? (remaining + count) raw = some table)
    (proverValues : Option (List F)) (proverDimension : Option Nat) (claim : F) (handle : Nat)
    (outputs : Values (Component (assignment F G)) reductionRoot.protocol.outputs) :
    (wrapperTerminal raw remaining count).Holds {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary (.returned outputs))
      (wrapperAssignments (G := G)) ↔
    (residualAtom remaining count).Holds (interpretation F G) {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary (.returned outputs))
      (store (owner := reductionRoot) (invocation := rootInvocation) table) :=
  (wrapper_terminal_iff raw remaining count table represented proverValues proverDimension claim handle
    outputs).trans (residual_iff remaining count table proverValues proverDimension claim handle outputs).symm

/-! ### Repacked Reduction root -/

def repackedRoot : ContractBinding SumcheckRepackedViews.imported where
  ownerIndex := ⟨0, by decide⟩
  protocolIndex := ⟨1, by decide⟩
  owner_eq := rfl

/-- Retained input positions in the repacked order. -/
def rootInputMap : Renaming SumcheckReduceBodies.runSignature.inputs
    SumcheckRepackedBodies.runSignature.inputs := by
  intro _ ref
  cases ref with
  | here => exact .there (.there (.there .here))
  | there ref => cases ref with
    | here => exact .there (.there .here)
    | there ref => cases ref with
      | here => exact .here
      | there ref => cases ref with
        | here => exact .there .here
        | there ref => cases ref with
          | here => exact .there (.there (.there (.there .here)))
          | there ref => nomatch ref

/-- Retained output positions in the repacked order. -/
def rootOutputMap : Renaming SumcheckReduceBodies.runSignature.outputs
    SumcheckRepackedBodies.runSignature.outputs := by
  intro _ ref
  cases ref with
  | here => exact .there (.there (.there .here))
  | there ref => cases ref with
    | here => exact .there (.there .here)
    | there ref => cases ref with
      | here => exact .here
      | there ref => cases ref with
        | here => exact .there .here
        | there ref => nomatch ref

/-- The retained root's ports in the repacked positions. Roles and scopes are kept. -/
def rootMap : PortMap reductionRoot.protocol.signature repackedRoot.protocol.signature where
  roles := rfl
  input := rootInputMap
  output := rootOutputMap
  inputScope := by
    intro _ ref
    cases ref with
    | here => rfl
    | there ref => cases ref with
      | here => rfl
      | there ref => cases ref with
        | here => rfl
        | there ref => cases ref with
          | here => rfl
          | there ref => cases ref with
            | here => rfl
            | there ref => nomatch ref
  outputScope := by
    intro _ ref
    cases ref with
    | here => rfl
    | there ref => cases ref with
      | here => rfl
      | there ref => cases ref with
        | here => rfl
        | there ref => cases ref with
          | here => rfl
          | there ref => nomatch ref

def repackedClaim : BoundarySelector repackedRoot.protocol.signature scalar :=
  ⟨.input .here, ⟨1, by decide⟩, by decide⟩
def repackedPoint : BoundarySelector repackedRoot.protocol.signature vector :=
  ⟨.output .here, ⟨1, by decide⟩, by decide⟩
def repackedValue : BoundarySelector repackedRoot.protocol.signature scalar :=
  ⟨.output (.there .here), ⟨1, by decide⟩, by decide⟩

/-- The map sends the retained observations to the repacked positions. -/
theorem map_observations :
    rootMap.selector rootClaim = repackedClaim ∧
    rootMap.selector residualRootPoint = repackedPoint ∧
    rootMap.selector residualRootValue = repackedValue := ⟨rfl, rfl, rfl⟩

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The repacked atoms are the transported ones: same predicates, same binder. -/
theorem repacked_atoms (remaining count : Nat) :
    rootMap.atom (residualAtom (F := F) (G := G) remaining count) =
      ⟨.residual remaining count, .cons (Term.binder (polynomial (remaining + count)))
        (.cons (.observed repackedPoint) (.cons (.observed repackedValue) .nil))⟩ ∧
    rootMap.atom (initialAtom (F := F) (G := G) (remaining + count)) =
      ⟨.sum (remaining + count), .cons (Term.binder (polynomial (remaining + count)))
        (.cons (.observed repackedClaim) .nil)⟩ := ⟨rfl, rfl⟩

def repackedInput (claim : F) (count : Nat) (proverDimension : Option Nat)
    (proverValues : Option (List F)) (handle : Nat) : ComponentInput repackedRoot F G :=
  ⟨{}, 1, SumcheckRepackedVerifier.rootInputs (some claim) (some count) proverDimension proverValues
    (some handle)⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Transport on the actual exports: the transported residual atom over
any returned repacked boundary is the retained residual atom over the retained
root's return of the same V values, with the same binder and the unchanged
`Residual` predicate. P's outputs are never read. -/
theorem repacked_residual_iff (remaining count : Nat) (table : Table F (remaining + count))
    (claim : F) (proverDimension : Option Nat) (proverValues : Option (List F)) (handle : Nat)
    (outputs : Values (Component (assignment F G)) repackedRoot.protocol.outputs) :
    (rootMap.atom (residualAtom remaining count)).Holds (interpretation F G) {}
      ((repackedInput (G := G) claim count proverDimension proverValues handle).boundary (.returned outputs))
      (store (owner := repackedRoot) (invocation := rootInvocation) table) ↔
    (residualAtom remaining count).Holds (interpretation F G) {}
      ((reductionRootInput proverValues proverDimension claim count handle).boundary
        (.returned (SumcheckReduceVerifier.reduceRootResults (outputs.get .here, outputs.get (.there .here)))))
      (store (owner := reductionRoot) (invocation := rootInvocation) table) := by
  rw [rootMap.atom_holds]
  rcases outputs with _ | ⟨point, _ | ⟨value, _ | ⟨valuesP, _ | ⟨pointP, _ | ⟨⟩⟩⟩⟩⟩
  exact Iff.rfl

/-! ### Controls -/

/-- Two binders of one sort. -/
abbrev twoTables (dimension : Nat) : List (LogicalType vocabulary.Sorts) :=
  [.sort (.table dimension), .sort (.table dimension)]

abbrev original (dimension : Nat) : Var (twoTables dimension) (.sort (.table dimension)) := .here
abbrev independent (dimension : Nat) : Var (twoTables dimension) (.sort (.table dimension)) := .there .here

def residualAt (remaining count : Nat)
    (binder : Var (twoTables (remaining + count)) (.sort (.table (remaining + count)))) :
    Atom vocabulary (assignment F G) reductionRoot.protocol.signature (twoTables (remaining + count)) :=
  ⟨.residual remaining count, .cons (Term.binder binder)
    (.cons (.observed residualRootPoint) (.cons (.observed residualRootValue) .nil))⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- Exchanging the residual's binder is justified by an equality of the two
tables, which must be supplied: nothing in the context relates two binders.
Equality is sufficient, not necessary (two tables may agree at one point);
`wrong_binder_at_actual_root` shows that without it the requests can differ. -/
theorem equal_tables_agree (remaining count : Nat)
    (first second : Table F (remaining + count)) (same : second = first)
    (boundary : BoundaryValuation (assignment F G) reductionRoot.protocol.inputs reductionRoot.protocol.outputs) :
    (residualAt remaining count (independent (remaining + count))).Holds (interpretation F G) {} boundary
        (Store.ofValues (owner := reductionRoot) (invocation := rootInvocation) (.cons first (.cons second .nil))) ↔
      (residualAt remaining count (original (remaining + count))).Holds (interpretation F G) {} boundary
        (Store.ofValues (owner := reductionRoot) (invocation := rootInvocation) (.cons first (.cons second .nil))) := by
  subst same
  rfl

def zeroTable : Table Int 1 := fun _ => 0
def oneTable : Table Int 1 := fun _ => 1

set_option smartUnfolding true in
theorem wrong_table_residual : Residual 0 1 zeroTable [0] 0 ∧ ¬ Residual 0 1 oneTable [0] 0 := by
  constructor
  · refine ⟨fun _ => 0, by simp [List.ofFn_succ], ?_⟩
    rw [Zkc.Protocols.Sumcheck.Multilinear.residualClaim_complete_iff]
    simp [extension, zeroTable]
  · rintro ⟨point, _, truth⟩
    rw [Zkc.Protocols.Sumcheck.Multilinear.residualClaim_complete_iff] at truth
    change extension 1 (fun _ => (1 : Int)) _ = 0 at truth
    rw [extension_one] at truth
    cases truth

/-- At the actual retained root and one returned tuple, the residual holds for
the original binder and fails for an independent binder of the same sort. -/
theorem wrong_binder_at_actual_root (claim : Int) (handle : Nat) :
    let boundary := (reductionRootInput (G := Int) none none claim 1 handle).boundary
      (.returned (SumcheckReduceVerifier.reduceRootResults (some [0], some 0)))
    let tables : Store (interpretation Int Int) reductionRoot rootInvocation (twoTables (0 + 1)) :=
      Store.ofValues (.cons zeroTable (.cons oneTable .nil))
    (residualAt 0 1 (original (0 + 1))).Holds (interpretation Int Int) {} boundary tables ∧
      ¬ (residualAt 0 1 (independent (0 + 1))).Holds (interpretation Int Int) {} boundary tables := by
  constructor
  · exact ⟨.cons zeroTable (.cons ([0] : List Int) (.cons (0 : Int) .nil)), rfl, wrong_table_residual.1⟩
  · rintro ⟨arguments, read, holds⟩
    cases read
    exact wrong_table_residual.2 holds

/-- The premise of the representation law is satisfiable for every table. -/
theorem representation_satisfiable (count : Nat) :
    ofList? count (List.ofFn (fun index : Fin (2 ^ count) => (index.val : Int))) =
      some (ofVector (fun index : Fin (2 ^ count) => (index.val : Int))) :=
  ofList?_ofFn _

/-! ### Inline clause and companion meaning lower into one context -/

/-- P's flat table input at the retained root. -/
def rootValues : BoundarySelector reductionRoot.protocol.signature vector :=
  ⟨.input .here, ⟨0, by decide⟩, by decide⟩

/-- An explicit view from P's runtime vector to a table of fixed arity: the
term an honest-agreement request would compare with the binder. -/
def decoded (dimension : Nat) :
    Term vocabulary (assignment F G) reductionRoot.protocol.signature (tableContext dimension)
      (.sort (.table dimension)) :=
  Term.view (V := vocabulary) (Value := assignment F G) (signature := reductionRoot.protocol.signature)
    (context := tableContext dimension) (TableView.decode dimension) (.observed rootValues)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The view reads exactly the table P's vector represents; it never consults
the binder. At V's boundary P's vector is absent, so V observes no table. -/
theorem decoded_read (dimension : Nat) (raw : List F) (count handle : Nat)
    (outcome : PIR.Outcome (Values (Component (assignment F G)) reductionRoot.protocol.outputs))
    (tables : Store (interpretation F G) reductionRoot rootInvocation (tableContext dimension)) :
    (decoded dimension).read (interpretation F G) {}
        ((⟨{}, 0, SumcheckReduceVerifier.reduceRootInputs (some raw) (some dimension) none none none⟩ :
          ComponentInput reductionRoot F G).boundary outcome) tables = ofList? dimension raw ∧
    (decoded dimension).read (interpretation F G) {}
        ((reductionRootInput (some raw) (some dimension) (0 : F) count handle).boundary outcome) tables =
      none := by
  constructor <;> rfl

/-- Lowering the retained `initial_sum` clause of Reduce with the existing
fixed-table assignment reads the same truth as the library atom over the
binder, provided the raw parameter represents the binder's table. -/
theorem inline_initial_lowers (raw : List F) (dimension : Nat) (table : Table F dimension)
    (represented : ofList? dimension raw = some table) (bounded : raw.length < indexLimit)
    (claim : F) (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) reductionOwner.protocol.inputs reductionOwner.protocol.outputs)
    (present : reductionClaim.read context boundary = some claim)
    {environment : RelationEnvironment SumcheckReduceViews.imported F G} :
    (lowerApplication (V := vocabulary) (context := tableContext dimension)
        (reductionInput (reductionEnvironment := environment)).binding).Holds
      ((interpretation F G).withRelations (relationMeaning environment)) context boundary
      (Store.extend (fixedReduction (invocation := rootInvocation) raw dimension) (.cons table .nil)) ↔
    claim = booleanSum table := by
  rw [← InterpretedApplication.holds_iff_lowered, Store.legacy_extend,
    reduction_input_holds_iff raw dimension claim context boundary present,
    reduction_truth_iff raw dimension claim bounded, booleanSum_ofList? raw table represented]

/-- The premises of `inline_initial_lowers` hold at the actual Reduce call for a
two-entry table: V's claim is read from the call's operand, the vector of
`List.ofFn` represents its table, and its length is below the capacity. -/
theorem inline_initial_lowers_at_call (claim : F) (count handle : Nat) (outcome)
    (values : Fin (2 ^ 1) → F)
    {environment : RelationEnvironment SumcheckReduceViews.imported F G} :
    (lowerApplication (V := vocabulary) (context := tableContext 1)
        (reductionInput (reductionEnvironment := environment)).binding).Holds
      ((interpretation F G).withRelations (relationMeaning environment)) (ProtocolContext.enter {} "s3" [0, 1])
      (reductionBoundary (G := G) claim count handle outcome)
      (Store.extend (fixedReduction (invocation := rootInvocation) (List.ofFn values) 1)
        (.cons (ofVector values) .nil)) ↔
    claim = booleanSum (ofVector values) :=
  inline_initial_lowers (List.ofFn values) 1 (ofVector values) (ofList?_ofFn values)
    (by rw [List.length_ofFn]; decide) claim _ _
    (reductionCall.boundaryOfOutcome_input {} 1 _ outcome reductionClaim
      (.there (.there (.there .here))) rfl rfl)

/-! ### Substitution at the actual public Sumcheck call -/

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- At the actual checked call from public Sumcheck into Reduce, the table
binder passes to the callee unchanged, and the store's legacy view is exactly
the existing instantiation that inherits the public table parameter. -/
theorem binder_through_public_call (raw : List F) (dimension : Nat) (table : Table F dimension)
    (context : ProtocolContext)
    (boundary : BoundaryValuation (assignment F G) publicOwner.protocol.inputs publicOwner.protocol.outputs) :
    (instantiate (interpretation := interpretation F G) SumcheckContractInstantiation.publicReductionCall
        (inherit SumcheckContractInstantiation.publicReductionCall (fun ref => ref)
          (SumcheckContractInstantiation.inheritPublicTable dimension))
        SumcheckContractInstantiation.noIterations context boundary
        (Store.extend (owner := publicOwner) (invocation := rootInvocation)
          (context := tableContext dimension) (fixedPublic raw)
          (.cons table .nil))).get (.binder (polynomial dimension)) = some table ∧
    (instantiate (interpretation := interpretation F G) SumcheckContractInstantiation.publicReductionCall
        (inherit SumcheckContractInstantiation.publicReductionCall (fun ref => ref)
          (SumcheckContractInstantiation.inheritPublicTable dimension))
        SumcheckContractInstantiation.noIterations context boundary
        (Store.extend (owner := publicOwner) (invocation := rootInvocation)
          (context := tableContext dimension) (fixedPublic raw)
          (.cons table .nil))).legacy =
      (SumcheckContractInstantiation.inheritPublicTable dimension).apply
        SumcheckContractInstantiation.noIterations context boundary (fixedPublic raw) := by
  constructor
  · rfl
  · rw [inherit_legacy, Store.legacy_extend]

end ZkcExamples.Structured.SumcheckLogicalContext
