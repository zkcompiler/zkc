module

public import Zkc.Core.LegalThreadRules

public section

/-! The refusals of a threading step, and what a legal program rules out.

A threading step (`stepProtocols`, of which Fiat–Shamir and serialize are instances)
refuses for three kinds of reason:

- **the construction item of the checker** (`StepRefusal.construction`): conditions on the
  shape of the program for the declared roles. `entry` is decided by `stepProtocols`;
  `towardProver`, `drawShape`, `lawInputs` and `interactive` by `touchesOp`, for every
  definition and every pair of roles it is reached with; `verifierInput` by the rule's
  `entryRefusal`; `thirdRole` by `thirdRoleRefusal`, before the step.
- **the rows of the declaration** (`StepRefusal.rows`): `row` (no suite, no layout, no
  start), `statement`, `message`, `undecoded`, and `unpopulated` (a message type without a
  value, for which no layout has a row). They are decided where the rule asks the suite or
  the layout for a row.
- **no condition of either kind** (`StepRefusal.internal`): `image` (an applied protocol
  has no image for the key, or a threaded value is not held by a participant of a
  `choose`) and `residual` (the image of a definition violates a residual condition).

A step that the construction item accepts and whose declaration has the rows returns or
refuses internally (`step_returns_or_internal`). For a program of well-formed definitions
neither internal refusal occurs, under two obligations of the rule:

- `Rule.External`: the rule never refuses internally. Both rules meet it
  (`fiatShamirRule_external`, `serializeRule_external`).
- `Rule.Legal` (`Core/LegalThread.lean`): the rule emits what the check of a definition
  accepts. Both rules meet it over tables whose types are types of the package
  (`fiatShamirRule_legal`, `serializeRule_legal` in `Core/LegalThreadRules.lean`), which
  the tables of a typed package are.

What is proved:

- **`image` is excluded** (`stepProtocols_not_image`), from `Rule.External`. The parts:
  - for a region (`threadRegion_external`, `threadRegion_returns`): `threadRegion` refuses
    internally only if its rule does or an application has no image to name. An
    application has an image to name when the callee has the image that threads for the
    preimages of the two roles or the image with its own header (`served`).
    `plainRegion_returns`: the copy of a region without a rewritten operation is not
    refused. `touches_participants` (`Core/LegalThread.lean`): inside a `repeat` or
    `choose` of a legal definition a region with a rewritten operation names both
    transcript roles, so the two threaded values of a threaded `choose` are held by its
    participants (`choose_states_held`). `touches_external`: what `touches` refuses is a
    condition of the construction item;
  - for a program (`rewriteProtocols_images`): every protocol has its image for every way
    it is reached (`DemandsServed`), because every application of a definition reaches its
    callee from every way the definition is reached (`propagate_reached`) and a
    definition is given the image that threads for every pair of roles for which it
    changes and the image with its own header for every other application
    (`rewriteDefinition_images`). So every application has an image to name
    (`served_of_demands`).
- **`residual` is excluded** (`stepProtocols_external`: no refusal of a step is internal),
  from both obligations. Hence `stepProtocols_returns`: a step that the construction item
  accepts and whose declaration has the rows returns. An image is added when its signature
  has no violation and its body passes the check with sites that pass the uniqueness test
  (`Images.add_returns`, `Images.addEntry_returns`), and each of the three kinds of image
  is such (`rewriteDefinition_external`):
  - the image with the definition's own header is the copy of the body, which passes
    with the sites of the body (`plainImage_returns`, `plainRegion_passes`);
  - the image that threads for a pair of roles is made only when the body contains a
    rewritten operation for the pair. Then the two roles are roles of the definition
    (`touches_below`), the types of the threaded values are types of the package, the
    signature has no violation (`Threads.header_legal`) and the body passes with sites
    among those of the definition (`threadRegion_passes`), which are pairwise different
    and below the limit (`sitesViolation_sublist`);
  - the image of the entry has the signature and the body that the rule's obligation
    covers (`Rule.Legal.entryPorts`, `Rule.Legal.entry`). The declared roles are roles of
    the entry: the step checks them (`declaredRolesBelow`) and no application reaches a
    protocol as the entry (`EntriesBelow`, `propagate_entry`).
- **On a typed package** neither step refuses internally, for every declaration:
  `fiatShamir_external`, `serializeProtocols_external`, `construct_external`, and with
  them `fiatShamir_returns`, `serializeProtocols_returns`, `construct_returns`.

What is not proved here: when the conditions of the construction item hold and when the
declaration has the rows. They are hypotheses of every statement that a step returns
(`ConstructionAccepts`, `RowsPresent`). Nothing is said of a rule that does not meet the
two obligations: a rule that emits an operation at a role that the definition does not
have, or a result of a type that the package does not have, is refused with `residual`
(`Tests/Core/StepRefusals.lean`). `stepProtocols_returns_or_residual` is the weaker
statement from `Rule.External` alone.

A declaration that names a role that the entry does not have, or one role twice, is
refused with `entry` by `stepProtocols`, before any definition is rewritten
(`declaredRolesBelow`; `Tests/Core/StepRefusals.lean`).
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-! ## The kinds of refusal -/

/-- A refusal of the checker's construction item: a condition on the shape of the program
for the declared entry and roles. -/
def StepRefusal.construction : StepRefusal → Bool
  | .entry | .verifierInput _ | .drawShape .. | .towardProver .. | .thirdRole .. | .lawInputs ..
  | .interactive .. => true
  | .undecoded .. | .message .. | .unpopulated .. | .statement _ | .row | .image
  | .residual _ => false

/-- A refusal for a row that the declaration's suite or layout does not have. -/
def StepRefusal.rows : StepRefusal → Bool
  | .undecoded .. | .message .. | .unpopulated .. | .statement _ | .row => true
  | .entry | .verifierInput _ | .drawShape .. | .towardProver .. | .thirdRole .. | .lawInputs ..
  | .interactive .. | .image | .residual _ => false

/-- A refusal that is neither a condition of the construction item nor a missing row. -/
def StepRefusal.internal : StepRefusal → Bool
  | .image | .residual _ => true
  | .entry | .verifierInput _ | .drawShape .. | .towardProver .. | .thirdRole .. | .lawInputs ..
  | .interactive .. | .undecoded .. | .message .. | .unpopulated .. | .statement _ | .row => false

/-- Every refusal is of exactly one kind. -/
theorem StepRefusal.kinds (refusal : StepRefusal) :
    (refusal.construction = true ∧ refusal.rows = false ∧ refusal.internal = false) ∨
      (refusal.construction = false ∧ refusal.rows = true ∧ refusal.internal = false) ∨
      (refusal.construction = false ∧ refusal.rows = false ∧ refusal.internal = true) := by
  cases refusal <;> simp [StepRefusal.construction, StepRefusal.rows, StepRefusal.internal]

/-- The construction item accepts: the step does not refuse for a condition on the shape
of the program. The item is the step's own pass (`touches` for every definition and pair,
the rule's `entryRefusal`, the entry check), so it is stated of the step's result. -/
def ConstructionAccepts {α : Type} (result : Except StepRefusal α) : Prop :=
  ∀ refusal, result = .error refusal → refusal.construction = false

/-- The declaration has the rows that the step asks for. -/
def RowsPresent {α : Type} (result : Except StepRefusal α) : Prop :=
  ∀ refusal, result = .error refusal → refusal.rows = false

/-- A step that the construction item accepts and whose declaration has the rows returns
or refuses internally. -/
theorem step_returns_or_internal {α : Type} {result : Except StepRefusal α}
    (accepted : ConstructionAccepts result) (present : RowsPresent result) :
    (∃ stepped, result = .ok stepped) ∨
      ∃ refusal, result = .error refusal ∧ refusal.internal = true := by
  cases result with
  | ok stepped => exact .inl ⟨stepped, rfl⟩
  | error refusal =>
      refine .inr ⟨refusal, rfl, ?_⟩
      have construction := accepted refusal rfl
      have rows := present refusal rfl
      rcases refusal.kinds with kind | kind | kind
      · rw [construction] at kind
        cases kind.1
      · rw [rows] at kind
        cases kind.2.1
      · exact kind.2.2

/-! ## A region that does not change -/

section Plain

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} (t : Threads)
  {table : CalleeTable t.header old new}

/-- Every protocol has an image with its own header. -/
def PlainImages (table : CalleeTable t.header old new) : Prop :=
  ∀ {header : ProtocolHeader} (callee : Var old header), ∃ image, table.find callee none = some image

mutual
  /-- The copy of a region is not refused when every protocol it applies has an image with
  its own header. It decides no residual condition. -/
  theorem plainRegion_ok (images : PlainImages t table) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        {Δ : List Located} (rename : Renaming Γ Δ),
        ∃ copy, plainRegion t table region rename = .ok copy
    | .ret values, _, rename => ⟨_, by unfold plainRegion; rfl⟩
    | .stop reason, _, _ => ⟨_, by unfold plainRegion; rfl⟩
    | .bind (mid := mid) body rest, _, rename => by
        obtain ⟨first, copiesBody⟩ := plainRegion_ok images body rename
        obtain ⟨second, copiesRest⟩ := plainRegion_ok images rest (rename.keepAll mid)
        unfold plainRegion
        rw [copiesBody, copiesRest]
        exact ⟨_, rfl⟩
    | .letOp (.at role op bodies) arguments nested rest, _, rename => by
        cases nested
        obtain ⟨next, copies⟩ :=
          plainRegion_ok images rest (rename.keepAll (Located.atRole role op.results))
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.exchange sender receiver site type) arguments nested rest, _, rename => by
        cases nested
        obtain ⟨next, copies⟩ := plainRegion_ok images rest (rename.keepAll [⟨type, receiver⟩])
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.draw owner receivers site (output := output) law populated) arguments nested rest, _,
        rename => by
        cases nested
        obtain ⟨next, copies⟩ := plainRegion_ok images rest
          (rename.keepAll (⟨output, owner⟩ :: Located.ofRoles output receivers))
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.sample owner site (output := output) law populated) arguments nested rest, _, rename => by
        cases nested
        obtain ⟨next, copies⟩ := plainRegion_ok images rest (rename.keepAll [⟨output, owner⟩])
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, _, rename => by
        obtain ⟨nested, copiesBodies⟩ := plainRegions_ok images bodies
        obtain ⟨next, copies⟩ := plainRegion_ok images rest (rename.keepAll _)
        unfold plainRegion
        rw [copiesBodies, copies]
        exact ⟨_, rfl⟩
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _,
        rename => by
        obtain ⟨nested, copiesBodies⟩ := plainRegions_ok images bodies
        obtain ⟨next, copies⟩ := plainRegion_ok images rest (rename.keepAll outputs)
        unfold plainRegion
        rw [copiesBodies, copies]
        exact ⟨_, rfl⟩
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest, _,
        rename => by
        cases nested
        obtain ⟨image, found⟩ := images callee
        obtain ⟨next, copies⟩ := plainRegion_ok images rest
          (rename.keepAll (header.outputs.map (Located.rename roleMap)))
        unfold plainRegion
        rw [found, copies]
        exact ⟨_, rfl⟩

  theorem plainRegions_ok (images : PlainImages t table)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        ∃ copies, plainRegions t table regions = .ok copies
    | .nil => ⟨_, by unfold plainRegions; rfl⟩
    | .cons (inputs := inputs) body tail => by
        obtain ⟨first, copiesBody⟩ := plainRegion_ok images body (Renaming.identity inputs)
        obtain ⟨later, copiesTail⟩ := plainRegions_ok images tail
        unfold plainRegions
        rw [copiesBody, copiesTail]
        exact ⟨_, rfl⟩
end

end Plain

/-! ## The refusals of a rule and of a region -/

/-- Both findings are refusals of the first or of the second. -/
theorem bothTouch_error {first second : Except StepRefusal Bool} {refusal : StepRefusal}
    (refused : bothTouch first second = .error refusal) :
    first = .error refusal ∨ second = .error refusal := by
  match first, second, refused with
  | .error _, _, refused => exact .inl (by cases refused; rfl)
  | .ok _, .error _, refused => exact .inr (by cases refused; rfl)

theorem bothTouch_false {first second : Except StepRefusal Bool}
    (untouched : bothTouch first second = .ok false) : first = .ok false ∧ second = .ok false := by
  match first, second, untouched with
  | .ok false, .ok false, _ => exact ⟨rfl, rfl⟩

/-- A rule never refuses internally: what it refuses at an exchange, at a draw and for the
header of the entry is a condition of the construction item or a missing row, and its
entry refuses otherwise only what its threaded body refuses. -/
structure Rule.External {t : Threads} {operations : List OperationSignature}
    {functions : List FunctionHeader} (rule : Rule t operations functions) : Prop where
  exchange : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place) (site : Nat)
    (type : Ty) {Δ : List Located} (value : Var Δ ⟨type, place.roles.prover⟩)
    (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
    (refusal : StepRefusal),
    rule.exchange (protocols := protocols) (deployed := deployed) place site type value first
      second = .error refusal → refusal.internal = false
  draw : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place) (site : Nat)
    {inputs : List Ty} {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    {Δ : List Located} (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles)) (refusal : StepRefusal),
    rule.draw (protocols := protocols) (deployed := deployed) place site law first second =
      .error refusal → refusal.internal = false
  entryRefusal : ∀ (roles : TranscriptRoles) (header : ProtocolHeader) (refusal : StepRefusal),
    rule.entryRefusal roles header = some refusal → refusal.internal = false
  entry : ∀ {protocols : List ProtocolHeader} {deployed : Bool} (place : Place)
    (header : ProtocolHeader)
    (body : {Δ : List Located} → Renaming (bindAll [] header.inputs) Δ →
      Var Δ (t.first place.roles) → Var Δ (t.second place.roles) →
        Except StepRefusal (Region (ProtocolDialect operations functions protocols deployed) Δ
          (t.states place.roles ++ header.outputs)))
    (refusal : StepRefusal),
    rule.entry place header body = .error refusal →
      refusal.internal = false ∨
        ∃ (Δ : List Located) (rename : Renaming (bindAll [] header.inputs) Δ)
          (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles)),
          body rename first second = .error refusal

section Refusals

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} (t : Threads)
  {derives : Bool} {table : CalleeTable t.header old new} {definition : Nat}
  {prover verifier : Option Nat}

/-- What `touchesOp` refuses is a condition of the construction item. -/
theorem touchesOp_external {op : ProtocolOp operations functions old deployed}
    {refusal : StepRefusal}
    (refused : touchesOp t derives table definition prover verifier op = .error refusal) :
    refusal.internal = false := by
  cases op <;> simp only [touchesOp] at refused <;> (repeat' split at refused) <;>
    first | (cases refused; rfl) | cases refused

mutual
  /-- What `touches` refuses is a condition of the construction item. -/
  theorem touches_external {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (refusal : StepRefusal),
        touches t derives table definition prover verifier region = .error refusal →
        refusal.internal = false
    | .ret _, _, refused => by simp only [touches] at refused; cases refused
    | .stop _, _, refused => by simp only [touches] at refused; cases refused
    | .bind body rest, refusal, refused => by
        unfold touches at refused
        rcases bothTouch_error refused with first | second
        · exact touches_external body refusal first
        · exact touches_external rest refusal second
    | .letOp op _ bodies rest, refusal, refused => by
        unfold touches at refused
        rcases bothTouch_error refused with own | later
        · exact touchesOp_external t own
        · rcases bothTouch_error later with nested | after
          · exact touchesRegions_external bodies refusal nested
          · exact touches_external rest refusal after

  theorem touchesRegions_external {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (refusal : StepRefusal),
        touchesRegions t derives table definition prover verifier regions = .error refusal →
        refusal.internal = false
    | .nil, _, refused => by simp only [touchesRegions] at refused; cases refused
    | .cons body tail, refusal, refused => by
        unfold touchesRegions at refused
        rcases bothTouch_error refused with first | later
        · exact touches_external body refusal first
        · exact touchesRegions_external tail refusal later
end

/-- An application has an image to name: the callee's image that threads for the preimages
of the two roles, or its image with its own header. Every other operation needs none. -/
@[expose] def servedOp (table : CalleeTable t.header old new) (prover verifier : Option Nat) :
    ProtocolOp operations functions old deployed → Bool
  | .apply callee roleMap _ _ =>
      (match preimageOf roleMap prover, preimageOf roleMap verifier with
        | some inner, some outer => (table.find callee (some ⟨inner, outer⟩)).isSome
        | _, _ => false) || (table.find callee none).isSome
  | .at .. | .exchange .. | .draw .. | .sample .. | .repeat .. | .choose .. => true

mutual
  /-- Every application of a region, nested regions included, has an image to name. -/
  @[expose] def served (table : CalleeTable t.header old new) (prover verifier : Option Nat)
      {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out → Bool
    | .ret _ => true
    | .stop _ => true
    | .bind body rest => served table prover verifier body && served table prover verifier rest
    | .letOp op _ bodies rest =>
        servedOp t table prover verifier op &&
          (servedAll table prover verifier bodies && served table prover verifier rest)

  @[expose] def servedAll (table : CalleeTable t.header old new) (prover verifier : Option Nat)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures → Bool
    | .nil => true
    | .cons body tail =>
        served table prover verifier body && servedAll table prover verifier tail
end

/-- An application that is not rewritten and has an image to name has the callee's image
with its own header. -/
theorem servedOp_plain {header : ProtocolHeader} {callee : Var old header} {roleMap : RoleMap}
    {site : Nat} {permitted : (deployed && header.specificationOnly) = false}
    (has : servedOp (operations := operations) (functions := functions) t table prover verifier
      (.apply callee roleMap site permitted) = true)
    (untouched : touchesOp (operations := operations) (functions := functions) t derives table
      definition prover verifier (.apply callee roleMap site permitted) = .ok false) :
    ∃ image, table.find callee none = some image := by
  simp only [servedOp, Bool.or_eq_true] at has
  simp only [touchesOp] at untouched
  rcases has with threads | plain
  · split at threads
    · rename_i inner outer atProver atVerifier
      rw [atProver, atVerifier] at untouched
      simp only [Except.ok.injEq] at untouched
      rw [untouched] at threads
      cases threads
    · cases threads
  · exact Option.isSome_iff_exists.mp plain

/-- An application for which `threadRegion` finds no image that threads, and that has an
image to name, has the callee's image with its own header. -/
theorem servedOp_unthreaded {roles : TranscriptRoles} {header : ProtocolHeader}
    {callee : Var old header} {roleMap : RoleMap} {site : Nat}
    {permitted : (deployed && header.specificationOnly) = false}
    (has : servedOp (operations := operations) (functions := functions) t table
      (some roles.prover) (some roles.verifier) (.apply callee roleMap site permitted) = true)
    (missing : threadedCallee t table roles roleMap callee = none) :
    ∃ image, table.find callee none = some image := by
  simp only [servedOp, Bool.or_eq_true] at has
  rcases has with threads | plain
  · exfalso
    unfold threadedCallee at missing
    change (match (preimage roleMap roles.prover).map (·.val),
        (preimage roleMap roles.verifier).map (·.val) with
      | some inner, some outer => (table.find callee (some ⟨inner, outer⟩)).isSome
      | _, _ => false) = true at threads
    cases atProver : preimage roleMap roles.prover with
    | none =>
        rw [atProver] at threads
        cases threads
    | some inner =>
        cases atVerifier : preimage roleMap roles.verifier with
        | none =>
            rw [atProver, atVerifier] at threads
            cases threads
        | some outer =>
            rw [atProver, atVerifier] at threads missing
            obtain ⟨inner, isProver⟩ := inner
            obtain ⟨outer, isVerifier⟩ := outer
            dsimp only [Option.map] at threads
            dsimp only at missing
            split at missing
            · cases missing
            · rename_i absent
              rw [absent] at threads
              cases threads
  · exact Option.isSome_iff_exists.mp plain

/-! ## A region that does not change, among images that exist -/

mutual
  /-- The copy of a region without a rewritten operation is not refused when every
  application of it has an image to name. -/
  theorem plainRegion_returns {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        served t table prover verifier region = true →
        touches t derives table definition prover verifier region = .ok false →
        ∀ {Δ : List Located} (rename : Renaming Γ Δ),
          ∃ copy, plainRegion t table region rename = .ok copy
    | .ret values, _, _, _, rename => ⟨_, by unfold plainRegion; rfl⟩
    | .stop reason, _, _, _, _ => ⟨_, by unfold plainRegion; rfl⟩
    | .bind (mid := mid) body rest, has, untouched, _, rename => by
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have parts := bothTouch_false untouched
        obtain ⟨first, copiesBody⟩ := plainRegion_returns body has.1 parts.1 rename
        obtain ⟨second, copiesRest⟩ := plainRegion_returns rest has.2 parts.2 (rename.keepAll mid)
        unfold plainRegion
        rw [copiesBody, copiesRest]
        exact ⟨_, rfl⟩
    | .letOp (.at role op bodies) arguments nested rest, has, untouched, _, rename => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have parts := bothTouch_false (bothTouch_false untouched).2
        obtain ⟨next, copies⟩ := plainRegion_returns rest has.2.2 parts.2
          (rename.keepAll (Located.atRole role op.results))
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.exchange sender receiver site type) arguments nested rest, has, untouched, _,
        rename => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have parts := bothTouch_false (bothTouch_false untouched).2
        obtain ⟨next, copies⟩ := plainRegion_returns rest has.2.2 parts.2
          (rename.keepAll [⟨type, receiver⟩])
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.draw owner receivers site (output := output) law populated) arguments nested rest,
        has, untouched, _, rename => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have parts := bothTouch_false (bothTouch_false untouched).2
        obtain ⟨next, copies⟩ := plainRegion_returns rest has.2.2 parts.2
          (rename.keepAll (⟨output, owner⟩ :: Located.ofRoles output receivers))
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.sample owner site (output := output) law populated) arguments nested rest, has,
        untouched, _, rename => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have parts := bothTouch_false (bothTouch_false untouched).2
        obtain ⟨next, copies⟩ := plainRegion_returns rest has.2.2 parts.2
          (rename.keepAll [⟨output, owner⟩])
        unfold plainRegion
        rw [copies]
        exact ⟨_, rfl⟩
    | .letOp (.repeat participants count carried collected captures covered) arguments
        bodies rest, has, untouched, _, rename => by
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have parts := bothTouch_false (bothTouch_false untouched).2
        obtain ⟨nested, copiesBodies⟩ := plainRegions_returns bodies has.2.1 parts.1
        obtain ⟨next, copies⟩ := plainRegion_returns rest has.2.2 parts.2 (rename.keepAll _)
        unfold plainRegion
        rw [copiesBodies, copies]
        exact ⟨_, rfl⟩
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, has,
        untouched, _, rename => by
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have parts := bothTouch_false (bothTouch_false untouched).2
        obtain ⟨nested, copiesBodies⟩ := plainRegions_returns bodies has.2.1 parts.1
        obtain ⟨next, copies⟩ := plainRegion_returns rest has.2.2 parts.2 (rename.keepAll outputs)
        unfold plainRegion
        rw [copiesBodies, copies]
        exact ⟨_, rfl⟩
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest, has,
        untouched, _, rename => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold touches at untouched
        have own := (bothTouch_false untouched).1
        have parts := bothTouch_false (bothTouch_false untouched).2
        obtain ⟨image, found⟩ := servedOp_plain t has.1 own
        obtain ⟨next, copies⟩ := plainRegion_returns rest has.2.2 parts.2
          (rename.keepAll (header.outputs.map (Located.rename roleMap)))
        unfold plainRegion
        rw [found, copies]
        exact ⟨_, rfl⟩

  theorem plainRegions_returns {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        servedAll t table prover verifier regions = true →
        touchesRegions t derives table definition prover verifier regions = .ok false →
        ∃ copies, plainRegions t table regions = .ok copies
    | .nil, _, _ => ⟨_, by unfold plainRegions; rfl⟩
    | .cons (inputs := inputs) body tail, has, untouched => by
        simp only [servedAll, Bool.and_eq_true] at has
        unfold touchesRegions at untouched
        have parts := bothTouch_false untouched
        obtain ⟨first, copiesBody⟩ := plainRegion_returns body has.1 parts.1
          (Renaming.identity inputs)
        obtain ⟨later, copiesTail⟩ := plainRegions_returns tail has.2 parts.2
        unfold plainRegions
        rw [copiesBody, copiesTail]
        exact ⟨_, rfl⟩
end

/-! ## A region that threads -/

section Threaded

variable {typeTable : TypeTable} {roles : Nat} {rule : Rule t operations functions}

/-- What the step refuses at an exchange is what the rule refuses there. -/
theorem rewrittenExchange_external (external : rule.External) {place : Place}
    {sender receiver site : Nat} {type : Ty} {Δ : List Located} {value : Var Δ ⟨type, sender⟩}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    {refusal : StepRefusal}
    (refused : rewrittenExchange (new := new) (deployed := deployed) t rule place sender receiver
      site type value first second = some (.error refusal)) :
    refusal.internal = false := by
  unfold rewrittenExchange at refused
  split at refused
  · split at refused
    · cases refused
    · rename_i raw emits
      cases refused
      exact external.exchange _ _ _ _ _ _ _ emits
  · cases refused

/-- What the step refuses at a draw is what the rule refuses there. -/
theorem rewrittenDraw_external (external : rule.External) {place : Place}
    {owner receiver site : Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {Δ : List Located}
    {first : Var Δ (t.first place.roles)} {second : Var Δ (t.second place.roles)}
    {refusal : StepRefusal}
    (refused : rewrittenDraw (new := new) (deployed := deployed) t rule place owner receiver site
      law first second = some (.error refusal)) :
    refusal.internal = false := by
  unfold rewrittenDraw at refused
  split at refused
  · split at refused
    · cases refused
    · rename_i raw emits
      cases refused
      exact external.draw _ _ _ _ _ _ emits
  · split at refused
    · split at refused
      · cases refused
      · rename_i raw emits
        cases refused
        exact external.draw _ _ _ _ _ _ emits
    · cases refused

mutual
  /-- A region of a legal definition that threads is not refused internally, when its rule
  never refuses internally and every application of it has an image to name: the refusal
  `image` cannot occur. -/
  theorem threadRegion_external (external : rule.External) (place : Place)
      {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (enclosing : Option (List Nat)), Region.Legal typeTable roles enclosing region →
        served t table (some place.roles.prover) (some place.roles.verifier) region = true →
        ∀ {Δ : List Located} (rename : Renaming Γ Δ) (first : Var Δ (t.first place.roles))
          (second : Var Δ (t.second place.roles)) (refusal : StepRefusal),
          threadRegion t rule table place region rename first second = .error refusal →
          refusal.internal = false
    | .ret values, _, _, _, _, _, _, _, _, refused => by
        simp only [threadRegion] at refused
        cases refused
    | .stop reason, _, _, _, _, _, _, _, _, refused => by
        simp only [threadRegion] at refused
        cases refused
    | .bind (mid := mid) body rest, enclosing, legal, has, _, rename, first, second, refusal,
        refused => by
        simp only [served, Bool.and_eq_true] at has
        unfold threadRegion at refused
        dsimp only at refused
        split at refused
        · cases refused
        · cases refused
          exact threadRegion_external external place body enclosing legal.bind.1 has.1 _ _ _ _
            (by assumption)
        · cases refused
          exact threadRegion_external external place rest enclosing legal.bind.2 has.2 _ _ _ _
            (by assumption)
    | .letOp (.at role op bodies) arguments nested rest, enclosing, legal, has, _, rename, first,
        second, refusal, refused => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold threadRegion at refused
        split at refused
        · cases refused
        · cases refused
          exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _ _
            _ (by assumption)
    | .letOp (.sample owner site law populated) arguments nested rest, enclosing, legal, has, _,
        rename, first, second, refusal, refused => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold threadRegion at refused
        split at refused
        · cases refused
        · cases refused
          exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _ _
            _ (by assumption)
    | .letOp (.exchange sender receiver site type) arguments nested rest, enclosing, legal, has, _,
        rename, first, second, refusal, refused => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold threadRegion at refused
        split at refused
        · split at refused
          · cases refused
          · cases refused
            exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _
              _ _ (by assumption)
        · cases refused
          exact rewrittenExchange_external t external (by assumption)
        · split at refused
          · cases refused
          · cases refused
            exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _
              _ _ (by assumption)
    | .letOp (.draw owner receivers site law populated) arguments nested rest, enclosing, legal,
        has, _, rename, first, second, refusal, refused => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        have later : ∀ {Δ : List Located} (rename : Renaming _ Δ)
            (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
            (refusal : StepRefusal),
            threadRegion t rule table place rest rename first second = .error refusal →
            refusal.internal = false :=
          fun rename first second refusal refused =>
            threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 rename
              first second refusal refused
        cases receivers with
        | nil =>
            unfold threadRegion at refused
            split at refused
            · cases refused
            · cases refused
              exact later _ _ _ _ (by assumption)
        | cons receiver others =>
            cases others with
            | cons another more =>
                unfold threadRegion at refused
                split at refused
                · cases refused
                · cases refused
                  exact later _ _ _ _ (by assumption)
            | nil =>
                unfold threadRegion at refused
                split at refused
                · split at refused
                  · cases refused
                  · cases refused
                    exact later _ _ _ _ (by assumption)
                · cases refused
                  exact rewrittenDraw_external t external (by assumption)
                · split at refused
                  · cases refused
                  · cases refused
                    exact later _ _ _ _ (by assumption)
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest, enclosing, legal, has, _, rename, first, second, refusal,
        refused => by
        simp only [served, servedAll, Bool.and_eq_true, and_true] at has
        unfold threadRegion at refused
        dsimp only at refused
        split at refused
        · split at refused
          rename_i inner same
          obtain ⟨rfl⟩ : body = inner := by injection same
          split at refused
          · cases refused
          · cases refused
            exact threadRegion_external external place body (some participants)
              (Regions.Legal.cons legal.letOp.2.1).1 has.2.1 _ _ _ _ (by assumption)
          · cases refused
            exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _
              _ _ (by assumption)
        · rename_i untouched
          obtain ⟨copies, returns⟩ := plainRegions_returns t (Regions.cons body Regions.nil)
            (by simp only [servedAll, Bool.and_eq_true, and_true]; exact has.2.1) untouched
          rw [returns] at refused
          split at refused
          · cases refused
          · rename_i impossible
            cases impossible
          · cases refused
            exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _
              _ _ (by assumption)
        · cases refused
          exact touchesRegions_external t _ _ (by assumption)
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, enclosing,
        legal, has, _, rename, first, second, refusal, refused => by
        simp only [served, Bool.and_eq_true] at has
        unfold threadRegion at refused
        split at refused
        · rename_i touched
          split at refused
          · dsimp only at refused
            split at refused
            · cases refused
            · cases refused
              exact threadRegions_external external place bodies _ (some participants)
                legal.letOp.2.1 has.2.1 _ (by assumption)
            · cases refused
              exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _
                _ _ _ (by assumption)
          · rename_i unheld
            exact absurd (choose_states_held t (covered := covered) legal.letOp.2.1 place touched) unheld
        · rename_i untouched
          obtain ⟨copies, returns⟩ := plainRegions_returns t bodies has.2.1 untouched
          rw [returns] at refused
          split at refused
          · cases refused
          · rename_i impossible
            cases impossible
          · cases refused
            exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _
              _ _ (by assumption)
        · cases refused
          exact touchesRegions_external t _ _ (by assumption)
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest,
        enclosing, legal, has, _, rename, first, second, refusal, refused => by
        cases nested
        simp only [served, Bool.and_eq_true] at has
        unfold threadRegion at refused
        split at refused
        · dsimp only at refused
          split at refused
          · cases refused
          · cases refused
            exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _
              _ _ (by assumption)
        · rename_i missing
          obtain ⟨image, found⟩ := servedOp_unthreaded t has.1 missing
          rw [found] at refused
          split at refused
          · cases refused
          · rename_i impossible
            cases impossible
          · cases refused
            exact threadRegion_external external place rest enclosing legal.letOp.2.2 has.2.2 _ _
              _ _ (by assumption)

  theorem threadRegions_external (external : rule.External) (place : Place)
      {signatures targets : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (threaded : ThreadedRegions t place.roles signatures targets)
        (enclosing : Option (List Nat)), Regions.Legal typeTable roles enclosing regions →
        servedAll t table (some place.roles.prover) (some place.roles.verifier) regions = true →
        ∀ (refusal : StepRefusal),
          threadRegions t rule table place regions threaded = .error refusal →
          refusal.internal = false
    | regions, threaded, enclosing, legal, has, refusal, refused =>
        match threaded, regions, legal, has, refused with
        | .nil, .nil, _, _, refused => by
            simp only [threadRegions] at refused
            cases refused
        | .cons leading added threaded, .cons body tail, legal, has, refused => by
            simp only [servedAll, Bool.and_eq_true] at has
            simp only [threadRegions] at refused
            split at refused
            · cases refused
            · cases refused
              exact threadRegion_external external place body enclosing
                (Regions.Legal.cons legal).1 has.1 _ _ _ _ (by assumption)
            · cases refused
              exact threadRegions_external external place tail threaded enclosing
                (Regions.Legal.cons legal).2 has.2 _ (by assumption)
end

/-- A region of a legal definition that threads has an image, when the construction item
accepts it, the declaration has the rows, the rule never refuses internally and every
application has an image to name. -/
theorem threadRegion_returns (external : rule.External) (place : Place) {Γ out : List Located}
    (region : Region (ProtocolDialect operations functions old deployed) Γ out)
    {enclosing : Option (List Nat)} (legal : Region.Legal typeTable roles enclosing region)
    (has : served t table (some place.roles.prover) (some place.roles.verifier) region = true)
    {Δ : List Located} (rename : Renaming Γ Δ) (first : Var Δ (t.first place.roles))
    (second : Var Δ (t.second place.roles))
    (accepted : ConstructionAccepts (threadRegion t rule table place region rename first second))
    (present : RowsPresent (threadRegion t rule table place region rename first second)) :
    ∃ image, threadRegion t rule table place region rename first second = .ok image := by
  rcases step_returns_or_internal accepted present with returned | ⟨refusal, refused, internal⟩
  · exact returned
  · rw [threadRegion_external t external place region enclosing legal has rename first second
      refusal refused] at internal
    cases internal

end Threaded

end Refusals

/-! ## The two rules never refuse internally -/

section Rules

variable {operations : List OperationSignature} {functions : List FunctionHeader}

/-- What a role's absorption of the statement refuses is a missing row. -/
theorem absorbStatement_external {protocols : List ProtocolHeader} {deployed : Bool}
    (suite : Suite operations functions) (role : Nat) {ports Δ : List Located}
    (values : Operands Δ ports) :
    ∀ (statement : List (Agreement ports)) (position : Nat)
      (sofar : Emitted (ProtocolDialect operations functions protocols deployed) Δ
        [⟨suite.state, role⟩]) (refusal : StepRefusal),
      absorbStatement suite role values position statement sofar = .error refusal →
      refusal.internal = false
  | [], _, _, _, refused => by
      simp only [absorbStatement] at refused
      cases refused
  | agreement :: rest, position, sofar, refusal, refused => by
      unfold absorbStatement at refused
      split at refused
      · exact absorbStatement_external suite role values rest _ _ refusal refused
      · cases refused
        rfl

/-- What a role's start of the entry refuses is a missing row. -/
theorem startState_external {protocols : List ProtocolHeader} {deployed : Bool}
    (suite : Suite operations functions) (role : Nat) {ports Δ : List Located}
    (statement : List (Agreement ports)) (values : Operands Δ ports) {refusal : StepRefusal}
    (refused : startState (protocols := protocols) (deployed := deployed) suite role statement
      values = .error refusal) : refusal.internal = false := by
  unfold startState at refused
  split at refused
  · cases refused
    rfl
  · exact absorbStatement_external suite role values statement _ _ refusal refused
  · split at refused
    · cases refused
    · cases refused
      rfl

/-- The Fiat–Shamir rule never refuses internally. -/
theorem fiatShamirRule_external (suite : Suite operations functions) :
    (fiatShamirRule suite).External where
  exchange := by
    intro protocols deployed place site type Δ value first second refusal refused
    simp only [fiatShamirRule] at refused
    split at refused
    · cases refused
      rfl
    · cases refused
  draw := by
    intro protocols deployed place site inputs output law Δ first second refusal refused
    simp only [fiatShamirRule] at refused
    split at refused
    · split at refused
      · cases refused
        rfl
      · cases refused
    · cases refused
      rfl
  entryRefusal := by
    intro roles header refusal refused
    simp only [fiatShamirRule, Option.map_eq_some_iff] at refused
    obtain ⟨position, _, rfl⟩ := refused
    rfl
  entry := by
    intro protocols deployed place header body refusal refused
    simp only [fiatShamirRule] at refused
    split at refused
    · cases refused
      exact .inl (startState_external suite _ _ _ (by assumption))
    · split at refused
      · cases refused
        exact .inl (startState_external suite _ _ _ (by assumption))
      · split at refused
        · cases refused
        · cases refused
          exact .inr ⟨_, _, _, _, by assumption⟩

/-- The serialize rule never refuses internally. -/
theorem serializeRule_external (layout : Layout operations) :
    (serializeRule (functions := functions) layout).External where
  exchange := by
    intro protocols deployed place site type Δ value first second refusal refused
    simp only [serializeRule] at refused
    split at refused
    · split at refused
      · cases refused
      · cases refused
        rfl
    · cases refused
      rfl
  draw := by
    intro protocols deployed place site inputs output law Δ first second refusal refused
    simp only [serializeRule] at refused
    cases refused
    rfl
  entryRefusal := by
    intro roles header refusal refused
    simp only [serializeRule] at refused
    cases refused
  entry := by
    intro protocols deployed place header body refusal refused
    simp only [serializeRule] at refused
    split at refused
    · cases refused
    · cases refused
      exact .inr ⟨_, _, _, _, by assumption⟩

end Rules

/-! ## The images that a step makes of a program

`rewriteProtocols` gives every protocol the images that the protocols after it ask for: a
protocol that is reached with a pair of roles for which it changes has the image that
threads for the pair, and a protocol that is reached otherwise has the image with its own
header. So every application of a definition has an image to name, and the refusal `image`
does not occur for a program of well-formed definitions. -/

section Tables

variable {K : Type} [DecidableEq K] {F : K → ProtocolHeader → ProtocolHeader}
  {old new : List ProtocolHeader}

theorem CalleeTable.has_weaken (table : CalleeTable F old new) (added : ProtocolHeader)
    (index : Nat) (key : K) : (table.weaken added).has index key = table.has index key := rfl

theorem CalleeTable.has_extend_zero (table : CalleeTable F old new) (header : ProtocolHeader)
    (list : List (K × Nat))
    (valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (F pair.1 header)) (key : K) :
    (table.extend header list valid).has 0 key = (CalleeTable.levelOf key list).isSome := by
  simp only [CalleeTable.has, CalleeTable.extend, Sequence.get?_eq, Sequence.toList_push]
  rfl

theorem CalleeTable.has_extend_succ (table : CalleeTable F old new) (header : ProtocolHeader)
    (list : List (K × Nat))
    (valid : ∀ pair ∈ list, atLevel? new table.depth pair.2 = some (F pair.1 header))
    (index : Nat) (key : K) :
    (table.extend header list valid).has (index + 1) key = table.has index key := by
  simp only [CalleeTable.has, CalleeTable.extend, Sequence.get?_eq, Sequence.toList_push]
  rfl

/-- A key that a list records has a level. -/
theorem CalleeTable.levelOf_isSome (key : K) :
    ∀ (list : List (K × Nat)) (level : Nat), (key, level) ∈ list →
      (CalleeTable.levelOf key list).isSome = true
  | [], _, member => nomatch member
  | (other, found) :: rest, level, member => by
      unfold CalleeTable.levelOf
      split
      · rfl
      · rename_i different
        rcases List.mem_cons.mp member with head | later
        · cases head
          exact absurd rfl different
        · have recorded := CalleeTable.levelOf_isSome key rest level later
          split
          · rfl
          · rename_i missing
            rw [missing] at recorded
            cases recorded

end Tables

/-! ### The demands of a protocol -/

/-- A protocol at a position is reached in a way. -/
def Reached (demands : List (List Demand)) (index : Nat) (demand : Demand) : Prop :=
  ∃ own, demands[index]? = some own ∧ demand ∈ own

theorem addDemand_reached (demand : Demand) :
    ∀ (index : Nat) (older : List (List Demand)), Reached (addDemand demand index older) index demand
  | 0, [] => ⟨[demand], rfl, List.mem_singleton.mpr rfl⟩
  | 0, own :: older => by
      refine ⟨_, rfl, ?_⟩
      split
      · rename_i present
        obtain ⟨other, member, same⟩ := List.any_eq_true.mp present
        rw [← of_decide_eq_true same]
        exact member
      · exact List.mem_cons_self
  | index + 1, [] => by
      obtain ⟨own, at_, member⟩ := addDemand_reached demand index []
      exact ⟨own, at_, member⟩
  | index + 1, first :: older => by
      obtain ⟨own, at_, member⟩ := addDemand_reached demand index older
      exact ⟨own, at_, member⟩

theorem addDemand_mono (demand : Demand) :
    ∀ (index : Nat) (older : List (List Demand)) (position : Nat) (other : Demand),
      Reached older position other → Reached (addDemand demand index older) position other
  | _, [], _, _, ⟨_, at_, _⟩ => nomatch at_
  | 0, own :: older, 0, other, ⟨found, at_, member⟩ => by
      cases at_
      refine ⟨_, rfl, ?_⟩
      split
      · exact member
      · exact List.mem_cons_of_mem _ member
  | 0, own :: older, position + 1, other, reached => reached
  | index + 1, own :: older, 0, other, reached => reached
  | index + 1, own :: older, position + 1, other, ⟨found, at_, member⟩ => by
      obtain ⟨later, at', member'⟩ :=
        addDemand_mono demand index older position other ⟨found, at_, member⟩
      exact ⟨later, at', member'⟩

/-- A property that every step of a fold keeps holds of the fold. -/
theorem foldl_keeps {α β : Type} (step : β → α → β) (holds : β → Prop)
    (keeps : ∀ state item, holds state → holds (step state item)) :
    ∀ (items : List α) (state : β), holds state → holds (items.foldl step state)
  | [], _, start => start
  | item :: rest, state, start => foldl_keeps step holds keeps rest _ (keeps state item start)

/-- What the step of each item establishes, and every later step keeps, holds of the fold
for each item. -/
theorem foldl_establishes {α β : Type} (step : β → α → β) (holds : α → β → Prop)
    (establishes : ∀ state item, holds item (step state item))
    (keeps : ∀ state item other, holds other state → holds other (step state item)) :
    ∀ (items : List α) (state : β) (item : α), item ∈ items → holds item (items.foldl step state)
  | first :: rest, state, item, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact foldl_keeps step (holds item) (fun state other => keeps state other item) rest _
          (establishes state item)
      · exact foldl_establishes step holds establishes keeps rest _ item later

/-- The way an application reaches its callee from a way its caller is reached. -/
def Demand.under (demand : Demand) (roleMap : RoleMap) : Demand :=
  .applied (preimageOf roleMap demand.prover) (preimageOf roleMap demand.verifier)

/-- The demands after a definition keep the demands before it. -/
theorem propagate_mono (own : List Demand) (applied : List (Nat × RoleMap))
    (older : List (List Demand)) (position : Nat) (other : Demand)
    (reached : Reached older position other) :
    Reached (propagate own applied older) position other :=
  foldl_keeps _ (fun demands => Reached demands position other)
    (fun state _ before =>
      foldl_keeps _ (fun demands => Reached demands position other)
        (fun state _ before => addDemand_mono _ _ state position other before) applied
        state before)
    own older reached

/-- Every application of a definition reaches its callee from every way the definition is
reached. -/
theorem propagate_reached (own : List Demand) (applied : List (Nat × RoleMap))
    (older : List (List Demand)) {demand : Demand} (member : demand ∈ own)
    {application : Nat × RoleMap} (applies : application ∈ applied) :
    Reached (propagate own applied older) application.1 (demand.under application.2) := by
  refine foldl_establishes _
    (fun (demand : Demand) demands => Reached demands application.1 (demand.under application.2))
    ?_ ?_ own older demand member
  · intro state demand
    exact foldl_establishes _
      (fun (application : Nat × RoleMap) demands =>
        Reached demands application.1 (demand.under application.2))
      (fun state application => addDemand_reached _ _ state)
      (fun state application other before => addDemand_mono _ _ state _ _ before) applied state
      application applies
  · intro state demand other before
    exact foldl_keeps _ (fun demands => Reached demands application.1 (other.under application.2))
      (fun state application before => addDemand_mono _ _ state _ _ before) applied state before

/-- A way a protocol is reached has its image: the one that threads for the two roles, or
the one with the protocol's own header. `has` says for which keys the protocol has an
image. -/
def Demand.served (has : Option TranscriptRoles → Bool) : Demand → Bool
  | .applied (some prover) (some verifier) => has (some ⟨prover, verifier⟩) || has none
  | .applied _ _ => has none
  | .entry _ => true

section Demands

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}

mutual
  /-- The applications of a region are found before those found so far. -/
  theorem applications_keeps {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (found : List (Nat × RoleMap)) (application : Nat × RoleMap),
        application ∈ found → application ∈ applications region found
    | .ret _, _, _, member => member
    | .stop _, _, _, member => member
    | .bind body rest, found, application, member =>
        applications_keeps rest _ application (applications_keeps body found application member)
    | .letOp _ _ bodies rest, _, application, member =>
        applications_keeps rest _ application
          (applicationsOf_keeps bodies _ application (List.mem_append_right _ member))

  theorem applicationsOf_keeps {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (found : List (Nat × RoleMap)) (application : Nat × RoleMap),
        application ∈ found → application ∈ applicationsOf regions found
    | .nil, _, _, member => member
    | .cons body tail, found, application, member =>
        applicationsOf_keeps tail _ application (applications_keeps body found application member)
end

variable (t) in
/-- An application whose callee has its image for the way the application reaches it has
an image to name. -/
theorem servedOp_of_demand {table : CalleeTable t.header old new} {prover verifier : Option Nat}
    {header : ProtocolHeader} {callee : Var old header} {roleMap : RoleMap} {site : Nat}
    {permitted : (deployed && header.specificationOnly) = false}
    (has : Demand.served (table.has callee.index)
      (.applied (preimageOf roleMap prover) (preimageOf roleMap verifier)) = true) :
    servedOp (operations := operations) (functions := functions) t table prover verifier
      (.apply callee roleMap site permitted) = true := by
  simp only [servedOp, CalleeTable.find_isSome]
  cases atProver : preimageOf roleMap prover with
  | none =>
      rw [atProver] at has
      simpa only [Demand.served, Bool.false_or] using has
  | some inner =>
      cases atVerifier : preimageOf roleMap verifier with
      | none =>
          rw [atProver, atVerifier] at has
          simpa only [Demand.served, Bool.false_or] using has
      | some outer =>
          rw [atProver, atVerifier] at has
          exact has

mutual
  /-- A region has an image to name at every application when every callee it applies has
  its image for the way the application reaches it. -/
  theorem served_of_demands {table : CalleeTable t.header old new} {prover verifier : Option Nat}
      {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (found : List (Nat × RoleMap)),
        (∀ application ∈ applications region found, application.1 < old.length →
          Demand.served (table.has application.1)
            (.applied (preimageOf application.2 prover) (preimageOf application.2 verifier)) =
              true) →
        served t table prover verifier region = true
    | .ret _, _, _ => rfl
    | .stop _, _, _ => rfl
    | .bind body rest, found, has => by
        simp only [served, Bool.and_eq_true]
        exact ⟨served_of_demands body found fun application member =>
            has application (applications_keeps rest _ application member),
          served_of_demands rest _ has⟩
    | .letOp op arguments bodies rest, found, has => by
        simp only [served, Bool.and_eq_true]
        refine ⟨?_, servedAll_of_demands bodies _ fun application member =>
            has application (applications_keeps rest _ application member),
          served_of_demands rest _ has⟩
        cases op with
        | apply callee roleMap site permitted =>
            exact servedOp_of_demand t (has (callee.index, roleMap)
              (applications_keeps rest _ _ (applicationsOf_keeps bodies _ _
                (List.mem_append_left _ List.mem_cons_self))) callee.index_lt)
        | _ => rfl

  theorem servedAll_of_demands {table : CalleeTable t.header old new}
      {prover verifier : Option Nat} {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (found : List (Nat × RoleMap)),
        (∀ application ∈ applicationsOf regions found, application.1 < old.length →
          Demand.served (table.has application.1)
            (.applied (preimageOf application.2 prover) (preimageOf application.2 verifier)) =
              true) →
        servedAll t table prover verifier regions = true
    | .nil, _, _ => rfl
    | .cons body tail, found, has => by
        simp only [servedAll, Bool.and_eq_true]
        exact ⟨served_of_demands body found fun application member =>
            has application (applicationsOf_keeps tail _ application member),
          servedAll_of_demands tail _ has⟩
end

end Demands

/-! ### Tables that have the same images -/

section Congruence

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new other : List ProtocolHeader} {deployed : Bool} {t : Threads} {derives : Bool}
  {definition : Nat} {prover verifier : Option Nat}
  {table : CalleeTable t.header old new} {image : CalleeTable t.header old other}

theorem touchesOp_congr (same : ∀ index key, image.has index key = table.has index key) :
    ∀ (op : ProtocolOp operations functions old deployed),
      touchesOp t derives image definition prover verifier op =
        touchesOp t derives table definition prover verifier op
  | .apply callee roleMap site permitted => by
      simp only [touchesOp, CalleeTable.find_isSome, same]
  | .at .. => rfl
  | .exchange .. => rfl
  | .draw .. => rfl
  | .sample .. => rfl
  | .repeat .. => rfl
  | .choose .. => rfl

theorem servedOp_congr (same : ∀ index key, image.has index key = table.has index key) :
    ∀ (op : ProtocolOp operations functions old deployed),
      servedOp t image prover verifier op = servedOp t table prover verifier op
  | .apply callee roleMap site permitted => by
      simp only [servedOp, CalleeTable.find_isSome, same]
  | .at .. => rfl
  | .exchange .. => rfl
  | .draw .. => rfl
  | .sample .. => rfl
  | .repeat .. => rfl
  | .choose .. => rfl

mutual
  /-- Whether a region contains a rewritten operation depends on the table only through
  the keys for which each protocol has an image. -/
  theorem touches_congr (same : ∀ index key, image.has index key = table.has index key)
      {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        touches t derives image definition prover verifier region =
          touches t derives table definition prover verifier region
    | .ret _ => by simp only [touches]
    | .stop _ => by simp only [touches]
    | .bind body rest => by
        unfold touches
        rw [touches_congr same body, touches_congr same rest]
    | .letOp op _ bodies rest => by
        unfold touches
        rw [touchesOp_congr same op, touchesRegions_congr same bodies, touches_congr same rest]

  theorem touchesRegions_congr (same : ∀ index key, image.has index key = table.has index key)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        touchesRegions t derives image definition prover verifier regions =
          touchesRegions t derives table definition prover verifier regions
    | .nil => by simp only [touchesRegions]
    | .cons body tail => by
        unfold touchesRegions
        rw [touches_congr same body, touchesRegions_congr same tail]
end

mutual
  theorem served_congr (same : ∀ index key, image.has index key = table.has index key)
      {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        served t image prover verifier region = served t table prover verifier region
    | .ret _ => by simp only [served]
    | .stop _ => by simp only [served]
    | .bind body rest => by
        unfold served
        rw [served_congr same body, served_congr same rest]
    | .letOp op _ bodies rest => by
        unfold served
        rw [servedOp_congr same op, servedAll_congr same bodies, served_congr same rest]

  theorem servedAll_congr (same : ∀ index key, image.has index key = table.has index key)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        servedAll t image prover verifier regions = servedAll t table prover verifier regions
    | .nil => by simp only [servedAll]
    | .cons body tail => by
        unfold servedAll
        rw [served_congr same body, servedAll_congr same tail]
end

/-- An operation is rewritten only for two roles that both exist. -/
theorem touchesOp_some {op : ProtocolOp operations functions old deployed}
    (touched : touchesOp t derives table definition prover verifier op = .ok true) :
    prover.isSome = true ∧ verifier.isSome = true := by
  cases prover with
  | some inner =>
      cases verifier with
      | some outer => exact ⟨rfl, rfl⟩
      | none =>
          exfalso
          cases op <;> simp only [touchesOp, isRole, preimageOf] at touched <;>
            (repeat' split at touched) <;> (try simp_all) <;>
            (repeat' split at touched) <;> cases touched
  | none =>
      exfalso
      cases op <;> simp only [touchesOp, isRole, preimageOf] at touched <;>
        (repeat' split at touched) <;> (try simp_all) <;>
            (repeat' split at touched) <;> cases touched

mutual
  /-- A region contains a rewritten operation only for two roles that both exist. -/
  theorem touches_some {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        touches t derives table definition prover verifier region = .ok true →
        prover.isSome = true ∧ verifier.isSome = true
    | .ret _, touched => by simp only [touches] at touched; cases touched
    | .stop _, touched => by simp only [touches] at touched; cases touched
    | .bind body rest, touched => by
        unfold touches at touched
        rcases bothTouch_true touched with first | second
        · exact touches_some body first
        · exact touches_some rest second
    | .letOp op _ bodies rest, touched => by
        unfold touches at touched
        rcases bothTouch_true touched with own | later
        · exact touchesOp_some own
        · rcases bothTouch_true later with nested | after
          · exact touchesRegions_some bodies nested
          · exact touches_some rest after

  theorem touchesRegions_some {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        touchesRegions t derives table definition prover verifier regions = .ok true →
        prover.isSome = true ∧ verifier.isSome = true
    | .nil, touched => by simp only [touchesRegions] at touched; cases touched
    | .cons body tail, touched => by
        unfold touchesRegions at touched
        rcases bothTouch_true touched with first | later
        · exact touches_some body first
        · exact touchesRegions_some tail later
end

end Congruence

/-! ### The images of one definition -/

section Images

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {t : Threads} {rule : Rule t operations functions}
  {old : List ProtocolHeader} {header : ProtocolHeader}

/-- A refusal that is not internal is not `image`. -/
theorem StepRefusal.not_image {refusal : StepRefusal} (external : refusal.internal = false) :
    refusal ≠ .image := by
  intro same
  subst same
  cases external

/-- What `classify` refuses is a condition of the construction item. -/
theorem classify_external {new : List ProtocolHeader} (table : CalleeTable t.header old new)
    (number : Nat) (definition : ProtocolDefinition operations functions old header) :
    ∀ (demands : List Demand) (refusal : StepRefusal),
      classify t rule table number definition demands = .error refusal → refusal.internal = false
  | [], _, refused => by simp only [classify] at refused; cases refused
  | demand :: rest, refusal, refused => by
      unfold classify at refused
      split at refused
      · cases refused
      · cases refused
        exact touches_external t _ _ (by assumption)
      · cases refused
        exact classify_external table number definition rest _ (by assumption)

/-- `classify` says of every demand whether the definition changes for it. -/
theorem classify_spec {new : List ProtocolHeader} (table : CalleeTable t.header old new)
    (number : Nat) (definition : ProtocolDefinition operations functions old header) :
    ∀ (demands : List Demand) (classified : List (Demand × Bool)),
      classify t rule table number definition demands = .ok classified →
      (∀ pair ∈ classified, pair.1 ∈ demands ∧
        touches t rule.derives table number pair.1.prover pair.1.verifier definition.body =
          .ok pair.2) ∧
      ∀ demand ∈ demands, ∃ active, (demand, active) ∈ classified
  | [], classified, classifies => by
      simp only [classify, Except.ok.injEq] at classifies
      subst classifies
      exact ⟨fun _ member => (nomatch member), fun _ member => (nomatch member)⟩
  | demand :: rest, classified, classifies => by
      unfold classify at classifies
      split at classifies
      · rename_i active later touched classifiesRest
        simp only [Except.ok.injEq] at classifies
        subst classifies
        obtain ⟨sound, complete⟩ := classify_spec table number definition rest later classifiesRest
        refine ⟨fun pair member => ?_, fun other member => ?_⟩
        · rcases List.mem_cons.mp member with rfl | earlier
          · exact ⟨List.mem_cons_self, touched⟩
          · exact ⟨List.mem_cons_of_mem _ (sound pair earlier).1, (sound pair earlier).2⟩
        · rcases List.mem_cons.mp member with rfl | earlier
          · exact ⟨active, List.mem_cons_self⟩
          · obtain ⟨found, recorded⟩ := complete other earlier
            exact ⟨found, List.mem_cons_of_mem _ recorded⟩
      · cases classifies
      · cases classifies

/-- One more image: its key is recorded, and every protocol has the images it had. -/
theorem Images.add_ok {images result : Images t typeTable operations functions old header}
    {key : Option TranscriptRoles}
    {body : Region
      (ProtocolDialect operations functions images.new (!(t.header key header).specificationOnly))
      (bindAll [] (t.header key header).inputs) (t.header key header).outputs}
    {origin : Origin} (added : images.add key body origin = .ok result) :
    result.list = (key, images.table.depth) :: images.list ∧
      ∀ index other, result.table.has index other = images.table.has index other := by
  unfold Images.add at added
  split at added
  · simp only [Except.ok.injEq] at added
    subst added
    exact ⟨rfl, fun _ _ => rfl⟩
  · cases added

/-- An image that is not added violates a residual condition. -/
theorem Images.add_error {images : Images t typeTable operations functions old header}
    {key : Option TranscriptRoles}
    {body : Region
      (ProtocolDialect operations functions images.new (!(t.header key header).specificationOnly))
      (bindAll [] (t.header key header).inputs) (t.header key header).outputs}
    {origin : Origin} {refusal : StepRefusal}
    (refused : images.add key body origin = .error refusal) : refusal ≠ .image := by
  unfold Images.add at refused
  split at refused
  · cases refused
  · cases refused
    exact fun same => nomatch same

theorem Images.addEntry_ok {images result : Images t typeTable operations functions old header}
    {ports : EntryPorts}
    {body : Region (ProtocolDialect operations functions images.new (!header.specificationOnly))
      (bindAll [] ports.inputs) ports.outputs}
    {origin : Origin} (added : images.addEntry ports body origin = .ok result) :
    result.list = images.list ∧
      ∀ index other, result.table.has index other = images.table.has index other := by
  unfold Images.addEntry at added
  split at added
  · simp only [Except.ok.injEq] at added
    subst added
    exact ⟨rfl, fun _ _ => rfl⟩
  · cases added

theorem Images.addEntry_error {images : Images t typeTable operations functions old header}
    {ports : EntryPorts}
    {body : Region (ProtocolDialect operations functions images.new (!header.specificationOnly))
      (bindAll [] ports.inputs) ports.outputs}
    {origin : Origin} {refusal : StepRefusal}
    (refused : images.addEntry ports body origin = .error refusal) : refusal ≠ .image := by
  unfold Images.addEntry at refused
  split at refused
  · cases refused
  · cases refused
    exact fun same => nomatch same

/-- One more image is added when its signature has no violation and its body passes the
check with sites that pass the uniqueness test. -/
theorem Images.add_returns {images : Images t typeTable operations functions old header}
    {key : Option TranscriptRoles}
    {body : Region
      (ProtocolDialect operations functions images.new (!(t.header key header).specificationOnly))
      (bindAll [] (t.header key header).inputs) (t.header key header).outputs}
    {origin : Origin} {kept : List Nat}
    (signature : (t.header key header).SignatureLegal typeTable)
    (passes : Region.Passes typeTable (t.header key header).roles none body kept)
    (clean : sitesViolation kept = none) : ∃ result, images.add key body origin = .ok result := by
  unfold Images.add
  split
  · exact ⟨_, rfl⟩
  · rename_i violation found
    rw [ProtocolDefinition.violation_of_passes (definition := ⟨body⟩) signature passes clean]
      at found
    cases found

/-- The image of the entry is added when its signature has no violation and its body
passes the check with sites that pass the uniqueness test. -/
theorem Images.addEntry_returns {images : Images t typeTable operations functions old header}
    {ports : EntryPorts}
    {body : Region (ProtocolDialect operations functions images.new (!header.specificationOnly))
      (bindAll [] ports.inputs) ports.outputs}
    {origin : Origin} {kept : List Nat}
    (signature : (ports.header header).SignatureLegal typeTable)
    (passes : Region.Passes typeTable header.roles none body kept)
    (clean : sitesViolation kept = none) :
    ∃ result, images.addEntry ports body origin = .ok result := by
  unfold Images.addEntry
  split
  · exact ⟨_, rfl⟩
  · rename_i violation found
    rw [ProtocolDefinition.violation_of_passes (header := ports.header header)
      (definition := ⟨body⟩) signature passes clean] at found
    cases found

/-- The image with the definition's own header, for a way the definition is reached for
which it does not change: it is not refused for a missing image, and it is recorded. -/
theorem plainImage_spec {base : List ProtocolHeader} {table : CalleeTable t.header old base}
    {derives : Bool} {prover verifier : Option Nat} (number : Nat)
    (definition : ProtocolDefinition operations functions old header) (made : Bool)
    (images : Images t typeTable operations functions old header)
    (same : ∀ index key, images.table.has index key = table.has index key)
    (untouched : touches t derives table number prover verifier definition.body = .ok false)
    (has : served t table prover verifier definition.body = true)
    (recorded : made = true → ∃ level, (none, level) ∈ images.list) :
    (∀ refusal, plainImage t number definition made images = .error refusal →
      refusal ≠ .image) ∧
    ∀ result, plainImage t number definition made images = .ok result →
      (∀ index key, result.table.has index key = table.has index key) ∧
      (∀ pair ∈ images.list, pair ∈ result.list) ∧ ∃ level, (none, level) ∈ result.list := by
  unfold plainImage
  split
  · rename_i already
    refine ⟨fun _ refused => (nomatch refused), fun result returned => ?_⟩
    simp only [Except.ok.injEq] at returned
    subst returned
    exact ⟨same, fun _ member => member, recorded already⟩
  · obtain ⟨copy, copies⟩ := plainRegion_returns (derives := derives) (definition := number) t
      definition.body ((served_congr same definition.body).trans has)
      ((touches_congr same definition.body).trans untouched) (Renaming.identity header.inputs)
    rw [copies]
    refine ⟨fun refusal refused => Images.add_error refused, fun result returned => ?_⟩
    obtain ⟨listed, kept⟩ := Images.add_ok returned
    refine ⟨fun index key => (kept index key).trans (same index key), fun pair member => ?_,
      ⟨images.table.depth, ?_⟩⟩
    · rw [listed]
      exact List.mem_cons_of_mem _ member
    · rw [listed]
      exact List.mem_cons_self

/-- The image with its own header of a well-formed definition is made, for a way the
definition is reached for which it does not change and every application of it has an
image to name: the copy of its body passes the check with the sites of the body. -/
theorem plainImage_returns {base : List ProtocolHeader} {table : CalleeTable t.header old base}
    {derives : Bool} {prover verifier : Option Nat} (number : Nat)
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none) (made : Bool)
    (images : Images t typeTable operations functions old header)
    (same : ∀ index key, images.table.has index key = table.has index key)
    (untouched : touches t derives table number prover verifier definition.body = .ok false)
    (has : served t table prover verifier definition.body = true) :
    ∃ result, plainImage t number definition made images = .ok result ∧
      ∀ index key, result.table.has index key = table.has index key := by
  unfold plainImage
  split
  · exact ⟨images, rfl, same⟩
  · obtain ⟨copy, copies⟩ := plainRegion_returns (derives := derives) (definition := number) t
      definition.body ((served_congr same definition.body).trans has)
      ((touches_congr same definition.body).trans untouched) (Renaming.identity header.inputs)
    rw [copies]
    obtain ⟨signature, clean⟩ := ProtocolDefinition.violation_parts wellFormed
    obtain ⟨result, added⟩ := Images.add_returns (images := images) (key := none) (body := copy)
      (origin := ⟨number, none, false⟩) signature
      (plainRegion_passes definition.body none (definition.body_legal wellFormed) _ copy copies)
      clean
    exact ⟨result, added, fun index key =>
      ((Images.add_ok added).2 index key).trans (same index key)⟩

/-- What the images of a definition record for a way it is reached: the image that threads
for a pair of roles for which the definition changes, the image with its own header for
every other application. -/
def Recorded (list : List (Option TranscriptRoles × Nat)) : Demand → Bool → Prop
  | .applied (some prover) (some verifier), true => ∃ level, (some ⟨prover, verifier⟩, level) ∈ list
  | .applied _ _, _ => ∃ level, (none, level) ∈ list
  | .entry _, _ => True

theorem Recorded.mono {list longer : List (Option TranscriptRoles × Nat)}
    (kept : ∀ pair ∈ list, pair ∈ longer) :
    ∀ {demand : Demand} {active : Bool}, Recorded list demand active → Recorded longer demand active
  | .applied (some _) (some _), true, ⟨level, member⟩ => ⟨level, kept _ member⟩
  | .applied (some _) (some _), false, ⟨level, member⟩ => ⟨level, kept _ member⟩
  | .applied (some _) none, _, ⟨level, member⟩ => ⟨level, kept _ member⟩
  | .applied none _, _, ⟨level, member⟩ => ⟨level, kept _ member⟩
  | .entry _, _, _ => trivial

/-- A recorded way has its image among the keys of the list. -/
theorem Recorded.served {list : List (Option TranscriptRoles × Nat)} :
    ∀ {demand : Demand} {active : Bool}, Recorded list demand active →
      demand.served (fun key => (CalleeTable.levelOf key list).isSome) = true
  | .applied (some _) (some _), true, ⟨level, member⟩ => by
      simp only [Demand.served, Bool.or_eq_true]
      exact .inl (CalleeTable.levelOf_isSome _ list level member)
  | .applied (some _) (some _), false, ⟨level, member⟩ => by
      simp only [Demand.served, Bool.or_eq_true]
      exact .inr (CalleeTable.levelOf_isSome _ list level member)
  | .applied (some _) none, _, ⟨level, member⟩ => CalleeTable.levelOf_isSome _ list level member
  | .applied none _, _, ⟨level, member⟩ => CalleeTable.levelOf_isSome _ list level member
  | .entry _, _, _ => rfl

end Images

/-! ### The images of a program -/

section Program

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {t : Threads} {rule : Rule t operations functions}

/-- What the images of one definition are, when they are made: no refusal `image`; every
earlier protocol has the images it had; the keys recorded before are kept; and every way
the definition is reached has its image recorded. -/
def DefinitionImages {old base : List ProtocolHeader} {header : ProtocolHeader}
    (table : CalleeTable t.header old base) (before : List (Option TranscriptRoles × Nat))
    (classified : List (Demand × Bool))
    (outcome : Except StepRefusal (Images t typeTable operations functions old header)) : Prop :=
  (∀ refusal, outcome = .error refusal → refusal ≠ .image) ∧
    ∀ result, outcome = .ok result →
      (∀ index key, result.table.has index key = table.has index key) ∧
      (∀ pair ∈ before, pair ∈ result.list) ∧
      ∀ pair ∈ classified, Recorded result.list pair.1 pair.2

theorem DefinitionImages.refused {old base : List ProtocolHeader} {header : ProtocolHeader}
    {table : CalleeTable t.header old base} {before : List (Option TranscriptRoles × Nat)}
    {classified : List (Demand × Bool)} {refusal : StepRefusal} (other : refusal ≠ .image) :
    DefinitionImages (typeTable := typeTable) (operations := operations) (functions := functions)
      (header := header) table before classified (.error refusal) :=
  ⟨fun _ same => by cases same; exact other, fun _ returned => (nomatch returned)⟩

/-- The arm of `rewriteDefinition` that makes the image with the definition's own header. -/
local macro "plain_arm " plain:term : tactic => `(tactic| (
  split
  · rename_i next produced
    exact ($plain).2 next produced
  · rename_i refusal refused
    exact DefinitionImages.refused (($plain).1 _ refused)))

/-- The images of one definition: none is refused for a missing image, and every way the
definition is reached has its image recorded, when every application of the definition has
an image to name for every way the definition is reached. -/
theorem rewriteDefinition_images (external : rule.External) {old base : List ProtocolHeader}
    {header : ProtocolHeader} (table : CalleeTable t.header old base) (number : Nat)
    (definition : ProtocolDefinition operations functions old header)
    (legal : Region.Legal typeTable header.roles none definition.body) (specialized : Bool) :
    ∀ (classified : List (Demand × Bool)) (made : Bool)
      (images : Images t typeTable operations functions old header),
      (∀ index key, images.table.has index key = table.has index key) →
      (∀ pair ∈ classified,
        touches t rule.derives table number pair.1.prover pair.1.verifier definition.body =
            .ok pair.2 ∧
          served t table pair.1.prover pair.1.verifier definition.body = true) →
      (made = true → ∃ level, (none, level) ∈ images.list) →
      DefinitionImages table images.list classified
        (rewriteDefinition t rule number definition specialized classified made images)
  | [], made, images, same, _, _ => by
      simp only [rewriteDefinition]
      refine ⟨fun _ refused => (nomatch refused), fun result returned => ?_⟩
      simp only [Except.ok.injEq] at returned
      subst returned
      exact ⟨same, fun _ member => member, fun _ member => (nomatch member)⟩
  | (demand, active) :: rest, made, images, same, facts, recorded => by
      have head := facts (demand, active) List.mem_cons_self
      -- The images of the other ways, after the image for this one.
      have later : ∀ (next : Images t typeTable operations functions old header) (nextMade : Bool),
          (∀ index key, next.table.has index key = table.has index key) →
          (∀ pair ∈ images.list, pair ∈ next.list) →
          (nextMade = true → ∃ level, (none, level) ∈ next.list) →
          Recorded next.list demand active →
          DefinitionImages table images.list ((demand, active) :: rest)
            (rewriteDefinition t rule number definition specialized rest nextMade next) := by
        intro next nextMade sameNext keptNext recordedNext headRecorded
        obtain ⟨errors, returns⟩ := rewriteDefinition_images external table number definition legal
          specialized rest nextMade next sameNext
          (fun pair member => facts pair (List.mem_cons_of_mem _ member)) recordedNext
        refine ⟨errors, fun result returned => ?_⟩
        obtain ⟨sameResult, keptResult, recordedRest⟩ := returns result returned
        refine ⟨sameResult, fun pair member => keptResult pair (keptNext pair member),
          fun pair member => ?_⟩
        rcases List.mem_cons.mp member with rfl | among
        · exact Recorded.mono keptResult headRecorded
        · exact recordedRest pair among
      -- The image with the definition's own header, when the definition does not change.
      have plain : touches t rule.derives table number demand.prover demand.verifier
            definition.body = .ok false →
          (∀ list : List (Option TranscriptRoles × Nat), (∃ level, (none, level) ∈ list) →
            Recorded list demand active) →
          (∀ refusal, plainImage t number definition made images = .error refusal →
            refusal ≠ .image) ∧
          ∀ next, plainImage t number definition made images = .ok next →
            DefinitionImages table images.list ((demand, active) :: rest)
              (rewriteDefinition t rule number definition specialized rest true next) := by
        intro untouched recordedPlain
        obtain ⟨plainErrors, plainReturns⟩ := plainImage_spec (derives := rule.derives) number
          definition made images same untouched head.2 recorded
        refine ⟨plainErrors, fun next produced => ?_⟩
        obtain ⟨sameNext, keptNext, noneNext⟩ := plainReturns next produced
        exact later next true sameNext keptNext (fun _ => noneNext) (recordedPlain _ noneNext)
      cases demand with
      | entry roles =>
          have servedHere : served t images.table (some roles.prover) (some roles.verifier)
              definition.body = true := (served_congr same definition.body).trans head.2
          simp only [rewriteDefinition]
          split
          · rename_i refusal refuses
            exact DefinitionImages.refused
              (StepRefusal.not_image (external.entryRefusal _ _ _ refuses))
          · split
            · split
              · rename_i body entered
                split
                · rename_i next added
                  obtain ⟨listed, kept⟩ := Images.addEntry_ok added
                  exact later next made (fun index key => (kept index key).trans (same index key))
                    (fun pair member => by rw [listed]; exact member)
                    (fun was => by rw [listed]; exact recorded was) trivial
                · rename_i refusal refused
                  exact DefinitionImages.refused (Images.addEntry_error refused)
              · rename_i refusal refused
                refine DefinitionImages.refused ?_
                rcases external.entry _ _ _ _ refused with outside | ⟨Δ, rename, first, second, inside⟩
                · exact StepRefusal.not_image outside
                · exact StepRefusal.not_image (threadRegion_external t external _ definition.body
                    none legal servedHere rename first second _ inside)
            · rename_i idle
              have inactive : active = false := by
                cases active with
                | false => rfl
                | true => exact absurd rfl idle
              subst inactive
              plain_arm (plain head.1 fun _ _ => trivial)
      | applied prover verifier =>
          cases prover with
          | none =>
              have inactive : active = false := by
                cases active with
                | false => rfl
                | true => exact absurd (touches_some definition.body head.1).1 Bool.false_ne_true
              subst inactive
              cases verifier <;> simp only [rewriteDefinition] <;>
                plain_arm (plain head.1 fun _ found => found)
          | some inner =>
              cases verifier with
              | none =>
                  have inactive : active = false := by
                    cases active with
                    | false => rfl
                    | true =>
                        exact absurd (touches_some definition.body head.1).2 Bool.false_ne_true
                  subst inactive
                  simp only [rewriteDefinition]
                  plain_arm (plain head.1 fun _ found => found)
              | some outer =>
                  cases active with
                  | false =>
                      simp only [rewriteDefinition]
                      plain_arm (plain head.1 fun _ found => found)
                  | true =>
                      have servedHere : served t images.table (some inner) (some outer)
                          definition.body = true := (served_congr same definition.body).trans head.2
                      simp only [rewriteDefinition]
                      split
                      · rename_i body threads
                        split
                        · rename_i next added
                          obtain ⟨listed, kept⟩ := Images.add_ok added
                          exact later next made
                            (fun index key => (kept index key).trans (same index key))
                            (fun pair member => by rw [listed]; exact List.mem_cons_of_mem _ member)
                            (fun was => by
                              obtain ⟨level, member⟩ := recorded was
                              exact ⟨level, by rw [listed]; exact List.mem_cons_of_mem _ member⟩)
                            ⟨images.table.depth, by rw [listed]; exact List.mem_cons_self⟩
                        · rename_i refusal refused
                          exact DefinitionImages.refused (Images.add_error refused)
                      · rename_i refusal refused
                        exact DefinitionImages.refused (StepRefusal.not_image
                          (threadRegion_external t external _ definition.body none legal servedHere
                            _ _ _ _ refused))

/-- Every protocol has its image for every way it is reached. -/
def DemandsServed {old new : List ProtocolHeader} (table : CalleeTable t.header old new)
    (demands : List (List Demand)) : Prop :=
  ∀ index, index < old.length → ∀ demand, Reached demands index demand →
    demand.served (table.has index) = true

/-- The images of the protocols of a program: none is refused for a missing image, and
every protocol has its image for every way it is reached. -/
theorem rewriteProtocols_images (external : rule.External) (identities : Identities) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      (demands : List (List Demand)),
      (∀ refusal, rewriteProtocols t rule identities protocols demands = .error refusal →
        refusal ≠ .image) ∧
      ∀ rewritten, rewriteProtocols t rule identities protocols demands = .ok rewritten →
        DemandsServed rewritten.table demands
  | _, .nil, demands => by
      simp only [rewriteProtocols]
      exact ⟨fun _ refused => (nomatch refused),
        fun rewritten returned index below => absurd below (Nat.not_lt_zero _)⟩
  | _, .snoc (protocols := earlier) (header := header) protocols definition wellFormed, demands => by
      obtain ⟨errors, returns⟩ := rewriteProtocols_images external identities protocols
        (propagate (demands.headD []) (applications definition.body []) demands.tail)
      simp only [rewriteProtocols]
      split
      · rename_i new typed table origins counted marks rewrites
        have servedEarlier := returns _ rewrites
        split
        · rename_i classified classifies
          obtain ⟨sound, complete⟩ := classify_spec table (identities earlier.length) definition _
            classified classifies
          obtain ⟨imageErrors, imageReturns⟩ := rewriteDefinition_images external table
            (identities earlier.length) definition (definition.body_legal wellFormed)
            (Nat.ble 2 (classified.filter fun entry => entry.2 && entry.1.isApplied).length)
            classified false ⟨new, typed, table, [], (fun _ member => nomatch member), origins, counted⟩
            (fun _ _ => rfl)
            (fun pair member => ⟨(sound pair member).2,
              served_of_demands definition.body [] fun application applies below =>
                servedEarlier application.1 below _
                  (propagate_reached _ _ _ (sound pair member).1 applies)⟩)
            (fun made => nomatch made)
          split
          · rename_i images produced
            refine ⟨fun _ refused => (nomatch refused), fun rewritten returned => ?_⟩
            simp only [Except.ok.injEq] at returned
            subst returned
            obtain ⟨sameTable, _, recorded⟩ := imageReturns images produced
            intro index below demand reached
            cases index with
            | zero =>
                obtain ⟨own, at_, member⟩ := reached
                have isOwn : demands.headD [] = own := by
                  cases demands with
                  | nil => cases at_
                  | cons first others =>
                      cases at_
                      rfl
                obtain ⟨active, classifiedMember⟩ := complete demand (isOwn ▸ member)
                have keys : (images.table.extend header images.list images.valid).has 0 =
                    fun key => (CalleeTable.levelOf key images.list).isSome :=
                  funext (CalleeTable.has_extend_zero _ _ _ _)
                show demand.served ((images.table.extend header images.list images.valid).has 0) = true
                rw [keys]
                exact (recorded _ classifiedMember).served
            | succ index =>
                have before : Reached demands.tail index demand := by
                  obtain ⟨own, at_, member⟩ := reached
                  cases demands with
                  | nil => cases at_
                  | cons first others => exact ⟨own, at_, member⟩
                have keys : (images.table.extend header images.list images.valid).has (index + 1) =
                    table.has index :=
                  funext fun key =>
                    (CalleeTable.has_extend_succ _ _ _ _ index key).trans (sameTable index key)
                show demand.served
                  ((images.table.extend header images.list images.valid).has (index + 1)) = true
                rw [keys]
                exact servedEarlier index (Nat.lt_of_succ_lt_succ below) demand
                  (propagate_mono _ _ _ index demand before)
          · rename_i refusal refused
            exact ⟨fun _ same => by cases same; exact imageErrors _ refused,
              fun _ returned => (nomatch returned)⟩
        · rename_i refusal refused
          exact ⟨fun _ same => by
              cases same
              exact StepRefusal.not_image (classify_external table _ definition _ _ refused),
            fun _ returned => (nomatch returned)⟩
      · rename_i refusal refused
        exact ⟨fun _ same => by cases same; exact errors _ refused,
          fun _ returned => (nomatch returned)⟩

/-- A step does not refuse a program of well-formed definitions for a missing image, when
its rule never refuses internally. -/
theorem stepProtocols_not_image (external : rule.External) (identities : Identities)
    (entry : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old) {refusal : StepRefusal}
    (refused : stepProtocols t rule identities entry roles protocols = .error refusal) :
    refusal ≠ .image := by
  unfold stepProtocols at refused
  split at refused
  · split at refused
    · cases refused
    · rename_i inner innerRefused
      cases refused
      exact (rewriteProtocols_images external identities protocols _).1 _ innerRefused
  · cases refused
    exact fun same => nomatch same

/-- A step on a program of well-formed definitions that the construction item accepts and
whose declaration has the rows returns, or it refuses because an image violates a residual
condition. -/
theorem stepProtocols_returns_or_residual (external : rule.External) (identities : Identities)
    (entry : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (accepted : ConstructionAccepts (stepProtocols t rule identities entry roles protocols))
    (present : RowsPresent (stepProtocols t rule identities entry roles protocols)) :
    (∃ stepped, stepProtocols t rule identities entry roles protocols = .ok stepped) ∨
      ∃ violation,
        stepProtocols t rule identities entry roles protocols = .error (.residual violation) := by
  rcases step_returns_or_internal accepted present with returned | ⟨refusal, refused, internal⟩
  · exact .inl returned
  · right
    cases refusal with
    | residual violation => exact ⟨violation, refused⟩
    | image => exact absurd rfl (stepProtocols_not_image external identities entry roles protocols refused)
    | _ => exact absurd internal Bool.false_ne_true

/-! ### No image violates a residual condition -/

/-- The images of one well-formed definition: what a step refuses while it makes them is a
condition of the construction item or a missing row, when its rule never refuses
internally and emits what the check accepts, every application of the definition has an
image to name for every way the definition is reached, and every way it is reached as the
entry names two of its roles. No image is refused for a residual condition:

- the image with the definition's own header is the copy of its body, which passes the
  check with the sites of the body (`plainImage_returns`);
- the image that threads for a pair of roles is made only when the body contains a
  rewritten operation for the pair. Then the two roles are roles of the definition
  (`touches_below`) and the types of the threaded values are types of the package, so the
  signature has no violation (`Threads.header_legal`) and the body passes with sites among
  those of the definition (`threadRegion_passes`);
- the image of the entry has the signature and the body that the rule's obligation covers
  (`Rule.Legal.entryPorts`, `Rule.Legal.entry`). -/
theorem rewriteDefinition_external (external : rule.External) (legalRule : rule.Legal typeTable)
    {old base : List ProtocolHeader} {header : ProtocolHeader}
    (table : CalleeTable t.header old base) (number : Nat)
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none) (specialized : Bool) :
    ∀ (classified : List (Demand × Bool)) (made : Bool)
      (images : Images t typeTable operations functions old header),
      (∀ index key, images.table.has index key = table.has index key) →
      (∀ pair ∈ classified,
        touches t rule.derives table number pair.1.prover pair.1.verifier definition.body =
            .ok pair.2 ∧
          served t table pair.1.prover pair.1.verifier definition.body = true) →
      (∀ roles active, (Demand.entry roles, active) ∈ classified →
        Nat.blt roles.prover header.roles = true ∧ Nat.blt roles.verifier header.roles = true) →
      ∀ refusal,
        rewriteDefinition t rule number definition specialized classified made images =
          .error refusal → refusal.internal = false
  | [], made, images, _, _, _, refusal, refused => by
      simp only [rewriteDefinition] at refused
      cases refused
  | (demand, active) :: rest, made, images, same, facts, entries, refusal, refused => by
      have head := facts (demand, active) List.mem_cons_self
      have legal := definition.body_legal wellFormed
      obtain ⟨signature, clean⟩ := ProtocolDefinition.violation_parts wellFormed
      -- The images of the other ways, after the image for this one.
      have later : ∀ (next : Images t typeTable operations functions old header)
          (nextMade : Bool), (∀ index key, next.table.has index key = table.has index key) →
          rewriteDefinition t rule number definition specialized rest nextMade next =
            .error refusal → refusal.internal = false :=
        fun next nextMade sameNext refusedNext =>
          rewriteDefinition_external external legalRule table number definition wellFormed
            specialized rest nextMade next sameNext
            (fun pair member => facts pair (List.mem_cons_of_mem _ member))
            (fun roles active member => entries roles active (List.mem_cons_of_mem _ member))
            refusal refusedNext
      -- The image with the definition's own header, when the definition does not change.
      have plain : touches t rule.derives table number demand.prover demand.verifier
            definition.body = .ok false →
          (match plainImage t number definition made images with
            | .ok images => rewriteDefinition t rule number definition specialized rest true images
            | .error refusal => .error refusal) = .error refusal →
          refusal.internal = false := by
        intro untouched refusedPlain
        obtain ⟨next, produced, sameNext⟩ := plainImage_returns number definition wellFormed made
          images same untouched head.2
        rw [produced] at refusedPlain
        exact later next true sameNext refusedPlain
      cases demand with
      | entry roles =>
          have servedHere : served t images.table (some roles.prover) (some roles.verifier)
              definition.body = true := (served_congr same definition.body).trans head.2
          have inRange := entries roles active List.mem_cons_self
          simp only [rewriteDefinition] at refused
          split at refused
          · rename_i other refuses
            cases refused
            exact external.entryRefusal _ _ _ refuses
          · split at refused
            · split at refused
              · rename_i body entered
                split at refused
                · rename_i next added
                  exact later next made
                    (fun index key =>
                      ((Images.addEntry_ok added).2 index key).trans (same index key))
                    refused
                · rename_i other addRefused
                  exfalso
                  obtain ⟨named, entryPasses⟩ := legalRule.entry _ _ _ _ entered
                  have ports := (ProtocolHeader.signatureLegal_iff.mp signature).1.2.2
                  rw [Located.allNamed_append] at ports
                  simp only [Bool.and_eq_true] at ports
                  obtain ⟨Δ, rename, first, second, threaded, threads, lifts⟩ :=
                    entryPasses inRange.1 inRange.2 ports.2
                  obtain ⟨kept, among, passes⟩ :=
                    (threadRegion_passes legalRule images.protocols.headersNamed _ definition.body
                      none legal Δ rename first second threaded threads).2 named
                  obtain ⟨result, adds⟩ := Images.addEntry_returns (images := images)
                    (origin := ⟨number, some roles, true⟩)
                    (legalRule.entryPorts roles header inRange.1 inRange.2 signature)
                    (lifts kept passes) (sitesViolation_sublist among clean)
                  rw [adds] at addRefused
                  cases addRefused
              · rename_i other entryRefused
                cases refused
                rcases external.entry _ _ _ _ entryRefused with
                  outside | ⟨Δ, rename, first, second, inside⟩
                · exact outside
                · exact threadRegion_external t external _ definition.body none legal servedHere
                    rename first second _ inside
            · rename_i idle
              have inactive : active = false := by
                cases active with
                | false => rfl
                | true => exact absurd rfl idle
              subst inactive
              exact plain head.1 refused
      | applied prover verifier =>
          cases prover with
          | none =>
              have inactive : active = false := by
                cases active with
                | false => rfl
                | true => exact absurd (touches_some definition.body head.1).1 Bool.false_ne_true
              subst inactive
              cases verifier <;> simp only [rewriteDefinition] at refused <;>
                exact plain head.1 refused
          | some inner =>
              cases verifier with
              | none =>
                  have inactive : active = false := by
                    cases active with
                    | false => rfl
                    | true =>
                        exact absurd (touches_some definition.body head.1).2 Bool.false_ne_true
                  subst inactive
                  simp only [rewriteDefinition] at refused
                  exact plain head.1 refused
              | some outer =>
                  cases active with
                  | false =>
                      simp only [rewriteDefinition] at refused
                      exact plain head.1 refused
                  | true =>
                      have servedHere : served t images.table (some inner) (some outer)
                          definition.body = true := (served_congr same definition.body).trans head.2
                      simp only [rewriteDefinition] at refused
                      split at refused
                      · rename_i body threads
                        split at refused
                        · rename_i next added
                          exact later next made
                            (fun index key =>
                              ((Images.add_ok added).2 index key).trans (same index key))
                            refused
                        · rename_i other addRefused
                          exfalso
                          have touched : touches t rule.derives images.table number (some inner)
                              (some outer) definition.body = .ok true :=
                            (touches_congr same definition.body).trans head.1
                          obtain ⟨namedOf, passesOf⟩ := threadRegion_passes legalRule
                            images.protocols.headersNamed ⟨number, ⟨inner, outer⟩, specialized⟩
                            definition.body none legal _ _ _ _ body threads
                          have named := namedOf touched
                          obtain ⟨kept, among, passes⟩ := passesOf named
                          have below := touches_below t definition.body none legal head.1
                          obtain ⟨result, adds⟩ := Images.add_returns (images := images)
                            (key := some ⟨inner, outer⟩)
                            (origin := ⟨number, some ⟨inner, outer⟩, false⟩)
                            (Threads.header_legal named below.1 below.2 signature) passes
                            (sitesViolation_sublist among clean)
                          rw [adds] at addRefused
                          cases addRefused
                      · rename_i other threadRefused
                        cases refused
                        exact threadRegion_external t external _ definition.body none legal
                          servedHere _ _ _ _ threadRefused

/-- A protocol that is reached in a way after one more demand is reached in that way
before it, or the way is the demand. -/
theorem addDemand_reached_only (demand : Demand) :
    ∀ (index : Nat) (older : List (List Demand)) (position : Nat) (other : Demand),
      Reached (addDemand demand index older) position other →
      other = demand ∨ Reached older position other
  | 0, [], 0, other, ⟨own, at_, member⟩ => by
      cases at_
      exact .inl (List.mem_singleton.mp member)
  | 0, [], position + 1, other, ⟨own, at_, member⟩ => by cases at_
  | 0, own :: older, 0, other, ⟨found, at_, member⟩ => by
      cases at_
      split at member
      · exact .inr ⟨own, rfl, member⟩
      · rcases List.mem_cons.mp member with rfl | earlier
        · exact .inl rfl
        · exact .inr ⟨own, rfl, earlier⟩
  | 0, own :: older, position + 1, other, reached => .inr reached
  | index + 1, [], 0, other, ⟨own, at_, member⟩ => by
      cases at_
      cases member
  | index + 1, [], position + 1, other, ⟨own, at_, member⟩ => by
      rcases addDemand_reached_only demand index [] position other ⟨own, at_, member⟩ with
        same | ⟨_, none_, _⟩
      · exact .inl same
      · cases none_
  | index + 1, own :: older, 0, other, reached => .inr reached
  | index + 1, own :: older, position + 1, other, ⟨found, at_, member⟩ => by
      rcases addDemand_reached_only demand index older position other ⟨found, at_, member⟩ with
        same | ⟨later, at', member'⟩
      · exact .inl same
      · exact .inr ⟨later, at', member'⟩

/-- An application reaches no protocol as the entry: a protocol that is reached as the
entry after a definition was reached so before it. -/
theorem propagate_entry (own : List Demand) (applied : List (Nat × RoleMap))
    (older : List (List Demand)) (position : Nat) (roles : TranscriptRoles) :
    Reached (propagate own applied older) position (.entry roles) →
      Reached older position (.entry roles) :=
  foldl_keeps _
    (fun demands => Reached demands position (.entry roles) → Reached older position (.entry roles))
    (fun state demand before =>
      foldl_keeps _
        (fun demands =>
          Reached demands position (.entry roles) → Reached older position (.entry roles))
        (fun state application before reached => by
          rcases addDemand_reached_only _ _ state position _ reached with same | earlier
          · cases same
          · exact before earlier) applied state before)
    own older id

/-- Every way a protocol is reached as the entry names two roles of the protocol. -/
def EntriesBelow (old : List ProtocolHeader) (demands : List (List Demand)) : Prop :=
  ∀ index roles, Reached demands index (.entry roles) →
    ∃ header, old[index]? = some header ∧ Nat.blt roles.prover header.roles = true ∧
      Nat.blt roles.verifier header.roles = true

/-- The demands of the protocols before a definition name roles of the protocols that are
reached as the entry, when the demands with the definition's do. -/
theorem EntriesBelow.earlier {old : List ProtocolHeader} {header : ProtocolHeader}
    {demands : List (List Demand)} (below : EntriesBelow (header :: old) demands)
    (applied : List (Nat × RoleMap)) :
    EntriesBelow old (propagate (demands.headD []) applied demands.tail) := by
  intro index roles reached
  have before := propagate_entry _ _ _ index roles reached
  have shifted : Reached demands (index + 1) (.entry roles) := by
    obtain ⟨own, at_, member⟩ := before
    cases demands with
    | nil => cases at_
    | cons first others => exact ⟨own, at_, member⟩
  exact below (index + 1) roles shifted

/-- The images of the protocols of a program: what a step refuses while it makes them is a
condition of the construction item or a missing row. -/
theorem rewriteProtocols_external (external : rule.External) (legalRule : rule.Legal typeTable)
    (identities : Identities) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      (demands : List (List Demand)), EntriesBelow old demands →
      ∀ refusal, rewriteProtocols t rule identities protocols demands = .error refusal →
        refusal.internal = false
  | _, .nil, demands, _, refusal, refused => by
      simp only [rewriteProtocols] at refused
      cases refused
  | _, .snoc (protocols := earlier) (header := header) protocols definition wellFormed, demands,
      below, refusal, refused => by
      simp only [rewriteProtocols] at refused
      split at refused
      · rename_i new typed table origins counted marks rewrites
        have servedEarlier := (rewriteProtocols_images external identities protocols
          (propagate (demands.headD []) (applications definition.body []) demands.tail)).2 _
          rewrites
        split at refused
        · rename_i classified classifies
          obtain ⟨sound, _⟩ := classify_spec table (identities earlier.length) definition _
            classified classifies
          split at refused
          · cases refused
          · rename_i other definitionRefused
            cases refused
            refine rewriteDefinition_external external legalRule table (identities earlier.length)
              definition wellFormed _ classified false
              ⟨new, typed, table, [], (fun _ member => nomatch member), origins, counted⟩
              (fun _ _ => rfl)
              (fun pair member => ⟨(sound pair member).2,
                served_of_demands definition.body [] fun application applies inside =>
                  servedEarlier application.1 inside _
                    (propagate_reached _ _ _ (sound pair member).1 applies)⟩)
              (fun roles active member => ?_) _ definitionRefused
            have reached : Reached demands 0 (.entry roles) := by
              have own := (sound _ member).1
              cases demands with
              | nil => cases own
              | cons first others => exact ⟨first, rfl, own⟩
            obtain ⟨found, at_, inRange⟩ := below 0 roles reached
            cases at_
            exact inRange
        · rename_i other classifyRefused
          cases refused
          exact classify_external table _ definition _ _ classifyRefused
      · rename_i other earlierRefused
        cases refused
        exact rewriteProtocols_external external legalRule identities protocols _
          (below.earlier _) _ earlierRefused

/-- The ways the protocols of a program are reached before any application is followed
are the declared protocol as the entry. -/
theorem entryDemands_reached {roles : TranscriptRoles} {other : Demand} :
    ∀ (before index : Nat),
      Reached (List.replicate before [] ++ [[Demand.entry roles]]) index other →
      index = before ∧ other = .entry roles
  | 0, 0, ⟨own, at_, member⟩ => by
      cases at_
      exact ⟨rfl, List.mem_singleton.mp member⟩
  | 0, index + 1, ⟨own, at_, member⟩ => by cases at_
  | before + 1, 0, ⟨own, at_, member⟩ => by
      cases at_
      cases member
  | before + 1, index + 1, ⟨own, at_, member⟩ => by
      obtain ⟨same, entry⟩ := entryDemands_reached before index ⟨own, at_, member⟩
      exact ⟨congrArg (· + 1) same, entry⟩

/-- What a step refuses on a program of well-formed definitions is a condition of the
construction item or a missing row, when its rule never refuses internally and emits what
the check of a definition accepts: no refusal is internal. -/
theorem stepProtocols_external (external : rule.External) (legalRule : rule.Legal typeTable)
    (identities : Identities) (entry : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old) {refusal : StepRefusal}
    (refused : stepProtocols t rule identities entry roles protocols = .error refusal) :
    refusal.internal = false := by
  unfold stepProtocols at refused
  split at refused
  · rename_i declared
    split at refused
    · cases refused
    · rename_i inner innerRefused
      cases refused
      refine rewriteProtocols_external external legalRule identities protocols _ ?_ _ innerRefused
      intro index found reached
      obtain ⟨rfl, same⟩ := entryDemands_reached _ index reached
      cases same
      simp only [Bool.and_eq_true] at declared
      have declaredRoles := declared.2
      cases at_ : old[old.length - 1 - entry]? with
      | none =>
          rw [at_] at declaredRoles
          cases declaredRoles
      | some header =>
          rw [at_] at declaredRoles
          simp only [declaredRolesBelow, Bool.and_eq_true] at declaredRoles
          exact ⟨header, rfl, declaredRoles.1, declaredRoles.2⟩
  · cases refused
    rfl

/-- A step on a program of well-formed definitions that the construction item accepts and
whose declaration has the rows returns, when its rule never refuses internally and emits
what the check of a definition accepts. -/
theorem stepProtocols_returns (external : rule.External) (legalRule : rule.Legal typeTable)
    (identities : Identities) (entry : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (accepted : ConstructionAccepts (stepProtocols t rule identities entry roles protocols))
    (present : RowsPresent (stepProtocols t rule identities entry roles protocols)) :
    ∃ stepped, stepProtocols t rule identities entry roles protocols = .ok stepped := by
  rcases step_returns_or_internal accepted present with returned | ⟨refusal, refused, internal⟩
  · exact returned
  · rw [stepProtocols_external external legalRule identities entry roles protocols refused]
      at internal
    cases internal

end Program

/-! ## The two steps on a typed package

The tables of a typed package have types of the package (`Typed.rowsNamed`,
`Typed.functionsNamed`), so the rule of every suite and of every layout over them emits
what the check of a definition accepts, and neither step refuses internally. -/

section Package

/-- What the check on online roles beside the transcript roles refuses is a condition of
the construction item. -/
theorem thirdRoleRefusal_external {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols)
      (reaches : List (List Reach)) (refusal : StepRefusal),
      thirdRoleRefusal program reaches = some refusal → refusal.internal = false
  | _, .nil, _, _, refused => by
      simp only [thirdRoleRefusal] at refused
      cases refused
  | _, .snoc earlier definition _, reaches, refusal, refused => by
      simp only [thirdRoleRefusal] at refused
      split at refused
      · cases refused
        rfl
      · exact thirdRoleRefusal_external earlier _ refusal refused

/-- What the Fiat–Shamir step refuses on a typed package is a condition of the
construction item or a missing row. -/
theorem fiatShamir_external (typed : Typed) (declaration : Raw.Declaration)
    {refusal : StepRefusal} (refused : fiatShamir typed declaration = .error refusal) :
    refusal.internal = false := by
  unfold fiatShamir at refused
  split at refused
  · cases refused
    rfl
  · dsimp only at refused
    split at refused
    · rename_i third found
      cases refused
      exact thirdRoleRefusal_external _ _ _ found
    · exact stepProtocols_external (fiatShamirRule_external _)
        (fiatShamirRule_legal typed.rowsNamed typed.functionsNamed _) _ _ _ _ refused

/-- The Fiat–Shamir step on a typed package that the construction item accepts and whose
declaration has the rows returns. -/
theorem fiatShamir_returns (typed : Typed) (declaration : Raw.Declaration)
    (accepted : ConstructionAccepts (fiatShamir typed declaration))
    (present : RowsPresent (fiatShamir typed declaration)) :
    ∃ stepped, fiatShamir typed declaration = .ok stepped := by
  rcases step_returns_or_internal accepted present with returned | ⟨refusal, refused, internal⟩
  · exact returned
  · rw [fiatShamir_external typed declaration refused] at internal
    cases internal

/-- What the serialize step refuses on a program of well-formed definitions over rows of
types of the package is a condition of the construction item or a missing row. -/
theorem serializeProtocols_external {typeTable : TypeTable}
    {operations : List OperationSignature} {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} (rows : RowsNamed typeTable operations)
    (declaration : Raw.Declaration) (identities : Identities)
    (program : Protocols typeTable operations functions protocols) {refusal : StepRefusal}
    (refused : serializeProtocols declaration identities program = .error refusal) :
    refusal.internal = false := by
  unfold serializeProtocols at refused
  split at refused
  · cases refused
    rfl
  · exact stepProtocols_external (serializeRule_external _) (serializeRule_legal rows _) _ _ _ _
      refused

/-- The serialize step on a program of well-formed definitions over rows of types of the
package that the construction item accepts and whose declaration has the rows returns. -/
theorem serializeProtocols_returns {typeTable : TypeTable}
    {operations : List OperationSignature} {functions : List FunctionHeader}
    {protocols : List ProtocolHeader} (rows : RowsNamed typeTable operations)
    (declaration : Raw.Declaration) (identities : Identities)
    (program : Protocols typeTable operations functions protocols)
    (accepted : ConstructionAccepts (serializeProtocols declaration identities program))
    (present : RowsPresent (serializeProtocols declaration identities program)) :
    ∃ stepped, serializeProtocols declaration identities program = .ok stepped := by
  rcases step_returns_or_internal accepted present with returned | ⟨refusal, refused, internal⟩
  · exact returned
  · rw [serializeProtocols_external rows declaration identities program refused] at internal
    cases internal

/-- What Fiat–Shamir and then serialize refuse on a typed package is a condition of the
construction item or a missing row. -/
theorem construct_external (typed : Typed) (declaration : Raw.Declaration)
    {refusal : StepRefusal} (refused : construct typed declaration = .error refusal) :
    refusal.internal = false := by
  unfold construct at refused
  split at refused
  · exact serializeProtocols_external typed.rowsNamed declaration _ _ refused
  · rename_i first firstRefused
    cases refused
    exact fiatShamir_external typed declaration firstRefused

/-- Fiat–Shamir and then serialize on a typed package return, when the construction item
accepts and the declaration has the rows. -/
theorem construct_returns (typed : Typed) (declaration : Raw.Declaration)
    (accepted : ConstructionAccepts (construct typed declaration))
    (present : RowsPresent (construct typed declaration)) :
    ∃ stepped, construct typed declaration = .ok stepped := by
  rcases step_returns_or_internal accepted present with returned | ⟨refusal, refused, internal⟩
  · exact returned
  · rw [construct_external typed declaration refused] at internal
    cases internal

end Package

/-! ## The images of one more protocol, for a statement that follows the program

What a statement that is proved along the protocols of a program, in the order in which
`rewriteProtocols` recurses, needs of the step on one more protocol: the images of the
earlier protocols, the marks that the step records, which images the newest protocol has,
and how each way it is reached is classified. -/

/-- A way the newest protocol is reached is one of its own demands. -/
theorem Reached.newest {demands : List (List Demand)} {demand : Demand}
    (reached : Reached demands 0 demand) : demand ∈ demands.headD [] := by
  obtain ⟨own, at_, member⟩ := reached
  cases demands with
  | nil => cases at_
  | cons first others =>
      cases at_
      exact member

/-- A way an earlier protocol is reached is a way it is reached among the earlier ones. -/
theorem Reached.earlier {demands : List (List Demand)} {index : Nat} {demand : Demand}
    (reached : Reached demands (index + 1) demand) : Reached demands.tail index demand := by
  obtain ⟨own, at_, member⟩ := reached
  cases demands with
  | nil => cases at_
  | cons first others => exact ⟨own, at_, member⟩

/-- An application of a definition reaches its callee with the preimages of the two roles
of every way the definition is reached. -/
theorem propagate_reached_applied (own : List Demand) (applied : List (Nat × RoleMap))
    (older : List (List Demand)) {demand : Demand} (member : demand ∈ own) {index : Nat}
    {roleMap : RoleMap} (applies : (index, roleMap) ∈ applied) :
    Reached (propagate own applied older) index
      (.applied (preimageOf roleMap demand.prover) (preimageOf roleMap demand.verifier)) :=
  propagate_reached own applied older member applies

/-- The declared protocol is reached as the entry. -/
theorem entry_reached (roles : TranscriptRoles) :
    ∀ index : Nat, Reached (List.replicate index [] ++ [[.entry roles]]) index (.entry roles)
  | 0 => ⟨[.entry roles], rfl, List.mem_singleton.mpr rfl⟩
  | index + 1 => by
      obtain ⟨own, at_, member⟩ := entry_reached roles index
      exact ⟨own, at_, member⟩

section Along

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {t : Threads} {rule : Rule t operations functions}

/-- The step on one more protocol: the images of the earlier protocols are those for the
demands that the protocol propagates; the marks of the protocol are those of its body; the
earlier protocols have the images they had; and every way the protocol is reached is
classified by `touches`, with the image that threads for a pair of roles for which the
protocol changes. -/
theorem rewriteProtocols_newest_images (external : rule.External) (identities : Identities)
    {old : List ProtocolHeader} {header : ProtocolHeader}
    (earlier : Protocols typeTable operations functions old)
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none) (demands : List (List Demand))
    (rewritten : Rewritten t typeTable operations functions (header :: old))
    (rewrites : rewriteProtocols t rule identities (.snoc earlier definition wellFormed) demands =
      .ok rewritten) :
    ∃ (prior : Rewritten t typeTable operations functions old) (specialized : Bool),
      rewriteProtocols t rule identities earlier
          (propagate (demands.headD []) (applications definition.body []) demands.tail) =
        .ok prior ∧
      rewritten.marks =
        .cons (fun roles => regionMarks prior.table.threads prior.marks
          ⟨identities old.length, roles, specialized⟩ definition.body) prior.marks ∧
      (∀ index key, rewritten.table.has (index + 1) key = prior.table.has index key) ∧
      ∀ demand ∈ demands.headD [], ∃ active,
        touches t rule.derives prior.table (identities old.length) demand.prover demand.verifier
            definition.body = .ok active ∧
          ∀ prover verifier, demand = .applied (some prover) (some verifier) → active = true →
            rewritten.table.has 0 (some ⟨prover, verifier⟩) = true := by
  obtain ⟨_, returns⟩ := rewriteProtocols_images external identities earlier
    (propagate (demands.headD []) (applications definition.body []) demands.tail)
  unfold rewriteProtocols at rewrites
  dsimp only at rewrites
  split at rewrites
  · rename_i new typed table origins counted marks rewritesEarlier
    have servedEarlier := returns _ rewritesEarlier
    split at rewrites
    · rename_i classified classifies
      obtain ⟨sound, complete⟩ := classify_spec table (identities old.length) definition _
        classified classifies
      obtain ⟨_, imageReturns⟩ := rewriteDefinition_images external table
        (identities old.length) definition (definition.body_legal wellFormed)
        (Nat.ble 2 (classified.filter fun entry => entry.2 && entry.1.isApplied).length)
        classified false ⟨new, typed, table, [], (fun _ member => nomatch member), origins, counted⟩
        (fun _ _ => rfl)
        (fun pair member => ⟨(sound pair member).2,
          served_of_demands definition.body [] fun application applies below =>
            servedEarlier application.1 below _
              (propagate_reached _ _ _ (sound pair member).1 applies)⟩)
        (fun made => nomatch made)
      split at rewrites
      · rename_i images produced
        have same := Except.ok.inj rewrites
        subst same
        obtain ⟨sameTable, _, recorded⟩ := imageReturns images produced
        refine ⟨⟨new, typed, table, origins, counted, marks⟩, _, rewritesEarlier, rfl, ?_, ?_⟩
        · intro index key
          show (images.table.extend header images.list images.valid).has (index + 1) key =
            table.has index key
          exact (CalleeTable.has_extend_succ images.table header images.list images.valid index
            key).trans (sameTable index key)
        · intro demand member
          obtain ⟨active, classifiedMember⟩ := complete demand member
          refine ⟨active, (sound _ classifiedMember).2, ?_⟩
          intro prover verifier isApplied isActive
          subst isApplied isActive
          obtain ⟨level, recordedMember⟩ := recorded _ classifiedMember
          show (images.table.extend header images.list images.valid).has 0 _ = true
          rw [CalleeTable.has_extend_zero]
          exact CalleeTable.levelOf_isSome _ images.list level recordedMember
      · cases rewrites
    · cases rewrites
  · cases rewrites

end Along

end Zkc.Core
