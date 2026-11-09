module

public import Zkc.IR.Source.Structured.CommonCoordinateExecution

@[expose] public section

/-! A source-prefix derivation. Edges preserve the actual optional operands. Advancing
past work requires a successful path of that exact process; entering a repeat requires
its actual bounded count, preceding iterations, and reached administrative boundary.
The certificate fixes each body; the path supplies execution facts, never an equality
of the selected coordinates. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

/-- Dynamic source boundaries are distinct from static binder origins. Matching this
list requires the same reached outer counters, without asserting equal loop counts. -/
inductive Boundary where
  | application (definition : Nat) (row : List Nat)
  | iteration (definition : Nat) (row : List Nat) (index : Nat)
  deriving DecidableEq, Repr

structure Frame (snapshot : Snapshot) (definitions : List CheckedProtocol) (pair : Pair)
    (model : DomainModel) where
  scope : Scope
  inputs : List Ty
  outputs : List Ty
  context : ProtocolContext
  reached : List Boundary
  cursor : Cursor
  origins : Origins scope
  body : Region protocolDialect inputs outputs
  symbols : Symbols scope inputs
  plan : Plan snapshot definitions pair context.roles cursor origins body symbols
  observations : Observations model scope
  values : Values (Component (ProtocolValue model.toCarriers)) inputs
  protocols : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model)

variable {snapshot : Snapshot} {definitions : List CheckedProtocol} {pair : Pair}
  {model : DomainModel}

def frame (context : ProtocolContext) {scope : Scope} {inputs outputs : List Ty}
    {cursor : Cursor} {origins : Origins scope} {body : Region protocolDialect inputs outputs}
    {symbols : Symbols scope inputs}
    (plan : Plan snapshot definitions pair context.roles cursor origins body symbols)
    (observations : Observations model scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) inputs)
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (reached : List Boundary := []) :
    Frame snapshot definitions pair model :=
  ⟨scope, inputs, outputs, context, reached, cursor, origins, body, symbols, plan,
    observations, values, protocols⟩

def Frame.Matched (current : Frame snapshot definitions pair model) : Prop :=
  Matches current.symbols current.observations current.values

variable (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model))

/-- Exactly the path of the existing finite repeat, with the same state masks,
callback body, captures, and administrative entry/leave actions. -/
def iterations (context : ProtocolContext) (spec : RepeatSpec) (site : String)
    (body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
    (protocols : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (captures : Values (Component (ProtocolValue model.toCarriers)) spec.captures)
    (state : Values (Component (ProtocolValue model.toCarriers)) spec.state) (count : Nat) :=
  let algebra := OracleProtocol.algebra model self ordinary helpers
  let mask := maskValues self (context.mapScopes spec.stateScopes)
  Finite.execute (.elements (List.range count)) (fun state index ↦
    (algebra.iteration context site index
      (body.denote (algebra.meaning protocols context self)
        (Values.cons (some (algebra.index index)) ((mask state).append captures)).get)).bind
          (fun result ↦ .done (mask result))) (mask state)

set_option genSizeOf false in
inductive Advance : Frame snapshot definitions pair model →
    Frame snapshot definitions pair model → Prop where
  | step {reachedPrefix context scope inputs outputs cursor origins op args bodies next symbols
      leaf noRegions checked tail observations values protocols results}
      (returned : Returned
        ((OracleProtocol.algebra model self ordinary helpers).operation protocols context self op
          (args.eval values.get)
          (bodies.denote ((OracleProtocol.algebra model self ordinary helpers).meaning
            protocols context self))) results) :
      Advance
        (frame context (Plan.step (scope := scope) (inputs := inputs) (outputs := outputs)
          (cursor := cursor) (origins := origins) (op := op) (args := args) (bodies := bodies)
          (next := next) (env := symbols) leaf noRegions checked tail) observations values protocols reachedPrefix)
        (frame context tail observations (results.append values) protocols reachedPrefix)
  | bindEnter {reachedPrefix context scope inputs middle outputs cursor origins body next symbols
      inside tail observations values protocols} :
      Advance
        (frame context (Plan.bind (scope := scope) (inputs := inputs) (middle := middle)
          (outputs := outputs) (cursor := cursor) (origins := origins) (body := body)
          (next := next) (env := symbols) inside tail) observations values protocols reachedPrefix)
        (frame context inside observations values protocols reachedPrefix)
  | bindNext {reachedPrefix context scope inputs middle outputs cursor origins body next symbols
      inside tail observations values protocols results}
      (returned : Returned (body.denote
        ((OracleProtocol.algebra model self ordinary helpers).meaning protocols context self)
          values.get) results) :
      Advance
        (frame context (Plan.bind (scope := scope) (inputs := inputs) (middle := middle)
          (outputs := outputs) (cursor := cursor) (origins := origins) (body := body)
          (next := next) (env := symbols) inside tail) observations values protocols reachedPrefix)
        (frame context tail observations (results.append values) protocols reachedPrefix)
  | applyEnter {reachedPrefix : List Boundary} {context : ProtocolContext} {scope : Scope} {inputs outputs : List Ty}
      {cursor : Cursor} {origins : Origins scope} {selected : List Nat} {site : String}
      {definition : CheckedProtocol} {args : Operands inputs definition.signature.inputs}
      {next : Region protocolDialect (definition.signature.outputs ++ inputs) outputs}
      {symbols : Symbols scope inputs} {member : definition ∈ definitions}
      {inside : Plan snapshot definitions pair (context.roles ∘ roleSubstitution selected)
        (cursor.enter (snapshot.definitions.findIdx (·.name == definition.name))) origins
        definition.body (maskSymbols pair (context.roles ∘ roleSubstitution selected)
          definition.inputScopes (args.eval symbols.get))}
      {tail : Plan snapshot definitions pair context.roles cursor origins next
        ((unknown scope definition.signature.outputs).append symbols)}
      {observations : Observations model scope}
      {values : Values (Component (ProtocolValue model.toCarriers)) inputs}
      {protocols captured : ProtocolTable (ProtocolValue model.toCarriers)
        (OracleProtocol.Interface model)}
      (lookup : protocols.find? (fun entry ↦ entry.signature.name == definition.signature.name) =
        some ⟨definition.signature,
          (OracleProtocol.algebra model self ordinary helpers).denote definition captured⟩)
      (active : (context.enter site selected).contains definition.signature self = true)
      (entered : Returned (I := OracleProtocol.Interface model)
        (.call (.application definition.signature site) .done) ()) :
      Advance
        (frame context (Plan.apply (scope := scope) (inputs := inputs) (outputs := outputs)
          (cursor := cursor) (origins := origins) (selected := selected) (site := site)
          (args := args) (next := next) (env := symbols) (signature := definition.signature)
          definition member rfl inside tail)
          observations values protocols reachedPrefix)
        (frame (context.enter site selected) inside observations
          (maskValues self ((context.enter site selected).mapScopes definition.inputScopes)
            (args.eval values.get)) captured
          (reachedPrefix ++ [.application cursor.definition cursor.row]))
  | applyNext {reachedPrefix : List Boundary} {context : ProtocolContext} {scope : Scope} {inputs outputs : List Ty}
      {cursor : Cursor} {origins : Origins scope} {selected : List Nat} {site : String}
      {definition : CheckedProtocol} {args : Operands inputs definition.signature.inputs}
      {next : Region protocolDialect (definition.signature.outputs ++ inputs) outputs}
      {symbols : Symbols scope inputs} {member : definition ∈ definitions}
      {inside : Plan snapshot definitions pair (context.roles ∘ roleSubstitution selected)
        (cursor.enter (snapshot.definitions.findIdx (·.name == definition.name))) origins
        definition.body (maskSymbols pair (context.roles ∘ roleSubstitution selected)
          definition.inputScopes (args.eval symbols.get))}
      {tail : Plan snapshot definitions pair context.roles cursor origins next
        ((unknown scope definition.signature.outputs).append symbols)}
      {observations : Observations model scope}
      {values : Values (Component (ProtocolValue model.toCarriers)) inputs}
      {protocols : ProtocolTable (ProtocolValue model.toCarriers)
        (OracleProtocol.Interface model)}
      {results : Values (Component (ProtocolValue model.toCarriers)) definition.signature.outputs}
      (returned : Returned
        ((OracleProtocol.algebra model self ordinary helpers).operation protocols context self
          (.protocolApply definition.signature selected site) (args.eval values.get) .nil) results) :
      Advance
        (frame context (Plan.apply (scope := scope) (inputs := inputs) (outputs := outputs)
          (cursor := cursor) (origins := origins) (selected := selected) (site := site)
          (args := args) (next := next) (env := symbols) (signature := definition.signature)
          definition member rfl inside tail)
          observations values protocols reachedPrefix)
        (frame context tail observations (results.append values) protocols reachedPrefix)
  | repeatEnter {reachedPrefix context scope inputs outputs cursor origins spec site args body next symbols
      inside tail observations values protocols count index state}
      (active : (spec.roles.map context.roles).contains self = true)
      (actualCount : ((args.eval values.get).get .here).bind ProtocolValue.toConcrete = some count)
      (bounded : count ≤ spec.maximum) (reached : index < count)
      (earlier : Returned (iterations self ordinary helpers context spec site body protocols
        ((laterEntries (args.eval values.get)).split spec.state).2
        ((laterEntries (args.eval values.get)).split spec.state).1 index) state)
      (entered : Returned (I := OracleProtocol.Interface model)
        (.call (.iteration site index) .done) ()) :
      Advance
        (frame context (Plan.repeat (scope := scope) (inputs := inputs) (outputs := outputs)
          (cursor := cursor) (origins := origins) (spec := spec) (site := site) (args := args)
          (body := body) (next := next) (env := symbols) inside tail) observations values protocols reachedPrefix)
        (frame context inside (.cons (some index) observations)
          (.cons (some (ProtocolValue.ofConcrete .index index))
            ((maskValues self (context.mapScopes spec.stateScopes) state).append
              ((laterEntries (args.eval values.get)).split spec.state).2)) protocols
          (reachedPrefix ++ [.iteration cursor.definition cursor.row index]))
  | repeatNext {reachedPrefix context scope inputs outputs cursor origins spec site args body next symbols
      inside tail observations values protocols results}
      (returned : Returned
        ((OracleProtocol.algebra model self ordinary helpers).operation protocols context self
          (.repeat spec site) (args.eval values.get)
          (.cons (fun values ↦ body.denote
            ((OracleProtocol.algebra model self ordinary helpers).meaning protocols context self)
              values.get) .nil)) results) :
      Advance
        (frame context (Plan.repeat (scope := scope) (inputs := inputs) (outputs := outputs)
          (cursor := cursor) (origins := origins) (spec := spec) (site := site) (args := args)
          (body := body) (next := next) (env := symbols) inside tail) observations values protocols reachedPrefix)
        (frame context tail observations (results.append values) protocols reachedPrefix)

theorem Advance.preserves {before after : Frame snapshot definitions pair model}
    (member : pair.includes self) (edge : Advance self ordinary helpers before after)
    (matched : before.Matched) : after.Matched := by
  cases edge with
  | step returned =>
    exact matches_append _ _ _ _ _
      (transfer_sound pair self member ordinary helpers _ _ _ _ _ _
        (matches_operands _ _ _ matched _) _ _ returned) matched
  | bindEnter => exact matched
  | bindNext returned => exact matches_append _ _ _ _ _ (matches_unknown _ _) matched
  | applyEnter lookup active entered =>
    dsimp only [Frame.Matched, frame] at matched ⊢
    intro ty position term known
    exact matches_mask pair self member _ _ _ _ _ (matches_operands _ _ _ matched _)
      position term known
  | applyNext returned => exact matches_append _ _ _ _ _ (matches_unknown _ _) matched
  | repeatEnter active actualCount bounded reached earlier entered =>
    exact matches_callback pair _ _ _ _ _ (matches_operands _ _ _ matched _) _ _
  | repeatNext returned => exact matches_append _ _ _ _ _ (matches_unknown _ _) matched

inductive Prefix : Frame snapshot definitions pair model →
    Frame snapshot definitions pair model → Prop where
  | refl (current) : Prefix current current
  | next {before current after}
      (path : Prefix before current) (edge : Advance self ordinary helpers current after) :
      Prefix before after

theorem Prefix.readback {before after : Frame snapshot definitions pair model}
    (member : pair.includes self) (path : Prefix self ordinary helpers before after)
    (initial : before.Matched) : after.Matched := by
  induction path with
  | refl => exact initial
  | next path edge ih => exact edge.preserves self ordinary helpers member ih

/-- At a checked source selection, the term is fixed by the actual operand lookup in the
certificate. The theorem includes absence, and asserts a value only when it is present. -/
theorem selection_readback (selection : Selection) (observations : Observations model selection.scope)
    (values : Values (Component (ProtocolValue model.toCarriers)) selection.inputs)
    (matched : Matches selection.environment observations values) :
    ((selection.operands.eval values.get).get (.there .here)).bind ProtocolValue.toConcrete =
      observe model selection.term observations := by
  rw [Operands.get_eval]
  exact matched _ _ selection.read

/-- Common-input and same-reached-counter observations are separate from availability.
No prover honesty, table equality, pairing, completion or equal loop counts is inferred. -/
theorem selection_agreement (selection : Selection)
    (left right : Observations model selection.scope)
    (leftValues rightValues : Values (Component (ProtocolValue model.toCarriers)) selection.inputs)
    (leftRead : Matches selection.environment left leftValues)
    (rightRead : Matches selection.environment right rightValues)
    (observations : AgreeOn model (demanded selection.term) left right) :
    ((selection.operands.eval leftValues.get).get (.there .here)).bind ProtocolValue.toConcrete =
      ((selection.operands.eval rightValues.get).get (.there .here)).bind ProtocolValue.toConcrete := by
  rw [selection_readback selection left leftValues leftRead,
    selection_readback selection right rightValues rightRead]
  exact observe_agreement model selection.term left right observations

end Zkc.Source.Structured.CommonCoordinate
