module

public import Zkc.Core.ThreadTogetherRegion
public import Zkc.Core.ThreadCompose

public section

/-! The refinement of a threading step for a side that holds both transcript roles, for a
whole program.

`definition_refines`: the image of a definition for a pair of transcript roles refines the
definition from every coupled state, for a side that holds both roles.

`rewriteProtocols_refines`: for the images that a step makes of the protocols of a program,
every image that threads refines its definition from every coupled state, for every side
that holds both of its transcript roles, and every image with its definition's own header
has the definition's meaning (`CalleesRefine`). It is the induction over the protocols in
program order of `rewriteProtocols_threads`, with the statement about one image
(`ImageRefines`) kept along the images of a definition by `rewriteDefinition_holds`.

`EntryCouples`: the obligation on the entry of a rule. For inputs that the rule admits, the
start returns a coupled state without an effect, and the region that the rule made of a
threaded body is that body, run once in an environment that holds the inputs and that state,
followed by the finish; the finish of a coupled state returns without an effect.
`EntrySound.runs` is not used here: it asks for the meaning of the threaded body as a
function of the inputs and the state, which is an equation, and a refinement gives none.

`stepProtocols_entry_together`: when the step rewrote the entry, the newest protocol of the
result refines the declared entry, for every side that holds both transcript roles and every
admitted input, and returns what the finish makes of the entry's outputs and a coupled
state. `stepProtocols_entry_copied` covers a step that copied the entry: the newest protocol
has the entry's meaning.

**What a user of the theorems supplies.** The equation `stepProtocols … = .ok …`, the
position of the declared protocol, and the per-rule facts `RuleSound`, `RuleCouples` and
`EntryCouples`. Nothing is asked of the functions of the program.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

section Definition

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {t : Threads} {rule : Rule t operations functions}
  {sem : RuleMeaning model t operations} {functionTable : FunctionTable model functions}
  {oldTable : ProtocolTable model old} {newTable : ProtocolTable model new}
  {table : CalleeTable t.header old new}
  {coupled : model.Value t.prover → model.Value t.verifier → Prop}

/-- The image of a definition that threads refines the definition from every coupled
state, for a side that holds both transcript roles. -/
theorem definition_refines (sound : RuleSound rule sem functionTable)
    (couples : RuleCouples rule sem coupled)
    (callees : CalleesRefine coupled table oldTable newTable) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions old header) (place : Place)
    (image : ProtocolDefinition operations functions new (t.header (some place.roles) header))
    (threads : threadRegion t rule table place definition.body
        (afterTwo (t.first place.roles) (t.second place.roles)
          (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).1
        (afterTwo (t.first place.roles) (t.second place.roles)
          (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).2.1
        (afterTwo (t.first place.roles) (t.second place.roles)
          (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).2.2 = .ok image.body)
    (identity : Nat) (path : List Nat) (side : Side)
    (isProver : side place.roles.prover = true) (isVerifier : side place.roles.verifier = true)
    (state : ThreadState model t (side place.roles.prover) (side place.roles.verifier))
    (arguments : Values (SideValue model side) header.inputs)
    (holds : CoupledState coupled isProver isVerifier state) :
    Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := place.roles)))
      (definition.meaning model functionTable oldTable identity path side arguments)
      (image.meaning model functionTable newTable identity path side
        (.cons state.1 (.cons state.2 arguments))) := by
  have start := afterTwo_agrees (Value := SideValue model side)
    (rename := Mapping.start (Δ := ([] : List Located)) 0 rfl)
    (old := Environment.empty) (new := Environment.empty) (fun reference => reference.elimNil)
    (t.first place.roles) (t.second place.roles) state.1 state.2 arguments
  exact threadRegion_refines (label := ownSites identity path) sound couples callees
    definition.body _ _ _ image.body threads _ _ start.1 (holds.of_eq start.2.1 start.2.2)

end Definition

section Statements

variable {model : Model} {t : Threads} {header : ProtocolHeader}

/-- The statement about an image of a definition: the image with the definition's own
header has the definition's meaning, and the image for a pair of transcript roles refines
the definition from every coupled state, for every side that holds both roles. -/
@[expose] def ImageRefines (coupled : model.Value t.prover → model.Value t.verifier → Prop)
    (meaning : header.Meaning model) :
    (key : Option TranscriptRoles) → (t.header key header).Meaning model → Prop
  | none, image => image = meaning
  | some roles, image =>
      ∀ (path : List Nat) (side : Side) (isProver : side roles.prover = true)
        (isVerifier : side roles.verifier = true)
        (state : ThreadState model t (side roles.prover) (side roles.verifier))
        (arguments : Values (SideValue model side) header.inputs),
        CoupledState coupled isProver isVerifier state →
        Refines (CoupledImage coupled isProver isVerifier (threadedValues (roles := roles)))
          (meaning path side arguments)
          (image path side (.cons state.1 (.cons state.2 arguments)))

end Statements

section Entry

variable {operations : List OperationSignature} {functions : List FunctionHeader}

/-- The entry of a rule starts the two threaded values coupled, for a side that holds both
transcript roles and inputs that the rule admits. -/
structure EntryCouples {model : Model} {t : Threads} (rule : Rule t operations functions)
    (entry : EntryMeaning model t rule) (functionTable : FunctionTable model functions)
    (coupled : model.Value t.prover → model.Value t.verifier → Prop)
    (admits : (side : Side) → (roles : TranscriptRoles) → (header : ProtocolHeader) →
      Values (SideValue model side) (rule.entryPorts roles header).inputs → Prop) : Prop where
  /-- For admitted inputs the start returns a coupled state without an effect, and the
  region that the rule made of a threaded body is one such body, run in an environment that
  holds the entry's inputs and that state, followed by the finish. -/
  runs : ∀ {protocols : List ProtocolHeader} {deployed : Bool}
    (table : ProtocolTable model protocols) (label : Nat → Site) (side : Side) (place : Place)
    (header : ProtocolHeader)
    (body : {Δ : List Located} → Renaming (bindAll [] header.inputs) Δ →
      Var Δ (t.first place.roles) → Var Δ (t.second place.roles) →
        Except StepRefusal (Region (ProtocolDialect operations functions protocols deployed) Δ
          (t.states place.roles ++ header.outputs)))
    (region : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] (rule.entryPorts place.roles header).inputs)
      (rule.entryPorts place.roles header).outputs),
    rule.entry place header body = .ok region →
    ∀ (isProver : side place.roles.prover = true) (isVerifier : side place.roles.verifier = true)
      (arguments : Values (SideValue model side) (rule.entryPorts place.roles header).inputs),
      admits side place.roles header arguments →
      ∃ (Δ : List Located) (rename : Renaming (bindAll [] header.inputs) Δ)
        (first : Var Δ (t.first place.roles)) (second : Var Δ (t.second place.roles))
        (threaded : Region (ProtocolDialect operations functions protocols deployed) Δ
          (t.states place.roles ++ header.outputs))
        (env : Environment (SideValue model side) Δ),
        body rename first second = .ok threaded ∧
        rename.Agrees (Environment.ofValues (entry.arguments side place.roles header arguments))
          env ∧
        entry.start side place.roles header arguments = .done (env first, env second) ∧
        CoupledState coupled isProver isVerifier (env first, env second) ∧
        region.denote (labelledMeaning model label functionTable table side)
            (Environment.ofValues arguments) =
          (threaded.denote (labelledMeaning model label functionTable table side) env).bind
            fun result => entry.finish side place.roles header (threadedParts result)
  /-- The finish of a coupled state returns without an effect. -/
  finishes : ∀ (side : Side) (roles : TranscriptRoles) (header : ProtocolHeader)
    (isProver : side roles.prover = true) (isVerifier : side roles.verifier = true)
    (outputs : Values (SideValue model side) header.outputs)
    (final : ThreadState model t (side roles.prover) (side roles.verifier)),
    CoupledState coupled isProver isVerifier final →
    ∃ result, entry.finish side roles header (outputs, final) = .done result

end Entry

section Program

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {t : Threads} {rule : Rule t operations functions}
  {sem : RuleMeaning model t operations} {functionTable : FunctionTable model functions}
  {coupled : model.Value t.prover → model.Value t.verifier → Prop}

/-- The images of the protocols of a program refine, for the sides that hold both
transcript roles. -/
theorem rewriteProtocols_refines (sound : RuleSound rule sem functionTable)
    (couples : RuleCouples rule sem coupled) (identities : Identities)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
    (demands : List (List Demand)) (rewritten : Rewritten t typeTable operations functions old)
    (rewrites : rewriteProtocols t rule identities protocols demands = .ok rewritten) :
    CalleesRefine coupled rewritten.table (protocols.table model functionTable identities)
      (rewritten.protocols.table model functionTable (originIdentities rewritten.origins)) := by
  induction protocols generalizing demands with
  | nil => exact ⟨fun callee => callee.elimNil, fun callee => callee.elimNil⟩
  | snoc earlier definition wellFormed ih =>
      rename_i earlierHeaders header
      unfold rewriteProtocols at rewrites
      dsimp only at rewrites
      split at rewrites
      · rename_i new typed table origins counted marks rewritesEarlier
        have calleesEarlier : CalleesRefine coupled table
            (earlier.table model functionTable identities)
            (typed.table model functionTable (originIdentities origins)) :=
          ih _ _ rewritesEarlier
        split at rewrites
        · rename_i classified classifies
          split at rewrites
          · rename_i images rewritesDefinition
            have same := Except.ok.inj rewrites
            subst same
            have holds := rewriteDefinition_holds (model := model) (functionTable := functionTable)
              (Callees := fun candidate newTable =>
                CalleesRefine coupled candidate (earlier.table model functionTable identities)
                  newTable)
              (Image := ImageRefines coupled
                (definition.meaning model functionTable (earlier.table model functionTable identities)
                  (identities earlierHeaders.length)))
              (fun candidate newTable added meaning callees => callees.weaken added meaning)
              _ definition _
              (fun images roles body callees threads path side isProver isVerifier state arguments
                  coupledState =>
                definition_refines sound couples callees definition ⟨_, roles, _⟩ ⟨body⟩ threads _
                  path side isProver isVerifier state arguments coupledState)
              (fun images body callees copies =>
                definition_plain callees.plain definition ⟨body⟩ copies _)
              _ _ _ _ rewritesDefinition ⟨calleesEarlier, fun _ _ member => nomatch member⟩
            refine ⟨fun {other} callee inner image named path side isProver isVerifier state
              arguments coupledState => ?_, ?_⟩
            · cases callee with
              | here =>
                  obtain ⟨level, member, index⟩ :=
                    CalleeTable.find_extend_here (F := t.header) images.table _ images.list
                      images.valid (some inner) image named
                  exact holds.own (some inner) level member image index path side isProver
                    isVerifier state arguments coupledState
              | there callee =>
                  rw [CalleeTable.find_extend_there] at named
                  exact holds.callees.threaded callee inner image named path side isProver
                    isVerifier state arguments coupledState
            · intro other callee image named
              cases callee with
              | here =>
                  obtain ⟨level, member, index⟩ :=
                    CalleeTable.find_extend_here (F := t.header) images.table _ images.list
                      images.valid none image named
                  exact holds.own none level member image index
              | there callee =>
                  rw [CalleeTable.find_extend_there] at named
                  exact holds.callees.plain callee image named
          · cases rewrites
        · cases rewrites
      · cases rewrites

variable {entryMeaning : EntryMeaning model t rule}
  {admits : (side : Side) → (roles : TranscriptRoles) → (header : ProtocolHeader) →
    Values (SideValue model side) (rule.entryPorts roles header).inputs → Prop}

/-- The image of an entry that the step rewrites, for the demands of the protocol that a
reference declares: it refines the entry for every side that holds both transcript roles and
every admitted input. -/
theorem rewriteProtocols_entry_together (sound : RuleSound rule sem functionTable)
    (couples : RuleCouples rule sem coupled)
    (entryCouples : EntryCouples rule entryMeaning functionTable coupled admits)
    (identities : Identities) (roles : TranscriptRoles) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      {header : ProtocolHeader} (declared : Var old header)
      (rewritten : Rewritten t typeTable operations functions old),
      rewriteProtocols t rule identities protocols
          (List.replicate declared.index [] ++ [[.entry roles]]) = .ok rewritten →
      ∀ (origin : Origin) (earlier : List Origin), rewritten.origins = origin :: earlier →
        origin.entry = true →
        ∃ image : Var rewritten.new ((rule.entryPorts roles header).header header),
          image.index = 0 ∧
          ∀ (path : List Nat) (side : Side) (isProver : side roles.prover = true)
            (isVerifier : side roles.verifier = true)
            (arguments : Values (SideValue model side) (rule.entryPorts roles header).inputs),
            admits side roles header arguments →
            Refines
              (fun outputs result => ∃ final, CoupledState coupled isProver isVerifier final ∧
                entryMeaning.finish side roles header (outputs, final) = .done result)
              ((protocols.table model functionTable identities).get declared path side
                (entryMeaning.arguments side roles header arguments))
              ((rewritten.protocols.table model functionTable
                (originIdentities rewritten.origins)).get image path side arguments)
  | _, .nil, _, declared, _, _ => declared.elimNil
  | _, .snoc (protocols := earlierHeaders) earlier definition wellFormed, _, declared, rewritten,
      rewrites => by
      cases declared with
      | here =>
          obtain ⟨prior, rewritesEarlier, entered | copied⟩ :=
            rewriteProtocols_declared identities roles earlier definition wellFormed rewritten
              rewrites
          · obtain ⟨body, wellFormedImage, table, enters, rfl⟩ := entered
            intro origin earlierOrigins newest isEntry
            refine ⟨Var.here, rfl, fun path side isProver isVerifier arguments admitted => ?_⟩
            have callees := rewriteProtocols_refines (model := model) sound couples identities
              earlier _ prior rewritesEarlier
            have meanings := Protocols.table_image (model := model) (functionTable := functionTable)
              prior.protocols _ wellFormedImage ⟨identities earlierHeaders.length, some roles, true⟩
              prior.origins prior.counted
            obtain ⟨Δ, rename, first, second, threaded, env, threads, agrees, starts, coupledStart,
                runs⟩ :=
              entryCouples.runs
                (prior.protocols.table model functionTable (originIdentities prior.origins))
                (ownSites (identities earlierHeaders.length) path) side
                ⟨identities earlierHeaders.length, roles, false⟩ _ _ body enters isProver isVerifier
                arguments admitted
            have refines := threadRegion_refines (label := ownSites (identities earlierHeaders.length) path)
              sound couples callees definition.body rename first second threaded threads
              (Environment.ofValues (entryMeaning.arguments side roles _ arguments)) env agrees
              coupledStart
            refine Refines.of_eq rfl ?_
              (Refines.andThen
                (newNext := fun result => entryMeaning.finish side roles _ (threadedParts result))
                refines ?_)
            · refine (congrArg (fun table : ProtocolTable model _ =>
                table.get Var.here path side arguments) meanings).trans ?_
              exact runs
            · rintro outputs made ⟨final, coupledFinal, rfl⟩
              obtain ⟨result, finishes⟩ := entryCouples.finishes side roles _ isProver isVerifier
                outputs final coupledFinal
              exact ⟨result, finishes, final, coupledFinal, finishes⟩
          · obtain ⟨body, wellFormedImage, table, copies, rfl⟩ := copied
            intro origin earlierOrigins newest isEntry
            cases newest
            cases isEntry
      | there declared =>
          obtain ⟨prior, rewritesEarlier, table, marks, rfl⟩ :=
            rewriteProtocols_unreached identities earlier definition wellFormed _ rewritten rewrites
          exact rewriteProtocols_entry_together sound couples entryCouples identities roles earlier
            declared prior rewritesEarlier

/-- The image of an entry that the step rewrote, for a side that holds both transcript
roles: the newest protocol of the result refines the declared entry on every admitted input,
and returns what the finish makes of the entry's outputs and a coupled state. -/
theorem stepProtocols_entry_together (sound : RuleSound rule sem functionTable)
    (couples : RuleCouples rule sem coupled)
    (entryCouples : EntryCouples rule entryMeaning functionTable coupled admits)
    (identities : Identities) (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number)
    (rewrote : stepped.rewroteEntry = true) :
    ∃ image : Var stepped.headers (rule.entryHeader roles header),
      image.index = 0 ∧
      ∀ (path : List Nat) (side : Side) (isProver : side roles.prover = true)
        (isVerifier : side roles.verifier = true)
        (arguments : Values (SideValue model side) (rule.entryPorts roles header).inputs),
        admits side roles header arguments →
        Refines
          (fun outputs result => ∃ final, CoupledState coupled isProver isVerifier final ∧
            entryMeaning.finish side roles header (outputs, final) = .done result)
          ((protocols.table model functionTable identities).get declared path side
            (entryMeaning.arguments side roles header arguments))
          ((stepped.protocols.table model functionTable stepped.identities).get image path side
            arguments) := by
  obtain ⟨origin, earlier, newest, rewritten⟩ := Stepped.rewroteEntry_newest rewrote
  obtain ⟨result, rewrites, rfl⟩ :=
    stepProtocols_rewritten identities number roles protocols stepped steps
  refine rewriteProtocols_entry_together sound couples entryCouples identities roles protocols
    declared result ?_ origin earlier newest rewritten
  rw [isEntry]
  exact rewrites

end Program

end Zkc.Core
