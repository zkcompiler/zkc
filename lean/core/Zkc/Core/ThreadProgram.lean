module

public import Zkc.Core.ThreadImages
public import Zkc.Core.ThreadEntry

public section

/-! The structural theorem of a threading step, for a whole program.

`rewriteProtocols_plain`: for the images that a step makes of the protocols of a program,
every image with its definition's own header has the definition's meaning
(`PlainCallees`). The statement does not mention the meaning of a rule.

`rewriteProtocols_threads`: for the images that a step makes of the protocols of a
program, every image that threads is its definition interpreted by every handler that
follows the definition's marks, for every side with exactly one transcript role, and every
image with its definition's own header has the definition's meaning (`CalleesThread`, with
what fits a callee derived: `stepFits`).

Both are inductions over the protocols in program order, as `rewriteProtocols` recurses.
For one definition the images are made one after the other; what holds of the images made
so far (`ImagesHold`) is the statement for the earlier definitions and, for every image
that the callee table will record, the statement about that image (`CopyHasMeaning`,
`ImageThreads`). An image that threads is covered by `definition_threads` with a handler
that fits because it follows the marks (`region_fits`), a copy by `definition_plain`.

`stepProtocols_entry`: the image of the declared entry is the entry interpreted by the
handler of the step's marks, between what the rule's entry does before and after the body.
`stepProtocols_plain_entry`: an entry that the step copies has its meaning. Both descend to
the declared protocol: a protocol after it is not reached, has no image and leaves the
result as it is (`rewriteProtocols_unreached`), and the declared protocol is reached as
the entry only, so the step makes one image of it (`rewriteProtocols_declared`).

`stepProtocols_newest`: the result of a step has a newest protocol, which comes from the
declared entry, and for a rule that rewrites an entry whose body has no rewritten operation
(`Rule.idleEntry`) it is the image of the entry, not a copy.

**Scope.** The statements about images that thread are for a side that holds exactly one
of the two transcript roles (`OneTranscriptRole`): the prover and the verifier as separate
sides, each with or without other roles. They are not statements about a side that holds
both: an exchange between two roles of one side performs no effect, so no handler of
effects can absorb its value, and `Fits` holds of no handler there
(`Tests/Core/ThreadingWitnesses.lean`). Nothing is stated for a side that holds neither.

**What a user of the theorems supplies.** The equations `stepProtocols … = .ok …`, the
position of the declared protocol, and the per-rule facts `RuleSound` and `EntrySound`,
which are proved for both rules. Nothing about a handler: the handler is
`threadHandler` on `stepMarks`, it follows the marks of the entry by construction
(`threadHandler_follows`), the marks of a callee below the site of its application are
the callee's marks, a callee without an image that threads is passed
(`Protocols.table_passes`), and `Fits` and the statement for the callees are derived by the
induction over the program. The equations are equations of processes, so they hold through
every reply of every effect, not along one run.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-! ## Callees after one more protocol of the result -/

section Callees

variable {model : Model} {operations : List OperationSignature} {t : Threads}
  {old new : List ProtocolHeader} {table : CalleeTable t.header old new}
  {oldTable : ProtocolTable model old} {newTable : ProtocolTable model new}

/-- The copies of the callees have the callees' meanings after one more protocol of the
result. -/
theorem PlainCallees.weaken (callees : PlainCallees table oldTable newTable)
    (added : ProtocolHeader) (meaning : added.Meaning model) :
    PlainCallees (table.weaken added) oldTable (.cons meaning newTable) := by
  intro header callee image named
  rw [CalleeTable.find_weaken] at named
  cases earlier : table.find callee none with
  | none => rw [earlier] at named; cases named
  | some earlierImage =>
      rw [earlier] at named
      have same : earlierImage.there = image := Option.some.inj named
      subst same
      exact callees callee earlierImage earlier

/-- The images of the callees thread after one more protocol of the result. -/
theorem CalleesThread.weaken {fits : Values (CalleeFit model t) old}
    (callees : CalleesThread table oldTable newTable fits) (added : ProtocolHeader)
    (meaning : added.Meaning model) :
    CalleesThread (table.weaken added) oldTable (.cons meaning newTable) fits := by
  refine ⟨fun {header} callee inner image named => ?_, PlainCallees.weaken callees.plain added meaning⟩
  rw [CalleeTable.find_weaken] at named
  cases earlier : table.find callee (some inner) with
  | none => rw [earlier] at named; cases named
  | some earlierImage =>
      rw [earlier] at named
      have same : earlierImage.there = image := Option.some.inj named
      subst same
      exact callees.threaded callee inner earlierImage earlier

/-- A held value along the equation of a membership with itself is the value. -/
theorem heldAlong_self (side : Side) (type : Ty) (role : Nat)
    (held : Held (model.Value type) (side role)) (same : side role = side role) :
    Held.along same held = held := by
  have read := retype_along (model := model) (side := side) (rfl : role = role)
    (Environment.push (Value := SideValue model side) Environment.empty held)
    (Var.here (ty := (⟨type, role⟩ : Located)))
  exact read.symm

end Callees

/-! ## The handler of a step follows the marks it reads -/

section Handler

variable {model : Model} {operations : List OperationSignature} {t : Threads}

/-- A path below itself, without it. -/
theorem pathBelow_append : ∀ (path rest : List Nat), pathBelow path (path ++ rest) = some rest
  | [], _ => rfl
  | first :: path, rest => by
      show (if first = first then pathBelow path (path ++ rest) else none) = some rest
      rw [if_pos rfl]
      exact pathBelow_append path rest

/-- The handler that reads the marks of a definition below a path follows the marks. -/
theorem threadHandler_follows (sem : RuleMeaning model t operations)
    (marks : Site → Option (Mark operations)) (prover verifier : Bool) (path : List Nat) :
    Follows sem prover verifier (threadHandler sem (marksBelow path marks) prover verifier) path
      marks := by
  intro effect rest below state
  show threadAct sem (marksBelow path marks effect.site) prover verifier effect state = _
  have same : marksBelow path marks effect.site =
      marks ⟨rest, effect.site.definition, effect.site.number⟩ := by
    unfold marksBelow
    rw [below, pathBelow_append]
  rw [same]

end Handler

/-! ## What holds of the images of one definition -/

section Statements

variable {model : Model} {operations : List OperationSignature} {t : Threads}
  {header : ProtocolHeader}

/-- The statement about an image of a definition when only its copy is of interest: the
image with the definition's own header has the definition's meaning. -/
@[expose] def CopyHasMeaning (meaning : header.Meaning model) :
    (key : Option TranscriptRoles) → (t.header key header).Meaning model → Prop
  | none, image => image = meaning
  | some _, _ => True

/-- The statement about an image of a definition: the image with the definition's own
header has the definition's meaning, and the image for a pair of transcript roles is the
definition interpreted by every handler that follows the definition's marks for the pair,
for every side with exactly one of the two roles. -/
@[expose] def ImageThreads (sem : RuleMeaning model t operations) (meaning : header.Meaning model)
    (marks : TranscriptRoles → Site → Option (Mark operations)) :
    (key : Option TranscriptRoles) → (t.header key header).Meaning model → Prop
  | none, image => image = meaning
  | some roles, image =>
      ∀ (path : List Nat) (side : Side),
        OneTranscriptRole (side roles.prover) (side roles.verifier) →
        ∀ handler : ThreadHandler model t (side roles.prover) (side roles.verifier),
          Follows sem (side roles.prover) (side roles.verifier) handler path (marks roles) →
          ∀ (state : ThreadState model t (side roles.prover) (side roles.verifier))
            (arguments : Values (SideValue model side) header.inputs),
            image path side (.cons state.1 (.cons state.2 arguments)) =
              ((meaning path side arguments).interpretWith handler state).bind fun result =>
                .done (threadedValues result)

end Statements

section Program

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {t : Threads} {rule : Rule t operations functions}
  {sem : RuleMeaning model t operations} {functionTable : FunctionTable model functions}

/-- The copies that a step makes of the protocols of a program have their meanings. -/
theorem rewriteProtocols_plain (identities : Identities) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      (demands : List (List Demand))
      (rewritten : Rewritten t typeTable operations functions old),
      rewriteProtocols t rule identities protocols demands = .ok rewritten →
        PlainCallees rewritten.table (protocols.table model functionTable identities)
          (rewritten.protocols.table model functionTable (originIdentities rewritten.origins))
  | _, .nil, _, rewritten, rewrites => by
      intro callee
      exact callee.elimNil
  | _, .snoc (protocols := earlierHeaders) (header := header) earlier definition wellFormed,
      demands, rewritten, rewrites => by
      unfold rewriteProtocols at rewrites
      dsimp only at rewrites
      split at rewrites
      · rename_i new typed table origins counted marks rewritesEarlier
        have calleesEarlier : PlainCallees table (earlier.table model functionTable identities)
            (typed.table model functionTable (originIdentities origins)) :=
          rewriteProtocols_plain identities earlier _ _ rewritesEarlier
        split at rewrites
        · rename_i classified classifies
          split at rewrites
          · rename_i images rewritesDefinition
            have same := Except.ok.inj rewrites
            subst same
            have holds := rewriteDefinition_holds (model := model) (functionTable := functionTable)
              (Callees := fun table newTable =>
                PlainCallees table (earlier.table model functionTable identities) newTable)
              (Image := CopyHasMeaning
                (definition.meaning model functionTable (earlier.table model functionTable identities)
                  (identities earlierHeaders.length)))
              (fun table newTable added meaning callees =>
                PlainCallees.weaken callees added meaning)
              _ definition _ (fun _ _ _ _ _ => trivial)
              (fun images body callees copies =>
                definition_plain callees definition ⟨body⟩ copies _)
              _ _ _ _ rewritesDefinition ⟨calleesEarlier, fun _ _ member => nomatch member⟩
            intro callee image named
            cases callee with
            | here =>
                obtain ⟨level, member, index⟩ :=
                  CalleeTable.find_extend_here (F := t.header) images.table _ images.list
                    images.valid none image named
                exact holds.own none level member image index
            | there callee =>
                rw [CalleeTable.find_extend_there] at named
                exact holds.callees callee image named
          · cases rewrites
        · cases rewrites
      · cases rewrites

/-- The images of the protocols of a program thread. -/
theorem rewriteProtocols_threads (quiet : QuietTable functionTable)
    (sound : RuleSound rule sem functionTable) (identities : Identities)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
    (demands : List (List Demand)) (rewritten : Rewritten t typeTable operations functions old)
    (rewrites : rewriteProtocols t rule identities protocols demands = .ok rewritten) :
    CalleesThread rewritten.table (protocols.table model functionTable identities)
      (rewritten.protocols.table model functionTable (originIdentities rewritten.origins))
      (stepFits sem rewritten.marks) := by
  induction protocols generalizing demands with
  | nil => exact ⟨fun callee => callee.elimNil, fun callee => callee.elimNil⟩
  | snoc earlier definition wellFormed ih =>
      rename_i earlierHeaders header
      unfold rewriteProtocols at rewrites
      dsimp only at rewrites
      split at rewrites
      · rename_i new typed table origins counted marks rewritesEarlier
        have calleesEarlier : CalleesThread table (earlier.table model functionTable identities)
            (typed.table model functionTable (originIdentities origins)) (stepFits sem marks) :=
          ih _ _ rewritesEarlier
        split at rewrites
        · rename_i classified classifies
          split at rewrites
          · rename_i images rewritesDefinition
            have same := Except.ok.inj rewrites
            subst same
            have passes : TablePasses (earlier.table model functionTable identities) :=
              Protocols.table_passes quiet identities earlier
            have unique := ProtocolDefinition.regionSites_nodup wellFormed
            have holds := rewriteDefinition_holds (model := model) (functionTable := functionTable)
              (Callees := fun candidate newTable =>
                candidate.threads = table.threads ∧
                  CalleesThread candidate (earlier.table model functionTable identities) newTable
                    (stepFits sem marks))
              (Image := ImageThreads sem
                (definition.meaning model functionTable (earlier.table model functionTable identities)
                  (identities earlierHeaders.length))
                (fun roles => regionMarks table.threads marks
                  ⟨identities earlierHeaders.length, roles,
                    Nat.ble 2 (List.filter (fun entry => entry.2 && entry.1.isApplied)
                      classified).length⟩
                  definition.body))
              (fun candidate newTable added meaning callees =>
                ⟨callees.1, callees.2.weaken added meaning⟩)
              _ definition _
              (fun images roles body callees threads path side one handler follows state
                  arguments =>
                definition_threads quiet sound callees.2 definition ⟨_, roles, _⟩ ⟨body⟩ threads _
                  path side handler
                  (region_fits rule sem quiet passes images.table marks ⟨_, roles, _⟩ side one _ path
                    handler definition.body unique (by rw [callees.1]; exact follows))
                  state arguments)
              (fun images body callees copies =>
                definition_plain callees.2.plain definition ⟨body⟩ copies _)
              _ _ _ _ rewritesDefinition ⟨⟨rfl, calleesEarlier⟩, fun _ _ member => nomatch member⟩
            refine ⟨fun {other} callee inner image named path side prover verifier isProver
              isVerifier handler fit first second arguments => ?_, ?_⟩
            · cases callee with
              | here =>
                  obtain ⟨level, member, index⟩ :=
                    CalleeTable.find_extend_here (F := t.header) images.table _ images.list
                      images.valid (some inner) image named
                  subst isProver
                  subst isVerifier
                  have threads := holds.own (some inner) level member image index path side fit.1
                    handler fit.2 (first, second) arguments
                  simp only [heldAlong_self]
                  exact threads
              | there callee =>
                  rw [CalleeTable.find_extend_there] at named
                  exact holds.callees.2.threaded callee inner image named path side prover verifier
                    isProver isVerifier handler fit first second arguments
            · intro other callee image named
              cases callee with
              | here =>
                  obtain ⟨level, member, index⟩ :=
                    CalleeTable.find_extend_here (F := t.header) images.table _ images.list
                      images.valid none image named
                  exact holds.own none level member image index
              | there callee =>
                  rw [CalleeTable.find_extend_there] at named
                  exact holds.callees.2.plain callee image named
          · cases rewrites
        · cases rewrites
      · cases rewrites

/-- The result of a step is the images of the protocols for the demands of the entry. -/
theorem stepProtocols_rewritten (identities : Identities) (number : Nat) (roles : TranscriptRoles)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped) :
    ∃ rewritten, rewriteProtocols t rule identities protocols
        (entryDemands old.length number roles) = .ok rewritten ∧
      stepped = ⟨rewritten.new, rewritten.protocols, rewritten.origins, rewritten.counted⟩ := by
  unfold stepProtocols at steps
  split at steps
  · split at steps
    · rename_i rewritten rewrites
      exact ⟨rewritten, rewrites, (Except.ok.inj steps).symm⟩
    · cases steps
  · cases steps

/-- The marks of a step that has a result are the marks of the declared protocol. -/
theorem stepMarks_rewritten (identities : Identities) (number : Nat) (roles : TranscriptRoles)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
    (rewritten : Rewritten t typeTable operations functions old)
    (rewrites : rewriteProtocols t rule identities protocols
      (entryDemands old.length number roles) = .ok rewritten) :
    stepMarks t rule identities number roles protocols =
      rewritten.marks.at (old.length - 1 - number) roles := by
  unfold stepMarks
  rw [rewrites]

/-- A protocol that is not reached has no image: the protocols of the result are those of
the result for the protocols before it. -/
theorem rewriteProtocols_unreached (identities : Identities) {old : List ProtocolHeader}
    {header : ProtocolHeader} (earlier : Protocols typeTable operations functions old)
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none) (demands : List (List Demand))
    (rewritten : Rewritten t typeTable operations functions (header :: old))
    (rewrites : rewriteProtocols t rule identities (.snoc earlier definition wellFormed)
      ([] :: demands) = .ok rewritten) :
    ∃ prior : Rewritten t typeTable operations functions old,
      rewriteProtocols t rule identities earlier demands = .ok prior ∧
        ∃ table marks, rewritten =
          ⟨prior.new, prior.protocols, table, prior.origins, prior.counted,
            .cons marks prior.marks⟩ := by
  unfold rewriteProtocols at rewrites
  dsimp only at rewrites
  simp only [List.headD_cons, List.tail_cons, propagate_nil] at rewrites
  split at rewrites
  · rename_i new typed table origins counted marks rewritesEarlier
    simp only [classify, rewriteDefinition, List.filter_nil] at rewrites
    exact ⟨_, rewritesEarlier, _, _, (Except.ok.inj rewrites).symm⟩
  · cases rewrites

/-- The declared protocol is reached as the entry only, so a step makes one image of it:
the image that the rule's entry makes of its threaded body, or its copy. In both cases the
protocols before the image are those of the result for the protocols before the declared
one, and the marks of the declared protocol are those of its body as a definition without
several images that thread. -/
theorem rewriteProtocols_declared (identities : Identities) (roles : TranscriptRoles)
    {old : List ProtocolHeader} {header : ProtocolHeader}
    (earlier : Protocols typeTable operations functions old)
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none)
    (rewritten : Rewritten t typeTable operations functions (header :: old))
    (rewrites : rewriteProtocols t rule identities (.snoc earlier definition wellFormed)
      [[.entry roles]] = .ok rewritten) :
    ∃ prior : Rewritten t typeTable operations functions old,
      rewriteProtocols t rule identities earlier
          (propagate [.entry roles] (applications definition.body []) []) = .ok prior ∧
        ((∃ body wellFormedImage table,
            rule.entry ⟨identities old.length, roles, false⟩ header
                (fun rename first second =>
                  threadRegion t rule prior.table ⟨identities old.length, roles, false⟩
                    definition.body rename first second) = .ok body ∧
              rewritten =
                ⟨(rule.entryPorts roles header).header header :: prior.new,
                  .snoc (header := (rule.entryPorts roles header).header header) prior.protocols
                    ⟨body⟩ wellFormedImage,
                  table, ⟨identities old.length, some roles, true⟩ :: prior.origins,
                  congrArg (· + 1) prior.counted,
                  .cons (fun inner => regionMarks prior.table.threads prior.marks
                    ⟨identities old.length, inner, false⟩ definition.body) prior.marks⟩) ∨
          (∃ body wellFormedImage table,
            plainRegion t prior.table definition.body (Renaming.identity header.inputs) =
                .ok body ∧
              rewritten =
                ⟨header :: prior.new, .snoc prior.protocols ⟨body⟩ wellFormedImage, table,
                  ⟨identities old.length, none, false⟩ :: prior.origins,
                  congrArg (· + 1) prior.counted,
                  .cons (fun inner => regionMarks prior.table.threads prior.marks
                    ⟨identities old.length, inner, false⟩ definition.body) prior.marks⟩)) := by
  unfold rewriteProtocols at rewrites
  dsimp only at rewrites
  simp only [List.headD_cons, List.tail_cons] at rewrites
  split at rewrites
  · rename_i new typed table origins counted marks rewritesEarlier
    refine ⟨_, rewritesEarlier, ?_⟩
    unfold classify at rewrites
    split at rewrites
    · rename_i classified classifies
      have reached : ∃ active, classified = [(Demand.entry roles, active)] := by
        cases touched : touches t rule.derives table (identities old.length)
            (Demand.entry roles).prover (Demand.entry roles).verifier definition.body with
        | ok active =>
            rw [touched] at classifies
            exact ⟨active, (Except.ok.inj classifies).symm⟩
        | error refusal =>
            rw [touched] at classifies
            cases classifies
      obtain ⟨active, rfl⟩ := reached
      have unspecialized : Nat.ble 2 (List.filter
          (fun entry : Demand × Bool => entry.2 && entry.1.isApplied)
          [(Demand.entry roles, active)]).length = false := by
        cases active <;> rfl
      rw [unspecialized] at rewrites
      simp only [rewriteDefinition] at rewrites
      split at rewrites
      · rename_i images made
        have same := Except.ok.inj rewrites
        subst same
        split at made
        · cases made
        · split at made
          · split at made
            · rename_i body enters
              split at made
              · rename_i entered adds
                have same := Except.ok.inj made
                subst same
                unfold Images.addEntry at adds
                split at adds
                · rename_i wellFormedImage
                  have same := Except.ok.inj adds
                  subst same
                  exact .inl ⟨body, wellFormedImage, _, enters, rfl⟩
                · cases adds
              · cases made
            · cases made
          · split at made
            · rename_i copied copies
              have same := Except.ok.inj made
              subst same
              unfold plainImage at copies
              simp only [Bool.false_eq_true, ↓reduceIte] at copies
              split at copies
              · rename_i body copiesBody
                unfold Images.add at copies
                split at copies
                · rename_i wellFormedImage
                  have same := Except.ok.inj copies
                  subst same
                  exact .inr ⟨body, wellFormedImage, _, copiesBody, rfl⟩
                · cases copies
              · cases copies
            · cases made
      · cases rewrites
    · cases rewrites
  · cases rewrites

/-- The image of an entry that the step rewrites, for the demands of the protocol that a
reference declares. -/
theorem rewriteProtocols_entry (quiet : QuietTable functionTable)
    (sound : RuleSound rule sem functionTable) {entryMeaning : EntryMeaning model t rule}
    (entrySound : EntrySound rule entryMeaning functionTable) (identities : Identities)
    (roles : TranscriptRoles) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      {header : ProtocolHeader} (declared : Var old header)
      (rewritten : Rewritten t typeTable operations functions old),
      rewriteProtocols t rule identities protocols
          (List.replicate declared.index [] ++ [[.entry roles]]) = .ok rewritten →
      ∀ (origin : Origin) (earlier : List Origin), rewritten.origins = origin :: earlier →
        origin.entry = true →
        ∃ image : Var rewritten.new ((rule.entryPorts roles header).header header),
          image.index = 0 ∧
          ∀ (path : List Nat) (side : Side),
            OneTranscriptRole (side roles.prover) (side roles.verifier) →
            ∀ arguments : Values (SideValue model side) (rule.entryPorts roles header).inputs,
              (rewritten.protocols.table model functionTable
                  (originIdentities rewritten.origins)).get image path side arguments =
                (entryMeaning.start side roles header arguments).bind fun state =>
                  (((protocols.table model functionTable identities).get declared path side
                      (entryMeaning.arguments side roles header arguments)).interpretWith
                    (threadHandler sem (marksBelow path (rewritten.marks.at declared.index roles))
                      (side roles.prover) (side roles.verifier)) state).bind fun result =>
                    entryMeaning.finish side roles header result
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
            refine ⟨Var.here, rfl, fun path side one arguments => ?_⟩
            have callees := rewriteProtocols_threads (model := model) quiet sound identities earlier
              _ prior rewritesEarlier
            have passes : TablePasses (earlier.table model functionTable identities) :=
              Protocols.table_passes quiet identities earlier
            have fit := region_fits rule sem quiet passes prior.table prior.marks
              ⟨identities earlierHeaders.length, roles, false⟩ side one
              (identities earlierHeaders.length) path _ definition.body
              (ProtocolDefinition.regionSites_nodup wellFormed)
              (threadHandler_follows sem
                (regionMarks prior.table.threads prior.marks
                  ⟨identities earlierHeaders.length, roles, false⟩ definition.body)
                (side roles.prover) (side roles.verifier) path)
            have meanings := Protocols.table_image (model := model) (functionTable := functionTable)
              prior.protocols _ wellFormedImage ⟨identities earlierHeaders.length, some roles, true⟩
              prior.origins prior.counted
            refine (congrArg (fun table : ProtocolTable model _ =>
              table.get Var.here path side arguments) meanings).trans ?_
            refine (entrySound.runs
              (prior.protocols.table model functionTable (originIdentities prior.origins))
              (ownSites (identities earlierHeaders.length) path) side
              ⟨identities earlierHeaders.length, roles, false⟩ _ _ body enters
              (fun arguments state =>
                ((definition.meaning model functionTable
                    (earlier.table model functionTable identities)
                    (identities earlierHeaders.length) path side arguments).interpretWith
                  (threadHandler sem
                    (marksBelow path (regionMarks prior.table.threads prior.marks
                      ⟨identities earlierHeaders.length, roles, false⟩ definition.body))
                    (side roles.prover) (side roles.verifier)) state).bind fun result =>
                  .done (threadedValues result))
              (fun rename first second threaded threads arguments env agrees =>
                threadRegion_meaning quiet sound callees definition.body rename first second
                  threaded threads fit (Environment.ofValues arguments) env agrees)
              arguments).trans ?_
            refine congrArg _ (funext fun state => ?_)
            exact (PIR.Process.bind_assoc _ _ _).trans rfl
          · obtain ⟨body, wellFormedImage, table, copies, rfl⟩ := copied
            intro origin earlierOrigins newest isEntry
            cases newest
            cases isEntry
      | there declared =>
          obtain ⟨prior, rewritesEarlier, table, marks, rfl⟩ :=
            rewriteProtocols_unreached identities earlier definition wellFormed _ rewritten rewrites
          exact rewriteProtocols_entry quiet sound entrySound identities roles earlier declared
            prior rewritesEarlier

/-- The image of an entry that the step copies, for the demands of the protocol that a
reference declares. -/
theorem rewriteProtocols_plain_entry (identities : Identities) (roles : TranscriptRoles) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      {header : ProtocolHeader} (declared : Var old header)
      (rewritten : Rewritten t typeTable operations functions old),
      rewriteProtocols t rule identities protocols
          (List.replicate declared.index [] ++ [[.entry roles]]) = .ok rewritten →
      ∀ (origin : Origin) (earlier : List Origin), rewritten.origins = origin :: earlier →
        origin.entry = false →
        ∃ image : Var rewritten.new header, image.index = 0 ∧
          (rewritten.protocols.table model functionTable
              (originIdentities rewritten.origins)).get image =
            (protocols.table model functionTable identities).get declared
  | _, .nil, _, declared, _, _ => declared.elimNil
  | _, .snoc (protocols := earlierHeaders) earlier definition wellFormed, _, declared, rewritten,
      rewrites => by
      cases declared with
      | here =>
          obtain ⟨prior, rewritesEarlier, entered | copied⟩ :=
            rewriteProtocols_declared identities roles earlier definition wellFormed rewritten
              rewrites
          · obtain ⟨body, wellFormedImage, table, enters, rfl⟩ := entered
            intro origin earlierOrigins newest isCopy
            cases newest
            cases isCopy
          · obtain ⟨body, wellFormedImage, table, copies, rfl⟩ := copied
            intro origin earlierOrigins newest isCopy
            refine ⟨Var.here, rfl, ?_⟩
            have callees : PlainCallees prior.table (earlier.table model functionTable identities)
                (prior.protocols.table model functionTable (originIdentities prior.origins)) :=
              rewriteProtocols_plain identities earlier _ prior rewritesEarlier
            have meanings := Protocols.table_image (model := model) (functionTable := functionTable)
              prior.protocols _ wellFormedImage ⟨identities earlierHeaders.length, none, false⟩
              prior.origins prior.counted
            refine (congrArg (fun table : ProtocolTable model _ => table.get Var.here)
              meanings).trans ?_
            exact definition_plain callees definition ⟨body⟩ copies _
      | there declared =>
          obtain ⟨prior, rewritesEarlier, table, marks, rfl⟩ :=
            rewriteProtocols_unreached identities earlier definition wellFormed _ rewritten rewrites
          exact rewriteProtocols_plain_entry identities roles earlier declared prior
            rewritesEarlier

/-- The image of an entry that the step rewrites: the newest protocol of the result is
the entry interpreted by the handler of the step's marks, between what the rule's entry
does before and after it. -/
theorem stepProtocols_entry (quiet : QuietTable functionTable)
    (sound : RuleSound rule sem functionTable) {entryMeaning : EntryMeaning model t rule}
    (entrySound : EntrySound rule entryMeaning functionTable) (identities : Identities)
    (number : Nat) (roles : TranscriptRoles) {old : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) (origin : Origin) (earlier : List Origin)
    (newest : stepped.origins = origin :: earlier) (rewritten : origin.entry = true) :
    ∃ image : Var stepped.headers ((rule.entryPorts roles header).header header),
      image.index = 0 ∧
      ∀ (path : List Nat) (side : Side),
        OneTranscriptRole (side roles.prover) (side roles.verifier) →
        ∀ arguments : Values (SideValue model side) (rule.entryPorts roles header).inputs,
          (stepped.protocols.table model functionTable stepped.identities).get image path side
              arguments =
            (entryMeaning.start side roles header arguments).bind fun state =>
              (((protocols.table model functionTable identities).get declared path side
                  (entryMeaning.arguments side roles header arguments)).interpretWith
                (threadHandler sem
                  (marksBelow path (stepMarks t rule identities number roles protocols))
                  (side roles.prover) (side roles.verifier)) state).bind fun result =>
                entryMeaning.finish side roles header result := by
  obtain ⟨result, rewrites, rfl⟩ :=
    stepProtocols_rewritten identities number roles protocols stepped steps
  rw [stepMarks_rewritten identities number roles protocols result rewrites, ← isEntry]
  refine rewriteProtocols_entry quiet sound entrySound identities roles protocols declared result
    ?_ origin earlier newest rewritten
  rw [isEntry]
  exact rewrites

/-- The image of an entry that the step copies: the newest protocol of the result has the
entry's meaning. -/
theorem stepProtocols_plain_entry (identities : Identities) (number : Nat) (roles : TranscriptRoles)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) (origin : Origin) (earlier : List Origin)
    (newest : stepped.origins = origin :: earlier) (plain : origin.entry = false) :
    ∃ image : Var stepped.headers header, image.index = 0 ∧
      (stepped.protocols.table model functionTable stepped.identities).get image =
        (protocols.table model functionTable identities).get declared := by
  obtain ⟨result, rewrites, rfl⟩ :=
    stepProtocols_rewritten identities number roles protocols stepped steps
  refine rewriteProtocols_plain_entry (rule := rule) identities roles protocols declared result ?_
    origin earlier newest plain
  rw [isEntry]
  exact rewrites

/-- Where the image of the declared protocol comes from: the result of a step has a newest
protocol, and for a rule that rewrites an entry whose body has no rewritten operation
(`Rule.idleEntry`) it is the image of the entry. -/
theorem rewriteProtocols_declared_origin (identities : Identities) (roles : TranscriptRoles)
    {old : List ProtocolHeader} {header : ProtocolHeader}
    (earlier : Protocols typeTable operations functions old)
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none)
    (rewritten : Rewritten t typeTable operations functions (header :: old))
    (rewrites : rewriteProtocols t rule identities (.snoc earlier definition wellFormed)
      [[.entry roles]] = .ok rewritten) :
    ∃ origin rest, rewritten.origins = origin :: rest ∧
      (rule.idleEntry = true → origin.entry = true) := by
  unfold rewriteProtocols at rewrites
  dsimp only at rewrites
  simp only [List.headD_cons, List.tail_cons] at rewrites
  split at rewrites
  · rename_i new typed table origins counted marks rewritesEarlier
    unfold classify at rewrites
    split at rewrites
    · rename_i classified classifies
      have reached : ∃ active, classified = [(Demand.entry roles, active)] := by
        cases touched : touches t rule.derives table (identities old.length)
            (Demand.entry roles).prover (Demand.entry roles).verifier definition.body with
        | ok active =>
            rw [touched] at classifies
            exact ⟨active, (Except.ok.inj classifies).symm⟩
        | error refusal =>
            rw [touched] at classifies
            cases classifies
      obtain ⟨active, rfl⟩ := reached
      have unspecialized : Nat.ble 2 (List.filter
          (fun entry : Demand × Bool => entry.2 && entry.1.isApplied)
          [(Demand.entry roles, active)]).length = false := by
        cases active <;> rfl
      rw [unspecialized] at rewrites
      simp only [rewriteDefinition] at rewrites
      split at rewrites
      · rename_i images made
        have same := Except.ok.inj rewrites
        subst same
        split at made
        · cases made
        · split at made
          · split at made
            · split at made
              · rename_i entered adds
                have same := Except.ok.inj made
                subst same
                unfold Images.addEntry at adds
                split at adds
                · have same := Except.ok.inj adds
                  subst same
                  exact ⟨_, _, rfl, fun _ => rfl⟩
                · cases adds
              · cases made
            · cases made
          · rename_i copies
            split at made
            · rename_i copied copiesImage
              have same := Except.ok.inj made
              subst same
              unfold plainImage at copiesImage
              simp only [Bool.false_eq_true, ↓reduceIte] at copiesImage
              split at copiesImage
              · unfold Images.add at copiesImage
                split at copiesImage
                · have same := Except.ok.inj copiesImage
                  subst same
                  exact ⟨_, _, rfl, fun idle => absurd (by rw [idle, Bool.or_true]) copies⟩
                · cases copiesImage
              · cases copiesImage
            · cases made
      · cases rewrites
    · cases rewrites
  · cases rewrites

/-- The result of the images of a program for the demands of a declared protocol has a
newest protocol; for a rule that rewrites an entry whose body has no rewritten operation it
is the image of the entry. -/
theorem rewriteProtocols_newest (identities : Identities) (roles : TranscriptRoles) :
    ∀ {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
      {header : ProtocolHeader} (declared : Var old header)
      (rewritten : Rewritten t typeTable operations functions old),
      rewriteProtocols t rule identities protocols
          (List.replicate declared.index [] ++ [[.entry roles]]) = .ok rewritten →
      ∃ origin rest, rewritten.origins = origin :: rest ∧
        (rule.idleEntry = true → origin.entry = true)
  | _, .nil, _, declared, _, _ => declared.elimNil
  | _, .snoc earlier definition wellFormed, _, declared, rewritten, rewrites => by
      cases declared with
      | here =>
          exact rewriteProtocols_declared_origin identities roles earlier definition wellFormed
            rewritten rewrites
      | there declared =>
          obtain ⟨prior, rewritesEarlier, table, marks, rfl⟩ :=
            rewriteProtocols_unreached identities earlier definition wellFormed _ rewritten rewrites
          exact rewriteProtocols_newest identities roles earlier declared prior rewritesEarlier

/-- The result of a step has a newest protocol, which comes from the declared entry; for a
rule that rewrites an entry whose body has no rewritten operation it is the image of the
entry. -/
theorem stepProtocols_newest (identities : Identities) (number : Nat) (roles : TranscriptRoles)
    {old : List ProtocolHeader} (protocols : Protocols typeTable operations functions old)
    (stepped : Stepped typeTable operations functions)
    (steps : stepProtocols t rule identities number roles protocols = .ok stepped)
    {header : ProtocolHeader} (declared : Var old header)
    (isEntry : declared.index = old.length - 1 - number) :
    ∃ origin earlier, stepped.origins = origin :: earlier ∧
      (rule.idleEntry = true → origin.entry = true) := by
  obtain ⟨result, rewrites, rfl⟩ :=
    stepProtocols_rewritten identities number roles protocols stepped steps
  refine rewriteProtocols_newest (rule := rule) identities roles protocols declared result ?_
  rw [isEntry]
  exact rewrites

end Program

end Zkc.Core
