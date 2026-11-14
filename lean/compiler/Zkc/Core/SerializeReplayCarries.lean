module

public import Zkc.Core.LegalStep
public import Zkc.Core.ThreadRules
public import Zkc.Core.LayoutLaws

public section

/-! The layout carries every message of a program that the serialize step accepted.

The serialize rule refuses an exchange from the prover to the verifier whose type the layout
does not carry: the flag, the value and the reader that taking returns must have values, and
the layout must have a row that puts and a row that takes a value of the type
(`Layout.Carries`). So that the layout carries the messages of a program is not a premise of
a statement about a program on which the step returned: it follows from the equation of the
step.

- `RegionCarries`: the layout carries the type of every exchange from the prover to the
  verifier of a region, nested regions included.
- `threadRegion_carries`: a region of which the serialize step made a threaded image has it.
  An exchange that the step rewrote was accepted by the rule
  (`serializeRule_exchange_carries`); a nested region that the step copied has no exchange
  from the prover to the verifier (`untouched_carries`).
- `rewriteDefinition_carries`: when the step made the images of a definition, the body of
  the definition has it for the roles of every way it is reached as the entry, and of every
  way it is reached by an application for which it changes. The entry of the serialize rule
  threads its body (`serializeRule_entry_threads`), and the rule rewrites every entry.
- `rewriteProtocols_newest_carries`: for the newest protocol of a program on which the step
  returned, and every way it is reached with both transcript roles among its own, the body
  has it for these roles: a definition that does not change for them has no exchange from
  the prover to the verifier. This is the form that a statement along the protocols of the
  program takes.

Nothing is assumed.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-- The types of the two threaded values of the serialize step. -/
abbrev Layout.threads {operations : List OperationSignature} (layout : Layout operations) :
    Threads :=
  ⟨layout.writer, layout.reader⟩

section Carries

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {old new : List ProtocolHeader} {deployed : Bool}

/-- The layout carries the type of the operation's message, when the operation is an
exchange from the prover to the verifier. -/
@[expose] def OperationCarries (layout : Layout operations) (roles : TranscriptRoles) :
    ProtocolOp operations functions old deployed → Prop
  | .exchange sender receiver _ type =>
      sender = roles.prover → receiver = roles.verifier → layout.Carries type
  | .at .. | .sample .. | .draw .. | .repeat .. | .choose .. | .apply .. => True

mutual
  /-- The layout carries the type of every exchange from the prover to the verifier of the
  region, nested regions included. -/
  @[expose] def RegionCarries (layout : Layout operations) (roles : TranscriptRoles)
      {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out → Prop
    | .ret _ => True
    | .stop _ => True
    | .bind body rest => RegionCarries layout roles body ∧ RegionCarries layout roles rest
    | .letOp op _ bodies rest =>
        OperationCarries layout roles op ∧ RegionsCarry layout roles bodies ∧
          RegionCarries layout roles rest

  /-- The same for each of several closed regions. -/
  @[expose] def RegionsCarry (layout : Layout operations) (roles : TranscriptRoles)
      {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures → Prop
    | .nil => True
    | .cons body tail => RegionCarries layout roles body ∧ RegionsCarry layout roles tail
end

/-- An exchange that the serialize rule accepted is of a type that the layout carries. -/
theorem serializeRule_exchange_carries (layout : Layout operations)
    {protocols : List ProtocolHeader} (place : Place) (site : Nat) (type : Ty) {Δ : List Located}
    (value : Var Δ ⟨type, place.roles.prover⟩) (first : Var Δ (layout.threads.first place.roles))
    (second : Var Δ (layout.threads.second place.roles))
    (emitted : Emitted (ProtocolDialect operations functions protocols deployed) Δ
      [⟨type, place.roles.verifier⟩, layout.threads.first place.roles,
        layout.threads.second place.roles])
    (emits : (serializeRule (functions := functions) layout).exchange place site type value first
      second = .ok emitted) :
    layout.Carries type := by
  simp only [serializeRule] at emits
  split at emits
  · rename_i populated
    split at emits
    · rename_i put take hasPut hasTake
      exact ⟨populated, ⟨put, hasPut⟩, take, hasTake⟩
    · cases emits
  · cases emits

/-- The entry of the serialize rule threads its body: when the rule made the entry, the
threaded body was made. -/
theorem serializeRule_entry_threads (layout : Layout operations) {protocols : List ProtocolHeader}
    (place : Place) (header : ProtocolHeader)
    (body : {Δ : List Located} → Renaming (bindAll [] header.inputs) Δ →
      Var Δ (layout.threads.first place.roles) → Var Δ (layout.threads.second place.roles) →
        Except StepRefusal (Region (ProtocolDialect operations functions protocols deployed) Δ
          (layout.threads.states place.roles ++ header.outputs)))
    (region : Region (ProtocolDialect operations functions protocols deployed)
      (bindAll [] ((serializeRule (functions := functions) layout).entryPorts place.roles
        header).inputs)
      ((serializeRule (functions := functions) layout).entryPorts place.roles header).outputs)
    (made : (serializeRule (functions := functions) layout).entry place header body = .ok region) :
    ∃ (Δ : List Located) (rename : Renaming (bindAll [] header.inputs) Δ)
      (first : Var Δ (layout.threads.first place.roles))
      (second : Var Δ (layout.threads.second place.roles))
      (threaded : Region (ProtocolDialect operations functions protocols deployed) Δ
        (layout.threads.states place.roles ++ header.outputs)),
      body rename first second = .ok threaded := by
  simp only [serializeRule] at made
  split at made
  · rename_i threaded threads
    exact ⟨_, _, _, _, threaded, threads⟩
  · cases made

/-- An operation that is not rewritten is not an exchange from the prover to the verifier. -/
theorem untouched_operation_carries (layout : Layout operations) {t : Threads}
    {table : CalleeTable t.header old new} (derives : Bool) (definition : Nat)
    (roles : TranscriptRoles) :
    ∀ (op : ProtocolOp operations functions old deployed),
      touchesOp t derives table definition (some roles.prover) (some roles.verifier) op =
        .ok false →
      OperationCarries layout roles op
  | .exchange sender receiver site type, untouched => by
      intro isSender isReceiver
      subst isSender isReceiver
      simp only [touchesOp, isRole, Nat.beq_refl, Bool.and_self, ↓reduceIte] at untouched
      cases untouched
  | .at .., _ => trivial
  | .sample .., _ => trivial
  | .draw .., _ => trivial
  | .repeat .., _ => trivial
  | .choose .., _ => trivial
  | .apply .., _ => trivial

mutual
  /-- A region without a rewritten operation has no exchange from the prover to the
  verifier. -/
  theorem untouched_carries (layout : Layout operations) {t : Threads}
      {table : CalleeTable t.header old new} (derives : Bool) (definition : Nat)
      (roles : TranscriptRoles) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        touches t derives table definition (some roles.prover) (some roles.verifier) region =
          .ok false →
        RegionCarries layout roles region
    | .ret _, _ => trivial
    | .stop _, _ => trivial
    | .bind body rest, untouched => by
        unfold touches at untouched
        obtain ⟨untouchedBody, untouchedRest⟩ := bothTouch_false untouched
        exact ⟨untouched_carries layout derives definition roles body untouchedBody,
          untouched_carries layout derives definition roles rest untouchedRest⟩
    | .letOp op arguments bodies rest, untouched => by
        unfold touches at untouched
        obtain ⟨untouchedOp, later⟩ := bothTouch_false untouched
        obtain ⟨untouchedBodies, untouchedRest⟩ := bothTouch_false later
        exact ⟨untouched_operation_carries layout derives definition roles op untouchedOp,
          untouched_regions_carry layout derives definition roles bodies untouchedBodies,
          untouched_carries layout derives definition roles rest untouchedRest⟩

  /-- The same for closed regions. -/
  theorem untouched_regions_carry (layout : Layout operations) {t : Threads}
      {table : CalleeTable t.header old new} (derives : Bool) (definition : Nat)
      (roles : TranscriptRoles) {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        touchesRegions t derives table definition (some roles.prover) (some roles.verifier)
          regions = .ok false →
        RegionsCarry layout roles regions
    | .nil, _ => trivial
    | .cons body tail, untouched => by
        unfold touchesRegions at untouched
        obtain ⟨untouchedBody, untouchedTail⟩ := bothTouch_false untouched
        exact ⟨untouched_carries layout derives definition roles body untouchedBody,
          untouched_regions_carry layout derives definition roles tail untouchedTail⟩
end

mutual
  /-- A region of which the serialize step made a threaded image: the layout carries the
  type of every exchange from the prover to the verifier, nested regions included. -/
  theorem threadRegion_carries (layout : Layout operations)
      {table : CalleeTable layout.threads.header old new} (place : Place) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        {Δ : List Located} (rename : Renaming Γ Δ)
        (first : Var Δ (layout.threads.first place.roles))
        (second : Var Δ (layout.threads.second place.roles))
        (image : Region (ProtocolDialect operations functions new deployed) Δ
          (layout.threads.states place.roles ++ out)),
        threadRegion layout.threads (serializeRule layout) table place region rename first
          second = .ok image →
        RegionCarries layout place.roles region
    | .ret values, _, _, _, _, _, _ => trivial
    | .stop reason, _, _, _, _, _, _ => trivial
    | .bind (mid := mid) body rest, _, rename, first, second, image, threads => by
        unfold threadRegion at threads
        dsimp only at threads
        split at threads
        · rename_i bodyImage restImage threadsBody threadsRest
          exact ⟨threadRegion_carries layout place body _ _ _ _ threadsBody,
            threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
        · cases threads
        · cases threads
    | .letOp (.at role op bodies) arguments nested rest, _, rename, first, second, image,
        threads => by
        cases nested
        unfold threadRegion at threads
        split at threads
        · rename_i restImage threadsRest
          exact ⟨trivial, trivial, threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
        · cases threads
    | .letOp (.sample owner site law populated) arguments nested rest, _, rename, first, second,
        image, threads => by
        cases nested
        unfold threadRegion at threads
        split at threads
        · rename_i restImage threadsRest
          exact ⟨trivial, trivial, threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
        · cases threads
    | .letOp (.exchange sender receiver site type) arguments nested rest, _, rename, first,
        second, image, threads => by
        cases nested
        unfold threadRegion at threads
        split at threads
        · rename_i emitted rewritten
          split at threads
          · rename_i restImage threadsRest
            refine ⟨fun isSender isReceiver => ?_, trivial,
              threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
            subst isSender isReceiver
            exact serializeRule_exchange_carries layout place site type _ _ _ emitted
              (rewrittenExchange_ok rewritten)
          · cases threads
        · cases threads
        · rename_i unchanged
          split at threads
          · rename_i restImage threadsRest
            refine ⟨fun isSender isReceiver => ?_, trivial,
              threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
            subst isSender isReceiver
            exact absurd unchanged rewrittenExchange_some
          · cases threads
    | .letOp (.draw owner receivers site law populated) arguments nested rest, _, rename, first,
        second, image, threads => by
        cases nested
        have later : ∀ {Δ : List Located} (rename : Renaming _ Δ)
            (first : Var Δ (layout.threads.first place.roles))
            (second : Var Δ (layout.threads.second place.roles))
            (restImage : Region (ProtocolDialect operations functions new deployed) Δ
              (layout.threads.states place.roles ++ out)),
            threadRegion layout.threads (serializeRule layout) table place rest rename first
              second = .ok restImage →
            RegionCarries layout place.roles
              (Region.letOp (dialect := ProtocolDialect operations functions old deployed)
                (.draw owner receivers site law populated) arguments .nil rest) :=
          fun rename first second restImage threadsRest =>
            ⟨trivial, trivial,
              threadRegion_carries layout place rest rename first second restImage threadsRest⟩
        cases receivers with
        | nil =>
            unfold threadRegion at threads
            split at threads
            · exact later _ _ _ _ (by assumption)
            · cases threads
        | cons receiver others =>
            cases others with
            | cons another more =>
                unfold threadRegion at threads
                split at threads
                · exact later _ _ _ _ (by assumption)
                · cases threads
            | nil =>
                unfold threadRegion at threads
                split at threads
                · split at threads
                  · exact later _ _ _ _ (by assumption)
                  · cases threads
                · cases threads
                · split at threads
                  · exact later _ _ _ _ (by assumption)
                  · cases threads
    | .letOp (.repeat participants count carried collected captures covered) arguments
        (.cons body .nil) rest, _, rename, first, second, image, threads => by
        unfold threadRegion at threads
        dsimp only at threads
        split at threads
        · split at threads
          rename_i inner same
          obtain ⟨rfl⟩ : body = inner := by injection same
          split at threads
          · rename_i bodyImage restImage threadsBody threadsRest
            exact ⟨trivial, ⟨threadRegion_carries layout place body _ _ _ _ threadsBody, trivial⟩,
              threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
          · cases threads
          · cases threads
        · rename_i untouched
          split at threads
          · rename_i copies restImage copied threadsRest
            exact ⟨trivial,
              untouched_regions_carry layout _ place.definition place.roles _ untouched,
              threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
          · cases threads
          · cases threads
        · cases threads
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, _,
        rename, first, second, image, threads => by
        unfold threadRegion at threads
        split at threads
        · split at threads
          · dsimp only at threads
            split at threads
            · rename_i bodiesImage restImage threadsBodies threadsRest
              exact ⟨trivial, threadRegions_carry layout place bodies _ _ threadsBodies,
                threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
            · cases threads
            · cases threads
          · cases threads
        · rename_i untouched
          split at threads
          · rename_i copies restImage copied threadsRest
            exact ⟨trivial,
              untouched_regions_carry layout _ place.definition place.roles _ untouched,
              threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
          · cases threads
          · cases threads
        · cases threads
    | .letOp (.apply (header := header) callee roleMap site permitted) arguments nested rest, _,
        rename, first, second, image, threads => by
        cases nested
        unfold threadRegion at threads
        split at threads
        · dsimp only at threads
          split at threads
          · rename_i restImage threadsRest
            exact ⟨trivial, trivial, threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
          · cases threads
        · split at threads
          · rename_i calleeImage restImage found threadsRest
            exact ⟨trivial, trivial, threadRegion_carries layout place rest _ _ _ _ threadsRest⟩
          · cases threads
          · cases threads

  /-- The same for the nested regions of an operation of which the step made threaded
  images. -/
  theorem threadRegions_carry (layout : Layout operations)
      {table : CalleeTable layout.threads.header old new} (place : Place)
      {signatures targets : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (threaded : ThreadedRegions layout.threads place.roles signatures targets)
        (images : Regions (ProtocolDialect operations functions new deployed) targets),
        threadRegions layout.threads (serializeRule layout) table place regions threaded =
          .ok images →
        RegionsCarry layout place.roles regions
    | regions, threaded, images, threads =>
        match threaded, regions, images, threads with
        | .nil, .nil, _, _ => trivial
        | .cons leading added threaded, .cons body tail, images, threads => by
            simp only [threadRegions] at threads
            split at threads
            · rename_i bodyImage tailImages threadsBody threadsTail
              exact ⟨threadRegion_carries layout place body _ _ _ _ threadsBody,
                threadRegions_carry layout place tail threaded _ threadsTail⟩
            · cases threads
            · cases threads
end

end Carries

/-! ## The images of a definition, and of a program -/

section Driver

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- What the equation of the step says of the body of a definition, for one way it is
reached with whether the definition changes for it: the layout carries its messages for the
roles of the entry, and for the roles of an application for which the definition changes. -/
@[expose] def DemandCarries (layout : Layout operations) {old : List ProtocolHeader}
    {header : ProtocolHeader} (definition : ProtocolDefinition operations functions old header) :
    Demand → Bool → Prop
  | .entry roles, _ => RegionCarries layout roles definition.body
  | .applied (some prover) (some verifier), true =>
      RegionCarries layout ⟨prover, verifier⟩ definition.body
  | .applied .., _ => True

/-- When the serialize step made the images of a definition, the layout carries the messages
of its body for every way it is reached. -/
theorem rewriteDefinition_carries (layout : Layout operations) {old : List ProtocolHeader}
    {header : ProtocolHeader} (number : Nat)
    (definition : ProtocolDefinition operations functions old header) (specialized : Bool) :
    ∀ (classified : List (Demand × Bool)) (made : Bool)
      (images result : Images layout.threads typeTable operations functions old header),
      rewriteDefinition layout.threads (serializeRule layout) number definition specialized
        classified made images = .ok result →
      ∀ pair ∈ classified, DemandCarries layout definition pair.1 pair.2
  | [], _, _, _, _ => fun _ member => nomatch member
  | (demand, active) :: rest, made, images, result, rewrites => by
      -- The other ways, after the image for this one.
      have later : ∀ (next : Images layout.threads typeTable operations functions old header)
          (nextMade : Bool),
          rewriteDefinition layout.threads (serializeRule layout) number definition specialized
            rest nextMade next = .ok result →
          DemandCarries layout definition demand active →
          ∀ pair ∈ (demand, active) :: rest, DemandCarries layout definition pair.1 pair.2 := by
        intro next nextMade rewritesRest head pair member
        rcases List.mem_cons.mp member with rfl | among
        · exact head
        · exact rewriteDefinition_carries layout number definition specialized rest nextMade next
            result rewritesRest pair among
      cases demand with
      | entry roles =>
          simp only [rewriteDefinition] at rewrites
          split at rewrites
          · cases rewrites
          · split at rewrites
            · split at rewrites
              · rename_i body entered
                split at rewrites
                · rename_i next added
                  obtain ⟨Δ, rename, first, second, threaded, threads⟩ :=
                    serializeRule_entry_threads layout ⟨number, roles, false⟩ header _ body entered
                  exact later next made rewrites
                    (threadRegion_carries layout ⟨number, roles, false⟩ definition.body rename
                      first second threaded threads)
                · cases rewrites
              · cases rewrites
            · rename_i idle
              exact absurd (Bool.or_true active) idle
      | applied prover verifier =>
          cases prover with
          | none =>
              cases verifier <;> simp only [rewriteDefinition] at rewrites <;>
                (split at rewrites
                 · exact later _ true rewrites trivial
                 · cases rewrites)
          | some inner =>
              cases verifier with
              | none =>
                  simp only [rewriteDefinition] at rewrites
                  split at rewrites
                  · exact later _ true rewrites trivial
                  · cases rewrites
              | some outer =>
                  cases active with
                  | false =>
                      simp only [rewriteDefinition] at rewrites
                      split at rewrites
                      · exact later _ true rewrites trivial
                      · cases rewrites
                  | true =>
                      simp only [rewriteDefinition] at rewrites
                      split at rewrites
                      · rename_i body threads
                        split at rewrites
                        · exact later _ made rewrites
                            (threadRegion_carries layout ⟨number, ⟨inner, outer⟩, specialized⟩
                              definition.body _ _ _ body threads)
                        · cases rewrites
                      · cases rewrites

/-- The serialize step on one more protocol: for every way the protocol is reached with both
transcript roles among its own, as the entry or by an application, the layout carries the
messages of its body for these roles. -/
theorem rewriteProtocols_newest_carries (layout : Layout operations) (identities : Identities)
    {old : List ProtocolHeader} {header : ProtocolHeader}
    (earlier : Protocols typeTable operations functions old)
    (definition : ProtocolDefinition operations functions old header)
    (wellFormed : definition.violation typeTable = none) (demands : List (List Demand))
    (rewritten : Rewritten layout.threads typeTable operations functions (header :: old))
    (rewrites : rewriteProtocols layout.threads (serializeRule layout) identities
      (.snoc earlier definition wellFormed) demands = .ok rewritten) :
    ∀ demand ∈ demands.headD [], ∀ roles : TranscriptRoles,
      demand.prover = some roles.prover → demand.verifier = some roles.verifier →
        RegionCarries layout roles definition.body := by
  unfold rewriteProtocols at rewrites
  dsimp only at rewrites
  split at rewrites
  · rename_i new typed table origins counted marks rewritesEarlier
    split at rewrites
    · rename_i classified classifies
      obtain ⟨sound, complete⟩ := classify_spec table (identities old.length) definition _
        classified classifies
      split at rewrites
      · rename_i images produced
        intro demand member roles atProver atVerifier
        obtain ⟨active, classifiedMember⟩ := complete demand member
        have touched := (sound _ classifiedMember).2
        have carried := rewriteDefinition_carries layout (identities old.length) definition _
          classified false _ images produced _ classifiedMember
        obtain ⟨prover, verifier⟩ := roles
        cases demand with
        | entry declared =>
            obtain ⟨declaredProver, declaredVerifier⟩ := declared
            cases Option.some.inj atProver
            cases Option.some.inj atVerifier
            exact carried
        | applied reachedProver reachedVerifier =>
            cases atProver
            cases atVerifier
            cases active with
            | true => exact carried
            | false => exact untouched_carries layout _ _ ⟨prover, verifier⟩ definition.body touched
      · cases rewrites
    · cases rewrites
  · cases rewrites

end Driver

end Zkc.Core
