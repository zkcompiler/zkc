module

public import Zkc.Core.ThreadSites
public import Zkc.Core.ThreadHandler

public section

/-! A handler that follows the marks of a definition fits its body.

`region_fits`: for a side with exactly one transcript role, a handler that follows the
marks of a region whose sites are pairwise different fits the region (`Fits`), which is
what the structural theorem of threading requires of a handler. `Protocols.table_passes`:
every protocol of a program is passed by a handler that performs, as it is, every effect
below the path under which the protocol is reached.

The file has four parts.

- **Passing.** `region_passes`: a handler that performs as it is every effect whose site,
  relative to a path, starts at a site of a region (`PassesSites`) passes the region's
  process under that path, over a table whose protocols are passed. The start of a
  relative site (`Site.head`) is the site number of the operation of the region that
  performs the effect or applies the protocol that performs it.
- **Marks and sites.** A region marks only relative sites that start at one of its sites
  (`regionMarks_outside`), and a region without a rewritten operation marks none
  (`regionMarks_untouched`).
- **What a side does at a rewritten operation.** The equations of `threadAct` at an
  exchange and at a draw, for the memberships of the two transcript roles
  (`send_acts`, `receive_acts`, `owner_draw_acts`, `receiver_draw_acts`).
- **Fitting.** `region_fits_marks` is `region_fits` for a part of the region whose marks
  the handler follows: the marks of the whole region agree with the marks of the part at
  the relative sites that start in the part, because the sites are pairwise different.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-- Where a site relative to a definition starts: at the site of the application through
which its effect is reached, or, for an effect of the definition's own operation, at the
site number of that operation. -/
@[expose] def Site.head (at_ : Site) : Nat :=
  match at_.path with
  | [] => at_.number
  | first :: _ => first

/-! ## Passing -/

section Passing

variable {model : Model} {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool} {S : Type}
  {handler : PIR.StatefulInterpretation (Effects model) (Effects model) S}

/-- A handler passes an effect that it performs as it is, followed by processes that it
passes. -/
theorem call_passes {A : Type} {effect : Effect model.Value}
    {next : Effect.Reply effect → PIR.Process (Effects model) A}
    (performed : ∀ state, handler effect state = passEffect effect state)
    (passesNext : ∀ reply, PIR.Passes handler (next reply)) :
    PIR.Passes handler (.call effect next) := by
  intro state
  show (handler effect state).bind _ = _
  rw [performed state]
  show PIR.Process.call (I := Effects model) effect _ = PIR.Process.call effect _
  congr 1
  funext reply
  exact passesNext reply state

/-- A handler performs as it is every effect below a path whose site, relative to the
path, starts at an allowed number. -/
@[expose] def PassesSites (handler : PIR.StatefulInterpretation (Effects model) (Effects model) S)
    (path : List Nat) (allowed : Nat → Prop) : Prop :=
  ∀ (effect : Effect model.Value) (rest : List Nat), effect.site.path = path ++ rest →
    allowed (Site.head ⟨rest, effect.site.definition, effect.site.number⟩) →
      ∀ state : S, handler effect state = passEffect effect state

/-- A handler that performs every effect below a path as it is does so wherever the
effect's site starts. -/
theorem PassesBelow.sites {path : List Nat} (below : PassesBelow handler path) :
    PassesSites handler path fun _ => True :=
  fun effect rest under _ => below effect rest under

/-- An effect of an operation of the definition that is reached under the path, at an
allowed site number. -/
theorem PassesSites.own {path : List Nat} {allowed : Nat → Prop}
    (passesSites : PassesSites handler path allowed) (identity : Nat) {number : Nat}
    (allowedNumber : allowed number) (effect : Effect model.Value)
    (own : effect.site = ⟨path, identity, number⟩) (state : S) :
    handler effect state = passEffect effect state := by
  refine passesSites effect [] ?_ ?_ state
  · rw [own, List.append_nil]
  · rw [own]
    exact allowedNumber

/-- The effects of a protocol applied at an allowed site. -/
theorem PassesSites.below {path : List Nat} {allowed : Nat → Prop}
    (passesSites : PassesSites handler path allowed) {site : Nat} (allowedSite : allowed site) :
    PassesBelow handler (path ++ [site]) := by
  intro effect rest under state
  refine passesSites effect (site :: rest) ?_ allowedSite state
  rw [under, List.append_assoc]
  rfl

/-- The handler passes every process of every region function. -/
@[expose] def PassAll {side : Side}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) S) :
    {signatures : List (List Located × List Located)} →
      Values (RegionFunction (SideValue model side) (Effects model)) signatures → Prop
  | [], _ => True
  | _ :: _, regions =>
      (∀ values, PIR.Passes handler ((regions.get .here) values)) ∧ PassAll handler regions.tail

/-- For a handler of the threaded values, the same as `PassRegions`. -/
theorem PassAll.passRegions {t : Threads} {place : Place} {side : Side}
    {handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier)} :
    ∀ {signatures : List (List Located × List Located)}
      (regions : Values (RegionFunction (SideValue model side) (Effects model)) signatures),
      PassAll handler regions → PassRegions t place side handler regions
  | [], _, _ => trivial
  | _ :: _, regions, passAll => ⟨passAll.1, PassAll.passRegions regions.tail passAll.2⟩

/-- The regions of a list that a handler passes: every selection is passed. -/
theorem passAll_select {side : Side} (signature : List Located × List Located) :
    ∀ (count : Nat)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (List.replicate count signature)),
      PassAll handler regions →
      ∀ (number : Fin count) values,
        PIR.Passes handler (selectArm signature count regions number values)
  | 0, _, _, number, _ => number.elim0
  | _ + 1, _, passAll, ⟨0, _⟩, values => passAll.1 values
  | count + 1, regions, passAll, ⟨number + 1, below⟩, values =>
      passAll_select signature count regions.tail passAll.2
        ⟨number, Nat.lt_of_succ_lt_succ below⟩ values

/-- The regions of a choice on a variant that a handler passes: the region of every
alternative is passed, on whatever payloads. -/
theorem alternativeProcess_passAll {side : Side} {participants : List Nat}
    {captures outputs : List Located} :
    ∀ (alternatives : List Ty)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (alternatives.map fun payload =>
          (Located.ofRoles payload participants ++ captures, outputs))),
      PassAll handler regions →
      ∀ (number : Nat)
        (copies : Values (fun role => Held (Ty.Variant model.Carrier alternatives) (side role))
          participants)
        (values : Values (SideValue model side) captures),
        PIR.Passes handler
          (alternativeProcess model side participants captures outputs alternatives regions number
            copies values)
  | [], _, _, _, _, _ => PIR.Passes.halt handler _
  | payload :: rest, regions, passAll, 0, copies, values => by
      cases found : firstPayloads model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_first_other found]
          exact PIR.Passes.halt handler _
      | some payloads =>
          rw [alternativeProcess_first found]
          exact passAll.1 _
  | payload :: rest, regions, passAll, number + 1, copies, values => by
      cases found : laterCopies model side payload rest participants copies with
      | none =>
          rw [alternativeProcess_later_other number found]
          exact PIR.Passes.halt handler _
      | some later =>
          rw [alternativeProcess_later number found]
          exact alternativeProcess_passAll rest regions.tail passAll.2 number later values

/-- The regions of a `choose` that a handler passes: the region that a tag selects is
passed. -/
theorem chosenRegion_passAll {side : Side} {participants : List Nat}
    {captures outputs : List Located} :
    ∀ (tag : ChoiceTag)
      (regions : Values (RegionFunction (SideValue model side) (Effects model))
        (tag.regions participants captures outputs)),
      PassAll handler regions →
      ∀ (copies : Values (fun role => Held (model.Value tag.type) (side role)) participants)
        (values : Values (SideValue model side) captures) (value : model.Value tag.type),
        PIR.Passes handler
          (chosenRegion model side participants captures outputs tag regions copies values value)
  | .condition, regions, passAll, _, values, _ =>
      passAll_select (captures, outputs) 2 regions passAll _ values
  | .arm count, regions, passAll, _, values, _ =>
      passAll_select (captures, outputs) count regions passAll _ values
  | .alternative _ alternatives, regions, passAll, copies, values, _ =>
      alternativeProcess_passAll alternatives regions passAll _ copies values

/-- The announcements of a draw from outside the side are passed by a handler that
performs a `receive` at the draw's site as it is. -/
theorem receiverReplies_passes (side : Side) (site : Site) (type : Ty)
    (performed : ∀ state, handler (.receive site type) state = passEffect (.receive site type) state) :
    ∀ receivers : List Nat,
      PIR.Passes handler (receiverReplies model side site type receivers)
  | [] => PIR.Passes.done handler _
  | role :: rest => by
      cases member : side role with
      | true =>
          rw [receiverReplies_present model side site type role rest member]
          exact call_passes performed fun _ =>
            (receiverReplies_passes side site type performed rest).bind fun _ =>
              PIR.Passes.done handler _
      | false =>
          rw [receiverReplies_absent model side site type role rest member]
          exact (receiverReplies_passes side site type performed rest).bind fun _ =>
            PIR.Passes.done handler _

variable {functionTable : FunctionTable model functions} {table : ProtocolTable model protocols}

/-- A handler passes an operation of a definition that is reached under a path, when it
performs as it is the effects that start at the operation's site, passes the operation's
regions, and the protocols of the table are passed. -/
theorem operation_passes (quiet : QuietTable functionTable) (passes : TablePasses table)
    (identity : Nat) {path : List Nat} (side : Side) {allowed : Nat → Prop}
    (passesSites : PassesSites handler path allowed) :
    ∀ (op : ProtocolOp operations functions protocols deployed),
      (∀ site ∈ ProtocolOp.sites op, allowed site) →
      ∀ (arguments : Values (SideValue model side) op.arguments)
        (regions : Values (RegionFunction (SideValue model side) (Effects model)) op.regions),
        PassAll handler regions →
          PIR.Passes handler
            (labelledOperation model (ownSites identity path) functionTable table side op arguments
              regions)
  | .at role op bodies, _, arguments, regions, _ => by
      cases regions
      exact (at_quiet quiet _ table side role op bodies arguments).passes handler
  | .exchange sender receiver site type, allowedSite, arguments, regions, _ => by
      have performed := passesSites.own identity
        (allowedSite site (by rw [ProtocolOp.sites_exchange]; exact List.mem_singleton_self site))
      cases senderMember : side sender <;> cases receiverMember : side receiver
      · rw [labelled_exchange_outside senderMember receiverMember]
        exact PIR.Passes.done handler _
      · rw [labelled_exchange_receive senderMember receiverMember]
        exact call_passes (performed _ rfl) fun _ => PIR.Passes.done handler _
      · rw [labelled_exchange_send senderMember receiverMember]
        exact call_passes (performed _ rfl) fun _ => PIR.Passes.done handler _
      · rw [labelled_exchange_internal senderMember receiverMember]
        exact PIR.Passes.done handler _
  | .draw owner receivers site law populated, allowedSite, arguments, regions, _ => by
      have performed := passesSites.own identity
        (allowedSite site (by rw [ProtocolOp.sites_draw]; exact List.mem_singleton_self site))
      cases member : side owner with
      | true =>
          rw [labelled_draw_owner member]
          exact call_passes (performed _ rfl) fun _ => PIR.Passes.done handler _
      | false =>
          rw [labelled_draw_outside member]
          exact (receiverReplies_passes side _ _ (performed _ rfl) receivers).bind fun _ =>
            PIR.Passes.done handler _
  | .sample owner site law populated, allowedSite, arguments, regions, _ => by
      have performed := passesSites.own identity
        (allowedSite site (by rw [ProtocolOp.sites_sample]; exact List.mem_singleton_self site))
      cases member : side owner with
      | true =>
          rw [labelled_sample_owner member]
          exact call_passes (performed _ rfl) fun _ => PIR.Passes.done handler _
      | false =>
          rw [labelled_sample_outside member]
          exact PIR.Passes.done handler _
  | .repeat participants count carried collected captures covered, _, arguments, regions,
      passAll => by
      show PIR.Passes handler (agreed Nat.beq side _ _ participants _ _)
      refine agreed_holds (PIR.Passes handler) Nat.beq side _ _ ?_ (PIR.Passes.halt handler _)
        participants _ _ fun _ => PIR.Passes.done handler _
      intro agreed
      exact repeatProcess_passes side count carried collected (fun _ _ => passAll.1 _) agreed _
  | .choose participants tag captures outputs covered, _, arguments, regions, passAll => by
      show PIR.Passes handler (agreed (tag.same model.Carrier) side _ _ participants _ _)
      refine agreed_holds (PIR.Passes handler) (tag.same model.Carrier) side _ _ ?_
        (PIR.Passes.halt handler _) participants _ _ fun _ => PIR.Passes.done handler _
      intro value
      exact chosenRegion_passAll tag regions passAll _ _ value
  | .apply callee roleMap site permitted, allowedSite, arguments, regions, _ => by
      rw [labelled_apply_meaning]
      exact (passes handler callee _ _ _ (passesSites.below
        (allowedSite site (by rw [ProtocolOp.sites_apply]; exact List.mem_singleton_self site)))).bind
          fun _ => PIR.Passes.done handler _

mutual
  /-- A handler passes a region of a definition that is reached under a path, when it
  performs as it is every effect that starts at a site of the region and the protocols of
  the table are passed. -/
  theorem region_passes (quiet : QuietTable functionTable) (passes : TablePasses table)
      (identity : Nat) {path : List Nat} (side : Side) {allowed : Nat → Prop}
      (passesSites : PassesSites handler path allowed) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions protocols deployed) Γ out),
        (∀ site ∈ regionSites region, allowed site) →
        ∀ env : Environment (SideValue model side) Γ,
          PIR.Passes handler
            (region.denote (labelledMeaning model (ownSites identity path) functionTable table side)
              env)
    | .ret _, _, _ => PIR.Passes.done handler _
    | .stop _, _, _ => PIR.Passes.halt handler _
    | .bind body rest, allowedSites, env =>
        PIR.Passes.bind
          (region_passes quiet passes identity side passesSites body
            (fun site member => allowedSites site (List.mem_append_right _ member)) env)
          fun _ => region_passes quiet passes identity side passesSites rest
            (fun site member => allowedSites site (List.mem_append_left _ member)) _
    | .letOp op arguments bodies rest, allowedSites, env =>
        PIR.Passes.bind
          (operation_passes quiet passes identity side passesSites op
            (fun site member => allowedSites site
              (List.mem_append_right _ (List.mem_append_right _ member))) _ _
            (regions_pass quiet passes identity side passesSites bodies
              fun site member => allowedSites site
                (List.mem_append_right _ (List.mem_append_left _ member))))
          fun _ => region_passes quiet passes identity side passesSites rest
            (fun site member => allowedSites site (List.mem_append_left _ member)) _

  /-- The same for closed regions. -/
  theorem regions_pass (quiet : QuietTable functionTable) (passes : TablePasses table)
      (identity : Nat) {path : List Nat} (side : Side) {allowed : Nat → Prop}
      (passesSites : PassesSites handler path allowed)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions protocols deployed) signatures),
        (∀ site ∈ regionsSites regions, allowed site) →
          PassAll handler
            (regions.denote (labelledMeaning model (ownSites identity path) functionTable table side))
    | .nil, _ => trivial
    | .cons body tail, allowedSites =>
        ⟨fun _ => region_passes quiet passes identity side passesSites body
            (fun site member => allowedSites site (List.mem_append_right _ member)) _,
          regions_pass quiet passes identity side passesSites tail
            fun site member => allowedSites site (List.mem_append_left _ member)⟩
end

end Passing

/-! ## Marks and sites -/

section Marks

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}

theorem bothTouch_false {first second : Except StepRefusal Bool}
    (untouched : bothTouch first second = .ok false) : first = .ok false ∧ second = .ok false := by
  match first, second, untouched with
  | .ok false, .ok false, _ => exact ⟨rfl, rfl⟩

/-- The image that threads of a callee has the transcript roles that the marks of the
application use. -/
theorem threadedRoles_of_callee (table : CalleeTable t.header old new) (roles : TranscriptRoles)
    (roleMap : RoleMap) {header : ProtocolHeader} (callee : Var old header)
    {threaded : ThreadedCallee t new roles roleMap header}
    (found : threadedCallee t table roles roleMap callee = some threaded) :
    threadedRoles table.threads roles roleMap callee.index = some threaded.inner := by
  unfold threadedCallee at found
  unfold threadedRoles
  cases atProver : preimage roleMap roles.prover with
  | none =>
      rw [atProver] at found
      cases found
  | some prover =>
      cases atVerifier : preimage roleMap roles.verifier with
      | none =>
          rw [atProver, atVerifier] at found
          cases found
      | some verifier =>
          rw [atProver, atVerifier] at found
          obtain ⟨prover, isProver⟩ := prover
          obtain ⟨verifier, isVerifier⟩ := verifier
          dsimp only at found ⊢
          cases image : table.find callee (some ⟨prover, verifier⟩) with
          | none =>
              rw [image] at found
              cases found
          | some image' =>
              rw [image] at found
              have has : table.threads callee.index ⟨prover, verifier⟩ = true := by
                show table.has callee.index (some ⟨prover, verifier⟩) = true
                rw [← CalleeTable.find_isSome, image]
                rfl
              rw [if_pos has]
              cases found
              rfl

/-- A callee without an image that threads has no marks at its application. -/
theorem threadedRoles_none (table : CalleeTable t.header old new) (roles : TranscriptRoles)
    (roleMap : RoleMap) {header : ProtocolHeader} (callee : Var old header)
    (missing : threadedCallee t table roles roleMap callee = none) :
    threadedRoles table.threads roles roleMap callee.index = none := by
  unfold threadedCallee at missing
  unfold threadedRoles
  cases atProver : preimage roleMap roles.prover with
  | none => rfl
  | some prover =>
      cases atVerifier : preimage roleMap roles.verifier with
      | none => rfl
      | some verifier =>
          rw [atProver, atVerifier] at missing
          obtain ⟨prover, isProver⟩ := prover
          obtain ⟨verifier, isVerifier⟩ := verifier
          dsimp only at missing ⊢
          cases image : table.find callee (some ⟨prover, verifier⟩) with
          | none =>
              have has : table.threads callee.index ⟨prover, verifier⟩ = false := by
                show table.has callee.index (some ⟨prover, verifier⟩) = false
                rw [← CalleeTable.find_isSome, image]
                rfl
              rw [if_neg (by rw [has]; exact Bool.false_ne_true)]
          | some image' =>
              rw [image] at missing
              cases missing

variable (threads : Nat → TranscriptRoles → Bool) (callees : MarkTable operations old)
  (place : Place)

/-- An operation marks only relative sites that start at its site. -/
theorem opMarks_outside (op : ProtocolOp operations functions old deployed) (at_ : Site)
    (outside : at_.head ∉ ProtocolOp.sites op) : opMarks threads callees place op at_ = none := by
  obtain ⟨path, definition, number⟩ := at_
  cases op with
  | «at» role op bodies => rfl
  | sample owner site law populated => rfl
  | «repeat» participants count carried collected captures covered => rfl
  | choose participants tag captures outputs covered => rfl
  | exchange sender receiver site type =>
      unfold opMarks
      refine if_neg fun marked => outside ?_
      obtain ⟨_, _, emptyPath, sameNumber⟩ := marked
      dsimp only at emptyPath sameNumber
      subst emptyPath
      rw [ProtocolOp.sites_exchange]
      exact List.mem_singleton.mpr sameNumber
  | draw owner receivers site law populated =>
      match receivers with
      | [] => rfl
      | _ :: _ :: _ => rfl
      | [receiver] =>
          unfold opMarks
          refine if_neg fun marked => outside ?_
          obtain ⟨emptyPath, sameNumber⟩ := marked
          dsimp only at emptyPath sameNumber
          subst emptyPath
          rw [ProtocolOp.sites_draw]
          exact List.mem_singleton.mpr sameNumber
  | apply callee roleMap site permitted =>
      cases path with
      | nil => rfl
      | cons first rest =>
          unfold opMarks
          dsimp only
          refine if_neg fun same => outside ?_
          rw [ProtocolOp.sites_apply]
          exact List.mem_singleton.mpr same

mutual
  /-- A region marks only relative sites that start at one of its sites. -/
  theorem regionMarks_outside {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out) (at_ : Site),
        at_.head ∉ regionSites region → regionMarks threads callees place region at_ = none
    | .ret _, _, _ => rfl
    | .stop _, _, _ => rfl
    | .bind body rest, at_, outside => by
        show (regionMarks threads callees place body at_).or
          (regionMarks threads callees place rest at_) = none
        rw [regionMarks_outside body at_ fun member => outside (List.mem_append_right _ member),
          regionMarks_outside rest at_ fun member => outside (List.mem_append_left _ member)]
        rfl
    | .letOp op _ bodies rest, at_, outside => by
        show (opMarks threads callees place op at_).or
          ((regionsMarks threads callees place bodies at_).or
            (regionMarks threads callees place rest at_)) = none
        rw [opMarks_outside threads callees place op at_ fun member =>
            outside (List.mem_append_right _ (List.mem_append_right _ member)),
          regionsMarks_outside bodies at_ fun member =>
            outside (List.mem_append_right _ (List.mem_append_left _ member)),
          regionMarks_outside rest at_ fun member => outside (List.mem_append_left _ member)]
        rfl

  theorem regionsMarks_outside {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (at_ : Site),
        at_.head ∉ regionsSites regions → regionsMarks threads callees place regions at_ = none
    | .nil, _, _ => rfl
    | .cons body tail, at_, outside => by
        show (regionMarks threads callees place body at_).or
          (regionsMarks threads callees place tail at_) = none
        rw [regionMarks_outside body at_ fun member => outside (List.mem_append_right _ member),
          regionsMarks_outside tail at_ fun member => outside (List.mem_append_left _ member)]
        rfl
end

/-- The mark of an exchange. -/
theorem opMarks_exchange (sender receiver site : Nat) (type : Ty) (at_ : Site) :
    opMarks (functions := functions) (deployed := deployed) threads callees place
        (.exchange sender receiver site type) at_ =
      if sender = place.roles.prover ∧ receiver = place.roles.verifier ∧ at_.path = [] ∧
          at_.number = site then some (.exchange place site)
      else none := by
  rfl

/-- The mark of a draw with one receiver. -/
theorem opMarks_draw (owner receiver site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
    (at_ : Site) :
    opMarks (functions := functions) (deployed := deployed) threads callees place
        (.draw owner [receiver] site law populated) at_ =
      if at_.path = [] ∧ at_.number = site then
        if owner = place.roles.verifier ∧ receiver = place.roles.prover then
          some (.draw true place site law)
        else if owner = place.roles.prover ∧ receiver = place.roles.verifier then
          some (.draw false place site law)
        else none
      else none := by
  rfl

/-- The marks of an application below its site: the marks of the callee for the
transcript roles of its image that threads. -/
theorem opMarks_apply {header : ProtocolHeader} (callee : Var old header) (roleMap : RoleMap)
    (site : Nat) (permitted : (deployed && header.specificationOnly) = false) (rest : List Nat)
    (definition number : Nat) :
    opMarks (functions := functions) threads callees place (.apply callee roleMap site permitted)
        ⟨site :: rest, definition, number⟩ =
      match threadedRoles threads place.roles roleMap callee.index with
      | some inner => (callees.get callee) inner ⟨rest, definition, number⟩
      | none => none := by
  show (if site = site then _ else none) = _
  rw [if_pos rfl]
  rfl

/-- An operation that is not rewritten has no mark. -/
theorem opMarks_untouched (table : CalleeTable t.header old new) (derives : Bool)
    (definition : Nat) (op : ProtocolOp operations functions old deployed)
    (untouched : touchesOp t derives table definition (some place.roles.prover)
      (some place.roles.verifier) op = .ok false) (at_ : Site) :
    opMarks table.threads callees place op at_ = none := by
  cases op with
  | «at» role op bodies => rfl
  | sample owner site law populated => rfl
  | «repeat» participants count carried collected captures covered => rfl
  | choose participants tag captures outputs covered => rfl
  | exchange sender receiver site type =>
      rw [opMarks_exchange]
      refine if_neg fun marked => ?_
      obtain ⟨isProver, isVerifier, _⟩ := marked
      subst isProver isVerifier
      simp [touchesOp, isRole] at untouched
  | draw owner receivers site law populated =>
      match receivers, untouched with
      | [], _ => rfl
      | _ :: _ :: _, _ => rfl
      | [receiver], untouched =>
          rw [opMarks_draw]
          split
          · split
            · rename_i byVerifier
              obtain ⟨isVerifier, isProver⟩ := byVerifier
              subst isProver isVerifier
              exfalso
              by_cases same : place.roles.prover = place.roles.verifier <;> cases derives <;>
                simp [touchesOp, isRole, occursIn, same] at untouched <;>
                split at untouched <;> cases untouched
            · split
              · rename_i byProver
                obtain ⟨isProver, isVerifier⟩ := byProver
                subst isProver isVerifier
                exfalso
                by_cases same : place.roles.prover = place.roles.verifier <;> cases derives <;>
                  simp [touchesOp, isRole, occursIn, same] at untouched <;>
                  split at untouched <;> cases untouched
              · rfl
          · rfl
  | apply callee roleMap site permitted =>
      obtain ⟨path, siteDefinition, number⟩ := at_
      cases path with
      | nil => rfl
      | cons first rest =>
          by_cases same : first = site
          · subst same
            rw [opMarks_apply]
            have unthreaded : threadedRoles table.threads place.roles roleMap callee.index = none := by
              unfold threadedRoles
              cases atProver : preimage roleMap place.roles.prover with
              | none => rfl
              | some prover =>
                  cases atVerifier : preimage roleMap place.roles.verifier with
                  | none => rfl
                  | some verifier =>
                      have innerProver : preimageOf roleMap (some place.roles.prover) =
                          some prover.val := by
                        show (preimage roleMap place.roles.prover).map (·.val) = _
                        rw [atProver]
                        rfl
                      have innerVerifier : preimageOf roleMap (some place.roles.verifier) =
                          some verifier.val := by
                        show (preimage roleMap place.roles.verifier).map (·.val) = _
                        rw [atVerifier]
                        rfl
                      simp only [touchesOp, innerProver, innerVerifier] at untouched
                      have missing := Except.ok.inj untouched
                      rw [CalleeTable.find_isSome] at missing
                      exact if_neg fun has => Bool.false_ne_true (missing.symm.trans has)
            rw [unthreaded]
          · show (if first = site then _ else none) = none
            exact if_neg same

mutual
  /-- A region without a rewritten operation marks no site. -/
  theorem regionMarks_untouched (table : CalleeTable t.header old new) (derives : Bool)
      (definition : Nat) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        touches t derives table definition (some place.roles.prover) (some place.roles.verifier)
          region = .ok false →
        ∀ at_ : Site, regionMarks table.threads callees place region at_ = none
    | .ret _, _, _ => rfl
    | .stop _, _, _ => rfl
    | .bind body rest, untouched, at_ => by
        unfold touches at untouched
        obtain ⟨first, second⟩ := bothTouch_false untouched
        show (regionMarks table.threads callees place body at_).or
          (regionMarks table.threads callees place rest at_) = none
        rw [regionMarks_untouched table derives definition body first at_,
          regionMarks_untouched table derives definition rest second at_]
        rfl
    | .letOp op _ bodies rest, untouched, at_ => by
        unfold touches at untouched
        obtain ⟨own, later⟩ := bothTouch_false untouched
        obtain ⟨nested, after⟩ := bothTouch_false later
        show (opMarks table.threads callees place op at_).or
          ((regionsMarks table.threads callees place bodies at_).or
            (regionMarks table.threads callees place rest at_)) = none
        rw [opMarks_untouched callees place table derives definition op own at_,
          regionsMarks_untouched table derives definition bodies nested at_,
          regionMarks_untouched table derives definition rest after at_]
        rfl

  theorem regionsMarks_untouched (table : CalleeTable t.header old new) (derives : Bool)
      (definition : Nat) {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        touchesRegions t derives table definition (some place.roles.prover)
          (some place.roles.verifier) regions = .ok false →
        ∀ at_ : Site, regionsMarks table.threads callees place regions at_ = none
    | .nil, _, _ => rfl
    | .cons body tail, untouched, at_ => by
        unfold touchesRegions at untouched
        obtain ⟨first, later⟩ := bothTouch_false untouched
        show (regionMarks table.threads callees place body at_).or
          (regionsMarks table.threads callees place tail at_) = none
        rw [regionMarks_untouched table derives definition body first at_,
          regionsMarks_untouched table derives definition tail later at_]
        rfl
end

end Marks

/-! ## What a side does at a rewritten operation -/

section Acts

variable {model : Model} {operations : List OperationSignature} {t : Threads}
  (sem : RuleMeaning model t operations)

/-- At a site without a mark a side performs the effect as it is. -/
theorem threadAct_unmarked (prover verifier : Bool) (effect : Effect model.Value)
    (state : ThreadState model t prover verifier) :
    threadAct sem none prover verifier effect state = passEffect effect state := by
  cases prover <;> cases verifier <;> rfl

variable {sem} {prover verifier : Bool} {handler : ThreadHandler model t prover verifier}
  {path : List Nat} {marks : Site → Option (Mark operations)}

/-- A handler that follows marks performs as it is an effect at a relative site without a
mark. -/
theorem Follows.unmarked (follows : Follows sem prover verifier handler path marks)
    (effect : Effect model.Value) (rest : List Nat) (under : effect.site.path = path ++ rest)
    (unmarked : marks ⟨rest, effect.site.definition, effect.site.number⟩ = none)
    (state : ThreadState model t prover verifier) :
    handler effect state = passEffect effect state := by
  rw [follows effect rest under state, unmarked]
  exact threadAct_unmarked sem prover verifier effect state

/-- A handler that follows marks performs as it is every effect that starts at a site
whose relative sites have no mark. -/
theorem Follows.passesSites (follows : Follows sem prover verifier handler path marks)
    (allowed : Nat → Prop) (unmarked : ∀ at_ : Site, allowed at_.head → marks at_ = none) :
    PassesSites handler path allowed :=
  fun effect rest under allowedHead state =>
    follows.unmarked effect rest under (unmarked _ allowedHead) state

/-- A handler that follows marks, at an effect of an operation of the definition. -/
theorem Follows.own (follows : Follows sem prover verifier handler path marks)
    (identity number : Nat) (effect : Effect model.Value)
    (own : effect.site = ⟨path, identity, number⟩) (state : ThreadState model t prover verifier) :
    handler effect state =
      threadAct sem (marks ⟨[], identity, number⟩) prover verifier effect state := by
  have acts := follows effect [] (by rw [own, List.append_nil]) state
  rw [own] at acts
  exact acts

/-- A handler that follows the marks of a definition follows, below the site of an
application, the marks that the definition has below that site. -/
theorem Follows.below (follows : Follows sem prover verifier handler path marks) (site : Nat)
    (inner : Site → Option (Mark operations))
    (same : ∀ (rest : List Nat) (definition number : Nat),
      marks ⟨site :: rest, definition, number⟩ = inner ⟨rest, definition, number⟩) :
    Follows sem prover verifier handler (path ++ [site]) inner := by
  intro effect rest under state
  rw [follows effect (site :: rest) (by rw [under, List.append_assoc]; rfl) state, same]

variable (sem)

/-- The prover's side at a rewritten exchange: its `send`, under a handler that acts by
the mark of the exchange, is the rule's exchange. -/
theorem send_acts {A : Type} (prover verifier : Bool) (isProver : prover = true)
    (isVerifier : verifier = false) (handler : ThreadHandler model t prover verifier)
    (place : Place) (number : Nat) (site : Site) (type : Ty)
    (value : Held (model.Value type) prover) (pack : Held (model.Value type) verifier → A)
    (acts : ∀ effect : Effect model.Value, effect.site = site → ∀ state,
      handler effect state =
        threadAct sem (some (.exchange place number)) prover verifier effect state)
    (state : ThreadState model t prover verifier) :
    (PIR.Process.call (I := Effects model) (.send site type (Held.value prover isProver value))
        fun _ => .done (pack (Held.absent verifier isVerifier))).interpretWith handler state =
      (sem.exchange prover verifier place number site type value state).bind fun result =>
        .done (pack result.1, result.2) := by
  subst isProver isVerifier
  show (handler _ state).bind _ = _
  rw [acts _ rfl state]
  show ((sem.exchange true false place number site type value state).bind _).bind _ = _
  rw [PIR.Process.bind_assoc]
  rfl

/-- The verifier's side at a rewritten exchange: its `receive`, under a handler that acts
by the mark of the exchange, is the rule's exchange. -/
theorem receive_acts {A : Type} (prover verifier : Bool) (isProver : prover = false)
    (isVerifier : verifier = true) (handler : ThreadHandler model t prover verifier)
    (place : Place) (number : Nat) (site : Site) (type : Ty)
    (value : Held (model.Value type) prover) (pack : Held (model.Value type) verifier → A)
    (acts : ∀ effect : Effect model.Value, effect.site = site → ∀ state,
      handler effect state =
        threadAct sem (some (.exchange place number)) prover verifier effect state)
    (state : ThreadState model t prover verifier) :
    (PIR.Process.call (I := Effects model) (.receive site type)
        fun reply => .done (pack (Held.of verifier reply))).interpretWith handler state =
      (sem.exchange prover verifier place number site type value state).bind fun result =>
        .done (pack result.1, result.2) := by
  subst isProver isVerifier
  show (handler _ state).bind _ = _
  rw [acts _ rfl state]
  show ((sem.exchange false true place number site type PUnit.unit state).bind _).bind _ = _
  rw [PIR.Process.bind_assoc]
  rfl

/-- The owner's side at a rewritten draw: its `draw`, under a handler that acts by the
mark of the draw, is the rule's draw. -/
theorem owner_draw_acts {A : Type} (byVerifier prover verifier : Bool)
    (isProver : prover = !byVerifier) (isVerifier : verifier = byVerifier)
    (handler : ThreadHandler model t prover verifier) (place : Place) (number : Nat) (site : Site)
    {inputs : List Ty} {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (populated : output.populated = true) (arguments : Values model.Value inputs)
    (pack : Held (model.Value output) prover → Held (model.Value output) verifier → A)
    (acts : ∀ effect : Effect model.Value, effect.site = site → ∀ state,
      handler effect state =
        threadAct sem (some (.draw byVerifier place number law)) prover verifier effect state)
    (state : ThreadState model t prover verifier) :
    (PIR.Process.call (I := Effects model) (.draw site (.of law populated) arguments)
        fun reply => .done (pack (Held.of prover reply) (Held.of verifier reply))).interpretWith
        handler state =
      (sem.draw prover verifier place number site law state).bind fun result =>
        .done (pack result.1.1 result.1.2, result.2) := by
  subst isProver isVerifier
  cases verifier
  · show (handler _ state).bind _ = _
    rw [acts _ rfl state]
    show ((if same : output = output then
        (sem.draw true false place number site law state).bind fun result =>
          PIR.Process.done (cast (congrArg model.Value same) result.1.1, result.2)
      else _).bind _) = _
    rw [dif_pos rfl, PIR.Process.bind_assoc]
    rfl
  · show (handler _ state).bind _ = _
    rw [acts _ rfl state]
    show ((if same : output = output then
        (sem.draw false true place number site law state).bind fun result =>
          PIR.Process.done (cast (congrArg model.Value same) result.1.2, result.2)
      else _).bind _) = _
    rw [dif_pos rfl, PIR.Process.bind_assoc]
    rfl

/-- The receiver's side at a rewritten draw: its `receive` of the announcement, under a
handler that acts by the mark of the draw, is the rule's draw. -/
theorem receiver_draw_acts {A : Type} (byVerifier prover verifier : Bool)
    (isProver : prover = byVerifier) (isVerifier : verifier = !byVerifier)
    (handler : ThreadHandler model t prover verifier) (place : Place) (number : Nat) (site : Site)
    {inputs : List Ty} {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (after : model.Value output → A)
    (pack : Held (model.Value output) prover → Held (model.Value output) verifier → A)
    (same : ∀ reply, after reply = pack (Held.of prover reply) (Held.of verifier reply))
    (acts : ∀ effect : Effect model.Value, effect.site = site → ∀ state,
      handler effect state =
        threadAct sem (some (.draw byVerifier place number law)) prover verifier effect state)
    (state : ThreadState model t prover verifier) :
    (PIR.Process.call (I := Effects model) (.receive site output)
        fun reply => .done (after reply)).interpretWith handler state =
      (sem.draw prover verifier place number site law state).bind fun result =>
        .done (pack result.1.1 result.1.2, result.2) := by
  subst isProver isVerifier
  cases prover
  · show (handler _ state).bind _ = _
    rw [acts _ rfl state]
    show ((if same : output = output then
        (sem.draw false true place number site law state).bind fun result =>
          PIR.Process.done (cast (congrArg model.Value same) result.1.2, result.2)
      else _).bind _) = _
    rw [dif_pos rfl, PIR.Process.bind_assoc]
    congr 1
    funext result
    exact congrArg (fun packed => PIR.Process.done (packed, result.2)) (same result.1.2)
  · show (handler _ state).bind _ = _
    rw [acts _ rfl state]
    show ((if same : output = output then
        (sem.draw true false place number site law state).bind fun result =>
          PIR.Process.done (cast (congrArg model.Value same) result.1.1, result.2)
      else _).bind _) = _
    rw [dif_pos rfl, PIR.Process.bind_assoc]
    congr 1
    funext result
    exact congrArg (fun packed => PIR.Process.done (packed, result.2)) (same result.1.1)

end Acts


section Fits

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {old new : List ProtocolHeader} {deployed : Bool}
  {t : Threads}

/-- Every protocol of a program is passed by a handler that performs every effect below
its path as it is. -/
theorem Protocols.table_passes {functionTable : FunctionTable model functions}
    (quiet : QuietTable functionTable) (identities : Identities) {protocols : List ProtocolHeader}
    (program : Protocols typeTable operations functions protocols) :
    TablePasses (program.table model functionTable identities) := by
  induction program with
  | nil => exact fun handler _ callee => callee.elimNil
  | snoc earlier definition wellFormed ih =>
      intro S handler header callee
      cases callee with
      | here =>
          intro path side arguments below
          exact region_passes quiet ih _ side below.sites definition.body (fun _ _ => trivial) _
      | there callee => exact ih handler callee

/-! ## Fitting -/

section Parts

variable (threads : Nat → TranscriptRoles → Bool) (callees : MarkTable operations old)
  (place : Place) (whole : Site → Option (Mark operations))

/-- The marks of a sequence of two regions whose sites are pairwise different are, at the
relative sites that start in either, the marks of that one. -/
theorem bind_marks {Γ mid out : List Located}
    (body : Region (ProtocolDialect operations functions old deployed) Γ mid)
    (rest : Region (ProtocolDialect operations functions old deployed) (bindAll Γ mid) out)
    (unique : (regionSites (Region.bind body rest)).Nodup)
    (agrees : ∀ at_ : Site, at_.head ∈ regionSites (Region.bind body rest) →
      whole at_ = regionMarks threads callees place (Region.bind body rest) at_) :
    ((regionSites body).Nodup ∧ ∀ at_ : Site, at_.head ∈ regionSites body →
        whole at_ = regionMarks threads callees place body at_) ∧
      ((regionSites rest).Nodup ∧ ∀ at_ : Site, at_.head ∈ regionSites rest →
        whole at_ = regionMarks threads callees place rest at_) := by
  have split : (regionSites rest ++ regionSites body).Nodup := unique
  obtain ⟨restUnique, bodyUnique, apart⟩ := List.nodup_append.mp split
  refine ⟨⟨bodyUnique, fun at_ inside => ?_⟩, ⟨restUnique, fun at_ inside => ?_⟩⟩
  · rw [agrees at_ (List.mem_append_right _ inside)]
    show (regionMarks threads callees place body at_).or
      (regionMarks threads callees place rest at_) = _
    rw [regionMarks_outside threads callees place rest at_ fun other =>
      apart _ other _ inside rfl, Option.or_none]
  · rw [agrees at_ (List.mem_append_left _ inside)]
    show (regionMarks threads callees place body at_).or
      (regionMarks threads callees place rest at_) = _
    rw [regionMarks_outside threads callees place body at_ fun other =>
      apart _ inside _ other rfl, Option.none_or]

/-- The marks of an operation, its regions and the region after it, when their sites are
pairwise different: at the relative sites that start in one of the three, the marks of
that one. -/
theorem letOp_marks {Γ out : List Located}
    (op : ProtocolOp operations functions old deployed)
    (arguments : Operands Γ (ProtocolOp.arguments op))
    (bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op))
    (rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (ProtocolOp.results op)) out)
    (unique : (regionSites (Region.letOp (dialect := ProtocolDialect operations functions old
      deployed) op arguments bodies rest)).Nodup)
    (agrees : ∀ at_ : Site,
      at_.head ∈ regionSites (Region.letOp (dialect := ProtocolDialect operations functions old
        deployed) op arguments bodies rest) →
      whole at_ = regionMarks threads callees place (Region.letOp (dialect := ProtocolDialect
        operations functions old deployed) op arguments bodies rest) at_) :
    (∀ at_ : Site, at_.head ∈ ProtocolOp.sites op →
        whole at_ = opMarks threads callees place op at_) ∧
      ((regionsSites bodies).Nodup ∧ ∀ at_ : Site, at_.head ∈ regionsSites bodies →
        whole at_ = regionsMarks threads callees place bodies at_) ∧
      ((regionSites rest).Nodup ∧ ∀ at_ : Site, at_.head ∈ regionSites rest →
        whole at_ = regionMarks threads callees place rest at_) := by
  have split : (regionSites rest ++ (regionsSites bodies ++ ProtocolOp.sites op)).Nodup := unique
  obtain ⟨restUnique, nestedUnique, apart⟩ := List.nodup_append.mp split
  obtain ⟨bodiesUnique, _, nestedApart⟩ := List.nodup_append.mp nestedUnique
  have marks : ∀ at_ : Site,
      regionMarks threads callees place (Region.letOp (dialect := ProtocolDialect operations
        functions old deployed) op arguments bodies rest) at_ =
        (opMarks threads callees place op at_).or
          ((regionsMarks threads callees place bodies at_).or
            (regionMarks threads callees place rest at_)) := fun _ => rfl
  refine ⟨fun at_ inside => ?_, ⟨bodiesUnique, fun at_ inside => ?_⟩,
    ⟨restUnique, fun at_ inside => ?_⟩⟩
  · rw [agrees at_ (List.mem_append_right _ (List.mem_append_right _ inside)), marks,
      regionsMarks_outside threads callees place bodies at_ fun other =>
        nestedApart _ other _ inside rfl,
      regionMarks_outside threads callees place rest at_ fun other =>
        apart _ other _ (List.mem_append_right _ inside) rfl,
      Option.or_none, Option.or_none]
  · rw [agrees at_ (List.mem_append_right _ (List.mem_append_left _ inside)), marks,
      opMarks_outside threads callees place op at_ fun other =>
        nestedApart _ inside _ other rfl,
      regionMarks_outside threads callees place rest at_ fun other =>
        apart _ other _ (List.mem_append_left _ inside) rfl,
      Option.or_none, Option.none_or]
  · rw [agrees at_ (List.mem_append_left _ inside), marks,
      opMarks_outside threads callees place op at_ fun other =>
        apart _ inside _ (List.mem_append_right _ other) rfl,
      regionsMarks_outside threads callees place bodies at_ fun other =>
        apart _ inside _ (List.mem_append_left _ other) rfl,
      Option.none_or, Option.none_or]

/-- The marks of the first of several closed regions and of the later ones, when their
sites are pairwise different. -/
theorem cons_marks {inputs outputs : List Located}
    {signatures : List (List Located × List Located)}
    (body : Region (ProtocolDialect operations functions old deployed) (bindAll [] inputs) outputs)
    (tail : Regions (ProtocolDialect operations functions old deployed) signatures)
    (unique : (regionsSites (Regions.cons body tail)).Nodup)
    (agrees : ∀ at_ : Site, at_.head ∈ regionsSites (Regions.cons body tail) →
      whole at_ = regionsMarks threads callees place (Regions.cons body tail) at_) :
    ((regionSites body).Nodup ∧ ∀ at_ : Site, at_.head ∈ regionSites body →
        whole at_ = regionMarks threads callees place body at_) ∧
      ((regionsSites tail).Nodup ∧ ∀ at_ : Site, at_.head ∈ regionsSites tail →
        whole at_ = regionsMarks threads callees place tail at_) := by
  have split : (regionsSites tail ++ regionSites body).Nodup := unique
  obtain ⟨tailUnique, bodyUnique, apart⟩ := List.nodup_append.mp split
  refine ⟨⟨bodyUnique, fun at_ inside => ?_⟩, ⟨tailUnique, fun at_ inside => ?_⟩⟩
  · rw [agrees at_ (List.mem_append_right _ inside)]
    show (regionMarks threads callees place body at_).or
      (regionsMarks threads callees place tail at_) = _
    rw [regionsMarks_outside threads callees place tail at_ fun other =>
      apart _ other _ inside rfl, Option.or_none]
  · rw [agrees at_ (List.mem_append_left _ inside)]
    show (regionMarks threads callees place body at_).or
      (regionsMarks threads callees place tail at_) = _
    rw [regionMarks_outside threads callees place body at_ fun other =>
      apart _ inside _ other rfl, Option.none_or]

end Parts

/-- A handler passes regions of an empty list of signatures. -/
theorem passAll_none {side : Side} {S : Type}
    (handler : PIR.StatefulInterpretation (Effects model) (Effects model) S) :
    ∀ {signatures : List (List Located × List Located)}
      (regions : Values (RegionFunction (SideValue model side) (Effects model)) signatures),
      signatures = [] → PassAll handler regions
  | [], _, _ => trivial

section Operations

variable (rule : Rule t operations functions) {sem : RuleMeaning model t operations}
  {functionTable : FunctionTable model functions} (quiet : QuietTable functionTable)
  {oldTable : ProtocolTable model old} (passes : TablePasses oldTable)
  (table : CalleeTable t.header old new) (marks : MarkTable operations old) {place : Place}
  {side : Side} (one : OneTranscriptRole (side place.roles.prover) (side place.roles.verifier))
  (identity : Nat) {path : List Nat}
  {handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier)}
  {whole : Site → Option (Mark operations)}
  (follows : Follows sem (side place.roles.prover) (side place.roles.verifier) handler path whole)

include quiet passes follows in
/-- A handler that follows marks passes an operation without regions whose site has no
mark. -/
theorem unmarked_operation_passes (op : ProtocolOp operations functions old deployed)
    (closed : ProtocolOp.regions op = [])
    (unmarked : ∀ at_ : Site, at_.head ∈ ProtocolOp.sites op → whole at_ = none) :
    OperationPasses t functionTable oldTable place side (ownSites identity path) handler op :=
  fun arguments regions =>
    operation_passes quiet passes identity side
      (follows.passesSites (· ∈ ProtocolOp.sites op) unmarked) op (fun _ member => member)
      arguments regions (passAll_none handler regions closed)

include quiet passes follows in
/-- A handler that follows marks passes regions without a rewritten operation. -/
theorem untouched_regions_pass {signatures : List (List Located × List Located)}
    (bodies : Regions (ProtocolDialect operations functions old deployed) signatures)
    (untouched : touchesRegions t rule.derives table place.definition (some place.roles.prover)
      (some place.roles.verifier) bodies = .ok false)
    (agrees : ∀ at_ : Site, at_.head ∈ regionsSites bodies →
      whole at_ = regionsMarks table.threads marks place bodies at_) :
    PassRegions t place side handler
      (bodies.denote (labelledMeaning model (ownSites identity path) functionTable oldTable side)) :=
  PassAll.passRegions _
    (regions_pass quiet passes identity side
      (follows.passesSites (· ∈ regionsSites bodies) fun at_ inside =>
        (agrees at_ inside).trans
          (regionsMarks_untouched marks place table rule.derives place.definition bodies untouched
            at_))
      bodies fun _ member => member)

include one follows in
/-- A handler that follows the mark of an exchange from the prover to the verifier acts as
the rule there. -/
theorem exchange_acts (site : Nat) (type : Ty)
    (marked : whole ⟨[], identity, site⟩ = some (.exchange place site)) :
    ExchangeActs (operations := operations) (deployed := deployed) t sem functionTable oldTable
      place side (ownSites identity path) handler site type := by
  intro arguments state
  have acts : ∀ effect : Effect model.Value, effect.site = ownSites identity path site →
      ∀ state, handler effect state =
        threadAct sem (some (.exchange place site)) (side place.roles.prover)
          (side place.roles.verifier) effect state := fun effect own state => by
    rw [← marked]
    exact follows.own identity site effect own state
  rcases one with ⟨isProver, isVerifier⟩ | ⟨isProver, isVerifier⟩
  · rw [labelled_exchange_send isProver isVerifier]
    exact send_acts sem _ _ isProver isVerifier handler place site _ type (arguments.get .here)
      (fun held => (Values.cons held .nil :
        Values (SideValue model side) [⟨type, place.roles.verifier⟩])) acts state
  · rw [labelled_exchange_receive isProver isVerifier]
    exact receive_acts sem _ _ isProver isVerifier handler place site _ type
      (arguments.get .here)
      (fun held => (Values.cons held .nil :
        Values (SideValue model side) [⟨type, place.roles.verifier⟩])) acts state

include one follows in
/-- A handler that follows the mark of a draw by the verifier for the prover acts as the
rule there. -/
theorem draw_by_verifier_acts (site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
    (marked : whole ⟨[], identity, site⟩ = some (.draw true place site law)) :
    DrawByVerifierActs (deployed := deployed) t sem functionTable oldTable place side
      (ownSites identity path) handler site law populated := by
  intro arguments state
  have acts : ∀ effect : Effect model.Value, effect.site = ownSites identity path site →
      ∀ state, handler effect state =
        threadAct sem (some (.draw true place site law)) (side place.roles.prover)
          (side place.roles.verifier) effect state := fun effect own state => by
    rw [← marked]
    exact follows.own identity site effect own state
  rcases one with ⟨isProver, isVerifier⟩ | ⟨isProver, isVerifier⟩
  · rw [labelled_draw_outside isVerifier,
      receiverReplies_present model side _ _ _ _ isProver]
    exact receiver_draw_acts sem true _ _ isProver isVerifier handler place site _ law
      (fun reply => (Values.cons (Held.absent (side place.roles.verifier) isVerifier)
        (Values.cons (Held.of (side place.roles.prover) reply) .nil) :
          Values (SideValue model side)
            [⟨output, place.roles.verifier⟩, ⟨output, place.roles.prover⟩]))
      (fun own other => Values.cons other (Values.cons own .nil))
      (fun reply => cons_congr (Held.eq_absent _ isVerifier _).symm rfl) acts state
  · rw [labelled_draw_owner isVerifier]
    exact owner_draw_acts sem true _ _ isProver isVerifier handler place site _ law populated _
      (fun own other => (Values.cons other (Values.cons own .nil) :
        Values (SideValue model side)
          [⟨output, place.roles.verifier⟩, ⟨output, place.roles.prover⟩])) acts state

include one follows in
/-- A handler that follows the mark of a draw by the prover for the verifier acts as the
rule there. -/
theorem draw_by_prover_acts (site : Nat) {inputs : List Ty} {output : Ty}
    (law : Var operations ⟨inputs, [output], .sampling⟩) (populated : output.populated = true)
    (marked : whole ⟨[], identity, site⟩ = some (.draw false place site law)) :
    DrawByProverActs (deployed := deployed) t sem functionTable oldTable place side
      (ownSites identity path) handler site law populated := by
  intro arguments state
  have acts : ∀ effect : Effect model.Value, effect.site = ownSites identity path site →
      ∀ state, handler effect state =
        threadAct sem (some (.draw false place site law)) (side place.roles.prover)
          (side place.roles.verifier) effect state := fun effect own state => by
    rw [← marked]
    exact follows.own identity site effect own state
  rcases one with ⟨isProver, isVerifier⟩ | ⟨isProver, isVerifier⟩
  · rw [labelled_draw_owner isProver]
    exact owner_draw_acts sem false _ _ isProver isVerifier handler place site _ law populated _
      (fun own other => (Values.cons own (Values.cons other .nil) :
        Values (SideValue model side)
          [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩])) acts state
  · rw [labelled_draw_outside isProver,
      receiverReplies_present model side _ _ _ _ isVerifier]
    exact receiver_draw_acts sem false _ _ isProver isVerifier handler place site _ law
      (fun reply => (Values.cons (Held.absent (side place.roles.prover) isProver)
        (Values.cons (Held.of (side place.roles.verifier) reply) .nil) :
          Values (SideValue model side)
            [⟨output, place.roles.prover⟩, ⟨output, place.roles.verifier⟩]))
      (fun own other => Values.cons own (Values.cons other .nil))
      (fun reply => cons_congr (Held.eq_absent _ isProver _).symm rfl) acts state

include quiet passes one follows in
/-- A handler that follows the marks of a draw does at it what the theorem requires. -/
theorem draw_fits (owner : Nat) (receivers : List Nat) (site : Nat) {inputs : List Ty}
    {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (populated : output.populated = true)
    (agrees : ∀ at_ : Site,
      at_.head ∈ ProtocolOp.sites (functions := functions) (protocols := old)
        (deployed := deployed) (.draw owner receivers site law populated) →
      whole at_ = opMarks (functions := functions) (deployed := deployed) table.threads marks
        place (.draw owner receivers site law populated) at_) :
    DrawFits (deployed := deployed) t sem functionTable oldTable place side
      (ownSites identity path) handler owner receivers site law populated := by
  have own : (⟨[], identity, site⟩ : Site).head ∈
      ProtocolOp.sites (functions := functions) (protocols := old) (deployed := deployed)
        (.draw owner receivers site law populated) := by
    rw [ProtocolOp.sites_draw]
    exact List.mem_singleton_self site
  have different : place.roles.prover ≠ place.roles.verifier := by
    intro same
    rcases one with ⟨isProver, isVerifier⟩ | ⟨isProver, isVerifier⟩
    · rw [same, isVerifier] at isProver
      cases isProver
    · rw [same, isVerifier] at isProver
      cases isProver
  match receivers, agrees, own with
  | [], agrees, _ =>
      exact unmarked_operation_passes quiet passes identity follows _ rfl fun at_ inside =>
        agrees at_ inside
  | _ :: _ :: _, agrees, _ =>
      exact unmarked_operation_passes quiet passes identity follows _ rfl fun at_ inside =>
        agrees at_ inside
  | [receiver], agrees, own =>
      refine ⟨fun isVerifier isProver => ?_, fun _ isProver isVerifier => ?_,
        fun notByVerifier notByProver => ?_⟩
      · subst isVerifier isProver
        refine draw_by_verifier_acts one identity follows site law populated ?_
        rw [agrees _ own, opMarks_draw, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]
      · subst isVerifier isProver
        refine draw_by_prover_acts one identity follows site law populated ?_
        rw [agrees _ own, opMarks_draw, if_pos ⟨rfl, rfl⟩,
          if_neg fun both => different both.1, if_pos ⟨rfl, rfl⟩]
      · refine unmarked_operation_passes quiet passes identity follows _ rfl fun at_ inside => ?_
        rw [agrees at_ inside, opMarks_draw]
        split <;> rfl

include passes one follows in
/-- A handler that follows the marks of an application fits the callee's image that
threads below the site of the application, and passes a callee without one. -/
theorem apply_fits {header : ProtocolHeader} (callee : Var old header) (roleMap : RoleMap)
    (site : Nat) (permitted : (deployed && header.specificationOnly) = false)
    (agrees : ∀ at_ : Site,
      at_.head ∈ ProtocolOp.sites (operations := operations) (functions := functions)
        (.apply callee roleMap site permitted) →
      whole at_ = opMarks (functions := functions) table.threads marks place
        (.apply callee roleMap site permitted) at_) :
    (∀ threaded : ThreadedCallee t new place.roles roleMap header,
      threadedCallee t table place.roles roleMap callee = some threaded →
        ((stepFits sem marks).get callee) threaded.inner (ownSites identity path site).below
          (Side.preimage roleMap side) (side place.roles.prover) (side place.roles.verifier)
          (congrArg side threaded.prover) (congrArg side threaded.verifier) handler) ∧
      (threadedCallee t table place.roles roleMap callee = none →
        ∀ arguments : Values (SideValue model (Side.preimage roleMap side)) header.inputs,
          PIR.Passes handler
            ((oldTable.get callee) (ownSites identity path site).below
              (Side.preimage roleMap side) arguments)) := by
  have below : ∀ (rest : List Nat) (definition number : Nat),
      whole ⟨site :: rest, definition, number⟩ =
        match threadedRoles table.threads place.roles roleMap callee.index with
        | some inner => (marks.get callee) inner ⟨rest, definition, number⟩
        | none => none := fun rest definition number =>
    (agrees _ (by rw [ProtocolOp.sites_apply]; exact List.mem_singleton_self site)).trans
      (opMarks_apply table.threads marks place callee roleMap site permitted rest definition number)
  refine ⟨fun threaded found => ?_, fun missing arguments => ?_⟩
  · rw [stepFits_get]
    refine ⟨one, follows.below site _ fun rest definition number => ?_⟩
    rw [below, threadedRoles_of_callee table place.roles roleMap callee found]
  · refine passes handler callee _ _ arguments fun effect rest under state => ?_
    refine follows.unmarked effect (site :: rest) (by rw [under, List.append_assoc]; rfl) ?_ state
    rw [below, threadedRoles_none table place.roles roleMap callee missing]

/- The statement for closed regions names the four hypotheses only through the statement
for a region, which the linter of section variables does not see. -/
set_option linter.unusedSectionVars false in
include quiet passes one follows in
mutual
  /-- A handler that follows marks fits a region whose sites are pairwise different, when
  the marks are those of the region at every relative site that starts at one of its
  sites. -/
  theorem region_fits_marks {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out),
        (regionSites region).Nodup →
        (∀ at_ : Site, at_.head ∈ regionSites region →
          whole at_ = regionMarks table.threads marks place region at_) →
        Fits t rule sem functionTable oldTable table (stepFits sem marks) place side
          (ownSites identity path) handler region
    | .ret _, _, _ => trivial
    | .stop _, _, _ => trivial
    | .bind body rest, unique, agrees => by
        have parts := bind_marks table.threads marks place whole body rest unique agrees
        exact And.intro (region_fits_marks body parts.1.1 parts.1.2)
          (region_fits_marks rest parts.2.1 parts.2.2)
    | .letOp (.at role op localBodies) arguments bodies rest, unique, agrees => by
        have parts := letOp_marks table.threads marks place whole
          (.at role op localBodies) arguments bodies rest unique agrees
        exact region_fits_marks rest parts.2.2.1 parts.2.2.2
    | .letOp (.sample owner site law populated) arguments bodies rest, unique, agrees => by
        have parts := letOp_marks table.threads marks place whole
          (.sample owner site law populated) arguments bodies rest unique agrees
        exact And.intro
          (unmarked_operation_passes quiet passes identity follows _ rfl fun at_ inside =>
            parts.1 at_ inside)
          (region_fits_marks rest parts.2.2.1 parts.2.2.2)
    | .letOp (.exchange sender receiver site type) arguments bodies rest, unique, agrees => by
        have parts := letOp_marks table.threads marks place whole
          (.exchange sender receiver site type) arguments bodies rest unique agrees
        have own : (⟨[], identity, site⟩ : Site).head ∈
            ProtocolOp.sites (operations := operations) (functions := functions)
              (protocols := old) (deployed := deployed) (.exchange sender receiver site type) := by
          rw [ProtocolOp.sites_exchange]
          exact List.mem_singleton_self site
        refine And.intro (fun isProver isVerifier => ?_) (And.intro (fun other => ?_)
          (region_fits_marks rest parts.2.2.1 parts.2.2.2))
        · subst isProver isVerifier
          refine exchange_acts one identity follows site type ?_
          rw [parts.1 _ own, opMarks_exchange, if_pos ⟨rfl, rfl, rfl, rfl⟩]
        · refine unmarked_operation_passes quiet passes identity follows _ rfl fun at_ inside => ?_
          rw [parts.1 at_ inside, opMarks_exchange]
          exact if_neg fun marked => other ⟨marked.1, marked.2.1⟩
    | .letOp (.draw owner receivers site law populated) arguments bodies rest, unique, agrees => by
        have parts := letOp_marks table.threads marks place whole
          (.draw owner receivers site law populated) arguments bodies rest unique agrees
        exact And.intro
          (draw_fits quiet passes table marks one identity follows owner receivers site law
            populated parts.1)
          (region_fits_marks rest parts.2.2.1 parts.2.2.2)
    | .letOp (.repeat participants count carried collected captures covered) arguments bodies rest,
        unique, agrees => by
        have parts := letOp_marks table.threads marks place whole
          (.repeat participants count carried collected captures covered) arguments bodies rest unique agrees
        exact And.intro (fun _ => regions_fit_marks bodies parts.2.1.1 parts.2.1.2)
          (And.intro
            (fun untouched => untouched_regions_pass rule quiet passes table marks identity follows
              bodies untouched parts.2.1.2)
            (region_fits_marks rest parts.2.2.1 parts.2.2.2))
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, unique,
        agrees => by
        have parts := letOp_marks table.threads marks place whole
          (.choose participants tag captures outputs covered) arguments bodies rest unique agrees
        exact And.intro (fun _ => regions_fit_marks bodies parts.2.1.1 parts.2.1.2)
          (And.intro
            (fun untouched => untouched_regions_pass rule quiet passes table marks identity follows
              bodies untouched parts.2.1.2)
            (region_fits_marks rest parts.2.2.1 parts.2.2.2))
    | .letOp (.apply callee roleMap site permitted) arguments bodies rest, unique, agrees => by
        have parts := letOp_marks table.threads marks place whole
          (.apply callee roleMap site permitted) arguments bodies rest unique agrees
        have applied := apply_fits passes table marks one identity follows callee roleMap site
          permitted parts.1
        exact And.intro applied.1 (And.intro applied.2
          (region_fits_marks rest parts.2.2.1 parts.2.2.2))

  /-- The same for closed regions. -/
  theorem regions_fit_marks {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures),
        (regionsSites regions).Nodup →
        (∀ at_ : Site, at_.head ∈ regionsSites regions →
          whole at_ = regionsMarks table.threads marks place regions at_) →
        FitsAll t rule sem functionTable oldTable table (stepFits sem marks) place side
          (ownSites identity path) handler regions
    | .nil, _, _ => trivial
    | .cons body tail, unique, agrees => by
        have parts := cons_marks table.threads marks place whole body tail unique agrees
        exact And.intro (region_fits_marks body parts.1.1 parts.1.2)
          (regions_fit_marks tail parts.2.1 parts.2.2)
end

end Operations

/-- A handler that follows the marks of a region fits the region. -/
theorem region_fits (rule : Rule t operations functions) (sem : RuleMeaning model t operations)
    {functionTable : FunctionTable model functions} (quiet : QuietTable functionTable)
    {oldTable : ProtocolTable model old} (passes : TablePasses oldTable)
    (table : CalleeTable t.header old new) (marks : MarkTable operations old) (place : Place)
    (side : Side) (one : OneTranscriptRole (side place.roles.prover) (side place.roles.verifier))
    (identity : Nat) (path : List Nat)
    (handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier))
    {Γ out : List Located}
    (region : Region (ProtocolDialect operations functions old deployed) Γ out)
    (unique : (regionSites region).Nodup)
    (follows : Follows sem (side place.roles.prover) (side place.roles.verifier) handler path
      (regionMarks table.threads marks place region)) :
    Fits t rule sem functionTable oldTable table (stepFits sem marks) place side
      (ownSites identity path) handler region :=
  region_fits_marks rule quiet passes table marks one identity follows region unique
    fun _ _ => rfl

end Fits

end Zkc.Core
