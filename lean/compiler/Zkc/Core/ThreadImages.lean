module

public import Zkc.Core.ThreadFits

public section

/-! The images of one definition under a threading step, and what holds of them.

A step makes the images of a definition one after the other (`rewriteDefinition`); each
image is one more protocol of the result, typed over the protocols before it.

- `Protocols.table_image`: the meanings of the protocols of the result after one more
  image are the meanings before it and the meaning of the image, with the identity of the
  image's definition (`originIdentities`).
- `ImagesHold`: a statement about the callees and a statement about every image of the
  definition that the callee table will record hold of the images made so far. Both
  statements are parameters: the whole-program theorems use it once for the images that
  copy and once for the images that thread.
- `Images.add_holds`, `Images.addEntry_holds`, `plainImage_holds`, `rewriteDefinition_holds`:
  the images after one more image, and after every image of a definition, keep it, when
  the statement about the callees survives one more protocol of the result and holds of an
  image that threads and of an image that copies.
- `MarkTable.at_index`: the marks at the position of a reference are the marks of the
  reference.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-- The marks of the protocol at the position of a reference. -/
theorem MarkTable.at_index {operations : List OperationSignature} :
    ∀ {protocols : List ProtocolHeader} (marks : MarkTable operations protocols)
      {header : ProtocolHeader} (callee : Var protocols header),
      MarkTable.at marks callee.index = marks.get callee
  | [], _, _, callee => callee.elimNil
  | _ :: _, marks, _, callee => by
      cases callee with
      | here => rfl
      | there callee =>
          match marks with
          | .cons _ rest => exact MarkTable.at_index rest callee

section Tables

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {functionTable : FunctionTable model functions}

/-- The meanings of the protocols of a program depend on the identities of its protocols
only. -/
theorem Protocols.table_congr {identities other : Identities} :
    ∀ {protocols : List ProtocolHeader}
      (program : Protocols typeTable operations functions protocols),
      (∀ number, number < protocols.length → identities number = other number) →
        program.table model functionTable identities = program.table model functionTable other
  | _, .nil, _ => rfl
  | _, .snoc (protocols := earlierHeaders) earlier definition _, same => by
      show Values.cons _ _ = Values.cons _ _
      rw [Protocols.table_congr earlier fun number below => same number (Nat.lt_succ_of_lt below),
        same earlierHeaders.length (Nat.lt_succ_self _)]

/-- Below the number of the earlier origins, one more origin changes no identity. -/
theorem originIdentities_earlier (origin : Origin) (origins : List Origin) {number : Nat}
    (below : number < origins.length) :
    originIdentities (origin :: origins) number = originIdentities origins number :=
  if_neg (Nat.ne_of_lt below)

/-- The protocol of the newest origin has the identity of its definition. -/
theorem originIdentities_newest (origin : Origin) (origins : List Origin) :
    originIdentities (origin :: origins) origins.length = origin.definition :=
  if_pos rfl

/-- The meanings of the protocols of a result after one more image: the meanings before
it, and the meaning of the image with the identity of its definition. -/
theorem Protocols.table_image {new : List ProtocolHeader}
    (protocols : Protocols typeTable operations functions new) {header : ProtocolHeader}
    (definition : ProtocolDefinition operations functions new header)
    (wellFormed : definition.violation typeTable = none) (origin : Origin) (origins : List Origin)
    (counted : origins.length = new.length) :
    (Protocols.snoc protocols definition wellFormed).table model functionTable
        (originIdentities (origin :: origins)) =
      .cons (definition.meaning model functionTable
          (protocols.table model functionTable (originIdentities origins)) origin.definition)
        (protocols.table model functionTable (originIdentities origins)) := by
  show Values.cons _ _ = _
  rw [Protocols.table_congr protocols (other := originIdentities origins) fun number below =>
      originIdentities_earlier origin origins (counted ▸ below),
    ← counted, originIdentities_newest]

end Tables

section Images

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {t : Threads} {old : List ProtocolHeader}
  {header : ProtocolHeader}
variable (model : Model) (functionTable : FunctionTable model functions)

/-- The meanings of the images made so far and of the protocols before them. -/
@[expose] def Images.meanings (images : Images t typeTable operations functions old header) :
    ProtocolTable model images.new :=
  images.protocols.table model functionTable (originIdentities images.origins)

/-- What holds of the images made so far: `Callees` of the table of the earlier
definitions and the meanings of the protocols made so far, and `Image` of the meaning of
every image of the definition that the table will record, by its key. -/
structure ImagesHold
    (Callees : {new : List ProtocolHeader} → CalleeTable t.header old new →
      ProtocolTable model new → Prop)
    (Image : (key : Option TranscriptRoles) → (t.header key header).Meaning model → Prop)
    (images : Images t typeTable operations functions old header) : Prop where
  callees : Callees images.table (images.meanings model functionTable)
  own : ∀ (key : Option TranscriptRoles) (level : Nat), (key, level) ∈ images.list →
    ∀ image : Var images.new (t.header key header),
      image.index = images.table.depth - 1 - level →
        Image key ((images.meanings model functionTable).get image)

variable {model} {functionTable}
  {Callees : {new : List ProtocolHeader} → CalleeTable t.header old new →
    ProtocolTable model new → Prop}
  {Image : (key : Option TranscriptRoles) → (t.header key header).Meaning model → Prop}

/-- The images made before one more protocol of the result keep what holds of them. -/
theorem ImagesHold.earlier
    {images : Images t typeTable operations functions old header}
    (holds : ImagesHold model functionTable Callees Image images) (added : ProtocolHeader)
    (meaning : added.Meaning model) (key : Option TranscriptRoles) (level : Nat)
    (member : (key, level) ∈ images.list)
    (image : Var (added :: images.new) (t.header key header))
    (at_ : image.index = images.table.depth + 1 - 1 - level) :
    Image key ((Values.cons meaning (images.meanings model functionTable)).get image) := by
  have valid := images.valid (key, level) member
  have below : level < images.table.depth := by
    unfold atLevel? at valid
    split at valid
    · assumption
    · cases valid
  have position : images.new[images.table.depth - 1 - level]? = some (t.header key header) := by
    unfold atLevel? at valid
    simpa only [below, ↓reduceIte] using valid
  have there : image = (Var.mk (images.table.depth - 1 - level) position).there := by
    apply Var.ext
    rw [at_]
    show images.table.depth + 1 - 1 - level = images.table.depth - 1 - level + 1
    omega
  subst there
  exact holds.own key level member ⟨_, position⟩ rfl

/-- One more image of the definition keeps what holds, when `Image` holds of it. -/
theorem Images.add_holds
    (weakens : ∀ {new : List ProtocolHeader} (table : CalleeTable t.header old new)
      (newTable : ProtocolTable model new) (added : ProtocolHeader)
      (meaning : added.Meaning model),
      Callees table newTable → Callees (table.weaken added) (.cons meaning newTable))
    {images : Images t typeTable operations functions old header}
    (holds : ImagesHold model functionTable Callees Image images) {key : Option TranscriptRoles}
    {body : Region
      (ProtocolDialect operations functions images.new (!(t.header key header).specificationOnly))
      (bindAll [] (t.header key header).inputs) (t.header key header).outputs}
    {origin : Origin} {result : Images t typeTable operations functions old header}
    (adds : images.add key body origin = .ok result)
    (good : Image key
      ((⟨body⟩ : ProtocolDefinition operations functions images.new (t.header key header)).meaning
        model functionTable (images.meanings model functionTable) origin.definition)) :
    ImagesHold model functionTable Callees Image result := by
  unfold Images.add at adds
  split at adds
  · rename_i wellFormed
    have same := Except.ok.inj adds
    subst same
    have meanings := Protocols.table_image (model := model) (functionTable := functionTable)
      images.protocols ⟨body⟩ wellFormed origin images.origins images.counted
    refine ⟨?_, ?_⟩
    · show Callees (images.table.weaken _) (Protocols.table model functionTable _ _)
      rw [meanings]
      exact weakens _ _ _ _ holds.callees
    · intro other level member image at_
      show Image other ((Protocols.table model functionTable _ _).get image)
      rw [meanings]
      rcases List.mem_cons.mp member with same | earlier
      · cases same
        have here : image = Var.here := by
          apply Var.ext
          rw [at_]
          show images.table.depth + 1 - 1 - images.table.depth = 0
          omega
        subst here
        exact good
      · exact holds.earlier _ _ other level earlier image at_
  · cases adds

/-- The image of the entry, which the callee table does not record, keeps what holds. -/
theorem Images.addEntry_holds
    (weakens : ∀ {new : List ProtocolHeader} (table : CalleeTable t.header old new)
      (newTable : ProtocolTable model new) (added : ProtocolHeader)
      (meaning : added.Meaning model),
      Callees table newTable → Callees (table.weaken added) (.cons meaning newTable))
    {images : Images t typeTable operations functions old header}
    (holds : ImagesHold model functionTable Callees Image images) {ports : EntryPorts}
    {body : Region (ProtocolDialect operations functions images.new (!header.specificationOnly))
      (bindAll [] ports.inputs) ports.outputs}
    {origin : Origin} {result : Images t typeTable operations functions old header}
    (adds : images.addEntry ports body origin = .ok result) :
    ImagesHold model functionTable Callees Image result := by
  unfold Images.addEntry at adds
  split at adds
  · rename_i wellFormed
    have same := Except.ok.inj adds
    subst same
    have meanings := Protocols.table_image (model := model) (functionTable := functionTable)
      images.protocols (header := ports.header header) ⟨body⟩ wellFormed origin images.origins
      images.counted
    refine ⟨?_, ?_⟩
    · show Callees (images.table.weaken _) (Protocols.table model functionTable _ _)
      rw [meanings]
      exact weakens _ _ _ _ holds.callees
    · intro other level member image at_
      show Image other ((Protocols.table model functionTable _ _).get image)
      rw [meanings]
      exact holds.earlier _ _ other level member image at_
  · cases adds

variable {rule : Rule t operations functions}

/-- The image with the definition's own header keeps what holds, when `Image` holds of a
copy of the definition. -/
theorem plainImage_holds
    (weakens : ∀ {new : List ProtocolHeader} (table : CalleeTable t.header old new)
      (newTable : ProtocolTable model new) (added : ProtocolHeader)
      (meaning : added.Meaning model),
      Callees table newTable → Callees (table.weaken added) (.cons meaning newTable))
    (number : Nat) (definition : ProtocolDefinition operations functions old header)
    (copied : ∀ (images : Images t typeTable operations functions old header)
      (body : Region (ProtocolDialect operations functions images.new (!header.specificationOnly))
        (bindAll [] header.inputs) header.outputs),
      Callees images.table (images.meanings model functionTable) →
      plainRegion t images.table definition.body (Renaming.identity header.inputs) = .ok body →
      Image none
        ((⟨body⟩ : ProtocolDefinition operations functions images.new header).meaning model
          functionTable (images.meanings model functionTable) number))
    (made : Bool) (images result : Images t typeTable operations functions old header)
    (copies : plainImage t number definition made images = .ok result)
    (holds : ImagesHold model functionTable Callees Image images) :
    ImagesHold model functionTable Callees Image result := by
  unfold plainImage at copies
  split at copies
  · exact Except.ok.inj copies ▸ holds
  · split at copies
    · rename_i body copiesBody
      exact Images.add_holds weakens holds copies (copied images body holds.callees copiesBody)
    · cases copies

/-- Every image of a definition keeps what holds, when `Image` holds of an image that
threads and of a copy of the definition. -/
theorem rewriteDefinition_holds
    (weakens : ∀ {new : List ProtocolHeader} (table : CalleeTable t.header old new)
      (newTable : ProtocolTable model new) (added : ProtocolHeader)
      (meaning : added.Meaning model),
      Callees table newTable → Callees (table.weaken added) (.cons meaning newTable))
    (number : Nat) (definition : ProtocolDefinition operations functions old header)
    (specialized : Bool)
    (threaded : ∀ (images : Images t typeTable operations functions old header)
      (roles : TranscriptRoles)
      (body : Region
        (ProtocolDialect operations functions images.new
          (!(t.header (some roles) header).specificationOnly))
        (bindAll [] (t.header (some roles) header).inputs) (t.header (some roles) header).outputs),
      Callees images.table (images.meanings model functionTable) →
      threadRegion t rule images.table ⟨number, roles, specialized⟩ definition.body
          (afterTwo (t.first roles) (t.second roles)
            (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).1
          (afterTwo (t.first roles) (t.second roles)
            (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).2.1
          (afterTwo (t.first roles) (t.second roles)
            (Mapping.start (Δ := ([] : List Located)) 0 rfl) header.inputs).2.2 = .ok body →
      Image (some roles)
        ((⟨body⟩ : ProtocolDefinition operations functions images.new
          (t.header (some roles) header)).meaning model functionTable
            (images.meanings model functionTable) number))
    (copied : ∀ (images : Images t typeTable operations functions old header)
      (body : Region (ProtocolDialect operations functions images.new (!header.specificationOnly))
        (bindAll [] header.inputs) header.outputs),
      Callees images.table (images.meanings model functionTable) →
      plainRegion t images.table definition.body (Renaming.identity header.inputs) = .ok body →
      Image none
        ((⟨body⟩ : ProtocolDefinition operations functions images.new header).meaning model
          functionTable (images.meanings model functionTable) number))
    (classified : List (Demand × Bool)) (made : Bool)
    (images result : Images t typeTable operations functions old header)
    (rewrites : rewriteDefinition t rule number definition specialized classified made images =
      .ok result)
    (holds : ImagesHold model functionTable Callees Image images) :
    ImagesHold model functionTable Callees Image result := by
  fun_induction rewriteDefinition t rule number definition specialized classified made images with
  | case1 => exact Except.ok.inj rewrites ▸ holds
  | case2 prover verifier rest made images place start body threads next adds ih =>
      exact ih rewrites
        (Images.add_holds weakens holds adds (threaded images _ body holds.callees threads))
  | case6 roles active rest made images _ place body _ next adds _ ih =>
      exact ih rewrites (Images.addEntry_holds weakens holds adds)
  | case9 roles active rest made images _ next copies _ ih =>
      exact ih rewrites (plainImage_holds weakens number definition copied _ _ _ copies holds)
  | case11 prover verifier active rest made images _ next copies ih =>
      exact ih rewrites (plainImage_holds weakens number definition copied _ _ _ copies holds)
  | case3 | case4 | case5 | case7 | case8 | case10 | case12 => cases rewrites

end Images

end Zkc.Core
