module

public import Zkc.Core.Thread

public section

/-! Which effects a threading step rewrites.

A handler of a side's effects sees an effect and its site, and nothing of the operation
that performed it. `Mark` says what the step did at a site: it rewrote an exchange from
the prover to the verifier, or a draw between the two. The marks of a definition's image
for a pair of transcript roles are a function of the site of an effect relative to the
definition: the path of applications below the definition, then the definition and the
site number of the operation.

- `opMarks`, `regionMarks`: the marks of an operation and of a region. An exchange from
  the prover to the verifier and a draw between the two with one receiver are marked at
  their own site, with an empty path. An application of a callee that has an image that
  threads for the preimages of the two roles has the callee's marks, below its site.
  Every other site has no mark.
- `MarkTable`: for every protocol of a program, its marks for every pair of roles.

The sites of a well-formed definition are pairwise different, so at most one operation of
a region marks a site; `regionMarks` returns the first mark it finds.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The site of an effect. -/
@[expose] def Effect.site {Value : Ty → Type} : Effect Value → Site
  | .send site .. => site
  | .receive site _ => site
  | .draw site .. => site
  | .sample site .. => site
  | .read site .. => site

/-- What a threading step did at a site: the place of the rewritten operation, its site
number, and for a draw its law and whether the verifier owned it. -/
inductive Mark (operations : List OperationSignature) where
  | exchange (place : Place) (site : Nat)
  | draw (byVerifier : Bool) (place : Place) (site : Nat) {inputs : List Ty} {output : Ty}
      (law : Var operations ⟨inputs, [output], .sampling⟩)

namespace CalleeTable

variable {K : Type} [DecidableEq K] {F : K → ProtocolHeader → ProtocolHeader}
  {old new : List ProtocolHeader}

/-- Whether the protocol at a position has an image for a key. -/
@[expose] def has (table : CalleeTable F old new) (index : Nat) (key : K) : Bool :=
  match table.images.get? index with
  | some list => (levelOf key list).isSome
  | none => false

/-- A callee has an image for a key exactly when the table has one at its position. -/
theorem find_isSome (table : CalleeTable F old new) {header : ProtocolHeader}
    (callee : Var old header) (key : K) :
    (table.find callee key).isSome = table.has callee.index key := by
  have atPosition : ∀ entry, table.images.get? callee.index = entry →
      table.has callee.index key =
        match entry with
        | some list => (levelOf key list).isSome
        | none => false := by
    intro entry same
    subst same
    rfl
  unfold find
  split
  · rename_i missing
    rw [atPosition none missing]
    rfl
  · rename_i list found
    rw [atPosition (some list) found]
    split
    · rename_i missing
      show _ = (levelOf key list).isSome
      rw [missing]
      rfl
    · rename_i level member recorded
      show _ = (levelOf key list).isSome
      rw [recorded]
      rfl

end CalleeTable

/-- Whether the protocol at a position has an image that threads for a pair of roles. -/
@[expose] def CalleeTable.threads {t : Threads} {old new : List ProtocolHeader}
    (table : CalleeTable t.header old new) : Nat → TranscriptRoles → Bool :=
  fun index roles => table.has index (some roles)

/-- The transcript roles of the image that threads of an applied protocol: the preimages
of the caller's two roles, when both exist and the callee has an image for them. -/
@[expose] def threadedRoles (threads : Nat → TranscriptRoles → Bool) (roles : TranscriptRoles)
    (roleMap : RoleMap) (callee : Nat) : Option TranscriptRoles :=
  match preimage roleMap roles.prover, preimage roleMap roles.verifier with
  | some prover, some verifier =>
      if threads callee ⟨prover.val, verifier.val⟩ then some ⟨prover.val, verifier.val⟩ else none
  | _, _ => none

/-- For every protocol of a program, the most recent first: its marks for a pair of
transcript roles, at a site relative to the protocol. -/
abbrev MarkTable (operations : List OperationSignature) (protocols : List ProtocolHeader) : Type :=
  Values (fun _ : ProtocolHeader => TranscriptRoles → Site → Option (Mark operations)) protocols

/-- The marks of the protocol at a position. -/
@[expose] def MarkTable.at {operations : List OperationSignature} :
    {protocols : List ProtocolHeader} → MarkTable operations protocols → Nat →
      TranscriptRoles → Site → Option (Mark operations)
  | [], _, _ => fun _ _ => none
  | _ :: _, marks, 0 => marks.get .here
  | _ :: _, marks, index + 1 => MarkTable.at marks.tail index

section Marks

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old : List ProtocolHeader} {deployed : Bool}
variable (threads : Nat → TranscriptRoles → Bool) (callees : MarkTable operations old)
  (place : Place)

/-- The mark of one operation at a site relative to its definition. -/
@[expose] def opMarks :
    ProtocolOp operations functions old deployed → Site → Option (Mark operations)
  | .exchange sender receiver site _, at_ =>
      if sender = place.roles.prover ∧ receiver = place.roles.verifier ∧ at_.path = [] ∧
          at_.number = site then some (.exchange place site)
      else none
  | .draw owner [receiver] site law _, at_ =>
      if at_.path = [] ∧ at_.number = site then
        if owner = place.roles.verifier ∧ receiver = place.roles.prover then
          some (.draw true place site law)
        else if owner = place.roles.prover ∧ receiver = place.roles.verifier then
          some (.draw false place site law)
        else none
      else none
  | .apply callee roleMap site _, at_ =>
      match at_.path with
      | first :: rest =>
          if first = site then
            match threadedRoles threads place.roles roleMap callee.index with
            | some inner => (callees.get callee) inner ⟨rest, at_.definition, at_.number⟩
            | none => none
          else none
      | [] => none
  | _, _ => none

mutual
  /-- The mark of a region at a site relative to its definition: the first mark of its
  operations, nested regions included. -/
  @[expose] def regionMarks {Γ out : List Located} :
      Region (ProtocolDialect operations functions old deployed) Γ out → Site →
        Option (Mark operations)
    | .ret _, _ => none
    | .stop _, _ => none
    | .bind body rest, at_ =>
        (regionMarks body at_).or (regionMarks rest at_)
    | .letOp op _ bodies rest, at_ =>
        (opMarks threads callees place op at_).or
          ((regionsMarks bodies at_).or (regionMarks rest at_))

  @[expose] def regionsMarks {signatures : List (List Located × List Located)} :
      Regions (ProtocolDialect operations functions old deployed) signatures → Site →
        Option (Mark operations)
    | .nil, _ => none
    | .cons body tail, at_ =>
        (regionMarks body at_).or (regionsMarks tail at_)
end

end Marks

end Zkc.Core
