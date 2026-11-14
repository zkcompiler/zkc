module

public import Zkc.Core.SerializeReplayOperations
public import Zkc.Core.SerializeReplayCarries
public import Zkc.Core.LegalStep
public import Zkc.Core.LegalProject
public import Zkc.Core.ThreadRules

public section

/-! The parts of a region of a program that is serialized replay its grouped run.

Two statements about a region of a definition of the program that the serialize step
accepts, for two disjoint sides of which the first holds the prover and no other role of
the definition and the second the verifier and no other role (`Side.Holds`):

- `region_admits_plain`: a region without a rewritten operation, for roles of which either
  may be absent. Its operations are related under the handlers that perform every effect as
  it is: no message passes between the two parts. An exchange from the prover to the
  verifier would be rewritten, and one from the verifier to the prover or a draw between the
  two is refused, so neither occurs.
- `region_admits`: a region of a definition that the step threads, under two handlers that
  fit it (`Fits`, which holds of every handler that follows the marks of the step), when the
  layout carries the type of every exchange from the prover to the verifier of the region
  (`RegionCarries`, which holds of every region of which the step made a threaded image).
  At such an exchange the prover's handler puts the value on its writer and the verifier's
  handler takes it from its reader (`exchange_forward`); the handlers pass every other
  operation, every region that the step copies and every callee without an image that
  threads, which are related by the first statement.

Both take the statement for the callees of the region as a premise, keyed by the roles that
an application gives its callee (`CalleeReplays`): `ThreadedReplays` for a callee with an
image that threads for them, `PlainReplays` otherwise.

`serializeChannel` is the channel of the step: a message can be carried when its value is
one that the layout can write (`Layout.Lawful.Writable`); the prover's state gains the
messages that its writer was given (`Layout.Written`), each of a type that has the rows and
of a value that the layout can write (`Layout.Lawful.Sendable`), and the verifier's state
gives the messages that its reader returns (`Layout.Takes`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Zkc.Core

open Zkc.Source

/-! ## Sides that hold one role -/

/-- Among the roles below a bound, the side has the role as its only member, or no member
when there is no role. -/
@[expose] def Side.Holds (side : Side) (role : Option Nat) (bound : Nat) : Prop :=
  ∀ other, Nat.blt other bound = true → side other = isRole role other

theorem natBeq_swap (first second : Nat) : Nat.beq first second = Nat.beq second first := by
  rw [Bool.eq_iff_iff]
  exact ⟨fun same => by rw [Nat.eq_of_beq_eq_true same]; exact Nat.beq_refl _,
    fun same => by rw [Nat.eq_of_beq_eq_true same]; exact Nat.beq_refl _⟩

/-- A member, below the bound, of a side that holds a role is the role. -/
theorem Side.Holds.member {side : Side} {role bound other : Nat}
    (holds : side.Holds (some role) bound) (below : Nat.blt other bound = true)
    (inside : side other = true) : other = role := by
  rw [holds other below] at inside
  exact (Nat.eq_of_beq_eq_true inside).symm

/-- A search for a preimage that finds none: no index below the bound runs as the role. -/
theorem preimageBelow_none (roleMap : RoleMap) (role : Nat) :
    ∀ (bound : Nat), preimageBelow roleMap role bound = none →
      ∀ index, index < bound → roleMap.apply index ≠ role
  | 0, _, _, below => absurd below (Nat.not_lt_zero _)
  | bound + 1, missing, index, below => by
      unfold preimageBelow at missing
      split at missing
      · cases missing
      · rename_i other
        rcases Nat.lt_succ_iff_lt_or_eq.mp below with earlier | same
        · exact preimageBelow_none roleMap role bound missing index earlier
        · rw [same]
          exact other

/-- The callee's side of an application holds the callee role that runs as the role that
the caller's side holds, when the role map is that of an application without a violation. -/
theorem Side.Holds.callee {side : Side} {role : Option Nat} {bound : Nat}
    (holds : side.Holds role bound) {roleMap : RoleMap} {roles : Nat}
    (below : ∀ entry ∈ roleMap, Nat.blt entry bound = true) (length : roleMap.length = roles)
    (distinct : distinctNumbers roleMap = true) :
    (Side.preimage roleMap side).Holds (preimageOf roleMap role) roles := by
  intro other otherBelow
  have within : other < roleMap.length := by
    rw [length]
    exact Nat.blt_eq.mp otherBelow
  show side (roleMap.apply other) = _
  rw [holds _ (below _ (RoleMap.apply_mem roleMap other within))]
  cases role with
  | none => rfl
  | some role =>
      show Nat.beq role (roleMap.apply other) = isRole ((Zkc.Core.preimage roleMap role).map (·.val)) other
      cases found : Zkc.Core.preimage roleMap role with
      | none =>
          show _ = false
          have differs := preimageBelow_none roleMap role roleMap.length found other within
          cases same : Nat.beq role (roleMap.apply other) with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true same).symm differs
      | some index =>
          show _ = Nat.beq index.val other
          have indexBelow := preimageBelow_lt roleMap role roleMap.length index found
          have atIndex := formalRole_decides role roleMap distinct index.val indexBelow
          rw [index.property, Nat.beq_refl] at atIndex
          have isFormal : index.val = formalRole role roleMap := Nat.eq_of_beq_eq_true atIndex.symm
          rw [natBeq_swap role, formalRole_decides role roleMap distinct other within, ← isFormal,
            natBeq_swap]

/-! ## Values of a present holder -/

theorem Held.of_value {X : Type} :
    ∀ (present : Bool) (member : present = true) (held : Held X present),
      Held.of present (Held.value present member held) = held
  | true, _, _ => rfl

theorem Held.value_inj {X : Type} :
    ∀ (present : Bool) (member : present = true) (one other : Held X present),
      Held.value present member one = Held.value present member other → one = other
  | true, _, _, _, same => same

/-! ## The channel of the serialize step -/

section Channel

variable {model : Model} {operations : List OperationSignature}

/-- The channel of the serialize step, over the states of the two handlers. A message can be
carried when its value is one that the layout can write. The prover's state gains the
messages that its writer was given, each of a type that has the rows and of a value that the
layout can write, and the verifier's state gives the messages that its reader returns. Each
state keeps its other component. -/
@[expose] def serializeChannel (layout : Layout operations) (laws : layout.Lawful model)
    (proverWrites proverReads verifierWrites verifierReads : Bool) (writes : proverWrites = true)
    (reads : verifierReads = true) :
    Channel model (ThreadState model layout.threads proverWrites proverReads)
      (ThreadState model layout.threads verifierWrites verifierReads) where
  Sendable := laws.Writable
  Written := fun state messages final =>
    layout.Written model (Held.value proverWrites writes state.1) messages
        (Held.value proverWrites writes final.1) ∧
      final.2 = state.2 ∧ ∀ message ∈ messages, laws.Sendable message.1 message.2
  Takes := fun state messages final =>
    layout.Takes model (Held.value verifierReads reads state.2) messages
        (Held.value verifierReads reads final.2) ∧ final.1 = state.1
  written_nil := fun state => ⟨.nil _, rfl, fun _ member => nomatch member⟩
  written_append := fun before after =>
    ⟨before.1.append after.1, after.2.1.trans before.2.1, fun message member =>
      (List.mem_append.mp member).elim (before.2.2 message) (after.2.2 message)⟩
  takes_nil := fun {reader final} takes =>
    Prod.ext takes.2 (Held.value_inj verifierReads reads _ _ takes.1.nil_inv)
  takes_append := fun {reader final first second} takes => by
    obtain ⟨middle, before, after⟩ := takes.1.split
    refine ⟨(reader.1, Held.of verifierReads middle), ⟨?_, rfl⟩, ?_, takes.2⟩
    · rw [Held.value_of]
      exact before
    · rw [Held.value_of]
      exact after

/-- Taking one message: the row that takes its type gives `true`, the value and the reader
that is left. -/
theorem Layout.Takes.single {layout : Layout operations} {type : Ty} {value : model.Value type}
    {reader final : model.Value layout.reader}
    (takes : layout.Takes model reader [⟨type, value⟩] final) :
    ∃ take populated, layout.take type = some take ∧
      model.pure (.of take) populated (.cons reader .nil) =
        .cons true (.cons value (.cons final .nil)) := by
  cases takes with
  | cons take populated row taken later =>
      cases later
      exact ⟨take, populated, row, taken⟩

/-- What the serialize rule does at an exchange for the side of the prover: it puts the
value on the writer. -/
theorem serializeMeaning_exchange_prover (layout : Layout operations) :
    ∀ (prover verifier : Bool) (isProver : prover = true) (isVerifier : verifier = false)
      (place : Place) (number : Nat) (site : Site) (type : Ty)
      (put : Var operations ⟨[layout.writer, type], [layout.writer], .pure⟩)
      (take : Var operations ⟨[layout.reader], [.bool, type, layout.reader], .pure⟩)
      (populated : Ty.allPopulated [.bool, type, layout.reader] = true)
      (hasPut : layout.put type = some put) (hasTake : layout.take type = some take)
      (value : Held (model.Value type) prover)
      (state : ThreadState model layout.threads prover verifier),
      (serializeMeaning (model := model) layout).exchange prover verifier place number site type
          value state =
        .done (Held.absent verifier isVerifier,
          (Held.of prover (layout.putValue model put (Held.value prover isProver state.1)
            (Held.value prover isProver value)), state.2))
  | true, false, _, _, place, number, site, type, put, take, populated, hasPut, hasTake, value,
      state => by
      simp only [serializeMeaning, dif_pos populated, hasPut, hasTake]
      rfl

/-- What the serialize rule does at an exchange for the side of the verifier: it takes a
value from the reader and guards the flag, which holds when the reader has the value. -/
theorem serializeMeaning_exchange_verifier (layout : Layout operations) :
    ∀ (prover verifier : Bool) (isProver : prover = false) (isVerifier : verifier = true)
      (place : Place) (number : Nat) (site : Site) (type : Ty)
      (put : Var operations ⟨[layout.writer, type], [layout.writer], .pure⟩)
      (take : Var operations ⟨[layout.reader], [.bool, type, layout.reader], .pure⟩)
      (populated : Ty.allPopulated [.bool, type, layout.reader] = true)
      (hasPut : layout.put type = some put) (hasTake : layout.take type = some take)
      (value : Held (model.Value type) prover)
      (state : ThreadState model layout.threads prover verifier) (taken : model.Value type)
      (rest : model.Value layout.reader),
      model.pure (.of take) populated (.cons (Held.value verifier isVerifier state.2) .nil) =
          .cons true (.cons taken (.cons rest .nil)) →
      (serializeMeaning (model := model) layout).exchange prover verifier place number site type
          value state =
        .done (Held.of verifier taken, (state.1, Held.of verifier rest))
  | false, true, _, _, place, number, site, type, put, take, populated, hasPut, hasTake, value,
      state, taken, rest, takes => by
      have unfolded : (serializeMeaning (model := model) layout).exchange false true place number
            site type value state =
          (cond ((model.pure (.of take) populated (.cons state.2 .nil)).get .here)
              (PIR.Process.done (Values.nil : Values (fun type => Held (model.Value type) true) []))
              (.halt Reason.reject.stop)).bind fun _ =>
            .done ((model.pure (.of take) populated (.cons state.2 .nil)).tail.get .here,
              (state.1, (model.pure (.of take) populated (.cons state.2 .nil)).tail.tail.get .here)) := by
        simp only [serializeMeaning, dif_pos populated, hasPut, hasTake]
        rfl
      rw [unfolded]
      have same : model.pure (.of take) populated (.cons state.2 .nil) =
          .cons true (.cons taken (.cons rest .nil)) := takes
      rw [same]
      rfl

end Channel

/-! ## The statements for the callees -/

section Callees

variable {model : Model} {operations : List OperationSignature} {old : List ProtocolHeader}

/-- A protocol that the step copies for a pair of roles, either of which may be absent: for
two disjoint sides that hold the two roles, the grouped process and the two parts are
related under the handlers that perform every effect as it is, over every channel. -/
@[expose] def PlainReplays (oldTable : ProtocolTable model old) {header : ProtocolHeader}
    (callee : Var old header) (prover verifier : Option Nat) : Prop :=
  ∀ {Writer Reader : Type} (channel : Channel model Writer Reader) (path : List Nat)
    (first second : Side), first.Disjoint second → first.Holds prover header.roles →
    second.Holds verifier header.roles →
    ∀ arguments : Values (SideValue model (first.union second)) header.inputs,
      PartsReplay channel (passHandler model Writer) (passHandler model Reader)
        (leftValues model first second) (rightValues model first second)
        ((oldTable.get callee) path (first.union second) arguments)
        ((oldTable.get callee) path first (leftValues model first second arguments))
        ((oldTable.get callee) path second (rightValues model first second arguments))

/-- A protocol that the step threads for a pair of roles: for two disjoint sides that hold
the two roles and two handlers that follow the protocol's marks for the pair, the grouped
process and the two parts under the handlers are related over the channel of the step. The
memberships of the two roles are parameters with their equations, so that a caller's
handler is a handler of the callee's side. -/
@[expose] def ThreadedReplays (layout : Layout operations) (laws : layout.Lawful model)
    (marks : MarkTable operations old) (oldTable : ProtocolTable model old)
    {header : ProtocolHeader} (callee : Var old header) (inner : TranscriptRoles) : Prop :=
  ∀ (path : List Nat) (first second : Side), first.Disjoint second →
    first.Holds (some inner.prover) header.roles → second.Holds (some inner.verifier) header.roles →
    ∀ (proverWrites proverReads verifierWrites verifierReads : Bool),
      first inner.prover = proverWrites → first inner.verifier = proverReads →
      second inner.prover = verifierWrites → second inner.verifier = verifierReads →
      ∀ (writes : proverWrites = true) (reads : verifierReads = true)
        (proverHandler : ThreadHandler model layout.threads proverWrites proverReads)
        (verifierHandler : ThreadHandler model layout.threads verifierWrites verifierReads),
        Follows (serializeMeaning layout) proverWrites proverReads proverHandler path
          (marks.get callee inner) →
        Follows (serializeMeaning layout) verifierWrites verifierReads verifierHandler path
          (marks.get callee inner) →
        ∀ arguments : Values (SideValue model (first.union second)) header.inputs,
          PartsReplay
            (serializeChannel layout laws proverWrites proverReads verifierWrites verifierReads
              writes reads)
            proverHandler verifierHandler (leftValues model first second)
            (rightValues model first second)
            ((oldTable.get callee) path (first.union second) arguments)
            ((oldTable.get callee) path first (leftValues model first second arguments))
            ((oldTable.get callee) path second (rightValues model first second arguments))

/-- The pair of roles has an image that threads of the protocol at a position. -/
@[expose] def Threaded (threads : Nat → TranscriptRoles → Bool) (index : Nat)
    (prover verifier : Option Nat) : Prop :=
  ∃ inner : TranscriptRoles, prover = some inner.prover ∧ verifier = some inner.verifier ∧
    threads index inner = true

/-- The statement for a callee that is reached with a pair of roles, either of which may be
absent: the one for a protocol that threads when it has the image that threads for the
pair, and the one for a protocol that is copied otherwise. -/
@[expose] def CalleeReplays (layout : Layout operations) (laws : layout.Lawful model)
    (threads : Nat → TranscriptRoles → Bool) (marks : MarkTable operations old)
    (oldTable : ProtocolTable model old) {header : ProtocolHeader} (callee : Var old header)
    (prover verifier : Option Nat) : Prop :=
  (∀ inner : TranscriptRoles, prover = some inner.prover → verifier = some inner.verifier →
    threads callee.index inner = true → ThreadedReplays layout laws marks oldTable callee inner) ∧
  (¬Threaded threads callee.index prover verifier → PlainReplays oldTable callee prover verifier)

end Callees

/-! ## What the step accepted -/

section Accepted

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {old new : List ProtocolHeader} {deployed : Bool} {t : Threads}
  {table : CalleeTable t.header old new} {definition : Nat}

/-- Both findings are findings when their combination is. -/
theorem bothTouch_ok {first second : Except StepRefusal Bool} {touched : Bool}
    (accepted : bothTouch first second = .ok touched) :
    (∃ found, first = .ok found) ∧ ∃ found, second = .ok found := by
  match first, second, accepted with
  | .ok one, .ok other, _ => exact ⟨⟨one, rfl⟩, ⟨other, rfl⟩⟩

/-- An exchange that is not refused and not rewritten is not between the two roles. -/
theorem exchange_apart {prover verifier : Option Nat} {sender receiver site : Nat} {type : Ty}
    (untouched : touchesOp (operations := operations) (functions := functions) (deployed := deployed)
      t false table definition prover verifier (.exchange sender receiver site type) = .ok false) :
    ¬(isRole prover sender = true ∧ isRole verifier receiver = true) ∧
      ¬(isRole verifier sender = true ∧ isRole prover receiver = true) := by
  simp only [touchesOp] at untouched
  refine ⟨fun between => ?_, fun between => ?_⟩
  · rw [between.1, between.2] at untouched
    cases untouched
  · rw [between.1, between.2] at untouched
    split at untouched <;> cases untouched

/-- An exchange that is not refused is not from the verifier to the prover. -/
theorem exchange_forward_only {prover verifier sender receiver site : Nat} {type : Ty}
    {touched : Bool} (differ : Nat.beq prover verifier = false)
    (accepted : touchesOp (operations := operations) (functions := functions) (deployed := deployed)
      t false table definition (some prover) (some verifier) (.exchange sender receiver site type) =
        .ok touched) :
    ¬(sender = verifier ∧ receiver = prover) := by
  rintro ⟨rfl, rfl⟩
  have other : Nat.beq sender receiver = false := by rw [natBeq_swap]; exact differ
  simp only [touchesOp, isRole, differ, other, Nat.beq_refl, Bool.false_and, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte] at accepted
  cases accepted

/-- A draw that is not refused in a program that is serialized: when its owner is one of
the two roles, the other role is not a receiver. -/
theorem draw_apart {prover verifier : Option Nat} {owner site : Nat} {receivers : List Nat}
    {inputs : List Ty} {output : Ty} {law : Var operations ⟨inputs, [output], .sampling⟩}
    {populated : output.populated = true} {touched : Bool}
    (accepted : touchesOp (functions := functions) (old := old) (deployed := deployed) t false table
      definition prover verifier (.draw owner receivers site law populated) = .ok touched) :
    (isRole prover owner = true → ∀ receiver ∈ receivers, isRole verifier receiver = false) ∧
      (isRole prover owner = false → isRole verifier owner = true →
        ∀ receiver ∈ receivers, isRole prover receiver = false) := by
  simp only [touchesOp, Bool.false_eq_true, ↓reduceIte] at accepted
  refine ⟨fun isProver receiver member => ?_, fun notProver isVerifier receiver member => ?_⟩
  · rw [isProver] at accepted
    simp only [Bool.true_or, ↓reduceIte] at accepted
    cases verifier with
    | none => rfl
    | some other =>
        simp only at accepted
        split at accepted
        · cases accepted
        · rename_i absent
          cases same : isRole (some other) receiver with
          | false => rfl
          | true =>
              have equal : other = receiver := Nat.eq_of_beq_eq_true same
              exact absurd ((occursIn_iff receivers other).mpr (equal ▸ member)) absent
  · rw [notProver, isVerifier] at accepted
    simp only [Bool.false_or, ↓reduceIte, Bool.false_eq_true] at accepted
    cases prover with
    | none => rfl
    | some other =>
        simp only at accepted
        split at accepted
        · cases accepted
        · rename_i absent
          cases same : isRole (some other) receiver with
          | false => rfl
          | true =>
              have equal : other = receiver := Nat.eq_of_beq_eq_true same
              exact absurd ((occursIn_iff receivers other).mpr (equal ▸ member)) absent

/-- An application that is not rewritten: its callee has no image that threads for the
roles that the application gives it. -/
theorem untouched_apply {prover verifier : Option Nat} {header : ProtocolHeader}
    {callee : Var old header} {roleMap : RoleMap} {site : Nat}
    {permitted : (deployed && header.specificationOnly) = false}
    (untouched : touchesOp (operations := operations) (functions := functions) t false table
      definition prover verifier (.apply callee roleMap site permitted) = .ok false) :
    ¬Threaded table.threads callee.index (preimageOf roleMap prover) (preimageOf roleMap verifier) := by
  rintro ⟨inner, atProver, atVerifier, threads⟩
  simp only [touchesOp, atProver, atVerifier] at untouched
  have missing := Except.ok.inj untouched
  rw [CalleeTable.find_isSome] at missing
  exact Bool.false_ne_true (missing.symm.trans threads)

/-- The image that threads of an applied protocol: the roles that the application gives
the callee, for which the callee has the image. -/
theorem threadedCallee_some {roles : TranscriptRoles} {roleMap : RoleMap} {header : ProtocolHeader}
    {callee : Var old header} {threaded : ThreadedCallee t new roles roleMap header}
    (found : threadedCallee t table roles roleMap callee = some threaded) :
    preimageOf roleMap (some roles.prover) = some threaded.inner.prover ∧
      preimageOf roleMap (some roles.verifier) = some threaded.inner.verifier ∧
      table.threads callee.index threaded.inner = true := by
  unfold threadedCallee at found
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
          dsimp only at found
          cases image : table.find callee (some ⟨prover, verifier⟩) with
          | none =>
              rw [image] at found
              cases found
          | some image' =>
              rw [image] at found
              cases found
              refine ⟨?_, ?_, ?_⟩
              · show (preimage roleMap roles.prover).map (·.val) = _
                rw [atProver]
                rfl
              · show (preimage roleMap roles.verifier).map (·.val) = _
                rw [atVerifier]
                rfl
              · show table.has callee.index (some ⟨prover, verifier⟩) = true
                rw [← CalleeTable.find_isSome, image]
                rfl

/-- An applied protocol without an image that threads for the roles that the application
gives it. -/
theorem threadedCallee_none {roles : TranscriptRoles} {roleMap : RoleMap} {header : ProtocolHeader}
    {callee : Var old header} (missing : threadedCallee t table roles roleMap callee = none) :
    ¬Threaded table.threads callee.index (preimageOf roleMap (some roles.prover))
      (preimageOf roleMap (some roles.verifier)) := by
  rintro ⟨⟨innerProver, innerVerifier⟩, atInnerProver, atInnerVerifier, threads⟩
  unfold threadedCallee at missing
  change (preimage roleMap roles.prover).map (·.val) = some innerProver at atInnerProver
  change (preimage roleMap roles.verifier).map (·.val) = some innerVerifier at atInnerVerifier
  cases atProver : preimage roleMap roles.prover with
  | none =>
      rw [atProver] at atInnerProver
      cases atInnerProver
  | some prover =>
      cases atVerifier : preimage roleMap roles.verifier with
      | none =>
          rw [atVerifier] at atInnerVerifier
          cases atInnerVerifier
      | some verifier =>
          rw [atProver] at atInnerProver
          rw [atVerifier] at atInnerVerifier
          rw [atProver, atVerifier] at missing
          obtain ⟨prover, isProver⟩ := prover
          obtain ⟨verifier, isVerifier⟩ := verifier
          have sameProver : prover = innerProver := Option.some.inj atInnerProver
          have sameVerifier : verifier = innerVerifier := Option.some.inj atInnerVerifier
          subst sameProver sameVerifier
          dsimp only at missing
          cases image : table.find callee (some ⟨prover, verifier⟩) with
          | none =>
              have has : table.has callee.index (some ⟨prover, verifier⟩) = false := by
                rw [← CalleeTable.find_isSome, image]
                rfl
              exact Bool.false_ne_true (has.symm.trans threads)
          | some image' =>
              rw [image] at missing
              cases missing

end Accepted

/-! ## A region that the step copies -/

section Plain

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {old new : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {oldTable : ProtocolTable model old}
  {t : Threads} {table : CalleeTable t.header old new}

/-- An operation that is not rewritten: the grouped process and the two parts are related
under the handlers that perform every effect as it is, when its regions and its callee
are. -/
theorem operation_admits_plain (quiet : QuietTable functionTable) (idle : CalleesIdle oldTable)
    {Writer Reader : Type} (channel : Channel model Writer Reader) (definition : Nat)
    (prover verifier : Option Nat) (bound : Nat) (label : Nat → Site) (first second : Side)
    (disjoint : first.Disjoint second) (holdsProver : first.Holds prover bound)
    (holdsVerifier : second.Holds verifier bound) (enclosing : Option (List Nat)) :
    ∀ (op : ProtocolOp operations functions old deployed)
      (bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op)),
      ProtocolOp.violation typeTable bound enclosing op = none → opEncloses op bodies →
      touchesOp t false table definition prover verifier op = .ok false →
      RegionsReplay channel (passHandler model Writer) (passHandler model Reader) first second _
        (bodies.denote (labelledMeaning model label functionTable oldTable (first.union second)))
        (bodies.denote (labelledMeaning model label functionTable oldTable first))
        (bodies.denote (labelledMeaning model label functionTable oldTable second)) →
      (∀ {header : ProtocolHeader} (callee : Var old header) (roleMap : RoleMap),
        (callee.index, roleMap) ∈ applicationOf op →
        ¬Threaded table.threads callee.index (preimageOf roleMap prover)
          (preimageOf roleMap verifier) →
        PlainReplays oldTable callee (preimageOf roleMap prover) (preimageOf roleMap verifier)) →
      OperationReplays channel (passHandler model Writer) (passHandler model Reader) functionTable
        oldTable label first second op bodies
  | .at role op localBodies, bodies, _, _, _, _, _ => fun arguments =>
      at_replays quiet disjoint role op localBodies arguments _ _ _
  | .sample owner site law populated, bodies, _, _, _, _, _ => fun arguments =>
      sample_replays disjoint owner site law populated (fun _ _ => passHandler_passes _)
        (fun _ _ => passHandler_passes _) arguments _ _ _
  | .exchange sender receiver site type, bodies, clean, _, untouched, _, _ => fun arguments => by
      have below := ProtocolOp.violation_exchange clean
      have apart := exchange_apart untouched
      refine exchange_replays disjoint sender receiver site type (fun inFirst inSecond => ?_) ?_
        arguments _ _ _
      · exact absurd ⟨(holdsProver sender below.1).symm.trans inFirst,
          (holdsVerifier receiver below.2).symm.trans inSecond⟩ apart.1
      · exact fun between => apart.2 ⟨(holdsVerifier sender below.1).symm.trans between.1,
          (holdsProver receiver below.2).symm.trans between.2⟩
  | .draw owner receivers site law populated, bodies, clean, _, untouched, _, _ =>
      fun arguments => by
      have below := ProtocolOp.violation_draw clean
      have apart := draw_apart untouched
      refine draw_replays disjoint owner receivers site law populated
        (fun _ _ => passHandler_passes _) (fun _ _ => passHandler_passes _)
        (fun inFirst receiver member => ?_) (fun inSecond receiver member => ?_) arguments _ _ _
      · rw [holdsVerifier receiver (below.2 receiver member)]
        exact apart.1 ((holdsProver owner below.1).symm.trans inFirst) receiver member
      · rw [holdsProver receiver (below.2 receiver member)]
        have notProver : isRole prover owner = false := by
          rw [← holdsProver owner below.1]
          have none := disjoint owner
          rw [inSecond, Bool.and_true] at none
          exact none
        exact apart.2 notProver ((holdsVerifier owner below.1).symm.trans inSecond) receiver member
  | .repeat participants count carried collected captures covered, bodies, _, encloses, _,
      related, _ => fun arguments =>
      repeat_replays participants count carried collected captures covered encloses.1 arguments
        _ _ _ related
        (fun outFirst => regions_idle idle first participants (absent_of_any outFirst) bodies
          encloses.2)
        (fun outSecond => regions_idle idle second participants (absent_of_any outSecond) bodies
          encloses.2)
  | .choose participants tag captures outputs covered, bodies, _, encloses, _, related, _ =>
      fun arguments =>
      choose_replays participants tag captures outputs covered arguments _ _ _ related
        (fun outFirst => regions_idle idle first participants (absent_of_any outFirst) bodies
          encloses)
        (fun outSecond => regions_idle idle second participants (absent_of_any outSecond) bodies
          encloses)
  | .apply (header := header) callee roleMap site permitted, bodies, clean, _, untouched, _,
      callees => fun arguments => by
      obtain ⟨below, length, distinct⟩ := ProtocolOp.violation_apply clean
      exact apply_replays callee roleMap site permitted
        (fun arguments => callees callee roleMap List.mem_cons_self (untouched_apply untouched)
          channel (label site).below (Side.preimage roleMap first) (Side.preimage roleMap second)
          (fun role => disjoint (roleMap.apply role)) (holdsProver.callee below length distinct)
          (holdsVerifier.callee below length distinct) arguments)
        arguments _ _ _

mutual
  /-- A region without a rewritten operation: every one of its operations is related under
  the handlers that perform every effect as it is. -/
  theorem region_admits_plain (quiet : QuietTable functionTable) (idle : CalleesIdle oldTable)
      {Writer Reader : Type} (channel : Channel model Writer Reader) (definition : Nat)
      (prover verifier : Option Nat) (bound : Nat) (label : Nat → Site) (first second : Side)
      (disjoint : first.Disjoint second) (holdsProver : first.Holds prover bound)
      (holdsVerifier : second.Holds verifier bound) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (enclosing : Option (List Nat)) (found : List (Nat × RoleMap)),
        Region.Legal typeTable bound enclosing region → regionEnclosed region →
        touches t false table definition prover verifier region = .ok false →
        (∀ {header : ProtocolHeader} (callee : Var old header) (roleMap : RoleMap),
          (callee.index, roleMap) ∈ applications region found →
          ¬Threaded table.threads callee.index (preimageOf roleMap prover)
            (preimageOf roleMap verifier) →
          PlainReplays oldTable callee (preimageOf roleMap prover) (preimageOf roleMap verifier)) →
        RegionAdmits channel (passHandler model Writer) (passHandler model Reader) functionTable
          oldTable label first second region
    | .ret _, _, _, _, _, _, _ => trivial
    | .stop _, _, _, _, _, _, _ => trivial
    | .bind body rest, enclosing, found, legal, enclosed, untouched, callees => by
        unfold touches at untouched
        obtain ⟨untouchedBody, untouchedRest⟩ := bothTouch_false untouched
        exact ⟨region_admits_plain quiet idle channel definition prover verifier bound label first
            second disjoint holdsProver holdsVerifier body enclosing found legal.bind.1 enclosed.1
            untouchedBody
            (fun callee roleMap member =>
              callees callee roleMap (applications_keeps rest _ _ member)),
          region_admits_plain quiet idle channel definition prover verifier bound label first
            second disjoint holdsProver holdsVerifier rest enclosing (applications body found)
            legal.bind.2 enclosed.2 untouchedRest callees⟩
    | .letOp op arguments bodies rest, enclosing, found, legal, enclosed, untouched, callees => by
        unfold touches at untouched
        obtain ⟨untouchedOp, later⟩ := bothTouch_false untouched
        obtain ⟨untouchedBodies, untouchedRest⟩ := bothTouch_false later
        obtain ⟨clean, legalBodies, legalRest⟩ := legal.letOp
        exact ⟨operation_admits_plain quiet idle channel definition prover verifier bound label
            first second disjoint holdsProver holdsVerifier enclosing op bodies clean enclosed.1
            untouchedOp
            (regions_replay bodies
              (regions_admit_plain quiet idle channel definition prover verifier bound label first
                second disjoint holdsProver holdsVerifier bodies (ProtocolOp.enclosing enclosing op)
                (applicationOf op ++ found) legalBodies enclosed.2.1 untouchedBodies
                (fun callee roleMap member =>
                  callees callee roleMap (applications_keeps rest _ _ member))))
            (fun callee roleMap member => callees callee roleMap
              (applications_keeps rest _ _
                (applicationsOf_keeps bodies _ _ (List.mem_append_left _ member)))),
          region_admits_plain quiet idle channel definition prover verifier bound label first
            second disjoint holdsProver holdsVerifier rest enclosing
            (applicationsOf bodies (applicationOf op ++ found)) legalRest enclosed.2.2 untouchedRest
            callees⟩

  /-- The same for closed regions. -/
  theorem regions_admit_plain (quiet : QuietTable functionTable) (idle : CalleesIdle oldTable)
      {Writer Reader : Type} (channel : Channel model Writer Reader) (definition : Nat)
      (prover verifier : Option Nat) (bound : Nat) (label : Nat → Site) (first second : Side)
      (disjoint : first.Disjoint second) (holdsProver : first.Holds prover bound)
      (holdsVerifier : second.Holds verifier bound)
      {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (enclosing : Option (List Nat)) (found : List (Nat × RoleMap)),
        Regions.Legal typeTable bound enclosing regions → regionsEnclosed regions →
        touchesRegions t false table definition prover verifier regions = .ok false →
        (∀ {header : ProtocolHeader} (callee : Var old header) (roleMap : RoleMap),
          (callee.index, roleMap) ∈ applicationsOf regions found →
          ¬Threaded table.threads callee.index (preimageOf roleMap prover)
            (preimageOf roleMap verifier) →
          PlainReplays oldTable callee (preimageOf roleMap prover) (preimageOf roleMap verifier)) →
        RegionsAdmit channel (passHandler model Writer) (passHandler model Reader) functionTable
          oldTable label first second regions
    | .nil, _, _, _, _, _, _ => trivial
    | .cons body tail, enclosing, found, legal, enclosed, untouched, callees => by
        unfold touchesRegions at untouched
        obtain ⟨untouchedBody, untouchedTail⟩ := bothTouch_false untouched
        exact ⟨region_admits_plain quiet idle channel definition prover verifier bound label first
            second disjoint holdsProver holdsVerifier body enclosing found legal.cons.1 enclosed.1
            untouchedBody
            (fun callee roleMap member =>
              callees callee roleMap (applicationsOf_keeps tail _ _ member)),
          regions_admit_plain quiet idle channel definition prover verifier bound label first
            second disjoint holdsProver holdsVerifier tail enclosing (applications body found)
            legal.cons.2 enclosed.2 untouchedTail callees⟩
end

end Plain

/-! ## A region that the step threads -/

section Threaded

variable {model : Model} {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader} {old new : List ProtocolHeader} {deployed : Bool}
  {functionTable : FunctionTable model functions} {oldTable : ProtocolTable model old}

/-- An exchange from the prover to the verifier of a type that the layout carries: the
grouped process has the value at once; the prover's handler puts it on its writer, and the
verifier's handler takes it from every reader that gives it. -/
theorem exchange_forward (layout : Layout operations) (laws : layout.Lawful model) (place : Place)
    {first second : Side} {label : Nat → Site} (isProver : first place.roles.prover = true)
    (noReader : first place.roles.verifier = false) (noWriter : second place.roles.prover = false)
    (isVerifier : second place.roles.verifier = true)
    (proverHandler : ThreadHandler model layout.threads (first place.roles.prover)
      (first place.roles.verifier))
    (verifierHandler : ThreadHandler model layout.threads (second place.roles.prover)
      (second place.roles.verifier))
    (site : Nat) (type : Ty) (carries : layout.Carries type)
    (actsProver : ExchangeActs (operations := operations) (deployed := deployed) layout.threads
      (serializeMeaning layout) functionTable oldTable place first label proverHandler site type)
    (actsVerifier : ExchangeActs (operations := operations) (deployed := deployed) layout.threads
      (serializeMeaning layout) functionTable oldTable place second label verifierHandler site type)
    (arguments : Values (SideValue model (first.union second)) [⟨type, place.roles.prover⟩]) :
    PartsReplay (serializeChannel layout laws _ _ _ _ isProver isVerifier) proverHandler
      verifierHandler (leftValues model first second) (rightValues model first second)
      (labelledOperation model label functionTable oldTable (first.union second)
        (operations := operations) (deployed := deployed)
        (.exchange place.roles.prover place.roles.verifier site type) arguments .nil)
      (labelledOperation model label functionTable oldTable first
        (operations := operations) (deployed := deployed)
        (.exchange place.roles.prover place.roles.verifier site type)
        (leftValues model first second arguments) .nil)
      (labelledOperation model label functionTable oldTable second
        (operations := operations) (deployed := deployed)
        (.exchange place.roles.prover place.roles.verifier site type)
        (rightValues model first second arguments) .nil) := by
  have inUnionProver : (first.union second) place.roles.prover = true := union_first isProver
  have inUnionVerifier : (first.union second) place.roles.verifier = true := union_second isVerifier
  -- The value that is exchanged, as the prover's side holds it.
  have proverValue : Held.value (first place.roles.prover) isProver
        ((leftValues model first second arguments).get .here) =
      Held.value ((first.union second) place.roles.prover) inUnionProver (arguments.get .here) :=
    (congrArg (Held.value (first place.roles.prover) isProver)
      (Values.map_get (fun {located} value => restrictLeft model first second (located := located)
        value) arguments .here)).trans
      (Held.value_left (first place.roles.prover) (second place.roles.prover) isProver
        inUnionProver _)
  -- The shares of what the grouped process returns.
  have shareProver : leftValues model first second
        (Values.cons (Value := SideValue model (first.union second))
          (ty := ⟨type, place.roles.verifier⟩)
          (Held.of ((first.union second) place.roles.verifier)
            (Held.value ((first.union second) place.roles.prover) inUnionProver (arguments.get .here)))
          .nil) =
      Values.cons (Value := SideValue model first) (ty := ⟨type, place.roles.verifier⟩)
        (Held.absent (first place.roles.verifier) noReader) .nil :=
    outside_values_unique
      (fun located member => by rw [List.mem_singleton.mp member]; exact noReader) _ _
  have shareVerifier : rightValues model first second
        (Values.cons (Value := SideValue model (first.union second))
          (ty := ⟨type, place.roles.verifier⟩)
          (Held.of ((first.union second) place.roles.verifier)
            (Held.value ((first.union second) place.roles.prover) inUnionProver (arguments.get .here)))
          .nil) =
      Values.cons (Value := SideValue model second) (ty := ⟨type, place.roles.verifier⟩)
        (Held.of (second place.roles.verifier)
          (Held.value ((first.union second) place.roles.prover) inUnionProver (arguments.get .here)))
        .nil :=
    congrArg (fun head => Values.cons (Value := SideValue model second)
        (ty := ⟨type, place.roles.verifier⟩) head .nil)
      (Held.right_of (first place.roles.verifier) (second place.roles.verifier) _)
  refine ⟨fun holds sends every sent sampler askedProver askedVerifier writer => ?_⟩
  rw [labelled_exchange_internal (side := first.union second) inUnionProver inUnionVerifier] at every
  rw [labelled_exchange_send (side := first) isProver noReader, proverValue] at sent
  obtain ⟨writable, carried⟩ := sent
  obtain ⟨populated, ⟨put, hasPut⟩, take, hasTake⟩ := carries
  refine ⟨_, [⟨type, Held.value ((first.union second) place.roles.prover) inUnionProver
      (arguments.get .here)⟩],
    (Held.of (first place.roles.prover)
      (layout.putValue model put (Held.value (first place.roles.prover) isProver writer.1)
        (Held.value ((first.union second) place.roles.prover) inUnionProver (arguments.get .here))),
      writer.2), askedProver, askedVerifier, every, ?_, ⟨?_, rfl, ?_⟩, ?_, ?_⟩
  · rw [shareProver]
    exact carried
  · show layout.Written model _ _ (Held.value _ isProver (Held.of _ _))
    rw [Held.value_of]
    exact .cons put hasPut (.nil _)
  · intro message member
    rw [List.mem_singleton.mp member]
    exact ⟨⟨populated, ⟨put, hasPut⟩, take, hasTake⟩, writable⟩
  · rw [actsProver (leftValues model first second arguments) writer,
      serializeMeaning_exchange_prover layout _ _ isProver noReader place site (label site) type put
        take populated hasPut hasTake _ writer, proverValue, shareProver]
    exact .done _ _
  · intro reader taken takes
    obtain ⟨takesReader, sameWriter⟩ := takes
    obtain ⟨other, populated', hasOther, takenRow⟩ := takesReader.single
    have same : other = take := Option.some.inj (hasOther.symm.trans hasTake)
    subst same
    rw [actsVerifier (rightValues model first second arguments) reader,
      serializeMeaning_exchange_verifier layout _ _ noWriter isVerifier place site (label site) type
        put other populated hasPut hasOther _ reader _ _ takenRow, shareVerifier, Held.of_value,
      ← sameWriter]
    exact .done _ _

/-- A handler that passes every process of the regions of an operation. -/
theorem passRegions_passAll {t : Threads} {place : Place} {side : Side}
    {handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier)} :
    ∀ {signatures : List (List Located × List Located)}
      (regions : Values (RegionFunction (SideValue model side) (Effects model)) signatures),
      PassRegions t place side handler regions → PassAll handler regions
  | [], _, _ => trivial
  | _ :: _, regions, passes => ⟨passes.1, passRegions_passAll regions.tail passes.2⟩

/-- A handler that fits a draw that is not between the two transcript roles passes it. -/
theorem drawFits_passes {t : Threads} {sem : RuleMeaning model t operations} {place : Place}
    {side : Side} {label : Nat → Site}
    {handler : ThreadHandler model t (side place.roles.prover) (side place.roles.verifier)}
    {owner site : Nat} {receivers : List Nat} {inputs : List Ty} {output : Ty}
    {law : Var operations ⟨inputs, [output], .sampling⟩} {populated : output.populated = true}
    (fits : DrawFits (deployed := deployed) t sem functionTable oldTable place side label handler
      owner receivers site law populated)
    (notByVerifier : ¬(owner = place.roles.verifier ∧ receivers = [place.roles.prover]))
    (notByProver : ¬(owner = place.roles.prover ∧ receivers = [place.roles.verifier])) :
    OperationPasses (deployed := deployed) t functionTable oldTable place side label handler
      (.draw owner receivers site law populated) := by
  cases receivers with
  | nil => exact fits
  | cons receiver rest =>
      cases rest with
      | nil =>
          exact fits.2.2 (fun both => notByVerifier ⟨both.1, by rw [both.2]⟩)
            (fun both => notByProver ⟨both.1, by rw [both.2]⟩)
      | cons _ _ => exact fits


/-- The findings for the parts of a region that starts with an operation are findings. -/
theorem accepted_letOp {t : Threads} {table : CalleeTable t.header old new} {derives : Bool}
    {definition : Nat} {prover verifier : Option Nat} {Γ out : List Located}
    {op : ProtocolOp operations functions old deployed}
    {arguments : Operands Γ (ProtocolOp.arguments op)}
    {bodies : Regions (ProtocolDialect operations functions old deployed) (ProtocolOp.regions op)}
    {rest : Region (ProtocolDialect operations functions old deployed)
      (bindAll Γ (ProtocolOp.results op)) out}
    (accepted : ∃ touched, touches t derives table definition prover verifier
      (Region.letOp (dialect := ProtocolDialect operations functions old deployed) op arguments
        bodies rest) = .ok touched) :
    (∃ touched, touchesOp t derives table definition prover verifier op = .ok touched) ∧
      (∃ touched, touchesRegions t derives table definition prover verifier bodies = .ok touched) ∧
      ∃ touched, touches t derives table definition prover verifier rest = .ok touched := by
  obtain ⟨touched, accepted⟩ := accepted
  unfold touches at accepted
  obtain ⟨acceptedOp, later, acceptedLater⟩ := bothTouch_ok accepted
  obtain ⟨acceptedBodies, acceptedRest⟩ := bothTouch_ok acceptedLater
  exact ⟨acceptedOp, acceptedBodies, acceptedRest⟩

section Operations

variable (layout : Layout operations) (laws : layout.Lawful model)
  {table : CalleeTable layout.threads.header old new} (place : Place) (bound : Nat)
  (label : Nat → Site) (first second : Side) (disjoint : first.Disjoint second)
  (holdsProver : first.Holds (some place.roles.prover) bound)
  (holdsVerifier : second.Holds (some place.roles.verifier) bound)
  (isProver : first place.roles.prover = true) (isVerifier : second place.roles.verifier = true)
  (proverHandler : ThreadHandler model layout.threads (first place.roles.prover)
    (first place.roles.verifier))
  (verifierHandler : ThreadHandler model layout.threads (second place.roles.prover)
    (second place.roles.verifier))

include disjoint isProver isVerifier in
/-- The two transcript roles differ, and each side holds one of them. -/
theorem roles_apart :
    first place.roles.verifier = false ∧ second place.roles.prover = false ∧
      place.roles.prover ≠ place.roles.verifier := by
  have noReader : first place.roles.verifier = false := by
    have none := disjoint place.roles.verifier
    rw [isVerifier, Bool.and_true] at none
    exact none
  have noWriter : second place.roles.prover = false := by
    have none := disjoint place.roles.prover
    rw [isProver, Bool.true_and] at none
    exact none
  refine ⟨noReader, noWriter, fun same => ?_⟩
  rw [same, noReader] at isProver
  cases isProver

include disjoint holdsProver holdsVerifier in
/-- An exchange of a definition that the step threads: from the prover to the verifier the
layout carries its type and the two handlers act as the rule; no exchange is from the
verifier to the prover. -/
theorem exchange_admits (sender receiver site : Nat) (type : Ty) {enclosing : Option (List Nat)}
    (nested : Regions (ProtocolDialect operations functions old deployed) [])
    (clean : ProtocolOp.violation (operations := operations) (functions := functions)
      (protocols := old) (deployed := deployed) typeTable bound enclosing
      (.exchange sender receiver site type) = none)
    (accepted : ∃ touched, touchesOp (operations := operations) (functions := functions)
      (deployed := deployed) layout.threads false table place.definition (some place.roles.prover)
      (some place.roles.verifier) (.exchange sender receiver site type) = .ok touched)
    (carries : sender = place.roles.prover → receiver = place.roles.verifier →
      layout.Carries type)
    (actsProver : sender = place.roles.prover → receiver = place.roles.verifier →
      ExchangeActs (operations := operations) (deployed := deployed) layout.threads
        (serializeMeaning layout) functionTable oldTable place first label proverHandler site type)
    (actsVerifier : sender = place.roles.prover → receiver = place.roles.verifier →
      ExchangeActs (operations := operations) (deployed := deployed) layout.threads
        (serializeMeaning layout) functionTable oldTable place second label verifierHandler site
        type) :
    OperationReplays (serializeChannel layout laws _ _ _ _ isProver isVerifier) proverHandler
      verifierHandler functionTable oldTable label first second (operations := operations)
      (deployed := deployed) (.exchange sender receiver site type) nested := by
  intro arguments
  obtain ⟨touched, accepted⟩ := accepted
  obtain ⟨noReader, noWriter, differ⟩ := roles_apart place first second disjoint isProver isVerifier
  have below := ProtocolOp.violation_exchange clean
  have unequal : Nat.beq place.roles.prover place.roles.verifier = false := by
    cases same : Nat.beq place.roles.prover place.roles.verifier with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true same) differ
  refine exchange_replays disjoint sender receiver site type (fun inFirst inSecond given => ?_)
    ?_ arguments _ _ _
  · have isSender : sender = place.roles.prover := holdsProver.member below.1 inFirst
    have isReceiver : receiver = place.roles.verifier := holdsVerifier.member below.2 inSecond
    subst isSender isReceiver
    exact exchange_forward layout laws place isProver noReader noWriter isVerifier proverHandler
      verifierHandler site type (carries rfl rfl) (actsProver rfl rfl) (actsVerifier rfl rfl) given
  · rintro ⟨inSecond, inFirst⟩
    exact exchange_forward_only unequal accepted
      ⟨holdsVerifier.member below.1 inSecond, holdsProver.member below.2 inFirst⟩

include disjoint holdsProver holdsVerifier in
/-- A draw of a definition that the step threads: no draw is between the two transcript
roles, so the handlers pass it, and the part without the owner has no receiver. -/
theorem draw_admits (owner : Nat) (receivers : List Nat) (site : Nat) {inputs : List Ty}
    {output : Ty} (law : Var operations ⟨inputs, [output], .sampling⟩)
    (populated : output.populated = true) {enclosing : Option (List Nat)}
    (nested : Regions (ProtocolDialect operations functions old deployed) [])
    (clean : ProtocolOp.violation (functions := functions) (protocols := old)
      (deployed := deployed) typeTable bound enclosing (.draw owner receivers site law populated) =
        none)
    (accepted : ∃ touched, touchesOp (functions := functions) (old := old) (deployed := deployed)
      layout.threads false table place.definition (some place.roles.prover)
      (some place.roles.verifier) (.draw owner receivers site law populated) = .ok touched)
    (fitsProver : DrawFits (deployed := deployed) layout.threads (serializeMeaning layout)
      functionTable oldTable place first label proverHandler owner receivers site law populated)
    (fitsVerifier : DrawFits (deployed := deployed) layout.threads (serializeMeaning layout)
      functionTable oldTable place second label verifierHandler owner receivers site law
      populated) :
    OperationReplays (serializeChannel layout laws _ _ _ _ isProver isVerifier) proverHandler
      verifierHandler functionTable oldTable label first second (deployed := deployed)
      (.draw owner receivers site law populated) nested := by
  intro arguments
  obtain ⟨touched, accepted⟩ := accepted
  obtain ⟨noReader, noWriter, differ⟩ := roles_apart place first second disjoint isProver isVerifier
  have below := ProtocolOp.violation_draw clean
  have apart := draw_apart accepted
  have apartProver : first owner = true → ∀ receiver ∈ receivers, second receiver = false := by
    intro inFirst receiver member
    rw [holdsVerifier receiver (below.2 receiver member)]
    exact apart.1 ((holdsProver owner below.1).symm.trans inFirst) receiver member
  have apartVerifier : second owner = true → ∀ receiver ∈ receivers, first receiver = false := by
    intro inSecond receiver member
    rw [holdsProver receiver (below.2 receiver member)]
    have notProver : isRole (some place.roles.prover) owner = false := by
      rw [← holdsProver owner below.1]
      have none := disjoint owner
      rw [inSecond, Bool.and_true] at none
      exact none
    exact apart.2 notProver ((holdsVerifier owner below.1).symm.trans inSecond) receiver member
  refine draw_replays disjoint owner receivers site law populated (fun inFirst arguments => ?_)
    (fun inSecond arguments => ?_) apartProver apartVerifier arguments _ _ _
  · have isOwner : owner = place.roles.prover := holdsProver.member below.1 inFirst
    refine drawFits_passes fitsProver (fun both => differ (isOwner.symm.trans both.1))
      (fun both => ?_) arguments .nil
    have outside := apartProver inFirst place.roles.verifier
      (by rw [both.2]; exact List.mem_singleton_self _)
    rw [isVerifier] at outside
    cases outside
  · have isOwner : owner = place.roles.verifier := holdsVerifier.member below.1 inSecond
    refine drawFits_passes fitsVerifier (fun both => ?_)
      (fun both => differ (both.1.symm.trans isOwner)) arguments .nil
    have outside := apartVerifier inSecond place.roles.prover
      (by rw [both.2]; exact List.mem_singleton_self _)
    rw [isProver] at outside
    cases outside

include disjoint holdsProver holdsVerifier in
/-- An application in a definition that the step threads: a callee with the image that
threads for the roles it is given is related under the two handlers, which follow its
marks; every other callee is related under handlers that perform every effect, and the two
handlers pass it. -/
theorem apply_admits (marks : MarkTable operations old) {header : ProtocolHeader}
    (callee : Var old header) (roleMap : RoleMap) (site : Nat)
    (permitted : (deployed && header.specificationOnly) = false) {enclosing : Option (List Nat)}
    (nested : Regions (ProtocolDialect operations functions old deployed) [])
    (clean : ProtocolOp.violation (operations := operations) (functions := functions) typeTable
      bound enclosing (.apply callee roleMap site permitted) = none)
    (fitsProver :
      (∀ threaded : ThreadedCallee layout.threads new place.roles roleMap header,
        threadedCallee layout.threads table place.roles roleMap callee = some threaded →
          ((stepFits (serializeMeaning (model := model) layout) marks).get callee) threaded.inner
            (label site).below (Side.preimage roleMap first) (first place.roles.prover)
            (first place.roles.verifier) (congrArg first threaded.prover)
            (congrArg first threaded.verifier) proverHandler) ∧
      (threadedCallee layout.threads table place.roles roleMap callee = none →
        ∀ arguments : Values (SideValue model (Side.preimage roleMap first)) header.inputs,
          PIR.Passes proverHandler
            ((oldTable.get callee) (label site).below (Side.preimage roleMap first) arguments)))
    (fitsVerifier :
      (∀ threaded : ThreadedCallee layout.threads new place.roles roleMap header,
        threadedCallee layout.threads table place.roles roleMap callee = some threaded →
          ((stepFits (serializeMeaning (model := model) layout) marks).get callee) threaded.inner
            (label site).below (Side.preimage roleMap second) (second place.roles.prover)
            (second place.roles.verifier) (congrArg second threaded.prover)
            (congrArg second threaded.verifier) verifierHandler) ∧
      (threadedCallee layout.threads table place.roles roleMap callee = none →
        ∀ arguments : Values (SideValue model (Side.preimage roleMap second)) header.inputs,
          PIR.Passes verifierHandler
            ((oldTable.get callee) (label site).below (Side.preimage roleMap second) arguments)))
    (calleeReplays : CalleeReplays layout laws table.threads marks oldTable callee
      (preimageOf roleMap (some place.roles.prover))
      (preimageOf roleMap (some place.roles.verifier))) :
    OperationReplays (serializeChannel layout laws _ _ _ _ isProver isVerifier) proverHandler
      verifierHandler functionTable oldTable label first second (operations := operations)
      (.apply callee roleMap site permitted) nested := by
  intro arguments
  obtain ⟨below, length, distinct⟩ := ProtocolOp.violation_apply clean
  refine apply_replays callee roleMap site permitted (fun arguments => ?_) arguments _ _ _
  cases found : threadedCallee layout.threads table place.roles roleMap callee with
  | some threaded =>
      obtain ⟨atProver, atVerifier, threads⟩ := threadedCallee_some found
      have followsProver := fitsProver.1 threaded found
      have followsVerifier := fitsVerifier.1 threaded found
      rw [stepFits_get] at followsProver followsVerifier
      exact calleeReplays.1 threaded.inner atProver atVerifier threads (label site).below
        (Side.preimage roleMap first) (Side.preimage roleMap second)
        (fun role => disjoint (roleMap.apply role))
        (atProver ▸ holdsProver.callee below length distinct)
        (atVerifier ▸ holdsVerifier.callee below length distinct) _ _ _ _
        (congrArg first threaded.prover) (congrArg first threaded.verifier)
        (congrArg second threaded.prover) (congrArg second threaded.verifier) isProver isVerifier
        proverHandler verifierHandler followsProver.2 followsVerifier.2 arguments
  | none =>
      exact (calleeReplays.2 (threadedCallee_none found) _ (label site).below
        (Side.preimage roleMap first) (Side.preimage roleMap second)
        (fun role => disjoint (roleMap.apply role)) (holdsProver.callee below length distinct)
        (holdsVerifier.callee below length distinct) arguments).ofPasses
        (fitsProver.2 found _) (fitsVerifier.2 found _)

end Operations

mutual
  /-- A region of a definition that the step threads and whose messages the layout carries:
  every one of its operations is related under two handlers that fit the region, over the
  channel of the step. -/
  theorem region_admits (layout : Layout operations) (laws : layout.Lawful model)
      {table : CalleeTable layout.threads.header old new} (quiet : QuietTable functionTable)
      (idle : CalleesIdle oldTable) (marks : MarkTable operations old) (place : Place) (bound : Nat)
      (label : Nat → Site) (first second : Side) (disjoint : first.Disjoint second)
      (holdsProver : first.Holds (some place.roles.prover) bound)
      (holdsVerifier : second.Holds (some place.roles.verifier) bound)
      (isProver : first place.roles.prover = true) (isVerifier : second place.roles.verifier = true)
      (proverHandler : ThreadHandler model layout.threads (first place.roles.prover)
        (first place.roles.verifier))
      (verifierHandler : ThreadHandler model layout.threads (second place.roles.prover)
        (second place.roles.verifier)) {Γ out : List Located} :
      ∀ (region : Region (ProtocolDialect operations functions old deployed) Γ out)
        (enclosing : Option (List Nat)) (found : List (Nat × RoleMap)),
        Region.Legal typeTable bound enclosing region → regionEnclosed region →
        (∃ touched, touches layout.threads false table place.definition (some place.roles.prover)
          (some place.roles.verifier) region = .ok touched) →
        RegionCarries layout place.roles region →
        Fits layout.threads (serializeRule (functions := functions) layout) (serializeMeaning layout)
          functionTable oldTable table (stepFits (serializeMeaning layout) marks) place first label
          proverHandler region →
        Fits layout.threads (serializeRule (functions := functions) layout) (serializeMeaning layout)
          functionTable oldTable table (stepFits (serializeMeaning layout) marks) place second label
          verifierHandler region →
        (∀ {header : ProtocolHeader} (callee : Var old header) (roleMap : RoleMap),
          (callee.index, roleMap) ∈ applications region found →
          CalleeReplays layout laws table.threads marks oldTable callee
            (preimageOf roleMap (some place.roles.prover))
            (preimageOf roleMap (some place.roles.verifier))) →
        RegionAdmits (serializeChannel layout laws _ _ _ _ isProver isVerifier) proverHandler
          verifierHandler functionTable oldTable label first second region
    | .ret _, _, _, _, _, _, _, _, _, _ => trivial
    | .stop _, _, _, _, _, _, _, _, _, _ => trivial
    | .bind body rest, enclosing, found, legal, enclosed, accepted, carries, fitsProver,
        fitsVerifier, callees => by
        obtain ⟨touched, accepted⟩ := accepted
        unfold touches at accepted
        obtain ⟨acceptedBody, acceptedRest⟩ := bothTouch_ok accepted
        exact ⟨region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler body enclosing found legal.bind.1 enclosed.1 acceptedBody
            carries.1 fitsProver.1 fitsVerifier.1
            (fun callee roleMap member =>
              callees callee roleMap (applications_keeps rest _ _ member)),
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing (applications body found) legal.bind.2 enclosed.2
            acceptedRest carries.2 fitsProver.2 fitsVerifier.2 callees⟩
    | .letOp (.at role op localBodies) arguments nested rest, enclosing, found, legal, enclosed,
        accepted, carries, fitsProver, fitsVerifier, callees =>
        ⟨fun arguments => at_replays quiet disjoint role op localBodies arguments _ _ _,
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing
            (applicationsOf nested (applicationOf (ProtocolOp.at role op localBodies) ++ found))
            legal.letOp.2.2 enclosed.2.2 (accepted_letOp accepted).2.2 carries.2.2 fitsProver
            fitsVerifier callees⟩
    | .letOp (.sample owner site law populated) arguments nested rest, enclosing, found, legal,
        enclosed, accepted, carries, fitsProver, fitsVerifier, callees =>
        ⟨fun arguments => sample_replays disjoint owner site law populated
            (fun _ arguments => fitsProver.1 arguments .nil)
            (fun _ arguments => fitsVerifier.1 arguments .nil) arguments _ _ _,
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing
            (applicationsOf nested (applicationOf (ProtocolOp.sample owner site law populated) ++ found))
            legal.letOp.2.2 enclosed.2.2 (accepted_letOp accepted).2.2 carries.2.2 fitsProver.2
            fitsVerifier.2 callees⟩
    | .letOp (.exchange sender receiver site type) arguments nested rest, enclosing, found, legal,
        enclosed, accepted, carries, fitsProver, fitsVerifier, callees =>
        ⟨exchange_admits layout laws place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler sender receiver site type
            nested legal.letOp.1 (accepted_letOp accepted).1 carries.1 fitsProver.1 fitsVerifier.1,
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing
            (applicationsOf nested (applicationOf (ProtocolOp.exchange sender receiver site type) ++ found))
            legal.letOp.2.2 enclosed.2.2 (accepted_letOp accepted).2.2 carries.2.2 fitsProver.2.2
            fitsVerifier.2.2 callees⟩
    | .letOp (.draw owner receivers site law populated) arguments nested rest, enclosing, found,
        legal, enclosed, accepted, carries, fitsProver, fitsVerifier, callees =>
        ⟨draw_admits layout laws place bound label first second disjoint holdsProver holdsVerifier
            isProver isVerifier proverHandler verifierHandler owner receivers site law populated
            nested legal.letOp.1 (accepted_letOp accepted).1 fitsProver.1 fitsVerifier.1,
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing
            (applicationsOf nested
              (applicationOf (ProtocolOp.draw owner receivers site law populated) ++ found))
            legal.letOp.2.2 enclosed.2.2 (accepted_letOp accepted).2.2 carries.2.2 fitsProver.2
            fitsVerifier.2 callees⟩
    | .letOp (.apply callee roleMap site permitted) arguments nested rest, enclosing, found, legal,
        enclosed, accepted, carries, fitsProver, fitsVerifier, callees =>
        ⟨apply_admits layout laws place bound label first second disjoint holdsProver holdsVerifier
            isProver isVerifier proverHandler verifierHandler marks callee roleMap site permitted
            nested legal.letOp.1 ⟨fitsProver.1, fitsProver.2.1⟩ ⟨fitsVerifier.1, fitsVerifier.2.1⟩
            (callees callee roleMap
              (applications_keeps rest _ _
                (applicationsOf_keeps nested _ _ (List.mem_append_left _ List.mem_cons_self)))),
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing
            (applicationsOf nested
              (applicationOf (ProtocolOp.apply callee roleMap site permitted) ++ found))
            legal.letOp.2.2 enclosed.2.2 (accepted_letOp accepted).2.2 carries.2.2 fitsProver.2.2
            fitsVerifier.2.2 callees⟩
    | .letOp (.repeat participants count carried collected captures covered) arguments bodies rest,
        enclosing, found, legal, enclosed, accepted, carries, fitsProver, fitsVerifier, callees => by
        obtain ⟨_, ⟨bodiesTouched, touchedBodies⟩, acceptedRest⟩ := accepted_letOp accepted
        obtain ⟨clean, legalBodies, legalRest⟩ := legal.letOp
        have related : RegionsReplay (serializeChannel layout laws _ _ _ _ isProver isVerifier)
            proverHandler verifierHandler first second _
            (bodies.denote (labelledMeaning model label functionTable oldTable (first.union second)))
            (bodies.denote (labelledMeaning model label functionTable oldTable first))
            (bodies.denote (labelledMeaning model label functionTable oldTable second)) := by
          cases bodiesTouched with
          | true =>
              exact regions_replay bodies
                (regions_admit layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler bodies (some participants)
                  (applicationOf
                    (ProtocolOp.repeat participants count carried collected captures covered) ++ found)
                  legalBodies enclosed.2.1 ⟨true, touchedBodies⟩ carries.2.1
                  (fitsProver.1 touchedBodies)
                  (fitsVerifier.1 touchedBodies)
                  (fun callee roleMap member =>
                    callees callee roleMap (applications_keeps rest _ _ member)))
          | false =>
              exact RegionsReplay.ofPasses _ _ _ _
                (regions_replay bodies
                  (regions_admit_plain quiet idle _ place.definition (some place.roles.prover)
                    (some place.roles.verifier) bound label first second disjoint holdsProver
                    holdsVerifier bodies (some participants)
                    (applicationOf
                      (ProtocolOp.repeat participants count carried collected captures covered) ++
                        found)
                    legalBodies enclosed.2.1 touchedBodies
                    (fun callee roleMap member =>
                      (callees callee roleMap (applications_keeps rest _ _ member)).2)))
                (passRegions_passAll _ (fitsProver.2.1 touchedBodies))
                (passRegions_passAll _ (fitsVerifier.2.1 touchedBodies))
        exact ⟨fun arguments =>
            repeat_replays participants count carried collected captures covered enclosed.1.1
              arguments _ _ _ related
              (fun outFirst => regions_idle idle first participants (absent_of_any outFirst) bodies
                enclosed.1.2)
              (fun outSecond => regions_idle idle second participants (absent_of_any outSecond)
                bodies enclosed.1.2),
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing
            (applicationsOf bodies
              (applicationOf
                (ProtocolOp.repeat participants count carried collected captures covered) ++ found))
            legalRest enclosed.2.2 acceptedRest carries.2.2 fitsProver.2.2 fitsVerifier.2.2
            callees⟩
    | .letOp (.choose participants tag captures outputs covered) arguments bodies rest, enclosing,
        found, legal, enclosed, accepted, carries, fitsProver, fitsVerifier, callees => by
        obtain ⟨_, ⟨bodiesTouched, touchedBodies⟩, acceptedRest⟩ := accepted_letOp accepted
        obtain ⟨clean, legalBodies, legalRest⟩ := legal.letOp
        have related : RegionsReplay (serializeChannel layout laws _ _ _ _ isProver isVerifier)
            proverHandler verifierHandler first second _
            (bodies.denote (labelledMeaning model label functionTable oldTable (first.union second)))
            (bodies.denote (labelledMeaning model label functionTable oldTable first))
            (bodies.denote (labelledMeaning model label functionTable oldTable second)) := by
          cases bodiesTouched with
          | true =>
              exact regions_replay bodies
                (regions_admit layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler bodies (some participants)
                  (applicationOf (ProtocolOp.choose participants tag captures outputs covered) ++
                    found)
                  legalBodies enclosed.2.1 ⟨true, touchedBodies⟩ carries.2.1
                  (fitsProver.1 touchedBodies)
                  (fitsVerifier.1 touchedBodies)
                  (fun callee roleMap member =>
                    callees callee roleMap (applications_keeps rest _ _ member)))
          | false =>
              exact RegionsReplay.ofPasses _ _ _ _
                (regions_replay bodies
                  (regions_admit_plain quiet idle _ place.definition (some place.roles.prover)
                    (some place.roles.verifier) bound label first second disjoint holdsProver
                    holdsVerifier bodies (some participants)
                    (applicationOf (ProtocolOp.choose participants tag captures outputs covered) ++
                      found)
                    legalBodies enclosed.2.1 touchedBodies
                    (fun callee roleMap member =>
                      (callees callee roleMap (applications_keeps rest _ _ member)).2)))
                (passRegions_passAll _ (fitsProver.2.1 touchedBodies))
                (passRegions_passAll _ (fitsVerifier.2.1 touchedBodies))
        exact ⟨fun arguments =>
            choose_replays participants tag captures outputs covered arguments _ _ _ related
              (fun outFirst => regions_idle idle first participants (absent_of_any outFirst) bodies
                enclosed.1)
              (fun outSecond => regions_idle idle second participants (absent_of_any outSecond)
                bodies enclosed.1),
          region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler rest enclosing
            (applicationsOf bodies
              (applicationOf (ProtocolOp.choose participants tag captures outputs covered) ++ found))
            legalRest enclosed.2.2 acceptedRest carries.2.2 fitsProver.2.2 fitsVerifier.2.2
            callees⟩

  /-- The same for closed regions. -/
  theorem regions_admit (layout : Layout operations) (laws : layout.Lawful model)
      {table : CalleeTable layout.threads.header old new} (quiet : QuietTable functionTable)
      (idle : CalleesIdle oldTable) (marks : MarkTable operations old) (place : Place) (bound : Nat)
      (label : Nat → Site) (first second : Side) (disjoint : first.Disjoint second)
      (holdsProver : first.Holds (some place.roles.prover) bound)
      (holdsVerifier : second.Holds (some place.roles.verifier) bound)
      (isProver : first place.roles.prover = true) (isVerifier : second place.roles.verifier = true)
      (proverHandler : ThreadHandler model layout.threads (first place.roles.prover)
        (first place.roles.verifier))
      (verifierHandler : ThreadHandler model layout.threads (second place.roles.prover)
        (second place.roles.verifier)) {signatures : List (List Located × List Located)} :
      ∀ (regions : Regions (ProtocolDialect operations functions old deployed) signatures)
        (enclosing : Option (List Nat)) (found : List (Nat × RoleMap)),
        Regions.Legal typeTable bound enclosing regions → regionsEnclosed regions →
        (∃ touched, touchesRegions layout.threads false table place.definition
          (some place.roles.prover) (some place.roles.verifier) regions = .ok touched) →
        RegionsCarry layout place.roles regions →
        FitsAll layout.threads (serializeRule (functions := functions) layout)
          (serializeMeaning layout) functionTable oldTable table
          (stepFits (serializeMeaning layout) marks) place first label proverHandler regions →
        FitsAll layout.threads (serializeRule (functions := functions) layout)
          (serializeMeaning layout) functionTable oldTable table
          (stepFits (serializeMeaning layout) marks) place second label verifierHandler regions →
        (∀ {header : ProtocolHeader} (callee : Var old header) (roleMap : RoleMap),
          (callee.index, roleMap) ∈ applicationsOf regions found →
          CalleeReplays layout laws table.threads marks oldTable callee
            (preimageOf roleMap (some place.roles.prover))
            (preimageOf roleMap (some place.roles.verifier))) →
        RegionsAdmit (serializeChannel layout laws _ _ _ _ isProver isVerifier) proverHandler
          verifierHandler functionTable oldTable label first second regions
    | .nil, _, _, _, _, _, _, _, _, _ => trivial
    | .cons body tail, enclosing, found, legal, enclosed, accepted, carries, fitsProver,
        fitsVerifier, callees => by
        obtain ⟨touched, accepted⟩ := accepted
        unfold touchesRegions at accepted
        obtain ⟨acceptedBody, acceptedTail⟩ := bothTouch_ok accepted
        exact ⟨region_admits layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler body enclosing found legal.cons.1 enclosed.1 acceptedBody
            carries.1 fitsProver.1 fitsVerifier.1
            (fun callee roleMap member =>
              callees callee roleMap (applicationsOf_keeps tail _ _ member)),
          regions_admit layout laws quiet idle marks place bound label first second disjoint holdsProver
            holdsVerifier isProver isVerifier proverHandler verifierHandler tail enclosing (applications body found) legal.cons.2 enclosed.2
            acceptedTail carries.2 fitsProver.2 fitsVerifier.2 callees⟩
end

end Threaded

end Zkc.Core
