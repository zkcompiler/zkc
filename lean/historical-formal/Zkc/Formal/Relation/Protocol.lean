module

public import Zkc.Formal.Relation.Local

@[expose] public section

/-! Two models related: protocols, for every side.

A value of a side is held by a role: it is there when the role is in the side. Two held
values are related when the holder is absent, or when they are related values
(`SideRelated`).

The protocol operations whose two meanings are related for every side: `at` with a local
operation that is covered, `exchange`, `draw` and `sample` of a law that is respected, and
`apply` of a protocol whose meanings are related. A `repeat` and a `choose` are not among them
yet (`ProtocolOp.relatable`).

`program_related`: in two models whose rows are respected, a program that passes the test has
related meanings: every function, and every protocol for every side and under every path of
applications.
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Source Zkc.Core PIR

variable {M N : Model}

/-- Two held values are related: related values when the holder is present. -/
def HeldRelated {X Y : Type} (related : X → Y → Prop) :
    (present : Bool) → Held X present → Held Y present → Prop
  | true, value, image => related value image
  | false, _, _ => True

/-- The relation of two models at the values of a side. -/
def SideRelated (R : Carriers M N) (side : Side) :
    (located : Located) → SideValue M side located → SideValue N side located → Prop
  | ⟨type, holder⟩ => HeldRelated (Related R type) (side holder)

theorem HeldRelated.of {X Y : Type} {related : X → Y → Prop} {value : X} {image : Y}
    (same : related value image) :
    ∀ present : Bool, HeldRelated related present (Held.of present value) (Held.of present image)
  | true => same
  | false => trivial

theorem HeldRelated.absent {X Y : Type} (related : X → Y → Prop) :
    ∀ (present : Bool) (absent : present = false),
      HeldRelated related present (Held.absent present absent) (Held.absent present absent)
  | false, _ => trivial

/-! ## Values under a map of their indices -/

theorem ValuesRelated.unmap {α β : Type} {F G : β → Type} (related : ∀ index, F index → G index → Prop)
    (f : α → β) :
    ∀ (items : List α) (values : Values F (items.map f)) (images : Values G (items.map f)),
      ValuesRelated related values images →
        ValuesRelated (fun item => related (f item)) (unmapValues f items values)
          (unmapValues f items images)
  | [], _, _, _ => ValuesRelated.nil
  | _ :: rest, values, images, same =>
      ValuesRelated.cons (related := fun item => related (f item)) (same _ Var.here)
        (ValuesRelated.unmap related f rest values.tail images.tail same.tail)

theorem ValuesRelated.remap {α β : Type} {F G : β → Type} (related : ∀ index, F index → G index → Prop)
    (f : α → β) :
    ∀ (items : List α) (values : Values (fun item => F (f item)) items)
      (images : Values (fun item => G (f item)) items),
      ValuesRelated (fun item => related (f item)) values images →
        ValuesRelated related (remapValues f items values) (remapValues f items images)
  | [], _, _, _ => ValuesRelated.nil
  | _ :: rest, values, images, same =>
      ValuesRelated.cons (related := related) (same _ Var.here)
        (ValuesRelated.remap related f rest values.tail images.tail same.tail)

/-! ## The steps of a side -/

section Steps

variable (R : Carriers M N)

theorem absentValues_related :
    ∀ types : List Ty, ValuesRelated (fun type => HeldRelated (Related R type) false)
      (absentValues (X := M.Value) types) (absentValues (X := N.Value) types)
  | [] => ValuesRelated.nil
  | _ :: rest =>
      ValuesRelated.cons (related := fun type => HeldRelated (Related R type) false) trivial
        (absentValues_related rest)

/-- `at`: the local operation when the role is present, and nothing otherwise. -/
theorem performStep_related {inputs outputs : List Ty}
    {run : Values M.Value inputs → Process (Effects M) (Values M.Value outputs)}
    {run' : Values N.Value inputs → Process (Effects N) (Values N.Value outputs)}
    (runs : ∀ values images, ValuesRelated (Related R) values images →
      ProcessRelated R (ValuesRelated (Related R)) (run values) (run' images)) :
    ∀ (present : Bool) (values : Values (fun type => Held (M.Value type) present) inputs)
      (images : Values (fun type => Held (N.Value type) present) inputs),
      ValuesRelated (fun type => HeldRelated (Related R type) present) values images →
        ProcessRelated R (ValuesRelated (fun type => HeldRelated (Related R type) present))
          (performStep M run present values) (performStep N run' present images)
  | true, values, images, same => runs values images same
  | false, _, _, _ => .done (absentValues_related R outputs)

/-- `exchange`, for the memberships of the sender and of the receiver. -/
theorem exchangeStep_related (site : Site) (type : Ty) :
    ∀ (sender receiver : Bool) (value : Held (M.Value type) sender)
      (image : Held (N.Value type) sender), HeldRelated (Related R type) sender value image →
        ProcessRelated R (HeldRelated (Related R type) receiver)
          (exchangeStep M site type sender receiver value)
          (exchangeStep N site type sender receiver image)
  | true, true, _, _, same => .done same
  | true, false, _, _, same => .send site type same (.done trivial)
  | false, true, _, _, _ => .receive site type fun _ _ same => .done same
  | false, false, _, _, _ => .done trivial

/-- `sample`, for the membership of the owner. -/
theorem sampleStep_related (site : Site) (law : SamplingRow) (covered : Covered R law.output) :
    ∀ (owner : Bool) (inputs : Values (fun type => Held (M.Value type) owner) law.inputs)
      (inputs' : Values (fun type => Held (N.Value type) owner) law.inputs),
      ValuesRelated (fun type => HeldRelated (Related R type) owner) inputs inputs' →
        ProcessRelated R (HeldRelated (Related R law.output) owner)
          (sampleStep M site law owner inputs) (sampleStep N site law owner inputs')
  | true, _, _, same => .sample site law covered same fun _ _ related => .done related
  | false, _, _, _ => .done trivial

/-- The announcement that one receiver outside the owner's side receives. -/
theorem receiveStep_related (site : Site) (type : Ty) :
    ∀ receiver : Bool, ProcessRelated R (HeldRelated (Related R type) receiver)
      (receiveStep M site type receiver) (receiveStep N site type receiver)
  | true => .receive site type fun _ _ same => .done same
  | false => .done trivial

/-- The owner's part of `draw`, for the membership of the owner. -/
theorem drawStep_related {A B : Type} {post : A → B → Prop} (site : Site) (law : SamplingRow)
    (covered : Covered R law.output)
    {onDraw : M.Value law.output → Process (Effects M) A}
    {onDraw' : N.Value law.output → Process (Effects N) B}
    (draws : ∀ reply image, Related R law.output reply image →
      ProcessRelated R post (onDraw reply) (onDraw' image)) :
    ∀ (owner : Bool) (inputs : Values (fun type => Held (M.Value type) owner) law.inputs)
      (inputs' : Values (fun type => Held (N.Value type) owner) law.inputs)
      (onOutside : owner = false → Process (Effects M) A)
      (onOutside' : owner = false → Process (Effects N) B),
      ValuesRelated (fun type => HeldRelated (Related R type) owner) inputs inputs' →
      (∀ absent, ProcessRelated R post (onOutside absent) (onOutside' absent)) →
        ProcessRelated R post (drawStep M site law onDraw owner inputs onOutside)
          (drawStep N site law onDraw' owner inputs' onOutside')
  | true, _, _, _, _, same, _ => .draw site law covered same draws
  | false, _, _, _, _, _, outside => outside rfl

variable (side : Side)

/-- The copies of one coin that the roles of a list hold in the side. -/
theorem heldCopies_related (type : Ty) {reply : M.Value type} {image : N.Value type}
    (same : Related R type reply image) :
    ∀ roles : List Nat, ValuesRelated (SideRelated R side) (heldCopies M side type reply roles)
      (heldCopies N side type image roles)
  | [] => ValuesRelated.nil
  | role :: rest =>
      ValuesRelated.cons (related := SideRelated R side) (HeldRelated.of same (side role))
        (heldCopies_related type same rest)

/-- The announcements of a draw whose owner is outside the side. -/
theorem receiverReplies_related (site : Site) (type : Ty) :
    ∀ receivers : List Nat, ProcessRelated R (ValuesRelated (SideRelated R side))
      (receiverReplies M side site type receivers) (receiverReplies N side site type receivers)
  | [] => .done ValuesRelated.nil
  | role :: rest =>
      ProcessRelated.bind (receiveStep_related R site type (side role)) _ _ fun _ _ head =>
        ProcessRelated.bind (receiverReplies_related site type rest) _ _ fun _ _ tail =>
          .done (ValuesRelated.cons (related := SideRelated R side) head tail)

end Steps

/-! ## Protocol operations -/

/-- Two tables of protocols are related: every protocol, for every side and under every path
of applications, gives related processes on related inputs. -/
def ProtocolsRelated (R : Carriers M N) {protocols : List ProtocolHeader}
    (first : ProtocolTable M protocols) (second : ProtocolTable N protocols) : Prop :=
  ∀ {header : ProtocolHeader} (callee : Var protocols header) (path : List Nat) (side : Side)
    (values : Values (SideValue M side) header.inputs)
    (images : Values (SideValue N side) header.inputs),
    ValuesRelated (SideRelated R side) values images →
      ProcessRelated R (ValuesRelated (SideRelated R side)) (first.get callee path side values)
        (second.get callee path side images)

section Operations

variable {operations : List OperationSignature} {functions : List FunctionHeader}
  {protocols : List ProtocolHeader} {deployed : Bool}

/-- The protocol operations that the relation of two models covers, with the rows that their
local operations may use. -/
def ProtocolOp.relatable (rows : List Nat) :
    ProtocolOp operations functions protocols deployed → Bool
  | .at _ op bodies => LocalOp.relatable rows op && bodies.all (LocalOp.relatable rows)
  | .exchange .. => true
  | .draw _ _ _ law _ => rows.contains law.index
  | .sample _ _ law _ => rows.contains law.index
  | .apply .. => true
  | .repeat .. => false
  | .choose .. => false

variable {R : Carriers M N} {rows : List Nat}
  {functionsFirst : FunctionTable M functions} {functionsSecond : FunctionTable N functions}
  {first : ProtocolTable M protocols} {second : ProtocolTable N protocols}

/-- A protocol operation that passes the test has related meanings for every side, in two
models whose rows are respected and whose functions and earlier protocols are related. -/
theorem protocol_compatible (respected : RowsRespected R operations rows)
    (functionsRelated : FunctionsRelated R functionsFirst functionsSecond)
    (protocolsRelated : ProtocolsRelated R first second) (label : Nat → Site) (side : Side) :
    ∀ op : ProtocolOp operations functions protocols deployed, ProtocolOp.relatable rows op = true →
      CompatibleAt R (labelledMeaning M label functionsFirst first side)
        (labelledMeaning N label functionsSecond second side) (SideRelated R side) op
  | .at role op bodies, within => by
    simp only [ProtocolOp.relatable, Bool.and_eq_true] at within
    intro values images same _ _ _
    refine ProcessRelated.bind
      (performStep_related R
        (fun values images same =>
          local_compatible respected functionsRelated op within.1 values images same _ _
            (regions_related (local_compatible respected functionsRelated) bodies within.2))
        (side role) _ _
        (ValuesRelated.unmap (SideRelated R side) (fun type => (⟨type, role⟩ : Located)) _ _ _ same))
      _ _ ?_
    intro results images' parts
    exact .done (ValuesRelated.remap (SideRelated R side) (fun type => (⟨type, role⟩ : Located)) _ _ _ parts)
  | .exchange sender receiver site type, _ => by
    intro values images same _ _ _
    refine ProcessRelated.bind
      (exchangeStep_related R (label site) type (side sender) (side receiver) _ _ (same _ Var.here))
      _ _ ?_
    intro result image part
    exact .done (ValuesRelated.cons (related := SideRelated R side) part ValuesRelated.nil)
  | .draw owner receivers site (output := output) law populated, within => by
    intro values images same _ _ _
    have covered : Covered R output :=
      respected law (List.contains_iff_mem.mp within) output (List.mem_singleton.mpr rfl)
    refine drawStep_related R (label site) (.of law populated) covered ?_ (side owner) _ _ _ _
      (ValuesRelated.unmap (SideRelated R side) (fun type => (⟨type, owner⟩ : Located)) _ _ _ same) ?_
    · intro reply image related
      exact .done (ValuesRelated.cons (related := SideRelated R side)
        (HeldRelated.of related (side owner)) (heldCopies_related R side output related receivers))
    · intro absent
      refine ProcessRelated.bind (receiverReplies_related R side (label site) output receivers) _ _ ?_
      intro replies images' parts
      exact .done (ValuesRelated.cons (related := SideRelated R side)
        (HeldRelated.absent _ _ absent) parts)
  | .sample owner site (output := output) law populated, within => by
    intro values images same _ _ _
    have covered : Covered R output :=
      respected law (List.contains_iff_mem.mp within) output (List.mem_singleton.mpr rfl)
    refine ProcessRelated.bind
      (sampleStep_related R (label site) (.of law populated) covered (side owner) _ _
        (ValuesRelated.unmap (SideRelated R side) (fun type => (⟨type, owner⟩ : Located)) _ _ _ same))
      _ _ ?_
    intro reply image part
    exact .done (ValuesRelated.cons (related := SideRelated R side) part ValuesRelated.nil)
  | .apply callee roleMap site _, _ => by
    intro values images same _ _ _
    refine ProcessRelated.bind
      (protocolsRelated callee (label site).below (Side.preimage roleMap side) _ _
        (ValuesRelated.unmap (SideRelated R side) (Located.rename roleMap) _ _ _ same)) _ _ ?_
    intro results images' parts
    exact .done (ValuesRelated.remap (SideRelated R side) (Located.rename roleMap) _ _ _ parts)
  | .repeat .., within => Bool.noConfusion within
  | .choose .., within => Bool.noConfusion within

end Operations

/-! ## The protocols of a program -/

section Program

variable {typeTable : TypeTable} {operations : List OperationSignature}
  {functions : List FunctionHeader}

/-- The body of every protocol of a program passes the test. -/
def _root_.Zkc.Core.Protocols.relatable (rows : List Nat) :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols → Bool
  | _, .nil => true
  | _, .snoc earlier definition _ =>
      earlier.relatable rows && definition.body.all (ProtocolOp.relatable rows)

/-- Every function and every protocol of a program passes the test. -/
def _root_.Zkc.Core.Program.relatable (rows : List Nat) {protocols : List ProtocolHeader}
    (program : Program typeTable operations functions protocols) : Bool :=
  program.functions.relatable rows && program.protocols.relatable rows

variable {R : Carriers M N} {rows : List Nat}
  {functionsFirst : FunctionTable M functions} {functionsSecond : FunctionTable N functions}

theorem protocols_related (respected : RowsRespected R operations rows)
    (functionsRelated : FunctionsRelated R functionsFirst functionsSecond) (identities : Identities) :
    {protocols : List ProtocolHeader} → (program : Protocols typeTable operations functions protocols) →
      program.relatable rows = true →
        ProtocolsRelated R (program.table M functionsFirst identities)
          (program.table N functionsSecond identities)
  | _, .nil, _ => fun callee => callee.elimNil
  | _, .snoc (protocols := earlierHeaders) earlier definition _, within => by
    simp only [Protocols.relatable, Bool.and_eq_true] at within
    have before : ProtocolsRelated R (earlier.table M functionsFirst identities)
        (earlier.table N functionsSecond identities) :=
      protocols_related respected functionsRelated identities earlier within.1
    intro callee path side values images same
    cases callee with
    | here =>
      exact region_related
        (protocol_compatible respected functionsRelated before
          (ownSites (identities earlierHeaders.length) path) side)
        definition.body within.2 _ _ (EnvironmentRelated.ofValues same)
    | there callee => exact before callee path side values images same

/-- The relation theorem. Two models whose rows, of the numbers given, are respected by a
relation give every function and every protocol of a program that passes the test related
meanings: on related inputs the two processes perform the same effects at the same sites with
related values, stop alike, and return related values. -/
theorem program_related (respected : RowsRespected R operations rows)
    {protocols : List ProtocolHeader} (program : Program typeTable operations functions protocols)
    (within : program.relatable rows = true) (identities : Identities) :
    FunctionsRelated R (program.functionTable M) (program.functionTable N) ∧
      ProtocolsRelated R (program.protocolTable M identities) (program.protocolTable N identities) := by
  simp only [Program.relatable, Bool.and_eq_true] at within
  have functionsRelated : FunctionsRelated R (program.functionTable M) (program.functionTable N) :=
    functions_related respected program.functions within.1
  exact ⟨functionsRelated,
    protocols_related respected functionsRelated identities program.protocols within.2⟩

end Program

end Zkc.Formal
