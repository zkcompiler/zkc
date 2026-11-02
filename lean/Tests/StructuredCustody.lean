import Zkc.Source.Structured.CustodySoundness
import Zkc.Source.Structured.Import
import Zkc.Construction.Scalar
import Zkc.Executable.Installed
import Zkc.Executable.Reading
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! Custody controls: the ledger's slot, occurrence, lineage, holder and frame
rules; the structured reader, binding admission and static custody admission;
the checked custody meaning against the erased one; and custody never becoming
an ordinary payload. -/

-- Direct reduction avoids repeatedly unfolding the dependent admission equations.
set_option smartUnfolding false

namespace StructuredCustodyTests
open Lean Zkc.Source Zkc.Source.Structured PIR.Custody

/-! ## Ledger -/

def ledger : Ledger := {}

def refusal {α : Type} : Except Refusal α → Option Refusal
  | .error reason => some reason
  | .ok _ => none

def accepted {α : Type} : Except Refusal α → Bool
  | .ok _ => true
  | .error _ => false

def errorOf {α : Type} : Except String α → Option String
  | .error code => some code
  | .ok _ => none

-- Different nominal slots: a permission of one slot never stands for another.
#guard refusal ((ledger.create "a" "V").2.consume "b" "V" 0) == some .slot
#guard refusal ((ledger.create "a" "V").2.pass "b" "V" 0) == some .slot

-- Same-slot distinct occurrences: two creations are two entries; consuming one
-- leaves the other live.
def twice : Ledger := ((ledger.create "a" "V").2.create "a" "V").2
#guard (ledger.create "a" "V").1 == 0 && ((ledger.create "a" "V").2.create "a" "V").1 == 1
#guard match twice.consume "a" "V" 0 with
  | .ok after => accepted (after.consume "a" "V" 1) && refusal (after.consume "a" "V" 0) == some .stale
  | .error _ => false

-- Pass continues the lineage; consume then create starts a new one.
def created : Ledger := (ledger.create "a" "V").2
#guard match created.pass "a" "V" 0 with
  | .ok (successor, after) => after.find? successor == some ⟨1, "a", "V", 0, 0⟩
  | .error _ => false
#guard match created.consume "a" "V" 0 with
  | .ok after => (after.create "a" "V").2.find? 1 == some ⟨1, "a", "V", 1, 0⟩
  | .error _ => false

-- Duplicate and stale use: a used token is stale, as is one never created.
#guard match created.consume "a" "V" 0 with
  | .ok after => refusal (after.consume "a" "V" 0) == some .stale
  | .error _ => false
#guard match created.pass "a" "V" 0 with
  | .ok (_, after) => refusal (after.pass "a" "V" 0) == some .stale &&
      refusal (after.consume "a" "V" 0) == some .stale
  | .error _ => false
#guard refusal (ledger.consume "a" "V" 0) == some .stale

-- Wrong holder: a role-local permission cannot be used by another role.
#guard refusal ((ledger.create "a" "P").2.consume "a" "V" 0) == some .holder

-- Frames: entry transfers the arguments; a return keeps only the returned
-- entries, now the caller's; a stop keeps none; outer entries are untouched.
def outer : Ledger := (((ledger.create "a" "V").2.create "a" "V").2.create "b" "V").2
#guard refusal (outer.enter "P" [0]) == some .holder
#guard refusal (outer.enter "V" [0, 0]) == some .duplicate
#guard match outer.enter "V" [0, 1] with
  | .ok inside =>
    -- A frame cannot use an outer entry it did not receive.
    refusal (inside.consume "b" "V" 2) == some .frame &&
    match (inside.create "a" "V") with
    | (fresh, withFresh) =>
      match withFresh.consume "a" "V" 1 with
      | .ok consumed =>
        match consumed.exit [fresh] with
        | .ok back =>
          -- Returned: the fresh entry, now in the caller's frame. Retired: the
          -- unreturned argument. Untouched: the outer entry.
          back.find? fresh == some ⟨fresh, "a", "V", fresh, 0⟩ && back.find? 0 == none &&
            back.find? 2 == some ⟨2, "b", "V", 2, 0⟩ && back.depth == 0
        | .error _ => false
      | .error _ => false
  | .error _ => false
#guard match outer.enter "V" [0] with
  | .ok inside =>
    let stopped := (inside.create "a" "V").2.stop
    stopped.find? 0 == none && stopped.find? 3 == none && stopped.find? 1 != none &&
      stopped.find? 2 != none && stopped.depth == 0
  | .error _ => false
-- A frame cannot return what it does not own.
#guard match outer.enter "V" [0] with
  | .ok inside => refusal (inside.exit [2]) == some .frame
  | .error _ => false

/-! ## Reader and binding admission -/

def slot : String := "zkl_resource_0123456789abcdef"
def unit : Ty := .resourceUnit slot
def unitJson (name : String := slot) : Json :=
  .arr #[.str "apply", .str "resource_unit", .arr #[.arr #[.str "domain", .str "Slot", .str name]]]

#guard match Structured.Format.type (unitJson) with
  | .ok type => type == unit
  | .error _ => false
#guard !(Structured.Format.type (unitJson "1slot")).isOk
#guard !(Structured.Format.type (unitJson "slot with space")).isOk

def bindingJson (contract : String) (sort : String) (inputs outputs : List Json) : Json :=
  .arr #[.str "binding", .str "b", .str contract,
    .arr #[.arr #[.str "domain", .str sort, .str slot]], .str "", .arr inputs.toArray, .arr outputs.toArray]

#guard (Structured.Format.binding (bindingJson "resource_unit.create" "Slot" [] [unitJson])).isOk
#guard (Structured.Format.binding (bindingJson "resource_unit.pass" "Slot" [unitJson] [unitJson])).isOk
#guard (Structured.Format.binding (bindingJson "resource_unit.consume" "Slot" [unitJson] [])).isOk
-- A slot is not a field root, a field root is not a slot, and signatures are
-- the installed ones.
#guard errorOf (Structured.Format.binding (bindingJson "resource_unit.create" "Field" [] [unitJson])) ==
  some "structured-binding-argument"
#guard errorOf (Structured.Format.binding (bindingJson "vector.empty" "Slot" [] [])) ==
  some "structured-binding-argument"
#guard errorOf (Structured.Format.binding (bindingJson "resource_unit.create" "Slot" [] [])) ==
  some "structured-binding-signature"
#guard errorOf (Structured.Format.binding (bindingJson "resource_unit.consume" "Slot" [unitJson] [unitJson])) ==
  some "structured-binding-signature"

/-! ## Static custody admission -/

def digest : String := "sha256:" ++ String.ofList (List.replicate 64 '0')

def binding (name contract : String) (inputs outputs : List Ty) : Binding :=
  ⟨name, contract, [slot], "", some ⟨[.domain "Slot" slot], inputs, outputs⟩⟩

def bindings : List Binding :=
  [binding "create" "resource_unit.create" [] [unit],
   binding "pass" "resource_unit.pass" [unit] [unit],
   binding "consume" "resource_unit.consume" [unit] []]

def exec (name : String) (operands : List Nat) (results : List Ty) (site : String) : Instruction :=
  .instruction (.exec "exec.apply" name []) operands results [] site

def localFunction (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .local, .privateDef, inputs, outputs, none, [], some (.local name []), body⟩

def mathFunction (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .math, .privateDef, inputs, outputs, none, [], none, body⟩

def protocol (name : String) (roles : List String) (inputs : List (Ty × List String))
    (outputs : List (Ty × List String)) (body : Block) : Definition :=
  .function ⟨name, .protocol, .publicDef, inputs.map (·.1), outputs.map (·.1),
    some ⟨roles, inputs.map (·.2), outputs.map (·.2)⟩, [], some (.protocol ⟨name, []⟩), body⟩

def unitSnapshot (definitions : List Definition) : Snapshot :=
  ⟨digest, "main", [], [], bindings, definitions,
    definitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows, {}⟩

def refused (raw : Snapshot) (code : String) : Bool :=
  match check raw with | .error actual => actual == code | .ok _ => false

def admitted (raw : Snapshot) : Bool := (check raw).isOk

/-- Create, pass and consume one permission inside one Local frame. -/
def roundTrip : Definition := localFunction "round" [] [.boolean]
  (.block [exec "create" [] [unit] "create", exec "pass" [0] [unit] "pass",
    exec "consume" [0] [] "consume", .instruction (.booleanConstant true) [] [.boolean] [] "true"]
    (.ret [0]))

def callRoot (callee : String) (outputs : List Ty) : Definition :=
  protocol "main" ["V"] [] (outputs.map (·, ["V"]))
    (.block [.instruction (.localCall callee "V") [] outputs [] "call"]
      (.ret (List.range outputs.length)))

#guard admitted (unitSnapshot [roundTrip, callRoot "round" [.boolean]])

-- The same permission used twice: refused by the frame check.
def duplicate : Definition := localFunction "round" [] [.boolean]
  (.block [exec "create" [] [unit] "create", exec "consume" [0] [] "consume",
    exec "consume" [0] [] "again", .instruction (.booleanConstant true) [] [.boolean] [] "true"]
    (.ret [0]))
#guard refused (unitSnapshot [duplicate, callRoot "round" [.boolean]]) "structured-custody-frame"

-- Returning the same permission twice duplicates it.
def returnedTwice : Definition := localFunction "round" [] [unit, unit]
  (.block [exec "create" [] [unit] "create"] (.ret [0, 0]))
#guard refused (unitSnapshot [returnedTwice, callRoot "round" [unit, unit]]) "structured-custody-frame"

-- A Local frame that creates and returns its permission is admitted, and the
-- protocol may carry it to its own port with one holder.
def issue : Definition := localFunction "issue" [] [unit]
  (.block [exec "create" [] [unit] "create"] (.ret [0]))
#guard admitted (unitSnapshot [issue, callRoot "issue" [unit]])

-- Math never mentions custody.
def mathCustody : Definition := mathFunction "keep" [unit] [unit] (.block [] (.ret [0]))
#guard refused (unitSnapshot [mathCustody, callRoot "round" [.boolean], roundTrip])
  "structured-header"

-- Custody does not cross a Local branch: frames are straight-line.
def branching : Definition := localFunction "round" [.boolean] [.boolean]
  (.block [exec "create" [] [unit] "create",
    .instruction .branch [1, 0] [] [.region [unit] [] (.block [exec "consume" [0] [] "inner"] (.yield [])),
      .region [unit] [] (.block [exec "consume" [0] [] "other"] (.yield []))] "branch"] (.ret [1]))
#guard refused (unitSnapshot [branching, protocol "main" ["V"] [(.boolean, ["V"])] [(.boolean, ["V"])]
    (.block [.instruction (.localCall "round" "V") [0] [.boolean] [] "call"] (.ret [0]))])
  "structured-custody-frame"

-- A custody port has one holder.
#guard refused (unitSnapshot [issue, protocol "main" ["P", "V"] [] [(unit, ["P", "V"])]
    (.block [.instruction (.localCall "issue" "V") [] [unit] [] "call"] (.ret [0]))])
  "structured-custody-holder"

-- A protocol body uses each permission at most once.
def drop : Definition := localFunction "drop" [unit] [.boolean]
  (.block [exec "consume" [0] [] "consume", .instruction (.booleanConstant true) [] [.boolean] [] "true"]
    (.ret [0]))
#guard refused (unitSnapshot [drop, protocol "main" ["V"] [(unit, ["V"])] [(.boolean, ["V"])]
    (.block [.instruction (.localCall "drop" "V") [0] [.boolean] [] "first",
      .instruction (.localCall "drop" "V") [1] [.boolean] [] "second"] (.ret [0]))])
  "structured-custody-use"
#guard admitted (unitSnapshot [drop, protocol "main" ["V"] [(unit, ["V"])] [(.boolean, ["V"])]
    (.block [.instruction (.localCall "drop" "V") [0] [.boolean] [] "first"] (.ret [0]))])

-- Custody is never transmitted.
#guard refused (unitSnapshot [issue, protocol "main" ["P", "V"] [] [(unit, ["V"])]
    (.block [.instruction (.localCall "issue" "P") [] [unit] [] "call",
      .instruction (.exchange "P" "V") [0] [unit] [] "send"] (.ret [0]))])
  "structured-service-use"

-- A repeated callback carries custody as state, never as a capture.
def repeatRoot (captured : Bool) : Definition :=
  let state : List Ty := if captured then [] else [unit]
  let captures : List Ty := if captured then [unit] else []
  protocol "main" ["V"] [(.index, ["V"]), (unit, ["V"])] (state.map (·, ["V"]))
    (.block [.instruction (.protocolRepeat state.length 4 ["V"] (state.map fun _ => ["V"])) [0, 1]
      state [.region (.index :: (state ++ captures)) state
        (.block [] (.yield (if captured then [] else [1])))] "repeat"]
      (.ret (List.range state.length)))
#guard admitted (unitSnapshot [repeatRoot false])
#guard refused (unitSnapshot [repeatRoot true]) "structured-custody-capture"

/-! ## Never a payload -/

#guard Ty.isHandle unit && !Ty.isForeignHandle unit && Ty.isCustody unit
#guard Ty.isForeignHandle (.service "random.bls12-381.fr/0")
#guard !Zkc.Construction.dataType unit
#guard (Catalogue.checkType blsRows admittedCatalogue unit).isOk
#guard !(Catalogue.checkType blsRows admittedCatalogue (.resourceUnit "1slot")).isOk

/-! ## Installed executable rows -/

section Executable
open Zkc.Executable

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def row (contract implementation : String) (arguments : List String := []) : Zkc.Executable.Binding :=
  ⟨"b", contract, arguments, implementation, []⟩

-- Each custody row takes exactly one valid slot and resolves to its transfer.
#guard installed.resolve (row "resource_unit.create" "logical/resource_unit.create" [slot]) [] ==
  some (.custody .create slot)
#guard installed.resolve (row "resource_unit.pass" "logical/resource_unit.pass" [slot]) [] ==
  some (.custody .pass slot)
#guard installed.resolve (row "resource_unit.consume" "logical/resource_unit.consume" [slot]) [] ==
  some (.custody .consume slot)
#guard installed.resolve (row "resource_unit.create" "logical/resource_unit.create" ["1slot"]) [] == none
#guard installed.resolve (row "resource_unit.create" "logical/resource_unit.create" []) [] == none
#guard installed.resolve (row "resource_unit.create" "logical/resource_unit.create" [slot, slot]) [] == none
-- The Boolean and checked index rows the current validators use.
#guard installed.resolve (row "bool.and" "arkworks/bool.and") [] == some (.calculate .booleanAnd)
#guard installed.resolve (row "bool.or" "arkworks/bool.or") [] == some (.calculate .booleanOr)
#guard installed.resolve (row "bool.not" "arkworks/bool.not") [] == some (.compute .booleanNot)
#guard installed.resolve (row "index.add" "native/index.add") [] ==
  some (.compute (.primitive .indexAdd))
#guard match (Computation.booleanNot.apply [.data (.boolean true)] : PIR.Outcome (List (Zkc.Construction.Value (ZMod 7) (ZMod 7)))) with
  | .returned [.data (.boolean false)] => true
  | _ => false
-- The custody sort of a valid slot is admitted at its logical representation only.
#guard installed.admits ⟨.data unit, "logical.resource_unit/0"⟩
#guard !installed.admits ⟨.data unit, "native.bool/0"⟩
#guard !installed.admits ⟨.data (.resourceUnit "1slot"), "logical.resource_unit/0"⟩
-- The constructed instruction profile has no custody transfer.
#guard match readOperation [] 0 "site" (.custody .create slot) [] with
  | .error (.unsupported "resource_unit") => true
  | _ => false

end Executable

/-! ## The checked meaning against the erased one -/

abbrev F := ZMod 7

example : SiteObservations.Interprets PIR.Custody.forget (custodyObservations "V") .closed :=
  custodyObservations_forget "V"

/-- create; pass; consume. -/
def frame : RawRegion Ty Op :=
  .letOp (.createUnit slot) [] [unit] .nil
    (.letOp (.passUnit slot) [0] [unit] .nil
      (.letOp (.consumeUnit slot) [0] [] .nil (.ret [])))

/-- create; consume; consume the same occurrence again: never admitted. -/
def doubleConsume : RawRegion Ty Op :=
  .letOp (.createUnit slot) [] [unit] .nil
    (.letOp (.consumeUnit slot) [0] [] .nil
      (.letOp (.consumeUnit slot) [0] [] .nil (.ret [])))

/-- create, then stop. -/
def stopping : RawRegion Ty Op :=
  .letOp (.createUnit slot) [] [unit] .nil (.stop .reject)

def empty : Environment (assignment F F) [] := fun position => nomatch position

def typed (raw : RawRegion Ty Op) : Option (Region dialect [] []) :=
  (raw.elaborate (dialect := dialect) [] []).toOption

def checked (region : Region dialect [] []) :=
  (region.denote (Evaluation.meaning (custodyObservations "V") ([] : Evaluation.Meanings F F _)) empty).run
    PIR.Custody.handler {}

def returnedRun (region : Region dialect [] []) : Bool :=
  match (checked region).outcome with | .returned _ => true | .stopped _ => false

#guard match typed frame with
  | some region => Region.custodyFrame (fun _ => false) [] region && returnedRun region &&
      (checked region).state.refused == none && (checked region).state.live == [] &&
      (checked region).events == [.create slot "V", .pass slot "V" 0, .consume slot "V" 1]
  | none => false
-- The ledger refuses what admission refuses statically.
#guard match typed doubleConsume with
  | some region => !Region.custodyFrame (fun _ => false) [] region && !returnedRun region &&
      (checked region).state.refused == some .stale
  | none => false
-- A stop leaves the created entry to its frame, whose stop retires it.
#guard match typed stopping with
  | some region => !returnedRun region && (checked region).state.refused == none &&
      (checked region).state.live.length == 1 && (checked region).state.stop.live == []
  | none => false

/-! ## Retained records -/

def records (records : List SourceRecord) : SourceDeclarations := { records := records }
def ticket : OriginTerm := .nominal .record "probe::Ticket" []
def holder : OriginTerm := .nominal .record "probe::Holder" []

-- Distributed records refuse: their retained row carries no role telescope and
-- no per-field placements.
#guard errorOf ((records []).leaves 8 (.nominal .logicalRecord "probe::State" []) []) ==
  some "component-declaration-distributed"
-- Nested records expand in place with their paths; a zero-length array of a
-- record contributes no leaf but still requires the record.
#guard match (records [⟨ticket, "ordinary", false, [("value", .field "f")]⟩,
    ⟨holder, "ordinary", true, [("inner", ticket), ("count", .index)]⟩]).leaves 8 holder ["port"] with
  | .ok leaves => leaves.map (·.path) == [["port", "inner", "value"], ["port", "count"]]
  | .error _ => false
#guard match (records [⟨ticket, "ordinary", false, [("value", .field "f")]⟩]).leaves 8
    (.array ticket "0") [] with
  | .ok leaves => leaves.isEmpty
  | .error _ => false
#guard errorOf ((records []).leaves 8 (.array ticket "0") []) == some "component-declaration-record"

-- The slots exhibited at custody leaves form one association: one slot per
-- closed resource record, distinct slots for distinct records, and every stored
-- custody type belongs to one of them.
def otherSlot : String := "zkl_resource_fedcba9876543210"
#guard (SourceDeclarations.checkSlots (unitSnapshot [issue]) [(ticket, slot), (ticket, slot)]).isOk
#guard errorOf (SourceDeclarations.checkSlots (unitSnapshot []) [(ticket, slot), (holder, slot)]) ==
  some "component-declaration-custody-identity"
#guard errorOf (SourceDeclarations.checkSlots (unitSnapshot []) [(ticket, slot), (ticket, otherSlot)]) ==
  some "component-declaration-custody-identity"
#guard errorOf (SourceDeclarations.checkSlots (unitSnapshot [issue]) []) ==
  some "component-declaration-custody-association"
-- A linear port has exactly one claim holder, checked apart from layout and
-- placement admission.
def linearTicket : SourceDeclarations := records [⟨ticket, "linear", false, [("value", .field "f")]⟩]
#guard errorOf (linearTicket.checkLinearHolders [⟨"ticket", ticket, ["P", "V"], 0, 1⟩]) ==
  some "component-claim-role"
#guard (linearTicket.checkLinearHolders [⟨"ticket", ticket, ["V"], 0, 1⟩]).isOk

end StructuredCustodyTests
