import Zkc.Source.Structured.Import

open Zkc.Source Zkc.Source.Structured

namespace Tests.StructuredOpenAdmission
set_option smartUnfolding false

private def math (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .math, .privateDef, inputs, outputs, none, [], none, body⟩
private def localHelper (name : String) (inputs outputs : List Ty) (body : Block) : Definition :=
  .function ⟨name, .local, .privateDef, inputs, outputs, none, [], some (.local name []), body⟩
private def root (inputs outputs : List Ty) (inputScopes outputScopes : List (List String))
    (body : Block) (roles : List String := ["P", "V"]) : Definition :=
  .function ⟨"main", .protocol, .publicDef, inputs, outputs,
    some ⟨roles, inputScopes, outputScopes⟩, [], some (.protocol ⟨"main", []⟩), body⟩
private def unit (definitions : List Definition) (relations : List Relation := []) : Snapshot :=
  (let contractDefinitions : List Definition := definitions
   ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000", "main", [], relations, [], contractDefinitions,
    contractDefinitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows, {}⟩)
private def accepted (snapshot : Snapshot) : Bool := (check snapshot).isOk
private def first := math "first" [.boolean, .boolean] [.boolean] (.block [] (.ret [0]))
private def relay := math "relay" [.boolean, .boolean] [.boolean]
  (.block [.instruction (.call "first") [0, 1] [.boolean] [] ""] (.ret [0]))
private def calling (name : String) := root [.boolean, .boolean] [.boolean] [["P"], ["V"]] [["P"]]
  (.block [.instruction (.call name) [0, 1] [.boolean] [] ""] (.ret [0]))

-- Whole-unit typed admission: the second input need not be present where the
-- first result is available. A nested named closure preserves that dependency.
example : accepted (unit [calling "first", first]) = true := by decide +kernel
example : accepted (unit [calling "relay", relay, first]) = true := by decide +kernel

private def unused := math "unused" [.boolean, .boolean] [.boolean]
  (.block [.instruction .booleanAnd [0, 1] [.boolean] [] ""] (.ret [1]))
-- A model counterexample to denotation-only admission: the unused intermediate
-- still needs a common owner. This rejected snapshot is not native evidence.
example : accepted (unit [calling "unused", unused]) = false := by decide +kernel

private def separated := math "separated" [.boolean, .boolean] [.boolean, .boolean] (.block [] (.ret [0, 1]))
private def separatedRoot := root [.boolean, .boolean] [.boolean, .boolean] [["P"], ["V"]] [["P"], ["V"]]
  (.block [.instruction (.call "separated") [0, 1] [.boolean, .boolean] [] ""] (.ret [0, 1]))
example : accepted (unit [separatedRoot, separated]) = true := by decide +kernel

private def constant := math "constant" [.boolean, .boolean] [.boolean]
  (.block [.instruction (.booleanConstant true) [] [.boolean] [] ""] (.ret [0]))
example : accepted (unit [calling "constant", constant]) = true := by decide +kernel

private def strictSelect := math "select" [.boolean, .boolean] [.boolean]
  (.block [.instruction (.select .boolean) [1, 0, 0] [.boolean] [] ""] (.ret [0]))
example : accepted (unit [calling "select", strictSelect]) = false := by decide +kernel

private def aborting := localHelper "abort" [] [] (.block [] (.stop .abort "local-stop"))
private def abortRoot := root [.boolean] [.boolean] [["P", "V"]] [["V"]]
  (.block [.instruction (.localCall "abort" "P") [] [] [] "invoke"] (.ret [0]))
example : accepted (unit [abortRoot, aborting]) = true := by decide +kernel

-- Exact helper kinds and every stored declaration, including dormant bodies.
example : accepted (unit [calling "first", localHelper "first" [.boolean, .boolean] [.boolean]
    (.block [] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [calling "first", first,
    math "dormant" [.boolean] [.boolean]
      (.block [.instruction (.apply "first") [0] [.boolean] [] "apply"] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [calling "first", first,
    math "dormant" [] [.boolean]
      (.block [.instruction (.call "missing") [] [.boolean] [] ""] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [calling "first", first,
    math "bad-domain" [] [.field "unknown"] (.block [] (.ret []))]) = false := by decide +kernel

private def trivial (roles : List String) (scope : List String) :=
  root [.boolean] [.boolean] [scope] [scope] (.block [] (.ret [0])) roles
example : accepted (unit [trivial [] []]) = false := by decide +kernel
example : accepted (unit [trivial ["P", "P"] ["P"]]) = false := by decide +kernel
example : accepted (unit [trivial ["P", "V"] ["unknown"]]) = false := by decide +kernel
example : accepted (unit [trivial ["P", "V"] []]) = false := by decide +kernel
example : accepted (unit [trivial ["P", "V"] ["P", "P"]]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [] [["P"]] (.block [] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P", "V"]] (.block [] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.guard "V") [0] [] [] "guard"] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.guard "unknown") [0] [] [] "guard"] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.exchange "P" "P") [0] [.boolean] [] "send"] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.restrict ["V"]) [0] [.boolean] [] ""] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.restrict []) [0] [.boolean] [] ""] (.ret [0]))]) = false := by decide +kernel

private def service : Ty := .service scalarServiceContract
private def scalar : Ty := .field scalarDomain
private def drawing (owner : String) (scope : List String) :=
  root [service] [scalar] [scope] [[owner]]
    (.block [.instruction (.draw owner scalarDomain) [0] [scalar] [] "draw"] (.ret [0]))
example : accepted (unit [drawing "P" ["P"]]) = true := by decide +kernel
example : accepted (unit [drawing "P" ["P", "V"]]) = false := by decide +kernel
example : accepted (unit [drawing "V" ["P"]]) = false := by decide +kernel
example : accepted (unit [root [service] [service] [["P"]] [["P"]] (.block [] (.ret [0]))]) = false := by decide +kernel
example : accepted (unit [root [service] [] [["P"]] []
    (.block [.instruction (.restrict ["P"]) [0] [service] [] ""] (.ret []))]) = false := by decide +kernel
example : accepted (unit [root [service] [] [["P"]] []
    (.block [.instruction (.exchange "P" "V") [0] [service] [] "send"] (.ret []))]) = false := by decide +kernel
example : accepted (unit [drawing "P" ["P"], math "service-helper" [service] [] (.block [] (.ret []))]) = false := by decide +kernel
example : accepted (unit [root [.service "unknown"] [] [["P"]] [] (.block [] (.ret []))]) = false := by decide +kernel

private def relation : Relation := ⟨"relation", .publicDef, "opaque-kind", "opaque-key", "rev",
  [.boolean], [.boolean], ["statement"], none, []⟩
private def statementRoot := root [.boolean] [.boolean] [["P"]] [["P"]]
  (.block [.instruction (.statement "relation" ["P"] 0 none) [0] [] [] ""] (.ret [0]))
private def statementSource : Snapshot :=
  { unit [statementRoot] [relation] with contracts := [⟨"main", [
    ⟨.target, "claim", ⟨"relation", [⟨.input, 0, "P"⟩]⟩, none, some ⟨.output, 0, "P"⟩⟩]⟩] }
example : accepted statementSource = true := by rfl
example : accepted (unit [statementRoot] [relation]) = true := by rfl
example : accepted { statementSource with contracts := [⟨"main", [
    ⟨.input, "premise", ⟨"relation", [⟨.input, 0, "P"⟩]⟩, none, none⟩]⟩] } = true := by rfl
example : accepted { statementSource with
    contracts := [⟨"main", [
      ⟨.target, "claim", ⟨"other", [⟨.input, 0, "P"⟩]⟩, none, some ⟨.output, 0, "P"⟩⟩]⟩]
    relations := [relation, {relation with name := "other"}] } = false := by rfl
example : accepted (unit [statementRoot]) = false := by decide +kernel
example : accepted (unit [statementRoot] [{relation with purposes := []}]) = false := by decide +kernel
example : accepted (unit [statementRoot] [{relation with purposes := ["unknown"]}]) = false := by decide +kernel
example : accepted (unit [statementRoot] [{relation with outputs := []}]) = false := by decide +kernel
example : accepted (unit [statementRoot] [{relation with name := "main"}]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.statement "relation" ["V"] 0 none) [0] [] [] ""] (.ret [0]))] [relation]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.booleanConstant true) [] [.boolean] [] "",
      .instruction (.statement "relation" ["P"] 0 none) [0] [] [] ""] (.ret [0]))] [relation]) = false := by decide +kernel
example : accepted (unit [root [.boolean] [.boolean] [["P"]] [["P"]]
    (.block [.instruction (.statement "relation" ["P"] 1 none) [0] [] [] ""] (.ret [0]))] [relation]) = false := by decide +kernel

end Tests.StructuredOpenAdmission
