import Zkc.Source.Structured.RealizationTotality
import Zkc.Source.Structured.NormalForm.Presentation
import Mathlib.Data.ZMod.Basic

/-! Total prefix restriction and exact reader/typed admission controls. -/
set_option autoImplicit false
open Lean Zkc.Source Zkc.Source.Structured
namespace Tests.StructuredRestrictPrefix

private abbrev F := ZMod 97

-- The equations hold for arbitrary lists, without a shape or resource premise.
example {K H : Type} [CommRing K] [AddCommGroup H] [Module K H]
    [DecidableEq K] [DecidableEq H] (xs point : List K) :
    Evaluation.operation (F := K) (G := H) SiteObservations.closed []
      (.multilinearRestrictPrefix scalarDomain) (.cons xs (.cons point .nil)) .nil =
    .done (.cons (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) .nil) := rfl

example (model : DomainModel) (d : String) (xs point : List (model.Field d)) :
    Evaluation.operationOn model SiteObservations.closed []
      (.multilinearRestrictPrefix d) (.cons xs (.cons point .nil)) .nil =
    .done (.cons (Zkc.Polynomial.Multilinear.restrictPrefixValues xs point) .nil) := rfl

example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([] : List F) [2, 3] = [] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([9] : List F) [] = [9] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([9] : List F) [2] = [] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([1, 7, 2] : List F) [2] = [13] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([1, 7, 2, 9, 99] : List F) [2] = [3, 11] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([1, 7, 2, 9] : List F) [2, 3] = [27] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([1, 7, 2, 9] : List F) [3, 2] = [22] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([1, 7, 2, 9] : List F) [2, 3, 4] = [] := rfl
example : Zkc.Polynomial.Multilinear.restrictPrefixValues ([0, 1, 1, 0] : List (ZMod 2)) [1, 0] = [1] := rfl

private def restrictionBody : Region protocolDialect
    [.vector scalarDomain, .vector scalarDomain] [.vector scalarDomain] :=
  .letOp (.calculate (.multilinearRestrictPrefix scalarDomain) rfl)
    (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil))

example : NormalForm.normalize {} restrictionBody 0 1 (.cons .present (.cons .present .nil)) =
    .ok (.done (.cons (.present (.calc (.multilinearRestrictPrefix scalarDomain) rfl
      (.cons (.var .here) (.cons (.var (.there .here)) .nil)) .here)) .nil)) := rfl

private abbrev vector := Ty.vector scalarDomain
private def root : Definition := .function ⟨"main", .protocol, .publicDef, [], [],
  some ⟨["P"], [], []⟩, [], some (.protocol ⟨"main", []⟩), .block [] (.ret [])⟩
private def helper (op : Descriptor := .multilinearRestrictPrefix scalarDomain)
    (inputs : List Ty := [vector, vector]) (outputs : List Ty := [vector])
    (kind : Kind := .math) (site : String := "")
    (regions : List WireRegion := []) : Definition :=
  .function ⟨"restrict", kind, .privateDef, inputs, outputs, none, [], (if kind == .local then some (.local "restrict" []) else none),
    .block [.instruction op (List.range inputs.length) outputs regions site] (.ret [0])⟩
private def snapshot (definition : Definition) : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], [],
    [root, definition], [⟨"main", []⟩], blsRows, {}⟩
private def refused {α : Type} (result : Except String α) (code : String) : Bool :=
  match result with | .error actual => actual == code | .ok _ => false

private def failed {α : Type} (result : Except String α) : Bool := !result.isOk

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let descriptor := Descriptor.multilinearRestrictPrefix scalarDomain
  test "exact wire" ((Format.descriptor (.arr #[.str "multilinear.restrict_prefix", .str scalarDomain])).toOption == some descriptor)
  for wire in [Json.arr #[.str "multilinear.restrict_prefix"],
      .arr #[.str "multilinear.restrict_prefix", .str scalarDomain, .str "extra"],
      .arr #[.str "multilinear.restrict_prefix", .num 0],
      .arr #[.str "multilinear.restrict_prefix", .str ""],
      .arr #[.str "multilinear.restrictPrefix", .str scalarDomain]] do
    test "malformed descriptor" (failed (Format.descriptor wire))
  test "admission" ((check (snapshot (helper))).isOk)
  test "unknown nominal" (refused (check (snapshot (helper (.multilinearRestrictPrefix "missing")))) "structured-domain-unknown")
  for (inputs, outputs) in [([vector], [vector]), ([vector, .index], [vector]),
      ([vector, .vector "koala-bear"], [vector]), ([vector, vector], [.index])] do
    test "ordered typed ports" (failed (check (snapshot (helper descriptor inputs outputs))))
  test "Local refusal" (refused (check (snapshot (helper descriptor [vector, vector] [vector] .local))) "structured-local-operation")
  test "site refusal" (refused (check (snapshot (helper descriptor [vector, vector] [vector] .math "extra"))) "structured-math-site")
  test "region refusal" (failed (check (snapshot (helper descriptor [vector, vector] [vector] .math "" [.region [] [] (.block [] (.ret []))]))))
  let source := snapshot (helper)
  test "realization" ((check {source with definitions := source.definitions ++ [
    .realization ⟨"restrict_local", [vector, vector], [vector], "restrict"⟩]}).isOk)
  let .ok program := check source | throw (IO.userError "restriction fixture did not admit")
  let table : Meanings F F := program.payload.definitions.foldl
    (Evaluation.extendMeanings SiteObservations.closed) []
  let domainTable : MeaningsOn (ringModel F F).toCarriers := program.payload.definitions.foldl
    (Evaluation.extendMeaningsOn (ringModel F F) SiteObservations.closed) []
  let spec : Helper := ⟨"restrict", .math, [vector, vector], [vector]⟩
  let cases : List (List F × List F × List F) := [([], [], []), ([], [2], []), ([9], [], [9]),
      ([9], [2], []), ([1, 7, 2], [], [1, 7, 2]), ([1, 7, 2], [2], [13]),
      ([1, 7, 2, 9, 99], [2], [3, 11]), ([1, 7, 2, 9], [2, 3], [27]),
      ([1, 7, 2, 9], [3, 2], [22]), ([1, 7, 2, 9], [2, 3, 4], [])]
  for (xs, point, expected) in cases do
    let args : Values (assignment F F) [vector, vector] := .cons xs (.cons point .nil)
    let result := fun (p : PIR.Process closedInterface (Values (assignment F F) [vector])) =>
      match p with | .done (.cons ys .nil) => ys == expected | _ => false
    test "admitted uniform denotation" (result (invoke table spec args))
    test "admitted domain denotation" (result (invoke domainTable spec args))
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError (String.intercalate ", " errors.reverse))
  IO.println s!"structured-restrict-prefix: {← count.get} controls passed"

#eval run
end Tests.StructuredRestrictPrefix
