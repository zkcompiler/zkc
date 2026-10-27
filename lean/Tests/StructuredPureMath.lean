import Zkc.Source.Structured.RealizationTotality
import Zkc.Source.Structured.NormalForm.Presentation
import Mathlib.Data.ZMod.Basic

/-! Authored reader and semantics controls for pure shape calculations.
These fixtures are not captures from the pending frontend exporter. -/

set_option autoImplicit false
open Lean Zkc.Source Zkc.Source.Structured

namespace Tests.StructuredPureMath

private abbrev F := ZMod 97

-- Kernel reduction checks the efficient procedure, including a huge supplied
-- exponent with a tiny input. No control constructs an enormous power or list.
example : naturalPowerOfTwo 0 0 = false := rfl
example : naturalPowerOfTwo 1 0 = true := rfl
example : naturalPowerOfTwo 2 1 = true := rfl
example : naturalPowerOfTwo 3 1 = false := rfl
example : naturalPowerOfTwo (2 ^ 63) 63 = true := rfl
example : naturalPowerOfTwo (2 ^ 64) 64 = true := rfl
example : naturalPowerOfTwo 2 (2 ^ 64 - 1) = false := rfl

example (n r : Nat) : naturalPowerOfTwo n r = true ↔ n = 2 ^ r :=
  naturalPowerOfTwo_eq_true n r

example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] .indexLess
    (.cons (2 ^ 64) (.cons (2 ^ 64 + 1) .nil)) .nil = .done (.cons true .nil) := rfl
example : Evaluation.operationOn (ringModel F F) SiteObservations.closed [] .indexPowerOfTwo
    (.cons (2 ^ 64) (.cons 64 .nil)) .nil = .done (.cons true .nil) := rfl
example : Evaluation.operation (F := F) (G := F) SiteObservations.closed [] (.exec .indexLess)
    (.cons (2 ^ 64) (.cons (2 ^ 64 + 1) .nil)) .nil = .halt .refused := rfl
example : Evaluation.operationOn (ringModel F F) SiteObservations.closed [] (.exec .indexLess)
    (.cons (2 ^ 64) (.cons (2 ^ 64 + 1) .nil)) .nil = .halt .refused := rfl

-- All lists return in Math; executable length separately checks admission.
example (xs : List F) :
    Evaluation.operation (F := F) (G := F) SiteObservations.closed [] (.vectorLength scalarDomain)
      (.cons xs .nil) .nil = .done (.cons xs.length .nil) := rfl
example (xs : List F) (overlarge : indexLimit ≤ xs.length) :
    Evaluation.operation (F := F) (G := F) SiteObservations.closed [] (.exec (.vectorLength scalarDomain))
      (.cons xs .nil) .nil = .halt .exhausted := by
  simp only [Evaluation.operation, Primitive.evaluate, not_lt.mpr overlarge, ↓reduceIte, primitiveOutcome]
example (xs : List F) (overlarge : indexLimit ≤ xs.length) :
    Evaluation.operationOn (ringModel F F) SiteObservations.closed [] (.exec (.vectorLength scalarDomain))
      (.cons xs .nil) .nil = .halt .exhausted := by
  simp only [Evaluation.operationOn, Primitive.evaluateOn, not_lt.mpr overlarge, ↓reduceIte, primitiveOutcome]

example (n r : Nat) (hn : n < indexLimit) :
    (if r < 64 then n = (1 <<< r) else False) ↔ n = 2 ^ r :=
  guarded_shift_powerOfTwo n r hn

-- All three operations enter the total normal-form term language. The kernel
-- checks the actual normalized form, rather than only its success flag.
private def powerBody : Region protocolDialect [.index, .index] [.boolean] :=
  .letOp (.calculate .indexPowerOfTwo rfl) (.cons .here (.cons (.there .here) .nil))
    .nil (.ret (.cons .here .nil))
private def lessBody : Region protocolDialect [.index, .index] [.boolean] :=
  .letOp (.calculate .indexLess rfl) (.cons .here (.cons (.there .here) .nil))
    .nil (.ret (.cons .here .nil))
private def lengthBody : Region protocolDialect [.vector scalarDomain] [.index] :=
  .letOp (.calculate (.vectorLength scalarDomain) rfl) (.cons .here .nil)
    .nil (.ret (.cons .here .nil))

example : NormalForm.normalize {} powerBody 0 1 (.cons .present (.cons .present .nil)) =
    .ok (.done (.cons (.present (.calc .indexPowerOfTwo rfl
      (.cons (.var .here) (.cons (.var (.there .here)) .nil)) .here)) .nil)) := rfl
example : NormalForm.normalize {} lessBody 0 1 (.cons .present (.cons .present .nil)) =
    .ok (.done (.cons (.present (.calc .indexLess rfl
      (.cons (.var .here) (.cons (.var (.there .here)) .nil)) .here)) .nil)) := rfl
example : NormalForm.normalize {} lengthBody 0 1 (.cons .present .nil) =
    .ok (.done (.cons (.present (.calc (.vectorLength scalarDomain) rfl
      (.cons (.var .here) .nil) .here)) .nil)) := rfl

example : Evaluation.componentOperation (F := F) (G := F) SiteObservations.closed ⟨[], []⟩
    .indexPowerOfTwo (.cons none (.cons (some (2 ^ 64 - 1)) .nil)) .nil =
      .done (.cons none .nil) := rfl

private def root : Definition := .function ⟨"main", .protocol, .publicDef, [], [],
  some ⟨["P"], [], []⟩, [], some (.protocol ⟨"main", []⟩), .block [] (.ret [])⟩

private def snapshot (definitions : List Definition) : Snapshot :=
  ⟨"sha256:" ++ String.ofList (List.replicate 64 '0'), "main", [], [], [], definitions,
    definitions.filterMap (fun definition =>
      if definition.kind == .protocol then some ⟨definition.name, []⟩ else none), blsRows, {}⟩

private def mathHelper (name : String) (op : Descriptor) (inputs outputs : List Ty)
    (site : String := "") (regions : List WireRegion := []) : Definition :=
  .function ⟨name, .math, .privateDef, inputs, outputs, none, [], none,
    .block [.instruction op (List.range inputs.length) outputs regions site]
      (.ret (List.range outputs.length))⟩

private def shapeInputs : List Ty := [.vector scalarDomain, .index, .index]
private def shape : Definition := .function ⟨"shape", .math, .privateDef, shapeInputs,
  [.boolean], none, [], none,
  .block [
    .instruction (.vectorLength scalarDomain) [0] [.index] [] "",
    .instruction .indexPowerOfTwo [0, 2] [.boolean] [] "",
    .instruction .indexLess [4, 3] [.boolean] [] "",
    .instruction (.booleanConstant false) [] [.boolean] [] "",
    .instruction .booleanEqual [0, 1] [.boolean] [] "",
    .instruction .booleanAnd [0, 3] [.boolean] [] ""] (.ret [0])⟩

private def shapeHelper : Helper := ⟨"shape", .math, shapeInputs, [.boolean]⟩

private def refusedWith {α : Type} (result : Except String α) (expected : String) : Bool :=
  match result with | .error actual => actual == expected | .ok _ => false

private def resultBool (result : PIR.Process closedInterface (Values (assignment F F) [.boolean])) :
    Option Bool :=
  match result with | .done (.cons value .nil) => some value | _ => none

private def run : IO Unit := do
  let failures ← IO.mkRef ([] : List String)
  let count ← IO.mkRef 0
  let test (name : String) (ok : Bool) : IO Unit := do
    count.modify (· + 1)
    unless ok do failures.modify (name :: ·)
  let less := mathHelper "less" .indexLess [.index, .index] [.boolean]
  let power := mathHelper "power" .indexPowerOfTwo [.index, .index] [.boolean]
  let length := mathHelper "length" (.vectorLength scalarDomain) [.vector scalarDomain] [.index]
  let source := snapshot [root, less, power, length, shape]
  let .ok program := check source | throw (IO.userError "pure Math fixture did not admit")
  test "pure realization closure" ((check { source with definitions := source.definitions ++ [
    .realization ⟨"less_realized", [.index, .index], [.boolean], "less"⟩,
    .realization ⟨"power_realized", [.index, .index], [.boolean], "power"⟩,
    .realization ⟨"length_realized", [.vector scalarDomain], [.index], "length"⟩,
    .realization ⟨"shape_realized", shapeInputs, [.boolean], "shape"⟩] }).isOk)
  let table : Meanings F F :=
    program.payload.definitions.foldl (Evaluation.extendMeanings SiteObservations.closed) []
  let domainTable : MeaningsOn (ringModel F F).toCarriers :=
    program.payload.definitions.foldl (Evaluation.extendMeaningsOn (ringModel F F) SiteObservations.closed) []
  for (n, r, expected) in [(0, 0, false), (1, 0, true), (2, 1, true), (3, 1, false),
      (2 ^ 63, 63, true), (2 ^ 64, 64, true), (2, 2 ^ 64 - 1, false)] do
    let args : Values (assignment F F) [.index, .index] := .cons n (.cons r .nil)
    let helper : Helper := ⟨"power", .math, [.index, .index], [.boolean]⟩
    test s!"Math power {n}/{r}" (resultBool (invoke table helper args) == some expected)
    test s!"domain Math power {n}/{r}" (resultBool (invoke domainTable helper args) == some expected)
  let lessHelper : Helper := ⟨"less", .math, [.index, .index], [.boolean]⟩
  for (a, b, expected) in [(0, 0, false), (0, 1, true), (2 ^ 64, 2 ^ 64 + 1, true)] do
    let args : Values (assignment F F) [.index, .index] := .cons a (.cons b .nil)
    test "Math less" (resultBool (invoke table lessHelper args) == some expected)
    test "domain Math less" (resultBool (invoke domainTable lessHelper args) == some expected)
  for xs in [[], [1], [1, 2, 3, 4]] do
    let helper : Helper := ⟨"length", .math, [.vector scalarDomain], [.index]⟩
    let args : Values (assignment F F) [.vector scalarDomain] := .cons xs .nil
    let lengthResult := fun (result : PIR.Process closedInterface (Values (assignment F F) [.index])) =>
      match result with | .done (.cons value .nil) => some value | _ => none
    test "Math length" (lengthResult (invoke table helper args) == some xs.length)
    test "domain Math length" (lengthResult (invoke domainTable helper args) == some xs.length)
  for (xs, r, maximum, expected) in
      [([], 0, 0, false), ([1], 0, 0, true), ([1, 2], 1, 1, true),
       ([1, 2], 1, 0, false), ([1, 2, 3], 1, 1, false), ([1], 2 ^ 64 - 1, 8, false)] do
    let args : Values (assignment F F) shapeInputs := .cons xs (.cons r (.cons maximum .nil))
    test "Math shape" (resultBool (invoke table shapeHelper args) == some expected)
    test "domain Math shape" (resultBool (invoke domainTable shapeHelper args) == some expected)
  for (wire, descriptor) in [
      (Json.arr #[.str "index.less"], Descriptor.indexLess),
      (.arr #[.str "index.power_of_two"], .indexPowerOfTwo),
      (.arr #[.str "vector.length", .str scalarDomain], .vectorLength scalarDomain)] do
    test "wire descriptor" ((Format.descriptor wire).toOption == some descriptor)
  for wire in [Json.arr #[.str "index.less", .str "extra"],
      .arr #[.str "index.power_of_two", .str "extra"], .arr #[.str "vector.length"],
      .arr #[.str "vector.length", .str scalarDomain, .str "extra"]] do
    test "wrong descriptor arity" (refusedWith (Format.descriptor wire) "structured-operation-unsupported")
  for (descriptor, inputs, outputs) in [(Descriptor.indexLess, [.index, .index], [.boolean]),
      (.indexPowerOfTwo, [.index, .index], [.boolean]),
      (.vectorLength scalarDomain, [.vector scalarDomain], [.index])] do
    let make (inputs outputs : List Ty) (site : String := "") (regions : List WireRegion := []) :=
      mathHelper "work" descriptor inputs outputs site regions
    test "wrong input types" (refusedWith (check (snapshot [root, make [.boolean] outputs]))
      "structured-formation")
    test "wrong output type" (refusedWith (check (snapshot [root, make inputs [.field scalarDomain]]))
      "structured-formation")
    test "Math operation site" (refusedWith (check (snapshot [root, make inputs outputs "site"]))
      "structured-math-site")
    test "unexpected callback" (!(check (snapshot [root, make inputs outputs ""
      [.region [] [] (.block [] (.yield []))]])).isOk)
    let .function f := make inputs outputs | throw (IO.userError "expected function")
    let localDefinition := Definition.function { f with kind := .local, origin := some (.local "work" []) }
    test "Local cannot own pure operation" (refusedWith (check (snapshot [root, localDefinition]))
      "structured-local-operation")
  for (domain, error) in [("missing", "structured-domain-unknown"),
      (groupDomain, "structured-domain-sort")] do
    test "wrong length domain" (refusedWith (check (snapshot [root,
      mathHelper "bad" (.vectorLength domain) [.vector scalarDomain] [.index]])) error)
  -- The pure calculation still needs a common available participant.
  let disjoint : Definition := .function ⟨"main", .protocol, .publicDef, [.index, .index], [.boolean],
    some ⟨["P", "V"], [["P"], ["V"]], [["V"]]⟩, [], some (.protocol ⟨"main", []⟩),
    .block [.instruction .indexLess [0, 1] [.boolean] [] ""] (.ret [0])⟩
  test "disjoint roles" (refusedWith (check (snapshot [disjoint])) "structured-availability-requirement")
  let .function f := disjoint | throw (IO.userError "expected protocol")
  let shared := Definition.function { f with interface := some ⟨["P", "V"], [["V"], ["V"]], [["V"]]⟩ }
  test "shared role" ((check (snapshot [shared])).isOk)
  let errors ← failures.get
  unless errors.isEmpty do throw (IO.userError s!"pure Math failures: {errors.reverse}")
  IO.println s!"structured-pure-math: {← count.get} controls passed"

#eval run

end Tests.StructuredPureMath
