import Zkc.Tools.IR.StructuredSource.NormalForm
import Zkc.Tools.IR.StructuredSource.Presentation

/-! Inspection and Lean syntax preserve typed service requests and ordered bounds. -/
set_option autoImplicit false
namespace Tests.NormalFormServicePrinting
open Lean Zkc.Source Zkc.Source.Structured NormalForm
open ZkcTools.StructuredSource.NormalForms

private def block (bound count : Nat) : Form [] [] [] [.indices] :=
  .query "positions" (.sampleIndices "random.F/0")
    (.cons (.capability "random.F/0" 7) (.cons (.index bound) (.cons (.index count) .nil)))
    (.done (.cons (.present (.var .here)) .nil))

example : formJson (block 8 3) = .arr #[.str "query", .str "positions",
    .arr #[.str "indices", .str "random.F/0"],
    .arr #[.arr #[.str "capability", .str "random.F/0", .num 7],
      .arr #[.str "index", .num 8], .arr #[.str "index", .num 3]],
    .arr #[.str "done", .arr #[.arr #[.str "present", .arr #[.str "var", .num 0]]]]] := rfl

example : serviceOpJson (.draw "F") = .arr #[.str "draw", .str "F"] := rfl
example : serviceOpJson (.sampleIndex "random.F/0") =
    .arr #[.str "index", .str "random.F/0"] := rfl
-- These output utilities use compiled JSON/string operations. Test them as tools;
-- the source normalizer and literal correspondence remain kernel checked.
#eval show IO Unit from do
  let printed := (ZkcTools.StructuredSource.Presentation.processText
    (laws := []) (callees := []) (initial := []) {} .outputs [] (block 8 3) 0).run' 0
  for (label, valid) in [
      ("process typed request", (printed.splitOn "(.sampleIndices \"random.F/0\")").length == 2),
      ("ordered bound/count", formJson (block 8 3) != formJson (block 3 8)),
      ("scalar/block method", serviceOpJson (.sampleIndex "random.F/0") !=
        serviceOpJson (.sampleIndices "random.F/0")),
      ("typed Lean literal", ZkcTools.StructuredSource.Presentation.serviceOpText
        (.sampleIndices "random.F/0") == "(.sampleIndices \"random.F/0\")")] do
    unless valid do throw (IO.userError ("normal-form service printing: " ++ label))

end Tests.NormalFormServicePrinting
