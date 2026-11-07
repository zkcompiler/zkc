module

public import Zkc.Source.Structured.Bindings.Selection
public import ZkcTools.StructuredSource.Presentation.Syntax

@[expose] public section

/-! Materialize a closed callback once from an admitted typed region. The
kernel checks the whole selected operation, including its captures and
unchanged suffix, before any client reasons about the smaller body. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings
open ZkcTools.StructuredSource.Presentation

/-- Keep the small typed header reducible without reevaluating admission at
every role equation. The suffix can also be materialized for a client proving its computation.
The complete descriptor equality checks the body and suffix in both cases. -/
def repeatSiteText (selected : RepeatSite) (name : String) (withContinuation : Bool) : String :=
  let source := name ++ "Selection.repeatSite"
  let suffix := "Eq.mp (show Region protocolDialect (" ++ source ++ ".spec.state ++ " ++
    source ++ ".context) " ++ source ++ ".outputs = Region protocolDialect " ++
    typesText (selected.spec.state ++ selected.context) ++ " " ++ typesText selected.outputs ++
    " from by kernel_rfl) " ++ source ++ ".next"
  let context := if withContinuation then name ++ "Context" else typesText selected.context
  "⟨" ++ ", ".intercalate [context, typesText selected.outputs,
    repeatText selected.spec, quoted selected.site, operandsText selected.operands,
    name ++ "Body", if withContinuation then name ++ "Next" else paren suffix] ++ "⟩"

def callbackDeclarations (name source : String) (ordinal : Nat) (callback : RepeatSite) (withContinuation := false) : List String :=
  let locator := toString ordinal ++ " " ++ source
  let continuation := if withContinuation then
    ["abbrev " ++ name ++ "Context : List Ty := " ++ typesText callback.context ++ "\n\n",
     "def " ++ name ++ "Next : Region protocolDialect (" ++ typesText callback.spec.state ++
      " ++ " ++ name ++ "Context) " ++ typesText callback.outputs ++ " :=\n  " ++ regionText callback.next ++ "\n\n"]
    else []
  ["def " ++ name ++ "Selection : RepeatOccurrence " ++ source ++
     " :=\n  checkedRepeat " ++ locator ++ " (by kernel_rfl)\n\n",
   "def " ++ name ++ "Body : Region protocolDialect " ++
     typesText (.index :: (callback.spec.state ++ callback.spec.captures)) ++ " " ++
     typesText callback.spec.state ++ " :=\n  " ++ regionText callback.body ++ "\n\n"] ++ continuation ++
  ["abbrev " ++ name ++ "Site : RepeatSite :=\n  " ++ repeatSiteText callback name withContinuation ++ "\n\n",
   "theorem " ++ name ++ "_body : " ++ name ++ "Site.body = " ++ name ++ "Body := rfl\n\n",
   "theorem " ++ name ++ "_selected : (selectRepeat " ++ locator ++
     ").map (·.repeatSite) = some " ++
     name ++ "Site := by\n  kernel_rfl\n\n",
   "def " ++ name ++ "Occurrence : RepeatAt " ++ name ++ "Site " ++ source ++
     " :=\n  selectedRepeat " ++ name ++ "_selected\n\n"]

end ZkcTools.StructuredSource.Bindings
