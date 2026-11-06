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
every role equation. The entire suffix is projected, never serialized. The
complete descriptor equality below checks this header and the shared body. -/
def repeatSiteText (selected : RepeatSite) (name : String) : String :=
  let source := name ++ "Selection.repeatSite"
  let suffix := "Eq.mp (show Region protocolDialect (" ++ source ++ ".spec.state ++ " ++
    source ++ ".context) " ++ source ++ ".outputs = Region protocolDialect " ++
    typesText (selected.spec.state ++ selected.context) ++ " " ++ typesText selected.outputs ++
    " from by kernel_rfl) " ++ source ++ ".next"
  "⟨" ++ ", ".intercalate [typesText selected.context, typesText selected.outputs,
    repeatText selected.spec, quoted selected.site, operandsText selected.operands,
    name ++ "Body", paren suffix] ++ "⟩"

def callbackDeclarations (name source : String) (ordinal : Nat) (callback : RepeatSite) : List String :=
  let locator := toString ordinal ++ " " ++ source
  ["def " ++ name ++ "Selection : RepeatOccurrence " ++ source ++
     " :=\n  checkedRepeat " ++ locator ++ " (by kernel_rfl)\n\n",
   "def " ++ name ++ "Body : Region protocolDialect " ++
     typesText (.index :: (callback.spec.state ++ callback.spec.captures)) ++ " " ++
     typesText callback.spec.state ++ " :=\n  " ++ regionText callback.body ++ "\n\n",
   "abbrev " ++ name ++ "Site : RepeatSite :=\n  " ++ repeatSiteText callback name ++ "\n\n",
   "theorem " ++ name ++ "_body : " ++ name ++ "Site.body = " ++ name ++ "Body := rfl\n\n",
   "theorem " ++ name ++ "_selected : (selectRepeat " ++ locator ++
     ").map (·.repeatSite) = some " ++
     name ++ "Site := by\n  kernel_rfl\n\n",
   "def " ++ name ++ "Occurrence : RepeatAt " ++ name ++ "Site " ++ source ++
     " :=\n  selectedRepeat " ++ name ++ "_selected\n\n"]

end ZkcTools.StructuredSource.Bindings
