import ZkcTools.StructuredSource.ProcessReference
import Lean.Meta.Check
import Lean.Util.NumObjs

/-! Narrow warm assembly costs at one, two and four placements. Each placement
uses the same installed theorem constant. This measures reference assembly and
kernel checking, not imports, source admission or a complete protocol build. -/
set_option autoImplicit false
namespace Tests.ProcessReferenceSharing
open PIR

def mathematical {I : Signature} (value : Nat) : Process I Nat := .done (value + 1)

def sourceHelper {I : Signature} (value : Nat) : Process I Nat :=
  (mathematical value).bind Process.done

theorem installed {I : Signature} (value : Nat) :
    sourceHelper (I := I) value = mathematical value := Process.bind_done _

def once {I : Signature} (value : Nat) : Process I Nat := sourceHelper value
def twice {I : Signature} (value : Nat) : Process I Nat :=
  (sourceHelper value).bind sourceHelper
def four {I : Signature} (value : Nat) : Process I Nat :=
  (sourceHelper value).bind fun first =>
    (sourceHelper first).bind fun second =>
      (sourceHelper second).bind sourceHelper

source_reference oneView from @once using [once, installed]
source_reference twoView from @twice using [twice, installed]
source_reference fourView from @four using [four, installed]

open Lean Elab Command Term Meta in
run_cmd do
  for (placements, source, rules) in [
      (1, (← `(term| @once)), (← `(term| once))),
      (2, (← `(term| @twice)), (← `(term| twice))),
      (4, (← `(term| @four)), (← `(term| four)))] do
    liftTermElabM do
      let started ← IO.monoNanosNow
      let expression ← withoutErrToSorry <| elabTerm
        (← `(term| checked_process_reference% $source using [$rules, installed])) none
      synthesizeSyntheticMVarsNoPostponing
      let expression ← instantiateMVars expression
      if expression.hasSorry || expression.hasMVar then throwError "unfinished reference"
      unless expression.getUsedConstants.contains ``installed do
        throwError "placement proof does not reuse the installed theorem"
      let proposed ← IO.monoNanosNow
      checkWithKernel expression
      let checked ← IO.monoNanosNow
      let objects ← expression.numObjs
      logInfo m!"placements={placements}; proposal_ns={proposed-started}; kernel_ns={checked-proposed}; expression_objects={objects}; shared_law=installed"

#print axioms oneView_equation
#print axioms twoView_equation
#print axioms fourView_equation
end Tests.ProcessReferenceSharing
