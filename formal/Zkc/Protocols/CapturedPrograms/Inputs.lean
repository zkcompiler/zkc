import Zkc.Source.Inputs
import Zkc.Semantics.Interaction
import Zkc.Protocols.CapturedPrograms.Installation

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.CapturedPrograms.Inputs
open PIR.SourceView Zkc.Protocols.CapturedPrograms Zkc.Source.Availability

variable {Role F H : Type} [DecidableEq Role]
variable [CommRing F] [DecidableEq F]

/-- The actual existing issuer checks finite code, selection guards and all
    captures, after interpreting the source's role-qualified input bindings. -/
def admit (actor : Role) (bindings : List (Slot Role)) (w : World Role F H)
    (tree : Tree) : Option (Issued F) :=
  issue (List.range bindings.length) (env actor bindings w) tree

theorem admission_same_view (actor : Role) (bindings : List (Slot Role))
    (w v : World Role F H) (tree : Tree) (agree : SameView actor w v) :
    admit actor bindings w tree = admit actor bindings v tree := by
  apply issue_agreement
  intro i _
  simp only [env]
  cases bindings[i]? with
  | none => rfl
  | some slot => exact read_agrees actor w v agree slot

/-- This derives actual availability and ownership of every read dependency,
    including branches not selected in this run. It assumes successful checking,
    not a pre-supplied ownership or source-equality certificate. -/
theorem admitted_reads (actor : Role) (bindings : List (Slot Role))
    (w : World Role F H) (tree : Tree) (x : Issued F)
    (accepted : admit actor bindings w tree = some x) (i : Nat) (used : i ∈ tree.deps) :
    ∃ slot value, bindings[i]? = some slot ∧ permitted actor slot ∧
      read actor w slot = some value := by
  obtain ⟨_,value,present⟩ := issued_reads_bound _ _ tree x accepted i used
  simp only [env] at present
  cases hb : bindings[i]? with
  | none => simp [hb] at present
  | some slot =>
    simp only [hb,Option.bind_some] at present
    exact ⟨slot,value,rfl,read_permitted actor w slot value present,present⟩

theorem admitted_code_inputs (actor : Role) (bindings : List (Slot Role))
    (w : World Role F H) (tree : Tree) (x : Issued F)
    (accepted : admit actor bindings w tree = some x) (i : Nat)
    (used : i ∈ Zkc.Protocols.Sumcheck.LocalProver.codeInputs x.code.causal) : ∃ value, x.inputs[i]? = some value :=
  issued_input_bound _ _ tree x accepted i used

/-- Joins the role-qualified source selection to the existing service-source
    law. This uses the same checked literal and captured values, not a code
    generator that can inspect a hidden witness before producing that literal. -/
theorem admitted_controller (actor : Role) (bindings : List (Slot Role))
    (w v : World Role F H) (tree : Tree) (x y : Issued F)
    (hx : admit actor bindings w tree = some x) (hy : admit actor bindings v tree = some y)
    (agree : SameView actor w v) (a b : Zkc.Protocols.CorrelatedSetup.Witness F) : controller x a = controller y b := by
  have eq : x = y := Option.some.inj (hx.symm.trans ((admission_same_view actor bindings w v tree agree).trans hy))
  subst y
  exact Zkc.Protocols.CorrelatedSetup.Source.same_controller x.code.service (issued_ok _ _ tree x hx).1 (setup x) a b

/-- Concrete role input binding for an installed namespace. Only the designated
    owner's local slots are exposed; the rest of the actual World is not an
    implicit source environment. -/
def installedWorld (actor : Role) (namespaceId : Zkc.Modules.FactorBinding.Namespace)
    (w : Zkc.Modules.FactorState.World F) (hidden : H) : World Role F H :=
  ⟨fun _ => none,
    fun owner => if owner = actor then Zkc.Protocols.CapturedPrograms.Installation.localEnv namespaceId w else fun _ => none,
    hidden⟩

def installedBindings (actor : Role) (n : Nat) : List (Slot Role) :=
  (List.range n).map (Slot.owned actor)

omit [CommRing F] [DecidableEq F] in
theorem installed_environment (actor : Role) (n : Nat) (namespaceId : Zkc.Modules.FactorBinding.Namespace)
    (w : Zkc.Modules.FactorState.World F) (hidden : H) (i : Nat) (hi : i < n) :
    env actor (installedBindings actor n) (installedWorld actor namespaceId w hidden) i =
      Zkc.Protocols.CapturedPrograms.Installation.localEnv namespaceId w i := by
  simp [env,installedBindings,installedWorld,PIR.SourceView.read,List.getElem?_range hi]

/-- Exact actual installer/issuer path; failure does not invoke the source. -/
def installAdmit (actor : Role) (capacity : Nat) (r : Zkc.Modules.Installation.Request F)
    (tree : Tree) (w : Zkc.Modules.FactorState.World F) (hidden : H) : Option (Issued F) :=
  let out := Zkc.Modules.Installation.execute capacity r w
  if out.success then admit actor (installedBindings actor r.captured.length)
    (installedWorld actor r.namespaceId out.world hidden) tree else none

theorem install_admission_exact (actor : Role) (capacity : Nat) (r : Zkc.Modules.Installation.Request F)
    (tree : Tree) (w : Zkc.Modules.FactorState.World F) (hidden : H) :
    installAdmit actor capacity r tree w hidden = Zkc.Protocols.CapturedPrograms.Installation.afterInstall capacity r tree w := by
  unfold installAdmit Zkc.Protocols.CapturedPrograms.Installation.afterInstall
  dsimp only
  split
  · unfold admit
    simp only [installedBindings,List.length_map,List.length_range]
    apply issue_agreement
    intro i hi
    exact installed_environment actor r.captured.length _ _ hidden i (List.mem_range.mp hi)
  · rfl


end Zkc.Protocols.CapturedPrograms.Inputs
