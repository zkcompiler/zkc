import Tests.ConnectionRouteCoverageControls

/-! The projected-repeat rule is consumed through the same generic coverage
path. Its full two-component logical row has one private component, while the
physical state has exactly one cell. Runtime counts remain symbolic. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionRouteCoverageProjected
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionCertificate ConnectionRouteCoverage
open Tests.ConnectionRouteCoverageControls (routing)

def spec : RepeatSpec := ⟨[.index, .index], [], [0,1], [[0,1],[0]], 7⟩
def scope : Scope := [.value .index, .value .index]
def layout : Layout scope :=
  [.data (.present (.var .here)), .data (.present (.var (.there .here)))]
def initial : Values (Comp [] scope) spec.state :=
  .cons (.present (.var (.there .here))) (.cons .absent .nil)
def callback : Region protocolDialect [.index,.index,.index] [.index,.index] :=
  .ret (.cons (.there .here) (.cons (.there (.there .here)) .nil))
def bodyForm : Form [] [] (RepeatScope spec.state scope) spec.state :=
  .done (projectedState 1 spec.stateScopes spec.state)
def next : Form [] [] (.tuple spec.state :: scope) [] := .done .nil
def source : Form [] [] scope [] :=
  .repeat spec "private" callback (.present (.var .here)) initial .nil next

def accepted : Derivation routing {} [] [] [] 1 [] [] none [] layout source
    (fun model => Domain.View.sequence
      (Domain.View.loop 7 [3] 0 [1] [.data .index] (Domain.View.empty (carriers := model.toCarriers))) Domain.View.empty) := by
  refine .projectedRepeat spec "private" callback (.var .here) initial .nil
    2 (RosterDistinct.root 1 2) rfl rfl [.data .index] rfl 0 rfl
    [.data 1,.absent] [.data 3,.absent] [1] [1] [3] [3] none none
    (.data 1 rfl (.absent .nil)) rfl rfl .plain rfl rfl bodyForm rfl
    (.done (.data 3 rfl (.absent .nil)) .plain) rfl (.done .nil .plain)

def coverage (model : DomainModel) (count publicValue : Nat) (history : Domain.History model.toCarriers) :=
  (accepted.covered model ⟨[],[]⟩ (fun entry => entry.elim0) [] (noCallees model _)
    (fun inputs => noCallees_hold _ inputs) (.cons count (.cons publicValue .nil)) history
    [.data (.index count), .data (.index publicValue)]
    (.cons ⟨count,rfl,rfl⟩ (.cons ⟨publicValue,rfl,rfl⟩ .nil))).coverage

-- Arbitrary hidden logical values are not forced present or physically encoded.
-- The source-owned mask alone removes this component before callback invocation.
example (model : DomainModel) (publicValue : Nat) (secret : Option Nat) :
    maskValues 1 spec.stateScopes
      (show Values (Component model.Value) spec.state from .cons (some publicValue) (.cons secret .nil)) =
      .cons (some publicValue) (.cons none .nil) := rfl

#print axioms coverage
end Tests.ConnectionRouteCoverageProjected
