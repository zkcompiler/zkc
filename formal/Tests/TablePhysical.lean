import Examples.TablePhysical.Format

/-! Controls for physical-region checking and the immutable alias premise. -/
set_option autoImplicit false
-- Not `Tests.TablePhysical`, which every other file here uses: this one opens the
-- library's own `TablePhysical`, and a namespace of that name would shadow it at
-- the `open` rather than being opened alongside it.
namespace TablePhysicalTests
open TableProtocol TablePhysical Zkc.Source Zkc.Realization

def source : RawRegion Ty Protocol.Operation :=
  .letOp (.base (.evaluate .seven 1)) [0, 1]
    (.letOp (.base (.add .seven)) [0, 0] (.ret 0))

example : (check [.residual .seven 1, .point .seven] (.scalar .seven)
    source (propose .lazy source)).isOk = true := by decide
example : (check [.residual .seven 1, .point .seven] (.scalar .seven)
    source (propose .materialized source)).isOk = true := by decide

-- Returning an earlier scalar instead of the computed sum is well typed but wrong.
example : (check [.residual .seven 1, .point .seven] (.scalar .seven) source
    (.letOp (.prepare .lazy .seven 1) [0, 1]
      (.letOp (.invoke (.base (.add .seven))) [0, 0] (.ret 1)))).isOk = false := by decide

-- An unused result does not permit deleting its evaluation or shape guard.
example : (check [.residual .seven 1, .point .seven, .boolean] .boolean
    (.letOp (.base (.evaluate .seven 1)) [0, 1] (.ret 3)) (.ret 2)).isOk = false := by decide

-- Checking traverses a dormant loop and the unselected branch.
example : (check [.boolean] .boolean (.iterate 0 .boolean 0 (.ret 0) (.ret 0))
    (.iterate 0 .boolean 0 (.ret 1) (.ret 0))).isOk = false := by decide
example : (check [.boolean] .boolean (.branch 0 (.ret 0) (.ret 0))
    (.branch 0 (.ret 0) (.stop .abort))).isOk = false := by decide

def before : TablePhysical.State :=
  { logical := {}, store := publish empty .seven (.scalar 1) }
def corrupt : TablePhysical.State :=
  { logical := {}, store := publish empty .seven (.scalar 2) }

-- Local returned-value/state/event correspondence alone accepts an overwrite
-- whose new result is right but whose old live reference has changed meaning.
example : PIR.Execution.Relates representation.states (representation.value (.scalar .seven))
    (fun event : Protocol.Trace => [event]) (fun event => [event])
    ⟨.returned 2, {}, []⟩ ⟨.returned (.reference 0), corrupt, []⟩ := by
  exact ⟨rfl, rfl, rfl⟩

theorem overwrite_breaks_frame : ¬representation.Frame {} before {} corrupt := by
  intro frame
  have old : representation.value (.scalar .seven) 1 {} (.reference 0) before := rfl
  have changed := frame (.scalar .seven) 1 (.reference 0) old
  have wrong : ¬representation.value (.scalar .seven) 1 {} (.reference 0) corrupt := by
    change ¬(some (2 : Field .seven) = some 1)
    decide
  exact wrong changed

-- Prepared cells cannot be read from a fresh empty owner in the reference.
example : read empty .seven 0 = none := rfl

end TablePhysicalTests
