module

public import Zkc.Source.Structured.OccurrencePresentation
public import ZkcExamples.Structured.Generated.Presentations.Gkr

/-! The real output callback can reuse a silent mathematical presentation.
The enclosing layer, with component applications and a nested repeat, cannot:
its occurrence boundaries must be handled by the loop and call contracts. -/
open Zkc.Source.Structured ZkcExamples.Structured

example : Generated.Presentations.Gkr.Root.outputBody.erase.operations.all
    OccurrencePresentation.contextFree = true := by kernel_rfl

example : Generated.Presentations.Gkr.Root.layerBody.erase.operations.all
    OccurrencePresentation.contextFree = false := by kernel_rfl

example : ¬ Generated.Presentations.Gkr.Root.layerBody.erase.operations.all
    OccurrencePresentation.contextFree = true := by decide +kernel
