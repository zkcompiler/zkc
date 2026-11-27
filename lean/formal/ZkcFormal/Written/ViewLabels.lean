module

public meta import Lean

public meta section

/-- A definition that the naming of views unfolds where its value leads to an input or a witness
telescope (`ZkcFormal.Written.Views`); the library's own are listed there by name. -/
register_label_attr view_unfold

/-- A proposition whose premise, after an input telescope, takes the name of its head constant with
its first letter in lower case (`Rejected` gives `rejected`); a premise with no registration is
anonymous. -/
register_label_attr view_premise
