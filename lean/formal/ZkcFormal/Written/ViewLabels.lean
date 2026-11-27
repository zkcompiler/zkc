module

public meta import Lean

public meta section

/-- A definition that the naming of views unfolds where its value leads to an input or a witness
telescope (`ZkcFormal.Written.Views`); the library's own are listed there by name. -/
register_label_attr view_unfold

/-- A proposition whose premise, after an input telescope, takes the name of its head constant with
its first letter in lower case (`Rejected` gives `rejected`). A premise with no registration is
anonymous where the rest of the proposition does not refer to its proof, and keeps its name where
the rest does. -/
register_label_attr view_premise
