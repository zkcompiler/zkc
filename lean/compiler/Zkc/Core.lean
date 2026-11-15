module

public import Zkc.Core.Process.Handler
public import Zkc.Core.Process.Process
public import Zkc.Core.Program.Conditions
public import Zkc.Core.Program.Dialects
public import Zkc.Core.Program.Elaborate
public import Zkc.Core.Program.ElaborateLocal
public import Zkc.Core.Program.Linear
public import Zkc.Core.Program.LocalRules
public import Zkc.Core.Program.Identity
public import Zkc.Core.Program.Located
public import Zkc.Core.Program.Print
public import Zkc.Core.Program.PrintProgram
public import Zkc.Core.Program.Refusal
public import Zkc.Core.Program.Requirement
public import Zkc.Core.Program.Project
public import Zkc.Core.Program.Record
public import Zkc.Core.Program.Shape
public import Zkc.Core.Program.Syntax
public import Zkc.Core.Program.Term
public import Zkc.Core.Program.Typed
public import Zkc.Core.Program.Vocabulary
public import Zkc.Core.Meaning.Call
public import Zkc.Core.Meaning.Events
public import Zkc.Core.Meaning.Fold
public import Zkc.Core.Meaning.Local
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Meaning.Protocol
public import Zkc.Core.Meaning.Role
public import Zkc.Core.Meaning.Validity
public import Zkc.Core.Projection.Proj
public import Zkc.Core.Projection.Sound
public import Zkc.Core.Projection.Theorem
public import Zkc.Core.Facts.Facts
public import Zkc.Core.Facts.OpFacts
public import Zkc.Core.Facts.State
public import Zkc.Core.Facts.Walk
public import Zkc.Core.Facts.Local
public import Zkc.Core.Facts.Valuation
public import Zkc.Core.Facts.Learning
public import Zkc.Core.Facts.Growth
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Facts.Soundness
public import Zkc.Core.Facts.Programs
public import Zkc.Core.Admission.Admission
public import Zkc.Core.Admission.Elaboration
public import Zkc.Core.World.Layer
public import Zkc.Core.World.Network
public import Zkc.Core.World.Runs
public import Zkc.Core.World.Stack
public import Zkc.Core.Scheme.Declaration
public import Zkc.Core.Scheme.Deployed
public import Zkc.Core.Scheme.Roles
public import Zkc.Core.Run.Run
public import Zkc.Core.Format.Format
public import Zkc.Core.Functions
public import Zkc.Core.Statements

/-!
# The core

The core of the compiler: its library imports every module of the core. The guide is
`Zkc/Core/README.md`.
-/
