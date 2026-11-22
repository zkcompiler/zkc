import Lean.Data.Json

/-!
# The Lake project of a check's modules

A check of a written subject writes its modules into a Lake project that requires the formal
package, builds them with one call of `lake build`, and reads from Lake's log what Lean said
of each. The proof modules that a check accepts are judged by the toolchain's
`lake comparator` in the same project: it builds the challenge and the solution in its own
sandbox and judges outside it (`Zkc.Frontend.Written.Statements.module` says what the two sides
are).

The project is as an author's: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` and the
modules as files named by their module names. It requires the formal package by its path and
uses the dependencies that the formal package has fetched and built, so nothing is fetched or
built again; its manifest is written from the formal package's and never by a build, so that no
text is elaborated to obtain it.

A check runs from the directory of the formal package (`lake lean checks/<Check>.lean`).
-/

namespace ZkcFormalTests.SubjectProject
open Lean

/-- The directory of the formal package: where a check runs. -/
def formalPackage : IO System.FilePath := do
  let directory ← IO.FS.realPath (← IO.currentDir)
  unless ← (directory / "lake-manifest.json").pathExists do
    throw (IO.userError s!"{directory} is not the directory of the formal package: it has no manifest")
  return directory

/-- What a module of a project is: a module of a subject, a control or a check, read with the
options of the formal package; or a challenge, whose theorems have no proof. -/
inductive Kind where
  | module
  | challenge
  deriving DecidableEq

/-- The path of a module's file in a project, by the components of its name. -/
def fileOf (module : Name) : System.FilePath :=
  (System.FilePath.mk ("/".intercalate (module.components.map (·.toString)))).addExtension "lean"

/-- A string as TOML and JSON write it. -/
def quoted (text : String) : String := (Json.str text).compress

/-- The modules that a project has, with what each is, in the order in which they were added. -/
def modules (project : System.FilePath) : IO (Array (Kind × Name)) := do
  let registry := project / "modules.txt"
  unless ← registry.pathExists do return #[]
  let mut found := #[]
  for line in (← IO.FS.readFile registry).splitOn "\n" do
    match line.splitOn "\t" with
    | ["module", name] => found := found.push (Kind.module, name.toName)
    | ["challenge", name] => found := found.push (Kind.challenge, name.toName)
    | _ => pure ()
  return found

/-- The configuration of the project for its modules: one library of the modules that are read
with the formal package's options, and one of the challenges, in which a theorem without a
proof is no error. Each module is elaborated one declaration after another: when declarations
are elaborated concurrently, a theorem whose proof ends in an exception is left as a name
without a body, and Lean then reports that it depends on no axioms. -/
def lakefile (formal : Option System.FilePath) (modules : Array (Kind × Name)) : String :=
  let names (kind : Kind) := (modules.filter (·.1 == kind)).map fun (_, name) => quoted name.toString
  let library (name options : String) (roots : Array String) : String :=
    if roots.isEmpty then "" else
      s!"\n[[lean_lib]]\nname = {quoted name}\nroots = [{", ".intercalate roots.toList}]\n" ++
      s!"leanOptions = \{{options}}\nmoreLeanArgs = [\"-DElab.async=false\"]\n"
  s!"name = \"subjects\"\nversion = \"0.0.0\"\n" ++
  (match formal with
    | some formal =>
      s!"packagesDir = {quoted (formal / ".lake" / "packages").toString}\n" ++
      s!"\n[[require]]\nname = \"zkc_formal\"\npath = {quoted formal.toString}\n"
    | none => "") ++
  library "Subjects" "autoImplicit = false, warningAsError = true" (names .module) ++
  library "Challenges" "autoImplicit = false" (names .challenge)

/-- The manifest of a project that requires nothing. -/
def bareManifest : String :=
  (Json.mkObj [("version", "1.3.0"), ("packagesDir", ".lake/packages"),
    ("packages", Json.arr #[]), ("name", "subjects"), ("lakeDir", ".lake"),
    ("fixedToolchain", false)]).pretty

/-- A project that requires no package: for modules that import Lean's own libraries only, on
which `lake` has nothing to resolve. Said of a project before a module is added. -/
def bare (project : System.FilePath) : IO Unit := do
  IO.FS.createDirAll project
  IO.FS.writeFile (project / "bare") ""

/-- The manifest of a project: the formal package by its path, and the packages of the formal
package's own manifest as what the project inherits. It is what Lake writes for such a project
on its first build. -/
def manifest (formal : System.FilePath) : IO String := do
  let theirs ← IO.ofExcept (Json.parse (← IO.FS.readFile (formal / "lake-manifest.json")))
  let packages ← IO.ofExcept (theirs.getObjValAs? (Array Json) "packages")
  let inherited := packages.map fun package =>
    let package := package.setObjVal! "inherited" true
    match package.getObjValAs? String "type", package.getObjValAs? String "dir" with
    | .ok "path", .ok directory =>
      if (System.FilePath.mk directory).isAbsolute then package
      else package.setObjVal! "dir" (formal / directory).toString
    | _, _ => package
  let own := Json.mkObj [("type", "path"), ("scope", ""), ("name", "zkc_formal"),
    ("manifestFile", "lake-manifest.json"), ("inherited", false), ("dir", formal.toString),
    ("copy", false), ("configFile", "lakefile.toml")]
  let version := (theirs.getObjVal? "version").toOption.getD (Json.str "1.3.0")
  return (Json.mkObj [("version", version),
    ("packagesDir", (formal / ".lake" / "packages").toString),
    ("packages", Json.arr (#[own] ++ inherited)), ("name", "subjects"), ("lakeDir", ".lake"),
    ("fixedToolchain", false)]).pretty

/-- A module added to a project: its file written, and its name noted. A module that the
project has is written again. -/
def add (project : System.FilePath) (module : Name) (source : String) (kind : Kind := .module) :
    IO System.FilePath := do
  let file := fileOf module
  if let some folder := (project / file).parent then IO.FS.createDirAll folder
  IO.FS.writeFile (project / file) source
  unless (← modules project).any (·.2 == module) do
    let line := (if kind == .challenge then "challenge" else "module") ++ s!"\t{module}\n"
    let handle ← IO.FS.Handle.mk (project / "modules.txt") .append
    handle.putStr line
  return file

/-- The files of the project that Lake reads before any module: written for the modules that
the project has now. -/
def configure (project : System.FilePath) : IO Unit := do
  let formal ← formalPackage
  IO.FS.createDirAll project
  IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (formal / "lean-toolchain"))
  if ← (project / "bare").pathExists then
    IO.FS.writeFile (project / "lakefile.toml") (lakefile none (← modules project))
    IO.FS.writeFile (project / "lake-manifest.json") bareManifest
  else
    IO.FS.writeFile (project / "lakefile.toml") (lakefile (some formal) (← modules project))
    IO.FS.writeFile (project / "lake-manifest.json") (← manifest formal)

/-- `lake` in a project, with what it printed. -/
def lake (project : System.FilePath) (arguments : Array String) : IO (Bool × String) := do
  let start ← IO.monoMsNow
  let out ← IO.Process.output { cmd := "lake", args := arguments, cwd := project }
  -- with `ZKC_TIMES` set, what each call of Lake cost, for a measurement of a check
  if (← IO.getEnv "ZKC_TIMES").isSome then
    IO.eprintln s!"lake {arguments[0]!} ({arguments.size - 1} arguments): {(← IO.monoMsNow) - start} ms"
  return (out.exitCode == 0, out.stdout ++ out.stderr)

/-- A line of Lake's log that carries a message of Lean, in Lean's own form: Lake prints
`error: File:3:8: text`, Lean `File:3:8: error: text`. Another line is as it is. -/
def leanLine (line : String) : String := Id.run do
  for severity in ["error", "warning", "info"] do
    let mark := severity ++ ": "
    if line.startsWith mark then
      let pieces := ((line.toList.drop mark.length |> String.ofList).splitOn ": ")
      -- the position ends the first piece that ends in `:<line>:<column>`
      let mut head := ""
      let mut rest := pieces
      while !rest.isEmpty do
        head := if head.isEmpty then rest.head! else head ++ ": " ++ rest.head!
        rest := rest.tail
        match (head.splitOn ":").reverse with
        | column :: row :: _ :: _ =>
          if !column.isEmpty && !row.isEmpty && column.all Char.isDigit && row.all Char.isDigit then
            return head ++ ": " ++ mark ++ ": ".intercalate rest
        | _ => pure ()
      return line
  return line

/-- What Lake's log says of each module that it names: whether Lake failed on it, and Lean's
messages on it in Lean's form. Lake heads the part of a module with a mark, its place among the
jobs, what it did and the module (`✖ [4/9] Building Bad (146ms)`, `ℹ [2/9] Built Good`,
`Replayed` when it built the module before); on a failure it prints the command, which is left
out. A module that Lake built with nothing to say has no part. -/
def parts (log : String) : Array (String × Bool × String) := Id.run do
  let mut found : Array (String × Bool × String) := #[]
  let mut current : Option (String × Bool × Array String) := none
  for line in log.splitOn "\n" do
    let header : Option (String × Bool) :=
      match line.splitOn " " with
      | mark :: place :: _ :: target :: _ =>
        if ["ℹ", "✔", "✖", "⚠"].contains mark && place.startsWith "[" then some (target, mark == "✖")
        else none
      | _ => none
    if let some (target, failed) := header then
      if let some (name, bad, lines) := current then
        found := found.push (name, bad, "\n".intercalate lines.toList)
      current := some (target, failed, #[])
    else if line.startsWith "Some required targets logged failures" then
      if let some (name, bad, lines) := current then
        found := found.push (name, bad, "\n".intercalate lines.toList)
      current := none
    else if let some (name, bad, lines) := current then
      unless line.startsWith "trace: " do
        current := some (name, bad, lines.push (leanLine line))
  if let some (name, bad, lines) := current then
    found := found.push (name, bad, "\n".intercalate lines.toList)
  return found

/-- The object of a module that Lake built in a project. -/
def objectOf (project : System.FilePath) (module : Name) : System.FilePath :=
  project / ".lake" / "build" / "lib" / "lean" / (fileOf module).withExtension "olean"

/-- The modules of a project built, all in one call: Lake's log, kept in the project, with the
modules that it covers. A module that fails does not stop the others. -/
def build (project : System.FilePath) : IO String := do
  configure project
  let targets := ((← modules project).filter (·.1 == .module)).map fun (_, name) => s!"+{name}"
  if targets.isEmpty then return ""
  let (_, log) ← lake project (#["build"] ++ targets)
  IO.FS.writeFile (project / "build.log") log
  IO.FS.writeFile (project / "built.txt") ("\n".intercalate targets.toList)
  return log

/-- Lake's log on the modules that the project has now: built when a module was added since
the last build. -/
def built (project : System.FilePath) : IO String := do
  let targets := ((← modules project).filter (·.1 == .module)).map fun (_, name) => s!"+{name}"
  let covered := project / "built.txt"
  if ← covered.pathExists then
    if (← IO.FS.readFile covered) == "\n".intercalate targets.toList then
      return ← IO.FS.readFile (project / "build.log")
  build project

/-- What Lean said of a module of the project, and whether the module is built: Lake did not
fail on it and its object is there. A module whose import failed is not built and has nothing
said of it. -/
def result (project : System.FilePath) (module : Name) : IO (Bool × String) := do
  let log ← built project
  let own := (parts log).filter (·.1 == module.toString)
  let failed := own.any (·.2.1)
  let output := "\n".intercalate (own.map (·.2.2)).toList
  return (!failed && (← (objectOf project module).pathExists), output)

/-- The judgment of proof modules by `lake comparator`: each published theorem of the
solutions has the statement of its challenge with everything that the statement uses, the
kernel accepts the solutions, and the published theorems rest on `axioms` at most. `pairs` are
the challenge and the solution modules of the subjects judged together, and `theorems` their
published theorems. The comparator takes one module on each side, so two modules written here
import those of the subjects; `label` names them and the configuration, so that a project can
hold several judgments. The result is the comparator's verdict and what it printed. -/
def judge (project : System.FilePath) (label : String) (pairs : List (Name × Name))
    (theorems : List Name) (axioms : List String) (paranoid := false) : IO (Bool × String) := do
  let challenge : Name := .str (.str .anonymous label) "Challenge"
  let solution : Name := .str (.str .anonymous label) "Solution"
  let imports (names : List Name) := String.join (names.map (s!"import {·}\n"))
  discard <| add project challenge (imports (pairs.map (·.1))) .challenge
  discard <| add project solution (imports (pairs.map (·.2)))
  configure project
  let config := s!"{label}.comparator.json"
  IO.FS.writeFile (project / config) (Json.mkObj [
    ("challenge_module", challenge.toString), ("solution_module", solution.toString),
    ("theorem_names", Json.arr (theorems.map fun name => Json.str name.toString).toArray),
    ("permitted_axioms", Json.arr (axioms.map Json.str).toArray)]).pretty
  let verdict ← lake project (#["comparator", "--config", config] ++ (if paranoid then #["--paranoid"] else #[]))
  IO.FS.writeFile (project / s!"{label}.judgment.log") verdict.2
  return verdict

end ZkcFormalTests.SubjectProject
