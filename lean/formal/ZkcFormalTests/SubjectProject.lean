import Lean.Data.Json
import Lean.Util.Path

/-!
# The Lake project of a check's modules

A check of a written subject writes its modules into a Lake project that requires the formal
package, and asks what Lean says of each and whether the proof modules that it accepts are as
their challenges state. The project is as an author's: `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json` and the modules as files named by their module names. It requires the
formal package by its path and uses the dependencies that the formal package has fetched and
built, so nothing is fetched or built again; its manifest is written from the formal package's
and never by a build.

A proof module holds a text, and a text is arbitrary Lean: it can run a program while Lean
reads it. So the project is settled in an order that leaves a text nothing to change
(`settle`), and every process that reads a text, or reads what a text's build wrote, runs
confined (`confined`): it sees the file system read-only, with the home folders and the
temporary folders covered, has no network and no other process, and can write the project's
`.lake` and nothing else.

1. The modules of the statements and the challenges are built, and each judgment's challenge is
   exported by the toolchain's `leanexport`, before any text is read. The exports are kept
   beside `.lake`, where no confined process writes.
2. The other modules are built, all in one call of `lake build`.
3. A judgment exports its solutions from the objects that step 2 left, and gives the two
   exports to the toolchain's `lake comparator`, which compares each named theorem's statement
   with everything that the statement uses, replays the solution in the kernel and reads the
   axioms that the theorems rest on. The comparator reads the exports and no object.

What a text can reach is therefore the objects of step 2 and the solution's export, which are
what the comparator judges. What Lean said of a module in step 2 is read from Lake's log, which
a text can write into; no proof module is accepted on it (`result`), and a module of a check
that holds no text is built in step 1.

A module is added, and a judgment expected, before the first asking; afterwards both are
errors, since a challenge exported after a text was read would rest on objects that the text
could have written.

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

/-- What a module of a project is. The statements and the challenges hold no text and are built
first, as is a module of a check that holds none and is given the kind of the statements; a challenge is read with a theorem without a proof as no error. Every other module (a
proof module, a control, a module of a check) may hold a text. -/
inductive Kind where
  | statements
  | challenge
  | module
  deriving DecidableEq

def Kind.word : Kind → String
  | .statements => "statements"
  | .challenge => "challenge"
  | .module => "module"

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
    | [word, name] =>
      for kind in [Kind.statements, .challenge, .module] do
        if kind.word == word then found := found.push (kind, name.toName)
    | _ => pure ()
  return found

/-- The configuration of the project for its modules: a library for each kind. Each module is
elaborated one declaration after another: when declarations are elaborated concurrently, a
theorem whose proof ends in an exception is left as a name without a body, and Lean then
reports that it depends on no axioms. -/
def lakefile (formal : Option System.FilePath) (modules : Array (Kind × Name)) : String :=
  let names (kind : Kind) := (modules.filter (·.1 == kind)).map fun (_, name) => quoted name.toString
  let library (name options : String) (roots : Array String) : String :=
    if roots.isEmpty then "" else
      s!"\n[[lean_lib]]\nname = {quoted name}\nroots = [{", ".intercalate roots.toList}]\n" ++
      s!"globs = [{", ".intercalate roots.toList}]\n" ++
      s!"leanOptions = \{{options}}\nmoreLeanArgs = [\"-DElab.async=false\"]\n"
  s!"name = \"subjects\"\nversion = \"0.0.0\"\n" ++
  (match formal with
    | some formal =>
      s!"packagesDir = {quoted (formal / ".lake" / "packages").toString}\n" ++
      s!"\n[[require]]\nname = \"zkc_formal\"\npath = {quoted formal.toString}\n"
    | none => "") ++
  -- each library is of its modules alone (`globs`), so that `Guess.Challenge` is not also of
  -- the library with the root `Guess`
  library "Subjects" "autoImplicit = false, warningAsError = true" (names .module) ++
  library "Stated" "autoImplicit = false, warningAsError = true" (names .statements) ++
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

def isBare (project : System.FilePath) : IO Bool := (project / "bare").pathExists

/-- The packages of the formal package's manifest, with the directory of each that is required
by a path made absolute. -/
def formalPackages (formal : System.FilePath) : IO (Json × Array Json) := do
  let theirs ← IO.ofExcept (Json.parse (← IO.FS.readFile (formal / "lake-manifest.json")))
  let packages ← IO.ofExcept (theirs.getObjValAs? (Array Json) "packages")
  return (theirs, packages.map fun package =>
    match package.getObjValAs? String "type", package.getObjValAs? String "dir" with
    | .ok "path", .ok directory =>
      if (System.FilePath.mk directory).isAbsolute then package
      else package.setObjVal! "dir" (formal / directory).toString
    | _, _ => package)

/-- The manifest of a project: the formal package by its path, and the packages of the formal
package's own manifest as what the project inherits. It is what Lake writes for such a project
on its first build. -/
def manifest (formal : System.FilePath) : IO String := do
  let (theirs, packages) ← formalPackages formal
  let inherited := packages.map (·.setObjVal! "inherited" true)
  let own := Json.mkObj [("type", "path"), ("scope", ""), ("name", "zkc_formal"),
    ("manifestFile", "lake-manifest.json"), ("inherited", false), ("dir", formal.toString),
    ("copy", false), ("configFile", "lakefile.toml")]
  let version := (theirs.getObjVal? "version").toOption.getD (Json.str "1.3.0")
  return (Json.mkObj [("version", version),
    ("packagesDir", (formal / ".lake" / "packages").toString),
    ("packages", Json.arr (#[own] ++ inherited)), ("name", "subjects"), ("lakeDir", ".lake"),
    ("fixedToolchain", false)]).pretty

/-- Whether the project was settled: its modules built and its challenges exported. -/
def isSettled (project : System.FilePath) : IO Bool := (project / "settled").pathExists

def unsettled (project : System.FilePath) (what : String) : IO Unit := do
  if ← isSettled project then
    throw (IO.userError (s!"{what} after the project {project} was built: every module is added, " ++
      "and every judgment expected, before the first asking (a project is not used twice)"))

/-- A module added to a project: its file written, and its name noted. A module that the
project has is added again only as what it is, with the same source: another source or kind
under a name that the project has would replace a module that something else rests on. -/
def add (project : System.FilePath) (module : Name) (source : String) (kind : Kind := .module) :
    IO System.FilePath := do
  unsettled project s!"the module {module} is added"
  let file := fileOf module
  if let some (had, _) := (← modules project).find? (·.2 == module) then
    unless had == kind && (← IO.FS.readFile (project / file)) == source do
      throw (IO.userError s!"the project {project} has another module named {module}")
    return file
  if let some folder := (project / file).parent then IO.FS.createDirAll folder
  IO.FS.writeFile (project / file) source
  do
    let handle ← IO.FS.Handle.mk (project / "modules.txt") .append
    handle.putStr s!"{kind.word}\t{module}\n"
  return file

/-- A judgment that a project expects: the challenge and the solution modules of the pairs
judged together, the theorems that it is of, and the axioms beyond which none may rest. -/
structure Expected where
  label : String
  challenges : Array String
  solutions : Array String
  theorems : Array String
  axioms : Array String
  deriving FromJson, ToJson

/-- The judgments that a project expects. -/
def expectations (project : System.FilePath) : IO (Array Expected) := do
  let registry := project / "expected.txt"
  unless ← registry.pathExists do return #[]
  ((← IO.FS.readFile registry).splitOn "\n" |>.filter (· != "")).toArray.mapM fun line =>
    IO.ofExcept (Json.parse line >>= fromJson?)

/-- A judgment expected of a project, under a label that names it: of `pairs`, the challenge
and the solution modules of the subjects judged together, over `theorems`. -/
def expect (project : System.FilePath) (label : String) (pairs : List (Name × Name))
    (theorems : List Name) (axioms : List String) : IO Unit := do
  unsettled project s!"the judgment {label} is expected"
  if (← expectations project).any (·.label == label) then
    throw (IO.userError s!"the project {project} expects two judgments named {label}")
  if theorems.isEmpty then throw (IO.userError s!"the judgment {label} is of no theorem")
  let expected : Expected := {
    label, challenges := (pairs.map (·.1.toString)).toArray,
    solutions := (pairs.map (·.2.toString)).toArray,
    theorems := (theorems.map (·.toString)).toArray, axioms := axioms.toArray }
  IO.FS.createDirAll project
  let handle ← IO.FS.Handle.mk (project / "expected.txt") .append
  handle.putStr ((toJson expected).compress ++ "\n")

/-- The files of the project that Lake reads before any module. -/
def configure (project : System.FilePath) : IO Unit := do
  let formal ← formalPackage
  IO.FS.createDirAll project
  IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (formal / "lean-toolchain"))
  if ← isBare project then
    IO.FS.writeFile (project / "lakefile.toml") (lakefile none (← modules project))
    IO.FS.writeFile (project / "lake-manifest.json") bareManifest
  else
    IO.FS.writeFile (project / "lakefile.toml") (lakefile (some formal) (← modules project))
    IO.FS.writeFile (project / "lake-manifest.json") (← manifest formal)

/-- What a confined process may read under the folders that are covered: the toolchain, the
project, and for a project that requires it the formal package with the packages that it
requires. -/
def readable (project : System.FilePath) : IO (Array System.FilePath) := do
  let mut paths := #[← findSysroot, project]
  unless ← isBare project do
    let formal ← formalPackage
    paths := paths.push formal
    for package in (← formalPackages formal).2 do
      if let .ok directory := package.getObjValAs? String "dir" then
        if ← (System.FilePath.mk directory).pathExists then
          paths := paths.push (← IO.FS.realPath directory)
  return paths

/-- A command run confined, in a project: as `lake comparator` confines what it builds. The
file system is read-only; the home folders, the temporary folders and the folders of running
services are covered by empty ones, and what `readable` lists is bound back read-only; the
environment is empty but for the toolchain's programs on the path; there is no network and no
other process. With `writable`, the project's `.lake` can be written, and nothing else. -/
def confined (project : System.FilePath) (writable : Bool) (cmd : String) (args : Array String) :
    IO IO.Process.Output := do
  let project ← IO.FS.realPath project
  let sysroot ← findSysroot
  IO.FS.createDirAll (project / ".lake")
  let lake := (project / ".lake").toString
  let cover := #["/home", "/root", "/run", "/var", "/tmp"].flatMap fun path => #["--tmpfs", path]
  let back := (← readable project).flatMap fun path => #["--ro-bind", path.toString, path.toString]
  let out ← IO.Process.output {
    cmd := "bwrap"
    args := #["--ro-bind", "/", "/"] ++ cover ++ #["--dir", "/tmp/home", "--dev", "/dev",
      "--proc", "/proc", "--clearenv"] ++ back ++
      #[if writable then "--bind" else "--ro-bind", lake, lake,
        "--setenv", "PATH", s!"{sysroot / "bin"}:/usr/bin:/bin",
        "--setenv", "HOME", "/tmp/home", "--setenv", "LEAN_ABORT_ON_PANIC", "1",
        "--unshare-all", "--die-with-parent", "--new-session",
        "--chdir", project.toString, "--", cmd] ++ args }
  return out

/-- The toolchain's `lake`, confined in a project. -/
def lake (project : System.FilePath) (writable : Bool) (arguments : Array String) :
    IO IO.Process.Output := do
  let start ← IO.monoMsNow
  let out ← confined project writable ((← findSysroot) / "bin" / "lake").toString arguments
  -- with `ZKC_TIMES` set, what each call of Lake cost, for a measurement of a check
  if (← IO.getEnv "ZKC_TIMES").isSome then
    IO.eprintln s!"lake {arguments[0]!} ({arguments.size - 1} arguments): {(← IO.monoMsNow) - start} ms"
  return out

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
jobs, what it did and the module (`✖ [4/9] Building Bad (146ms)`, `ℹ [2/9] Built Good`); on a
failure it prints the command, which is left out. A module that Lake built with nothing to say
has no part. -/
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

/-- The names that the comparator has exported beside the theorems of a judgment: the
constants that the kernel knows by name, the allowed axioms, and with `Quot.sound` the
quotient's own. It compares them on the two sides. The list is the comparator's
(`primitiveTargets` and `builtinTargets` of `Lake/CLI/Check.lean`, which are not public); if
the two came apart, the comparator would miss a name and refuse. -/
def exported (expected : Expected) : Array String :=
  (if expected.axioms.contains "Quot.sound" then #["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] else #[]) ++
    expected.theorems ++ expected.axioms ++
    #["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq",
      "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight",
      "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk", "Char",
      "optParam", "autoParam", "semiOutParam", "outParam"]

/-- One side of a judgment exported by the toolchain's `leanexport`, confined and with nothing
to write: the export is what the exporter printed, written here to `file`. On a failure the
result is what the exporter said. -/
def export_ (project : System.FilePath) (modules names : Array String) (file : System.FilePath)
    (solution := false) : IO (Option String) := do
  -- the exporter by its path in the toolchain: `lake env` puts the project's own programs on the path
  let exporter := ((← findSysroot) / "bin" / "leanexport").toString
  -- a name that a solution lacks is left out, and the comparator says that it is missing
  let out ← lake project false (#["env", exporter] ++ (if solution then #["--ignore-missing"] else #[]) ++
    modules ++ #["--"] ++ names)
  if out.exitCode == 0 then
    IO.FS.writeFile file out.stdout
    return none
  return some s!"the exporter ended with {out.exitCode}\n{out.stderr}"

def exportOf (project : System.FilePath) (label side : String) : System.FilePath :=
  project / "exports" / s!"{label}.{side}.ndjson"

/-- The project settled, once: what the head of this file says in its steps 1 and 2. Kept in
the project, where no confined process writes: Lake's log on the statements and the challenges
with the modules among them that it built, each judgment's challenge exported (or why it was
not), and Lake's log on the other modules. -/
def settle (project : System.FilePath) : IO Unit := do
  if ← isSettled project then return
  configure project
  if ← (project / ".lake").pathExists then
    throw (IO.userError s!"the project {project} has objects before it is built: a project is not used twice")
  let all ← modules project
  let targets (kinds : List Kind) := (all.filter (kinds.contains ·.1)).map fun (_, name) => s!"+{name}"
  -- 1. the statements and the challenges, before any text
  let first := targets [.statements, .challenge]
  let stated ← if first.isEmpty then pure "" else do
    let out ← lake project true (#["build"] ++ first)
    pure (out.stdout ++ out.stderr)
  IO.FS.writeFile (project / "stated.log") stated
  let mut built := #[]
  for (kind, name) in all do
    if kind != .module && (← (objectOf project name).pathExists) then built := built.push name.toString
  IO.FS.writeFile (project / "stated.built") ("\n".intercalate built.toList)
  IO.FS.createDirAll (project / "exports")
  let expected ← expectations project
  -- the exports run beside each other, a few at a time: each reads the whole of what it exports
  let mut waiting := expected.toList
  while !waiting.isEmpty do
    let now := waiting.take 3
    waiting := waiting.drop 3
    let running ← now.mapM fun judgment => IO.asTask (prio := .dedicated) do
      match judgment.challenges.find? (!built.contains ·) with
      | some missing =>
        let said := ((parts stated).filter (·.1 == missing)).map (·.2.2)
        return some s!"Lean did not build the challenge {missing}\n{"\n".intercalate said.toList}"
      | none => export_ project judgment.challenges (exported judgment) (exportOf project judgment.label "challenge")
    for (judgment, task) in now.zip running do
      if let some failure ← IO.ofExcept task.get then
        IO.FS.writeFile (project / "exports" / s!"{judgment.label}.challenge.failed") failure
  -- 2. every other module: from here on a text has been read
  let second := targets [.module]
  let log ← if second.isEmpty then pure "" else do
    let out ← lake project true (#["build"] ++ second)
    pure (out.stdout ++ out.stderr)
  IO.FS.writeFile (project / "build.log") log
  IO.FS.writeFile (project / "settled") ""

/-- What Lean said of a module of the project, and whether the module is built: Lake did not
fail on it and its object is there. A module whose import failed is not built and has nothing
said of it.

Of a module of statements or a challenge this is what was so before any text was read. Of
another module it is read from a log that a text of the same build can write into, and from an
object that it can write: it says what Lean reported, for a message and for a control that Lean
must refuse, and a module is accepted on its judgment only (`judge`). -/
def result (project : System.FilePath) (module : Name) : IO (Bool × String) := do
  settle project
  let some (kind, _) := (← modules project).find? (·.2 == module)
    | throw (IO.userError s!"the project {project} has no module {module}")
  let said (log : String) :=
    let own := (parts log).filter (·.1 == module.toString)
    (own.any (·.2.1), "\n".intercalate (own.map (·.2.2)).toList)
  if kind == .module then
    let (failed, output) := said (← IO.FS.readFile (project / "build.log"))
    return (!failed && (← (objectOf project module).pathExists), output)
  let (failed, output) := said (← IO.FS.readFile (project / "stated.log"))
  let built := ((← IO.FS.readFile (project / "stated.built")).splitOn "\n").contains module.toString
  return (!failed && built, output)

/-- What a judgment gave. `refused`: the comparator ended with a refusal, which it does on a
pair that it judged and refuses and also on an export that it cannot read or a kernel that did
not end, so that a control names what the comparator said. `failed`: there was no judgment (the
challenge was not built or exported, the solution could not be exported, the comparator could
not start); a failure is an error of the check. Only `accepted` accepts. -/
inductive Verdict where
  | accepted
  | refused
  | failed
  deriving DecidableEq, Repr

def Verdict.word : Verdict → String
  | .accepted => "accepted"
  | .refused => "refused"
  | .failed => "failed"

/-- The judgment `label` that the project expects, by `lake comparator` on the two exports:
each theorem of the solutions has the statement of its challenge with everything that the
statement uses, the kernel accepts the solutions, and the theorems rest on the allowed axioms
at most. With `paranoid`, every other kernel that the toolchain bundles replays the solutions
as well. The result is the verdict and what was said; it is made once and kept in the project,
which no process that read a text could write. -/
def judge (project : System.FilePath) (label : String) (paranoid := false) :
    IO (Verdict × String) := do
  settle project
  let project ← IO.FS.realPath project
  let some expected := (← expectations project).find? (·.label == label)
    | throw (IO.userError s!"the project {project} expects no judgment named {label}")
  let kept := project / s!"{label}.verdict"
  let log := project / s!"{label}.judgment.log"
  if ← kept.pathExists then
    let word ← IO.FS.readFile kept
    for verdict in [Verdict.accepted, .refused, .failed] do
      if verdict.word == word then return (verdict, ← IO.FS.readFile log)
  let keep (verdict : Verdict) (said : String) : IO (Verdict × String) := do
    IO.FS.writeFile log said
    IO.FS.writeFile kept verdict.word
    return (verdict, said)
  let challenge := exportOf project label "challenge"
  let failed := project / "exports" / s!"{label}.challenge.failed"
  if ← failed.pathExists then
    return ← keep .failed s!"the challenge was not exported: {← IO.FS.readFile failed}"
  let solution := exportOf project label "solution"
  if let some failure ← export_ project expected.solutions (exported expected) solution (solution := true) then
    return ← keep .failed s!"the solution was not exported: {failure}"
  let config := project / s!"{label}.comparator.json"
  IO.FS.writeFile config (Json.mkObj [
    ("challenge_module", Json.str (expected.challenges[0]?.getD "")),
    ("solution_module", Json.str (expected.solutions[0]?.getD "")),
    ("theorem_names", toJson expected.theorems),
    ("permitted_axioms", toJson expected.axioms)]).pretty
  let start ← IO.monoMsNow
  let out ← IO.Process.output {
    cmd := ((← findSysroot) / "bin" / "lake").toString
    args := #["comparator", "--config", config.toString, "--challenge-from-export", challenge.toString,
      "--solution-from-export", solution.toString] ++ (if paranoid then #["--paranoid"] else #[])
    cwd := project / "exports" }
  if (← IO.getEnv "ZKC_TIMES").isSome then
    IO.eprintln s!"lake comparator ({label}): {(← IO.monoMsNow) - start} ms"
  let said := out.stdout ++ out.stderr
  keep (match out.exitCode with | 0 => .accepted | 1 => .refused | _ => .failed) said

end ZkcFormalTests.SubjectProject
