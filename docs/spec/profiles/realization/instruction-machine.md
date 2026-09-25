# Instruction-list execution

This profile embeds an instruction machine's terminal classification as returned
data in the common execution model. It fixes the meaning of falloff and resumption.

## Embedded machine exits

A machine may return its terminal classification as data in an enclosing body.
The consumer's acceptance predicate then inspects that classification; an
outer return alone is not inner acceptance.

The selected instruction-list profile has:

```text
Exit = accept | reject(reason : String) | unavailable(reason : String)
     | incomplete
Terminal S E = (outcome : Exit, state : S, events : List E)
Step S E = next(state : S, events : List E)
         | halt(exit : Exit, state : S, events : List E)
```

For a primitive `step : Op → S → Step S E`, execution is:

```text
runList step [] s = (incomplete, s, [])
runList step (op :: rest) s =
  match step op s with
  | halt exit t es => (exit, t, es)
  | next t es => let (exit, u, fs) = runList step rest t
                 (exit, u, es ++ fs)
```

The enclosing signature replies with `Option Exit`. Its handler returns
`none` for a continuing primitive and `some exit` for a halting primitive,
retaining each primitive's state and events. The source continues on `none`,
returns the supplied exit on `some`, and returns `incomplete` at list falloff.
Its execution is exactly the list terminal embedded as
`(returned terminal.outcome, terminal.state, terminal.events)`.

Define `resume f terminal` to execute `f` on the terminal's state and concatenate
events when its exit is `incomplete`; otherwise it retains the terminal.
The list-append equation is:

```text
runList step (xs ++ ys) s = resume (runList step ys) (runList step xs s),
```

provided no primitive can explicitly halt with `incomplete`, at any input state.
The same premise permits executing a sequence of blocks by repeatedly resuming
their falloff, with the same result as their flattened instruction list.

If explicit `incomplete` halt is possible, the equation can fail: resumption
would execute beyond that halt. A representation distinguishing falloff from
terminal halt may use another justified composition rule. This profile never
resumes an outer PIR stopped outcome. Its `Exit` vocabulary is not imposed on
every native machine.
