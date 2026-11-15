/-!
# Programs for the canonical text

In the block format of the conformance tests; every program is admitted (`accept`). Among them
are the two forms that formatting must keep: `return ()` alone (FM1, GR1), and `-> ()` on a
`def` that without it is a member definition (FM2, GR4).

- A function `helper` at the top level of the file, in the suite of a module, or in the suite of
  a module that implements an interface; with no parameter or one; the result `()` with a body
  of `return` alone, an `if` expression or a guard followed by `return`, or the result `nat` with
  a body of `return` alone.
- In the suite of a module, a `def` without parameters and with the result `()` that keeps
  `-> ()` (after `spec`, after a kernel attribute, in a nested module) and one that loses it
  (after `pub` or `entry`, with static parameters, with a `where`, in a section).
- A member definition whose body is `return ()` alone; a body of `return` alone of a call whose
  result is `()`; a suite whose only line is the empty statement; comments next to `return ()`.
-/

namespace Zkc.Tests.Frontend

def formatCases : String := r##"
=== top-nullary-unit-return | accept | no parameter, the result `()`, a body of `return` alone, at the top level of the file
module t

def helper() -> ():
    return ()

=== top-nullary-unit-conditional | accept | no parameter, the result `()`, a body of an `if` expression, at the top level of the file
module t

def helper() -> ():
    if true then () else ()

=== top-nullary-unit-guarded | accept | no parameter, the result `()`, a body of a guard, then `return`, at the top level of the file
module t

def helper() -> ():
    guard true
    return ()

=== top-nullary-nat-return | accept | no parameter, the result `nat`, a body of `return` alone, at the top level of the file
module t

def helper() -> nat:
    return 0

=== top-unary-unit-return | accept | one parameter, the result `()`, a body of `return` alone, at the top level of the file
module t

def helper(x: nat) -> ():
    return ()

=== top-unary-unit-conditional | accept | one parameter, the result `()`, a body of an `if` expression, at the top level of the file
module t

def helper(x: nat) -> ():
    if true then () else ()

=== top-unary-unit-guarded | accept | one parameter, the result `()`, a body of a guard, then `return`, at the top level of the file
module t

def helper(x: nat) -> ():
    guard true
    return ()

=== top-unary-nat-return | accept | one parameter, the result `nat`, a body of `return` alone, at the top level of the file
module t

def helper(x: nat) -> nat:
    return 0

=== module-nullary-unit-return | accept | no parameter, the result `()`, a body of `return` alone, in the suite of a module
module t

module Implementation:
    def helper() -> ():
        return ()

=== module-nullary-unit-conditional | accept | no parameter, the result `()`, a body of an `if` expression, in the suite of a module
module t

module Implementation:
    def helper() -> ():
        if true then () else ()

=== module-nullary-unit-guarded | accept | no parameter, the result `()`, a body of a guard, then `return`, in the suite of a module
module t

module Implementation:
    def helper() -> ():
        guard true
        return ()

=== module-nullary-nat-return | accept | no parameter, the result `nat`, a body of `return` alone, in the suite of a module
module t

module Implementation:
    def helper() -> nat:
        return 0

=== module-unary-unit-return | accept | one parameter, the result `()`, a body of `return` alone, in the suite of a module
module t

module Implementation:
    def helper(x: nat) -> ():
        return ()

=== module-unary-unit-conditional | accept | one parameter, the result `()`, a body of an `if` expression, in the suite of a module
module t

module Implementation:
    def helper(x: nat) -> ():
        if true then () else ()

=== module-unary-unit-guarded | accept | one parameter, the result `()`, a body of a guard, then `return`, in the suite of a module
module t

module Implementation:
    def helper(x: nat) -> ():
        guard true
        return ()

=== module-unary-nat-return | accept | one parameter, the result `nat`, a body of `return` alone, in the suite of a module
module t

module Implementation:
    def helper(x: nat) -> nat:
        return 0

=== interface-nullary-unit-return | accept | no parameter, the result `()`, a body of `return` alone, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper() -> ():
        return ()

=== interface-nullary-unit-conditional | accept | no parameter, the result `()`, a body of an `if` expression, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper() -> ():
        if true then () else ()

=== interface-nullary-unit-guarded | accept | no parameter, the result `()`, a body of a guard, then `return`, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper() -> ():
        guard true
        return ()

=== interface-nullary-nat-return | accept | no parameter, the result `nat`, a body of `return` alone, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper() -> nat:
        return 0

=== interface-unary-unit-return | accept | one parameter, the result `()`, a body of `return` alone, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper(x: nat) -> ():
        return ()

=== interface-unary-unit-conditional | accept | one parameter, the result `()`, a body of an `if` expression, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper(x: nat) -> ():
        if true then () else ()

=== interface-unary-unit-guarded | accept | one parameter, the result `()`, a body of a guard, then `return`, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper(x: nat) -> ():
        guard true
        return ()

=== interface-unary-nat-return | accept | one parameter, the result `nat`, a body of `return` alone, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper(x: nat) -> nat:
        return 0

=== module-spec-nullary-unit | accept | `spec def` with no parameter and the result `()`, in the suite of a module: it keeps `-> ()`
module t

module Implementation:
    spec def helper() -> ():
        if true then () else ()

=== module-kernel-nullary-unit | accept | a `def` with a kernel attribute, no parameter and the result `()`, in the suite of a module: it keeps `-> ()`
module t

module Implementation:
    #[kernel("helper")]
    def helper() -> ():
        return ()

=== nested-module-nullary-unit | accept | no parameter and the result `()`, in the suite of a module in the suite of a module: it keeps `-> ()`
module t

module Outer:
    module Inner:
        def helper() -> ():
            if true then () else ()

=== module-pub-nullary-unit | accept | `pub def` with no parameter and the result `()`, in the suite of a module: it loses `-> ()`
module t

module Implementation:
    pub def helper() -> ():
        if true then () else ()

=== module-entry-nullary-unit | accept | `entry def` with no parameter and the result `()`, in the suite of a module: it loses `-> ()`
module t

module Implementation:
    entry def helper() -> ():
        if true then () else ()

=== module-static-nullary-unit | accept | static parameters, no parameter and the result `()`, in the suite of a module: it loses `-> ()`
module t

module Implementation:
    def helper<n: nat>() -> ():
        if true then () else ()
    def run(x: nat) -> ():
        return helper<1>()

=== module-where-nullary-unit | accept | a `where`, no parameter and the result `()`, in the suite of a module: it loses `-> ()`
module t

module Implementation:
    def helper() -> () where (1 > 0):
        if true then () else ()

=== section-nullary-unit | accept | no parameter and the result `()`, in a section in the suite of a module: it loses `-> ()`
module t

interface HasValue:
    def value() -> nat

module Three: HasValue:
    def value(): 3

module Implementation:
    section <K: HasValue>:
        def helper() -> ():
            if true then () else ()
    def run(x: nat) -> ():
        return helper<Three>()

=== member-definition-unit-return | accept | a member definition whose body is `return ()` alone, of an interface member with the result `()`
module t

interface Ticks:
    def tick() -> ()

module Clock: Ticks:
    def tick():
        return ()

def run() -> ():
    return Clock::tick()

=== top-unit-call-return | accept | a body of `return` alone of a call whose result is `()`, at the top level of the file
module t

def helper() -> ():
    return ()

def caller() -> ():
    return helper()

=== top-empty-statement | accept | a loop whose suite is the empty statement alone, at the top level of the file
module t

def helper(x: nat) -> nat:
    for i in 0..2:
        ()
    return x

=== top-nullary-unit-comments | accept | no parameter, the result `()`, a body of `return` alone with a comment before it and after it, at the top level of the file
module t

def helper() -> ():
    // nothing
    return () // done
"##

end Zkc.Tests.Frontend
