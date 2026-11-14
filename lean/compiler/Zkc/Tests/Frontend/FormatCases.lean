/-!
# Programs for the canonical text

In the block format of the conformance tests; every program is admitted (`accept`). A function
`helper` stands at the top level of the file, in the suite of a module, or in the suite of a
module that implements an interface; it has no parameter or one; its result is `()` or `nat`;
its body is `return` alone, an `if` expression, or a guard followed by `return`. The two forms
that formatting must keep are among them: `return ()` alone (FM1, GR1) and `-> ()` on a `def`
without parameters in the suite of a module (FM2, GR4).
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

=== top-nullary-nat-conditional | accept | no parameter, the result `nat`, a body of an `if` expression, at the top level of the file
module t

def helper() -> nat:
    if true then 0 else 0

=== top-nullary-nat-guarded | accept | no parameter, the result `nat`, a body of a guard, then `return`, at the top level of the file
module t

def helper() -> nat:
    guard true
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

=== top-unary-nat-conditional | accept | one parameter, the result `nat`, a body of an `if` expression, at the top level of the file
module t

def helper(x: nat) -> nat:
    if true then 0 else 0

=== top-unary-nat-guarded | accept | one parameter, the result `nat`, a body of a guard, then `return`, at the top level of the file
module t

def helper(x: nat) -> nat:
    guard true
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

=== module-nullary-nat-conditional | accept | no parameter, the result `nat`, a body of an `if` expression, in the suite of a module
module t

module Implementation:
    def helper() -> nat:
        if true then 0 else 0

=== module-nullary-nat-guarded | accept | no parameter, the result `nat`, a body of a guard, then `return`, in the suite of a module
module t

module Implementation:
    def helper() -> nat:
        guard true
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

=== module-unary-nat-conditional | accept | one parameter, the result `nat`, a body of an `if` expression, in the suite of a module
module t

module Implementation:
    def helper(x: nat) -> nat:
        if true then 0 else 0

=== module-unary-nat-guarded | accept | one parameter, the result `nat`, a body of a guard, then `return`, in the suite of a module
module t

module Implementation:
    def helper(x: nat) -> nat:
        guard true
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

=== interface-nullary-nat-conditional | accept | no parameter, the result `nat`, a body of an `if` expression, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper() -> nat:
        if true then 0 else 0

=== interface-nullary-nat-guarded | accept | no parameter, the result `nat`, a body of a guard, then `return`, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper() -> nat:
        guard true
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

=== interface-unary-nat-conditional | accept | one parameter, the result `nat`, a body of an `if` expression, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper(x: nat) -> nat:
        if true then 0 else 0

=== interface-unary-nat-guarded | accept | one parameter, the result `nat`, a body of a guard, then `return`, in the suite of a module that implements an interface
module t

interface HasValue:
    def value() -> nat

module Implementation: HasValue:
    def value(): 0
    def helper(x: nat) -> nat:
        guard true
        return 0
"##

end Zkc.Tests.Frontend
