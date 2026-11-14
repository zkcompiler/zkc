import Zkc.Tests.Core.Printed

/-! The printed links of the fixtures, checked by the kernel.

Each command prints what `core-tool literal … parts=0` prints into the module of the same
name, and elaborates it: every typed term is type-checked and every fact that links it to
its raw syntax is decided by the kernel. The statements about them are in
`Zkc.Tests.Core.LinkedStatements`. -/

set_option autoImplicit false

printed_package LinkedSchnorr from file "fixtures/schnorr.json"
printed_package LinkedSumcheck from file "fixtures/sumcheck.json"
printed_package LinkedOpening from file "fixtures/opening.json"
printed_package LinkedTypes from file "fixtures/types.json"
printed_package LinkedBuiltins from file "fixtures/builtins.json"
printed_package LinkedDeclarations from file "fixtures/declarations.json"
printed_package LinkedLoops from file "fixtures/loops.json"
printed_package LinkedFacts from file "fixtures/facts.json"
printed_package LinkedRepeats from file "fixtures/repeats.json"
printed_package LinkedRepeatsStatic from file "fixtures/repeats-static.json"
printed_package LinkedAlternatives from file "fixtures/alternatives.json"
