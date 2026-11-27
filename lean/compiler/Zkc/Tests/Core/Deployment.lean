import Zkc.Tests.Core.Deployment.Fixtures
import Zkc.Tests.Core.Deployment.Behavior
import Zkc.Tests.Core.Deployment.Refusals
import Zkc.Tests.Core.Deployment.Witnesses

/-!
Core deployment, ideal random-oracle, and DAG-preserving handler specialization test suite.

Split across four focused submodules under `Zkc/Tests/Core/Deployment/`:
- `Fixtures`: concrete models (`deployModel`, `primeOrderModel`, `twoLawModel`), admitted suites,
  layouts, protocols (including depth-8 diamond DAG), declarations, and execution helpers.
- `Behavior`: canonical wire format checks, end-to-end execution, negative controls, ideal RO
  oracle execution, distribution-aware `V.LawKey` dispatch, and linear-size DAG specialization.
- `Refusals`: fail-closed declaration, session, retry, layout, and law-keyed suite refusals.
- `Witnesses`: concrete kernel-checked witness instantiations of `Statements.*`, streaming,
  derived-samples, compact, and abort-and-retry completeness, ideal RO linkage and query
  uniqueness / domain separation, and DAG specialization soundness.
-/
