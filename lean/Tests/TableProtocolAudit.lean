import Examples.TableProtocol.Invocation
import Examples.TableProtocol.Admission
import Tools.DeclarationAudit

-- Select declarations by their defining modules, including generated bodies.
run_cmd Tools.DeclarationAudit.check [`Examples.TableProtocol] "TABLE-PROTOCOL-AUDIT-PASS"
