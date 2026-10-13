import TestsSecurity.PrefixSimulation
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [`ZkcSecurity.ArkLib.FiatShamir.Prefix,
    `TestsSecurity.PrefixSimulation] "PREFIX-SIMULATION-AUDIT-PASS"
