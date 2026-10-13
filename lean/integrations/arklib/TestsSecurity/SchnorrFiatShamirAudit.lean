import ZkcSecurity.Examples.SchnorrConstructed
import ZkcSecurity.Examples.SchnorrConstructionControls
import ZkcTools.DeclarationAudit

run_cmd ZkcTools.DeclarationAudit.check [`Zkc.Protocols.Schnorr.Construction,
    `Zkc.Protocols.Schnorr.NativeConstruction, `ZkcSecurity.VCVio.Schnorr.FiatShamir,
    `ZkcSecurity.Examples.SchnorrFiatShamir, `ZkcSecurity.Examples.SchnorrConstructed,
    `ZkcSecurity.Examples.SchnorrConstructedData,
    `ZkcSecurity.Examples.SchnorrConstructionControls] "SCHNORR-FS-AUDIT-PASS"
