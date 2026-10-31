//! Bind generated contracts to independently admitted operation owners.
use super::*;
use crate::entry::interface::{InputPort, raw::Port};

fn nominal(s: &Schema, family: &str, member: &str, constructible: bool) -> Result<()> {
    // Closed type arguments belong after the generated member, as in Layouts.
    let (base, args) = family
        .find('<')
        .map_or((family, ""), |i| (&family[..i], &family[i..]));
    require(
        s.display_type == format!("{base}::{member}{args}")
            && s.constructible == constructible
            && !s.custody,
        "entry-host-nominal",
    )
}
fn record<'a>(s: &Schema, fields: impl Iterator<Item = (&'a str, &'a Schema)>) -> Result<()> {
    require(s.kind == SchemaKind::Record, "entry-host-deployment-shape")?;
    let fields = fields.collect::<Vec<_>>();
    require(
        s.fields.len() == fields.len()
            && s.fields
                .iter()
                .zip(fields)
                .all(|(a, (n, s))| a.name == n && a.schema == *s),
        "entry-host-deployment-shape",
    )
}
pub(super) fn ordinary(interface: &super::super::Interface, p: InputPort<'_>) -> bool {
    interface.is_source_data(p)
}
fn input_record<'a>(
    s: &Schema,
    interface: &super::super::Interface,
    ports: impl Iterator<Item = InputPort<'a>>,
) -> Result<()> {
    record(
        s,
        ports
            .filter(|p| ordinary(interface, *p))
            .map(|p| (p.definition.name.as_str(), &p.definition.schema)),
    )
}
fn output_record<'a>(s: &Schema, ports: impl Iterator<Item = &'a Port>) -> Result<()> {
    record(s, ports.map(|p| (p.name.as_str(), &p.schema)))
}
pub(super) fn check_interface(
    d: &carrier::Deployment,
    interface: &super::super::Interface,
    families: &mut BTreeMap<String, String>,
) -> Result<()> {
    interface
        .check_executable_ports()
        .map_err(|e| EntryError::new(EntryPhase::Interface, e))?;
    require(d.results.len() == 1, "entry-host-deployment-signature")?;
    let r = &d.results[0];
    let source = interface.entry();
    let family = if d.operation == "run" {
        let (base, _) = source.rsplit_once("::").expect("qualified child entry");
        let args = r.display_type.strip_prefix(&format!("{base}::RunResult"));
        require(args.is_some(), "entry-host-nominal")?;
        let args = args.expect("checked family prefix");
        let family = format!("{base}{args}");
        let expected = if args.is_empty() {
            format!("{base}::run")
        } else {
            use sha2::{Digest, Sha256};
            format!(
                "{base}::run_{}",
                crate::io::bytes::hex(&Sha256::digest(family.as_bytes()))
            )
        };
        require(source == expected, "entry-host-nominal")?;
        family
    } else {
        source.to_owned()
    };
    let family = family.as_str();
    let source = family.split('<').next().expect("family base");
    // Identical nominal families cannot be rebound to a different checked source.
    let family_pin = format!(
        "{}:{}:{}",
        interface.capture(),
        interface.toolchain(),
        family
    );
    fn pin(
        s: &Schema,
        prefix: &str,
        family_pin: &str,
        families: &mut BTreeMap<String, String>,
    ) -> Result<()> {
        if s.display_type.starts_with(prefix) {
            for (key, value) in [
                (format!("identity:{}", s.identity), family_pin.to_owned()),
                (
                    format!("type:{}", s.display_type),
                    format!("{family_pin}:{}", s.identity),
                ),
            ] {
                if let Some(old) = families.insert(key, value.clone()) {
                    require(old == value, "entry-host-family")?;
                }
            }
            for f in &s.fields {
                pin(&f.schema, prefix, family_pin, families)?;
            }
            for f in s.alternatives.iter().flat_map(|a| &a.fields) {
                pin(&f.schema, prefix, family_pin, families)?;
            }
        }
        Ok(())
    }
    for s in d.parameters.iter().chain(&d.results) {
        pin(s, &format!("{source}::"), &family_pin, families)?;
    }
    if !interface.is_proof() {
        require(
            d.operation == "run" && d.parameters.len() == 1,
            "entry-host-deployment-signature",
        )?;
        nominal(&d.parameters[0], family, "Inputs", true)?;
        nominal(r, family, "RunResult", false)?;
        require(
            d.parameters[0].fields.len() == interface.roles().len()
                && r.fields.len() == interface.roles().len(),
            "entry-host-role-shape",
        )?;
        for ((input, output), role) in d.parameters[0]
            .fields
            .iter()
            .zip(&r.fields)
            .zip(interface.roles())
        {
            require(
                input.name == role.name && output.name == role.name,
                "entry-host-role-shape",
            )?;
            nominal(
                &input.schema,
                family,
                &format!("Inputs::{}", role.name),
                true,
            )?;
            nominal(
                &output.schema,
                family,
                &format!("RunResult::{}", role.name),
                false,
            )?;
            input_record(&input.schema, interface, interface.input_ports(role))?;
            output_record(&output.schema, interface.output_ports(role))?;
        }
    } else {
        require(d.parameters.len() == 2, "entry-host-deployment-signature")?;
        nominal(&d.parameters[0], family, "Public", true)?;
        input_record(&d.parameters[0], interface, interface.public_ports())?;
        let proof = interface.proof().ok_or_else(|| error("entry-host-stage"))?;
        if d.operation == "prove" {
            nominal(&d.parameters[1], family, "Witness", true)?;
            let role = &interface.roles()[proof.prover];
            input_record(&d.parameters[1], interface, interface.named_inputs(role))?;
            nominal(r, family, "ProveResult", false)?;
            require(
                r.kind == SchemaKind::Record
                    && r.fields.len() == 2
                    && r.fields[0].name == "proof"
                    && r.fields[1].name == "outputs",
                "entry-host-deployment-shape",
            )?;
            candidate(&r.fields[0].schema, family)?;
            nominal(&r.fields[1].schema, family, "ProverOutputs", false)?;
            output_record(&r.fields[1].schema, interface.output_ports(role))?;
        } else {
            require(d.operation == "verify", "entry-host-stage")?;
            candidate(&d.parameters[1], family)?;
            nominal(r, family, "VerifyResult", false)?;
            require(
                r.kind == SchemaKind::Variant && r.alternatives.len() == 2,
                "entry-host-deployment-shape",
            )?;
            let accepted = &r.alternatives[0];
            let rejected = &r.alternatives[1];
            require(
                accepted.name == "Accepted"
                    && accepted.fields.len() == 1
                    && accepted.fields[0].name == "outputs"
                    && rejected.name == "Rejected"
                    && rejected.fields.is_empty(),
                "entry-host-deployment-shape",
            )?;
            nominal(&accepted.fields[0].schema, family, "VerifierOutputs", false)?;
            output_record(
                &accepted.fields[0].schema,
                interface.output_ports(&interface.roles()[proof.verifier]),
            )?;
        }
    }
    Ok(())
}
fn candidate(s: &Schema, family: &str) -> Result<()> {
    nominal(s, family, "Proof", true)?;
    require(
        s.kind == SchemaKind::Record
            && s.fields.len() == 1
            && s.fields[0].name == "bytes"
            && s.fields[0].schema.kind == SchemaKind::Builtin
            && s.fields[0].schema.leaves == ["bytes"],
        "entry-host-proof-shape",
    )
}
