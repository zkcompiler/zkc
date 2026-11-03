//! Interpret shared declarations in the runtime's closed logical profile.
//!
//! Declarations determine scopes, ports and requirements. Installed domain
//! facts and native type admission independently decide whether they apply.
//! No declaration installs code, a codec, a representation or a service.
use super::super::{ResourceDomain, TypeArgument};
use super::*;
use zkc_catalog::{Facet, Kind, Operation, ParameterValidator, Port, Signature, Term};

#[derive(Clone)]
enum Argument {
    Domain {
        sort: &'static str,
        identity: Identity,
    },
    Slot(ResourceDomain),
    Type(LogicalType),
    Nat(u64),
}
impl Argument {
    fn kind(&self) -> Kind {
        match self {
            Self::Domain { sort, .. } => Kind::Domain(sort),
            Self::Slot(_) => Kind::Domain("Slot"),
            Self::Type(_) => Kind::Type,
            Self::Nat(_) => Kind::Nat,
        }
    }
    fn identity(&self) -> Result<Identity> {
        match self {
            Self::Domain { identity, .. } => Ok(*identity),
            _ => Err(support::failure()),
        }
    }
    fn ty(&self) -> Result<LogicalType> {
        match self {
            Self::Type(ty) => Ok(ty.clone()),
            _ => Err(support::failure()),
        }
    }
    fn structural(&self) -> Result<TypeArgument> {
        match self {
            Self::Domain { identity, .. } => Ok(TypeArgument::Domain(*identity)),
            Self::Type(ty) => Ok(TypeArgument::Type(ty.clone())),
            Self::Nat(n) => Ok(TypeArgument::Nat(*n)),
            Self::Slot(_) => Err(support::failure()),
        }
    }
}

/// An installed domain of the declared sort.
fn domain(sort: &'static str, identity: Identity) -> Result<Argument> {
    if identity.sort() != Some(sort) {
        return Err(support::failure());
    }
    Ok(Argument::Domain { sort, identity })
}

fn root(kind: Kind, text: &str) -> Result<Argument> {
    match kind {
        Kind::Domain("Slot") => ResourceDomain::parse(text)
            .map(Argument::Slot)
            .map_err(|_| AdmissionError::new(ErrorCode::Type, "binding-resource-unit-domain")),
        Kind::Domain(sort) => domain(sort, Identity::parse(text)?),
        Kind::Type => LogicalType::parse(text).map(Argument::Type),
        Kind::Nat => super::super::structural::natural(text).map(Argument::Nat),
    }
}

fn project(parent: &Argument, member: &str) -> Result<Argument> {
    let declaration = zkc_catalog::CATALOG
        .members
        .iter()
        .find(|row| row.owner == parent.kind() && row.name == member)
        .ok_or_else(support::failure)?;
    let Kind::Domain(sort) = declaration.result else {
        return Err(support::failure());
    };
    // The installed association of the owner's row.
    let value = parent
        .identity()?
        .member(member)
        .ok_or_else(support::failure)?;
    domain(sort, value)
}

fn apply(name: &str, indices: &[usize], scope: &[Argument]) -> Result<LogicalType> {
    let declaration = zkc_catalog::constructor(name).ok_or_else(support::failure)?;
    if indices.len() != declaration.parameters.len() {
        return Err(support::failure());
    }
    let args = indices
        .iter()
        .zip(declaration.parameters)
        .map(|(&index, &kind)| {
            let value = scope.get(index).ok_or_else(support::failure)?;
            if value.kind() != kind {
                return Err(support::failure());
            }
            Ok(value)
        })
        .collect::<Result<Vec<_>>>()?;
    let kind = Type::parse_kind(name)?;
    match kind {
        Type::Sequence | Type::FieldArray | Type::FixedVector => {
            let values = args
                .into_iter()
                .map(Argument::structural)
                .collect::<Result<Vec<_>>>()?;
            LogicalType::application(name, &values)
        }
        Type::ResourceUnit => match args.as_slice() {
            [Argument::Slot(slot)] => Ok(LogicalType::resource_unit(*slot)),
            _ => Err(support::failure()),
        },
        _ => {
            let identity = match args.as_slice() {
                [] => Identity::None,
                [argument] => argument.identity()?,
                _ => return Err(support::failure()),
            };
            LogicalType::new(kind, identity)
        }
    }
}

/// Installed capabilities are not inferred from a declaration's requirements:
/// a domain argument holds exactly the capabilities its installed row declares.
/// Unknown predicates fail closed, including declared but uninstalled codecs.
fn capability(name: &str, args: &[&Argument]) -> bool {
    let [Argument::Domain { sort, identity }] = args else {
        return false;
    };
    identity.sort() == Some(*sort) && identity.holds(name)
}

pub(super) fn natural_parameter_bound(contract: &str) -> u64 {
    use ParameterValidator as V;
    match zkc_catalog::operation(contract).map(|row| row.parameters.validator) {
        Some(V::Extent | V::MatrixVector | V::GatherIndices) => {
            super::super::NATURAL_ARGUMENT_LIMIT
        }
        _ => u64::MAX,
    }
}

fn attribute_rule(operation: &Operation, scope: &[Argument]) -> Result<AttributeRule> {
    use ParameterValidator as V;
    Ok(match operation.parameters.validator {
        V::None => AttributeRule::None,
        V::Natural => AttributeRule::Unsigned64,
        V::Extent => AttributeRule::NaturalIndex,
        V::FieldLiteral | V::FieldLiterals => {
            let field = scope
                .get(operation.parameters.field.ok_or_else(support::failure)?)
                .ok_or_else(support::failure)?
                .identity()?;
            support::literal_rule(
                if operation.parameters.validator == V::FieldLiteral {
                    AttributeRule::FieldDecimal
                } else {
                    AttributeRule::FieldDecimals
                },
                field,
            )
        }
        V::MatrixShape => AttributeRule::MatrixDimensions,
        V::MatrixIdentity => AttributeRule::MatrixIdentity,
        V::AssetIdentity => AttributeRule::AssetIdentity,
        V::MatrixVector => AttributeRule::MatrixShape,
        V::GatherIndices => AttributeRule::NaturalIndices,
        V::ScatterIndices => AttributeRule::ScatterShape,
        V::NumericalExpression => AttributeRule::NumericalExpression,
        V::NativeIndexBlock => match (operation.parameters.minimum, operation.parameters.maximum) {
            (3, Some(3)) => AttributeRule::NativeIndexBlock,
            (4, Some(4)) => AttributeRule::NativeGatedIndexBlock,
            _ => return Err(support::failure()),
        },
        V::NativeOrigin => {
            if operation
                .facets
                .iter()
                .any(|f| matches!(f, Facet::Observation { .. }))
            {
                AttributeRule::NativeMessageTemplate
            } else {
                match operation.facets.iter().find_map(|f| match f {
                    Facet::Sampling { domain, .. } => Some(domain),
                    _ => None,
                }) {
                    Some(zkc_catalog::SamplingDomain::Field) => {
                        AttributeRule::NativeChallengeTemplate
                    }
                    Some(zkc_catalog::SamplingDomain::BoundedIndex) => {
                        AttributeRule::NativeIndexTemplate
                    }
                    _ => return Err(support::failure()),
                }
            }
        }
    })
}

pub(super) fn signature(binding: &OperationBinding) -> Result<OperationSignature<LogicalType>> {
    let declaration = zkc_catalog::operation(&binding.contract).ok_or_else(support::failure)?;
    // Program/0 stores table layouts beside the field argument. They are
    // physical selections, not catalog roots. The physical owner validates
    // both layouts independently; this projection only derives erasure ports.
    let static_arguments = if binding.contract == "table.relayout" {
        let [field, _, _] = binding.arguments.as_slice() else {
            return Err(support::failure());
        };
        std::slice::from_ref(field)
    } else {
        binding.arguments.as_slice()
    };
    let mut arguments = static_arguments.iter();
    let mut scope = Vec::with_capacity(declaration.scope.len());
    for term in declaration.scope {
        scope.push(match term {
            Term::Root { parameter, .. } => {
                root(*parameter, arguments.next().ok_or_else(support::failure)?)?
            }
            Term::Project { member, parent } => {
                project(scope.get(*parent).ok_or_else(support::failure)?, member)?
            }
            Term::Apply {
                constructor,
                arguments,
            } => Argument::Type(apply(constructor, arguments, &scope)?),
            Term::Natural(n) => Argument::Nat(*n),
        });
    }
    for requirement in declaration.requirements {
        let args = requirement
            .arguments
            .iter()
            .map(|&index| scope.get(index).ok_or_else(support::failure))
            .collect::<Result<Vec<_>>>()?;
        if !capability(requirement.capability, &args) {
            return Err(support::failure());
        }
    }
    if let Signature::Numerical { result, .. } = declaration.signature {
        // The finite numerical family additionally carries its scalar/vector mask.
        return numerical::signature(binding, result);
    }
    if arguments.next().is_some() {
        return Err(support::failure());
    }
    let port = |port: &Port| match port {
        Port::Term(index) => scope.get(*index).ok_or_else(support::failure)?.ty(),
        Port::Apply {
            constructor,
            arguments,
        } => apply(constructor, arguments, &scope),
    };
    let Signature::Fixed { inputs, outputs } = declaration.signature else {
        unreachable!()
    };
    let signature = OperationSignature {
        inputs: inputs.iter().map(port).collect::<Result<_>>()?,
        outputs: outputs.iter().map(port).collect::<Result<_>>()?,
        attributes: attribute_rule(declaration, &scope)?,
    };
    // Observation payloads must have a complete installed canonical message
    // interpretation. A scoped Type alone cannot grant a wire capability.
    for facet in declaration.facets {
        if let Facet::Observation { payload_input, .. } = facet
            && !signature.inputs[*payload_input].is_native_message_data()
        {
            return Err(support::failure());
        }
    }
    Ok(signature)
}
