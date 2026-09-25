use crate::{
    Error, Stop,
    format::{array, list, natural, string},
};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use serde_json::{Value, json};
use std::collections::HashSet;

/// An owned descriptor resolved by the consumer's operation library.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sort(pub Value);
/// Consumer-installed static meaning. Dependencies, signatures, descriptors and
/// the condition sort must remain stable across binding and execution. Mutable
/// provider state belongs to Bindings; changing the library requires admission
/// against the newly selected meaning.
pub trait Library {
    type Operation: Clone;
    fn sort(&self, value: &Value) -> Result<Sort, Error>;
    /// The condition sort of this language; its values are interpreted by
    /// `Bindings::condition`, independently of their serialized spelling.
    fn condition_sort(&self) -> Sort;
    fn operation(&self, value: &Value) -> Result<Self::Operation, Error>;
    fn signature(&self, operation: &Self::Operation) -> (Vec<Sort>, Sort);
    fn dependencies(&self) -> Value;
}
#[derive(Debug)]
pub(crate) enum Program<O> {
    Return(usize),
    Stop(Stop),
    Apply(O, Vec<usize>, Box<Self>),
    Choose(usize, Box<Self>, Box<Self>),
    Repeat(BigUint, Sort, usize, Box<Self>, Box<Self>),
    Bind(Sort, Box<Self>, Box<Self>),
}
#[derive(Clone, Copy)]
pub(crate) enum SourceFormat {
    Finite,
    Region,
}
impl SourceFormat {
    /// A request names one of the installed source semantics; any other string
    /// is a shape error of the request.
    pub fn decode(semantics: &str) -> Result<Self, Error> {
        match semantics {
            "finite-source-1" => Ok(Self::Finite),
            "region-source-1" => Ok(Self::Region),
            _ => Err(Error("invalid-shape")),
        }
    }
}
#[derive(Debug)]
pub(crate) struct Input {
    pub name: String,
    pub sort: Sort,
}
pub(crate) struct Context {
    pub role: String,
    pub inputs: Vec<Input>,
    pub result: Sort,
    pub dependencies: Value,
    pub condition: Sort,
}
/// The context grammar: role, inputs with their access and kind, result and
/// dependency references. Decode each type before the following metadata, as
/// the independent codec does; callers check context validity separately.
pub(crate) fn context(library: &impl Library, value: &Value) -> Result<Context, Error> {
    let a = array(value, 4)?;
    let role = string(&a[0])?.to_owned();
    let mut inputs = Vec::new();
    for input in list(&a[1])? {
        let i = array(input, 4)?;
        let name = string(&i[0])?.to_owned();
        let sort = library.sort(&i[1])?;
        let access = list(&i[2])?;
        match access {
            [shared] if shared == "shared" => {}
            [private, role] if private == "private" => {
                string(role)?;
            }
            _ => return Err(Error("invalid-shape")),
        }
        if i[3] != "argument" && i[3] != "capture" {
            return Err(Error("invalid-shape"));
        }
        inputs.push(Input { name, sort });
    }
    let result = library.sort(&a[2])?;
    for dependency in list(&a[3])? {
        let d = array(dependency, 2)?;
        string(&d[0])?;
        string(&d[1])?;
    }
    Ok(Context {
        role,
        inputs,
        result,
        dependencies: a[3].clone(),
        condition: library.condition_sort(),
    })
}
/// A valid context (docs/spec/profiles/compiler/direct-plan.md): a nonempty
/// role; nonempty, distinct input names, each shared or private to that role;
/// distinct dependency names, with every name and revision nonempty. The value
/// has already been decoded by `context`.
pub(crate) fn valid_context(value: &Value) -> bool {
    let role = &value[0];
    let mut names = HashSet::new();
    let mut dependencies = HashSet::new();
    role.as_str().is_some_and(|role| !role.is_empty())
        && value[1].as_array().is_some_and(|inputs| {
            inputs.iter().all(|input| {
                input[0].as_str().is_some_and(|name| !name.is_empty())
                    && names.insert(input[0].clone())
                    && (input[2] == json!(["shared"]) || input[2] == json!(["private", role]))
            })
        })
        && value[3].as_array().is_some_and(|references| {
            references.iter().all(|reference| {
                reference[0].as_str().is_some_and(|name| !name.is_empty())
                    && reference[1]
                        .as_str()
                        .is_some_and(|revision| !revision.is_empty())
                    && dependencies.insert(reference[0].clone())
            })
        })
}
fn index(value: &Value, context: &[Sort], ty: &Sort) -> Result<usize, Error> {
    let i = natural(value)?.to_usize().ok_or(Error("invalid-operand"))?;
    if context.get(i) != Some(ty) {
        return Err(Error("invalid-operand"));
    }
    Ok(i)
}
pub(crate) fn decode<L: Library>(
    library: &L,
    value: &Value,
    context: &[Sort],
    result: &Sort,
    depth: usize,
    format: SourceFormat,
) -> Result<Program<L::Operation>, Error> {
    if depth == 0 {
        return Err(Error("depth-limit"));
    }
    let a = list(value)?;
    let tag = a.first().ok_or(Error("invalid-shape"))?;
    Ok(match (string(tag)?, a.len()) {
        ("return", 2) => Program::Return(index(&a[1], context, result)?),
        ("stop", 2) => Program::Stop(Stop::decode(string(&a[1])?)?),
        ("apply", 4) => {
            let op = library.operation(&a[1])?;
            let (args, output) = library.signature(&op);
            let operands = list(&a[2])?;
            if operands.len() != args.len() {
                return Err(Error("operand-count"));
            }
            let indices = operands
                .iter()
                .zip(args.iter())
                .map(|(i, t)| index(i, context, t))
                .collect::<Result<Vec<_>, _>>()?;
            let mut next_context = vec![output];
            next_context.extend_from_slice(context);
            Program::Apply(
                op,
                indices,
                Box::new(decode(
                    library,
                    &a[3],
                    &next_context,
                    result,
                    depth - 1,
                    format,
                )?),
            )
        }
        ("if", 4) => Program::Choose(
            index(&a[1], context, &library.condition_sort())?,
            Box::new(decode(library, &a[2], context, result, depth - 1, format)?),
            Box::new(decode(library, &a[3], context, result, depth - 1, format)?),
        ),
        ("repeat", 6) => {
            let count = natural(&a[1])?;
            let ty = library.sort(&a[2])?;
            let initial = index(&a[3], context, &ty)?;
            let mut scope = vec![ty.clone()];
            scope.extend_from_slice(context);
            Program::Repeat(
                count,
                ty.clone(),
                initial,
                Box::new(decode(library, &a[4], &scope, &ty, depth - 1, format)?),
                Box::new(decode(library, &a[5], &scope, result, depth - 1, format)?),
            )
        }
        ("bind", 4) if matches!(format, SourceFormat::Region) => {
            let ty = library.sort(&a[1])?;
            let body = decode(library, &a[2], context, &ty, depth - 1, format)?;
            let mut scope = vec![ty.clone()];
            scope.extend_from_slice(context);
            Program::Bind(
                ty,
                Box::new(body),
                Box::new(decode(library, &a[3], &scope, result, depth - 1, format)?),
            )
        }
        _ => return Err(Error("invalid-shape")),
    })
}
