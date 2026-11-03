//! Independent values and wire implementation; no native codecs or kernels.
#![allow(dead_code)]
use std::{cell::Cell, sync::Arc};
use zkc_runtime::{
    host::wire::{ProofBackend, WireBackend, WireError},
    vm::*,
};

pub const BOOL: &str = "bool@native.bool/0";
pub const BYTES: &str = "bytes@native.bytes/0";
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TestValue {
    Bool(bool),
    Index(u64),
    Bytes(Arc<[u8]>),
    Variant {
        ty: PhysicalType,
        alternative: usize,
        payload: Vec<TestValue>,
    },
}
impl Value for TestValue {
    fn physical_type(&self) -> PhysicalType {
        if let Self::Variant { ty, .. } = self {
            return ty.clone();
        }
        PhysicalType::parse(match self {
            Self::Bool(_) => BOOL,
            Self::Index(_) => "index@native.index/0",
            Self::Bytes(_) => BYTES,
            Self::Variant { .. } => unreachable!(),
        })
        .unwrap()
    }
    fn retained_bytes(&self) -> usize {
        match self {
            Self::Bytes(bytes) => bytes.len() + 32,
            Self::Variant { payload, .. } => {
                32 + payload.iter().map(Self::retained_bytes).sum::<usize>()
            }
            _ => 8,
        }
    }
    fn validate_serializable(&self) -> Result<(), BackendError> {
        Ok(())
    }
    fn unpack_variant(&self) -> Result<(PhysicalType, usize, Vec<Self>), BackendError> {
        match self {
            Self::Variant {
                ty,
                alternative,
                payload,
            } => Ok((ty.clone(), *alternative, payload.clone())),
            _ => Err(BackendError::new("variant")),
        }
    }
    fn control_variant_tag(&self) -> Result<usize, BackendError> {
        match self {
            Self::Variant { alternative, .. } => Ok(*alternative),
            _ => Err(BackendError::new("variant")),
        }
    }
    fn control_extent(&self, axis: usize) -> Result<u64, BackendError> {
        match (self, axis) {
            (Self::Bytes(bytes), 0) => Ok(bytes.len() as u64),
            _ => Err(BackendError::new("extent")),
        }
    }
    fn pack_variant(
        ty: PhysicalType,
        alternative: usize,
        payload: Vec<Self>,
    ) -> Result<Self, BackendError> {
        Ok(Self::Variant {
            ty,
            alternative,
            payload,
        })
    }
    fn control_bool(&self) -> Result<bool, BackendError> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => Err(BackendError::new("bool")),
        }
    }
    fn from_control_bool(b: bool) -> Result<Self, BackendError> {
        Ok(Self::Bool(b))
    }
    fn control_index(&self) -> Result<u64, BackendError> {
        match self {
            Self::Index(n) => Ok(*n),
            _ => Err(BackendError::new("index")),
        }
    }
    fn from_control_index(n: u64) -> Result<Self, BackendError> {
        Ok(Self::Index(n))
    }
}
#[derive(Clone, Copy, Default)]
pub enum Fault {
    #[default]
    None,
    MeasureLimit,
    MeasureBackend,
    DecodeInvalid,
    DecodeLimit,
    DecodeBackend,
    DecodeWrongType,
    EncodeLimit,
    EncodeBackend,
    EncodeOversizeBound,
    EncodeOverrun,
}
#[derive(Default)]
pub struct Host {
    pub fault: Fault,
    pub wire_disabled: bool,
    pub frames: Vec<FrameId>,
    pub leaves: Vec<FrameExit>,
    pub cleanup_failure: bool,
    pub decodes: Cell<usize>,
    pub encodes: Cell<usize>,
    pub measurements: Cell<usize>,
    pub raw_encodes: Cell<usize>,
}
impl Backend for Host {
    type Value = TestValue;
    type Operation = BoundSignature;
    type Call = ();
    type Checkpoint = ();
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn validate_value(&self, value: &TestValue) -> Result<(), BackendError> {
        value.validate_serializable()
    }
    fn enter_frame(&mut self, frame: &Frame, _: &[TestValue]) -> Result<(), BackendError> {
        assert_eq!(frame.parent(), self.frames.last().copied());
        self.frames.push(frame.id());
        Ok(())
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        _: &[TestValue],
    ) -> Result<(), BackendError> {
        assert_eq!(self.frames.pop(), Some(frame.id()));
        self.leaves.push(exit);
        if self.cleanup_failure {
            Err(BackendError::new("cleanup"))
        } else {
            Ok(())
        }
    }
    fn apply(
        &mut self,
        _: &BoundSignature,
        _: &Invocation<'_>,
        _: &[TestValue],
    ) -> Result<Vec<TestValue>, BackendError> {
        panic!("no installed operations")
    }
}
fn boolean(bytes: &[u8]) -> Result<bool, WireError> {
    if bytes.len() != 7 {
        return Err(WireError::Invalid(DecodeReason::Length));
    }
    if &bytes[..6] != b"ZKCV\0\x05" {
        return Err(WireError::Invalid(DecodeReason::Header));
    }
    match bytes[6] {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(WireError::Invalid(DecodeReason::Boolean)),
    }
}
impl WireBackend for Host {
    fn supports_wire(&self, ty: &PhysicalType) -> bool {
        !self.wire_disabled && ty.spelling() == BOOL
    }
    fn fixed_wire_size(&self, ty: &PhysicalType) -> Option<usize> {
        self.supports_wire(ty).then_some(7)
    }
    fn encoding_bound(&self, _: &TestValue) -> Result<usize, WireError> {
        Ok(if matches!(self.fault, Fault::EncodeOversizeBound) {
            usize::MAX
        } else {
            7
        })
    }
    fn decoding_bound(&self, _: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        self.measurements.set(self.measurements.get() + 1);
        match self.fault {
            Fault::MeasureLimit => return Err(WireError::Limit),
            Fault::MeasureBackend => return Err(WireError::Backend(BackendError::new("measure"))),
            _ => (),
        }
        boolean(bytes)?;
        Ok(8)
    }
    fn encode_wire(&self, value: &TestValue) -> Result<Vec<u8>, WireError> {
        self.encodes.set(self.encodes.get() + 1);
        match self.fault {
            Fault::EncodeLimit => return Err(WireError::Limit),
            Fault::EncodeBackend => return Err(WireError::Backend(BackendError::new("encode"))),
            Fault::EncodeOverrun => return Ok(vec![0; 8]),
            _ => (),
        }
        match value {
            TestValue::Bool(value) => {
                let mut frame = b"ZKCV\0\x05".to_vec();
                frame.push(u8::from(*value));
                Ok(frame)
            }
            _ => Err(WireError::Backend(BackendError::new("type"))),
        }
    }
    fn decode_wire(&self, _: &PhysicalType, bytes: &[u8]) -> Result<TestValue, WireError> {
        self.decodes.set(self.decodes.get() + 1);
        match self.fault {
            Fault::DecodeInvalid => Err(WireError::Invalid(DecodeReason::Boolean)),
            Fault::DecodeLimit => Err(WireError::Limit),
            Fault::DecodeBackend => Err(WireError::Backend(BackendError::new("decode"))),
            Fault::DecodeWrongType => Ok(TestValue::Index(1)),
            _ => Ok(TestValue::Bool(boolean(bytes)?)),
        }
    }
}
impl ProofBackend for Host {
    fn acceptance(&self, value: &TestValue) -> Option<bool> {
        if let TestValue::Bool(value) = value {
            Some(*value)
        } else {
            None
        }
    }
    fn raw_bytes<'a>(&self, value: &'a TestValue) -> Result<&'a [u8], WireError> {
        self.raw_encodes.set(self.raw_encodes.get() + 1);
        match value {
            TestValue::Bytes(bytes) => Ok(bytes),
            _ => Err(WireError::Backend(BackendError::new("raw-type"))),
        }
    }
    fn raw_decoding_bound(&self, _: &PhysicalType, bytes: &[u8]) -> Result<usize, WireError> {
        Ok(bytes.len() + 32)
    }
    fn decode_raw(&self, _: &PhysicalType, bytes: &[u8]) -> Result<TestValue, WireError> {
        Ok(TestValue::Bytes(bytes.into()))
    }
}

/// Omits both measurement methods deliberately: defaults must refuse closed.
#[derive(Default)]
pub struct Unmeasured(pub Host);
impl Backend for Unmeasured {
    type Value = TestValue;
    type Operation = BoundSignature;
    type Call = ();
    type Checkpoint = ();
    fn supports_boolean_literals(&self) -> bool {
        true
    }
    fn validate_value(&self, value: &TestValue) -> Result<(), BackendError> {
        value.validate_serializable()
    }
    fn enter_frame(&mut self, frame: &Frame, values: &[TestValue]) -> Result<(), BackendError> {
        self.0.enter_frame(frame, values)
    }
    fn leave_frame(
        &mut self,
        frame: &Frame,
        exit: FrameExit,
        values: &[TestValue],
    ) -> Result<(), BackendError> {
        self.0.leave_frame(frame, exit, values)
    }
    fn apply(
        &mut self,
        operation: &BoundSignature,
        invocation: &Invocation<'_>,
        values: &[TestValue],
    ) -> Result<Vec<TestValue>, BackendError> {
        self.0.apply(operation, invocation, values)
    }
}
impl WireBackend for Unmeasured {
    fn supports_wire(&self, ty: &PhysicalType) -> bool {
        self.0.supports_wire(ty)
    }
    fn fixed_wire_size(&self, ty: &PhysicalType) -> Option<usize> {
        self.0.fixed_wire_size(ty)
    }
    fn encoding_bound(&self, value: &TestValue) -> Result<usize, WireError> {
        self.0.encoding_bound(value)
    }
    fn encode_wire(&self, value: &TestValue) -> Result<Vec<u8>, WireError> {
        self.0.encode_wire(value)
    }
    fn decode_wire(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<TestValue, WireError> {
        self.0.decode_wire(ty, bytes)
    }
}
impl ProofBackend for Unmeasured {
    fn acceptance(&self, value: &TestValue) -> Option<bool> {
        self.0.acceptance(value)
    }
    fn raw_bytes<'a>(&self, value: &'a TestValue) -> Result<&'a [u8], WireError> {
        self.0.raw_bytes(value)
    }
    fn decode_raw(&self, ty: &PhysicalType, bytes: &[u8]) -> Result<TestValue, WireError> {
        self.0.decode_raw(ty, bytes)
    }
}
