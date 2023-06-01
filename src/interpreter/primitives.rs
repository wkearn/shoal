use crate::error::Error;
use crate::interpreter::Value;

/// Trait to be implemented by all primitive operators
pub trait PrimitiveOp {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error>;
}

/// Trait to be implemented by primitive binary operators
pub trait PrimitiveBinaryOp: PrimitiveOp {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error>;
}

/// Trait to be implemented by primitive unary operators
pub trait PrimitiveUnaryOp: PrimitiveOp {
    fn apply(&self, x: &Value) -> Result<Value, Error>;
}
