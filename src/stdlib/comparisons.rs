use crate::error::Error;
use crate::interpreter::{
    primitives::{PrimitiveBinaryOp, PrimitiveOp},
    Value,
};

pub struct LessThan;
impl PrimitiveOp for LessThan {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for LessThan {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Boolean(x < y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Boolean(x < y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}

pub struct LessThanOrEqual;
impl PrimitiveOp for LessThanOrEqual {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for LessThanOrEqual {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Boolean(x <= y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Boolean(x <= y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}

pub struct GreaterThan;
impl PrimitiveOp for GreaterThan {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for GreaterThan {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Boolean(x > y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Boolean(x > y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}

pub struct GreaterThanOrEqual;
impl PrimitiveOp for GreaterThanOrEqual {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for GreaterThanOrEqual {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Boolean(x >= y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Boolean(x >= y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}

pub struct Equal;
impl PrimitiveOp for Equal {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Equal {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Boolean(x == y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Boolean(x == y))
        } else if let (Value::Boolean(x), Value::Boolean(y)) = (x, y) {
            Ok(Value::Boolean(x == y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}

pub struct NotEqual;
impl PrimitiveOp for NotEqual {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for NotEqual {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Boolean(x != y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Boolean(x != y))
        } else if let (Value::Boolean(x), Value::Boolean(y)) = (x, y) {
            Ok(Value::Boolean(x != y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
