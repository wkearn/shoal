use crate::error::Error;
use crate::interpreter::{
    primitives::{PrimitiveBinaryOp, PrimitiveOp, PrimitiveUnaryOp},
    Value,
};

pub struct Add;
impl PrimitiveOp for Add {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Add {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Integer(x + y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Float(x + y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Sub;
impl PrimitiveOp for Sub {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Sub {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Integer(x - y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Float(x - y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Mul;
impl PrimitiveOp for Mul {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Mul {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Integer(x * y))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Float(x * y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Div;
impl PrimitiveOp for Div {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Div {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Float(x / y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct IDiv;
impl PrimitiveOp for IDiv {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for IDiv {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Integer(x / y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Mod;
impl PrimitiveOp for Mod {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Mod {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Integer(x % y))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Max;
impl PrimitiveOp for Max {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Max {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Integer(*x.max(y)))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Float(x.max(*y)))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Min;
impl PrimitiveOp for Min {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        PrimitiveBinaryOp::apply(self, x, y)
    }
}
impl PrimitiveBinaryOp for Min {
    fn apply(&self, x: &Value, y: &Value) -> Result<Value, Error> {
        if let (Value::Integer(x), Value::Integer(y)) = (x, y) {
            Ok(Value::Integer(*x.min(y)))
        } else if let (Value::Float(x), Value::Float(y)) = (x, y) {
            Ok(Value::Float(x.min(*y)))
        } else {
            Err(Error::RuntimeError(
                "Arguments to operator were of the wrong type".into(),
            ))
        }
    }
}

pub struct Exp;
impl PrimitiveOp for Exp {
    fn apply(&self, x: &Value, _: &Value) -> Result<Value, Error> {
        PrimitiveUnaryOp::apply(self, x)
    }
}
impl PrimitiveUnaryOp for Exp {
    fn apply(&self, x: &Value) -> Result<Value, Error> {
        if let Value::Float(x) = x {
            Ok(Value::Float(x.exp()))
        } else {
            Err(Error::RuntimeError(
                "Argument to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Log;
impl PrimitiveOp for Log {
    fn apply(&self, x: &Value, _: &Value) -> Result<Value, Error> {
        PrimitiveUnaryOp::apply(self, x)
    }
}
impl PrimitiveUnaryOp for Log {
    fn apply(&self, x: &Value) -> Result<Value, Error> {
        if let Value::Float(x) = x {
            Ok(Value::Float(x.ln()))
        } else {
            Err(Error::RuntimeError(
                "Argument to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Sin;
impl PrimitiveOp for Sin {
    fn apply(&self, x: &Value, _: &Value) -> Result<Value, Error> {
        PrimitiveUnaryOp::apply(self, x)
    }
}
impl PrimitiveUnaryOp for Sin {
    fn apply(&self, x: &Value) -> Result<Value, Error> {
        if let Value::Float(x) = x {
            Ok(Value::Float(x.sin()))
        } else {
            Err(Error::RuntimeError(
                "Argument to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Cos;
impl PrimitiveOp for Cos {
    fn apply(&self, x: &Value, _: &Value) -> Result<Value, Error> {
        PrimitiveUnaryOp::apply(self, x)
    }
}
impl PrimitiveUnaryOp for Cos {
    fn apply(&self, x: &Value) -> Result<Value, Error> {
        if let Value::Float(x) = x {
            Ok(Value::Float(x.cos()))
        } else {
            Err(Error::RuntimeError(
                "Argument to operator were of the wrong type".into(),
            ))
        }
    }
}
pub struct Tan;
impl PrimitiveOp for Tan {
    fn apply(&self, x: &Value, _: &Value) -> Result<Value, Error> {
        PrimitiveUnaryOp::apply(self, x)
    }
}
impl PrimitiveUnaryOp for Tan {
    fn apply(&self, x: &Value) -> Result<Value, Error> {
        if let Value::Float(x) = x {
            Ok(Value::Float(x.tan()))
        } else {
            Err(Error::RuntimeError(
                "Argument to operator were of the wrong type".into(),
            ))
        }
    }
}
