import LeanMLIR.Framework
import LeanMLIR.Util
import LeanMLIR.Tactic.SimpSet
import LeanMLIR.Basic


namespace Builtin

inductive Shape
  | scalar
  | vector : List Nat -> Shape -- for instance 3x4 vector. Hence the list
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

inductive IntType
  | int : Nat -> IntType -- ex: i32, i64
--| index : Nat -> IntType
--| uint : Nat -> IntType
--| sint : Nat -> IntType
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

-- From the mlir spec:
-- "Attributes are the mechanism for specifying constant data on operations
-- in places where a variable is never allowed"
inductive attr
  | intlit (lit : Nat) (width : Nat)

inductive Scalar
  | int : IntType -> Scalar
--| float : FloatType -> S
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

inductive Ty
  | shaped : Shape -> Scalar -> Ty
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

structure ShapedInt where
  shape : Shape
  val : IntType
  deriving DecidableEq, Inhabited, Lean.ToExpr, Repr

def ShapedInt.toTy (t : ShapedInt) : Ty := .shaped t.shape (.int (t.val))

def IntType.width : IntType -> Nat
  | .int w => w
